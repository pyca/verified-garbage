// The functions of `src/internal/vg_blake2b_compress_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_compress_avx512:
	mov r8d, r8d
	movabs rax, 7640891576956012808
	vmovq xmm11, rax
	movabs rax, -4942790177534073029
	vmovq xmm13, rax
	vpunpcklqdq xmm11, xmm11, xmm13
	movabs rax, 4354685564936845355
	vmovq xmm10, rax
	movabs rax, -6534734903238641935
	vmovq xmm13, rax
	vpunpcklqdq xmm10, xmm10, xmm13
	vinserti128 ymm11, ymm11, xmm10, 1
	movabs rax, 5840696475078001361
	vmovq xmm12, rax
	movabs rax, -7276294671716946913
	vmovq xmm13, rax
	vpunpcklqdq xmm12, xmm12, xmm13
	movabs rax, 2270897969802886507
	vmovq xmm10, rax
	movabs rax, 6620516959819538809
	vmovq xmm13, rax
	vpunpcklqdq xmm10, xmm10, xmm13
	vinserti128 ymm12, ymm12, xmm10, 1
	mov eax, 0
	test r8, r8
	je 20f
	mov r8, -1
	jmp 21f
20:
21:
	test rdx, rdx
	je 22f
24:
	vmovdqu ymm0, YMMWORD PTR [rdi]
	vmovdqu ymm1, YMMWORD PTR [rdi+32]
	vmovdqa ymm2, ymm11
	vmovq xmm13, rcx
	vmovq xmm4, rax
	vpunpcklqdq xmm13, xmm13, xmm4
	vmovq xmm4, r8
	vinserti128 ymm13, ymm13, xmm4, 1
	vpxor ymm3, ymm12, ymm13
	vbroadcasti128 ymm5, XMMWORD PTR [rsi]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+8]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+32]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+40]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+8]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+16]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+40]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+48]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+112]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+56]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+80]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+88]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+112]
	vpshufd ymm5, ymm5, 78
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+64]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+88]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+96]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+112]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+24]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+72]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+96]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+80]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+56]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+112]
	vpshufd ymm7, ymm7, 78
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+40]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+40]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+80]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+24]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+88]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+16]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+48]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+88]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+88]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+40]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+112]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+64]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi]
	vpshufd ymm6, ymm6, 78
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+16]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+96]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+72]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+72]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+24]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+48]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+32]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+104]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+48]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+56]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+16]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+104]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+80]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+72]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+96]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+104]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+112]
	vpshufd ymm5, ymm5, 78
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+8]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+40]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+24]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+64]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+40]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+80]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi]
	vpshufd ymm8, ymm8, 78
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+72]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+32]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+16]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+72]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+48]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+32]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+112]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+24]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+104]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+88]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+40]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+104]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+96]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+56]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+16]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+40]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+56]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+96]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+72]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+88]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+16]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+8]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+24]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+56]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+112]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+72]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+96]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+40]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+104]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+96]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+112]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+24]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+40]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+112]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+104]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+72]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+64]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi]
	vpshufd ymm6, ymm6, 78
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+48]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+64]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+88]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+48]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+24]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+8]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+104]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+48]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+96]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+16]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+88]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+104]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+8]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+64]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+16]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+32]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+112]
	vpshufd ymm7, ymm7, 78
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+56]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+80]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi]
	vpshufd ymm6, ymm6, 78
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+32]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+40]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+48]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+104]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+88]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi]
	vpshufd ymm8, ymm8, 78
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+112]
	vpshufd ymm5, ymm5, 78
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+64]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+24]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+56]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+80]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+88]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+104]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+40]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+8]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+56]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+24]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+80]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+56]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+56]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+16]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+24]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+48]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+32]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+104]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+112]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+72]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+16]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+80]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+112]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+88]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+8]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+32]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+40]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+8]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+16]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+40]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+48]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+112]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+56]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+80]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+88]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+112]
	vpshufd ymm5, ymm5, 78
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+64]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+88]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+96]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+112]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+24]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+72]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+96]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+80]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+56]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+112]
	vpshufd ymm7, ymm7, 78
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+40]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 147
	vpermq ymm2, ymm2, 57
	vpermq ymm3, ymm3, 78
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+40]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+80]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 32
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 24
	vbroadcasti128 ymm5, XMMWORD PTR [rsi+24]
	vbroadcasti128 ymm6, XMMWORD PTR [rsi+88]
	vpblendd ymm5, ymm5, ymm6, 12
	vbroadcasti128 ymm7, XMMWORD PTR [rsi+16]
	vbroadcasti128 ymm8, XMMWORD PTR [rsi+48]
	vpblendd ymm7, ymm7, ymm8, 192
	vpblendd ymm5, ymm5, ymm7, 240
	vpaddq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm1
	vpxor ymm3, ymm3, ymm0
	vprorq ymm3, ymm3, 16
	vpaddq ymm2, ymm2, ymm3
	vpxor ymm1, ymm1, ymm2
	vprorq ymm1, ymm1, 63
	vpermq ymm0, ymm0, 57
	vpermq ymm2, ymm2, 147
	vpermq ymm3, ymm3, 78
	vpxor ymm0, ymm0, ymm2
	vpxor ymm1, ymm1, ymm3
	vmovdqu ymm4, YMMWORD PTR [rdi]
	vpxor ymm0, ymm0, ymm4
	vmovdqu YMMWORD PTR [rdi], ymm0
	vmovdqu ymm4, YMMWORD PTR [rdi+32]
	vpxor ymm1, ymm1, ymm4
	vmovdqu YMMWORD PTR [rdi+32], ymm1
	add rsi, 128
	add rcx, 128
	adc rax, 0
	sub rdx, 1
	jne 24b
	jmp 23f
22:
23:
	vzeroupper
	ret
	.p2align 6
