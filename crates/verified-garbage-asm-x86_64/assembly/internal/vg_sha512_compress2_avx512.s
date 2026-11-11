// The functions of `src/internal/vg_sha512_compress2_avx512.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress2_avx512:
	movabs rax, 283686952306183
	vmovq xmm15, rax
	movabs rax, 579005069656919567
	vmovq xmm13, rax
	vpunpcklqdq xmm15, xmm15, xmm13
	vinserti128 ymm15, ymm15, xmm15, 1
	vmovdqu xmm8, XMMWORD PTR [rdi]
	vmovdqu xmm9, XMMWORD PTR [rdx]
	vpunpcklqdq xmm0, xmm8, xmm9
	vpunpckhqdq xmm1, xmm8, xmm9
	vmovdqu xmm8, XMMWORD PTR [rdi+16]
	vmovdqu xmm9, XMMWORD PTR [rdx+16]
	vpunpcklqdq xmm2, xmm8, xmm9
	vpunpckhqdq xmm3, xmm8, xmm9
	vmovdqu xmm8, XMMWORD PTR [rdi+32]
	vmovdqu xmm9, XMMWORD PTR [rdx+32]
	vpunpcklqdq xmm4, xmm8, xmm9
	vpunpckhqdq xmm5, xmm8, xmm9
	vmovdqu xmm8, XMMWORD PTR [rdi+48]
	vmovdqu xmm9, XMMWORD PTR [rdx+48]
	vpunpcklqdq xmm6, xmm8, xmm9
	vpunpckhqdq xmm7, xmm8, xmm9
	lea rax, {VG_SHA512_K2}
	mov r9, 0
	vmovdqu xmm12, XMMWORD PTR [rsi]
	vmovdqu xmm13, XMMWORD PTR [rcx]
	vinserti128 ymm12, ymm12, xmm13, 1
	vpshufb ymm12, ymm12, ymm15
	vpermq ymm12, ymm12, 216
	vmovdqu YMMWORD PTR [r8+r9*1], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm4, 14
	vprorq xmm9, xmm4, 18
	vprorq xmm10, xmm4, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm4
	vpternlogd xmm9, xmm5, xmm6, 202
	vpaddq xmm7, xmm7, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm7, xmm7, xmm8
	vpaddq xmm3, xmm3, xmm7
	vprorq xmm8, xmm0, 28
	vprorq xmm9, xmm0, 34
	vprorq xmm10, xmm0, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm0
	vpternlogd xmm9, xmm1, xmm2, 232
	vpaddq xmm7, xmm7, xmm8
	vpaddq xmm7, xmm7, xmm9
	vprorq xmm8, xmm3, 14
	vprorq xmm9, xmm3, 18
	vprorq xmm10, xmm3, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm3
	vpternlogd xmm9, xmm4, xmm5, 202
	vpaddq xmm6, xmm6, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm6, xmm6, xmm8
	vpaddq xmm2, xmm2, xmm6
	vprorq xmm8, xmm7, 28
	vprorq xmm9, xmm7, 34
	vprorq xmm10, xmm7, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm7
	vpternlogd xmm9, xmm0, xmm1, 232
	vpaddq xmm6, xmm6, xmm8
	vpaddq xmm6, xmm6, xmm9
	vmovdqu xmm12, XMMWORD PTR [rsi+16]
	vmovdqu xmm13, XMMWORD PTR [rcx+16]
	vinserti128 ymm12, ymm12, xmm13, 1
	vpshufb ymm12, ymm12, ymm15
	vpermq ymm12, ymm12, 216
	vmovdqu YMMWORD PTR [r8+r9*1+32], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+32]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm2, 14
	vprorq xmm9, xmm2, 18
	vprorq xmm10, xmm2, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm2
	vpternlogd xmm9, xmm3, xmm4, 202
	vpaddq xmm5, xmm5, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm5, xmm5, xmm8
	vpaddq xmm1, xmm1, xmm5
	vprorq xmm8, xmm6, 28
	vprorq xmm9, xmm6, 34
	vprorq xmm10, xmm6, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm6
	vpternlogd xmm9, xmm7, xmm0, 232
	vpaddq xmm5, xmm5, xmm8
	vpaddq xmm5, xmm5, xmm9
	vprorq xmm8, xmm1, 14
	vprorq xmm9, xmm1, 18
	vprorq xmm10, xmm1, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm1
	vpternlogd xmm9, xmm2, xmm3, 202
	vpaddq xmm4, xmm4, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm4, xmm4, xmm8
	vpaddq xmm0, xmm0, xmm4
	vprorq xmm8, xmm5, 28
	vprorq xmm9, xmm5, 34
	vprorq xmm10, xmm5, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm5
	vpternlogd xmm9, xmm6, xmm7, 232
	vpaddq xmm4, xmm4, xmm8
	vpaddq xmm4, xmm4, xmm9
	vmovdqu xmm12, XMMWORD PTR [rsi+32]
	vmovdqu xmm13, XMMWORD PTR [rcx+32]
	vinserti128 ymm12, ymm12, xmm13, 1
	vpshufb ymm12, ymm12, ymm15
	vpermq ymm12, ymm12, 216
	vmovdqu YMMWORD PTR [r8+r9*1+64], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+64]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm0, 14
	vprorq xmm9, xmm0, 18
	vprorq xmm10, xmm0, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm0
	vpternlogd xmm9, xmm1, xmm2, 202
	vpaddq xmm3, xmm3, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm3, xmm3, xmm8
	vpaddq xmm7, xmm7, xmm3
	vprorq xmm8, xmm4, 28
	vprorq xmm9, xmm4, 34
	vprorq xmm10, xmm4, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm4
	vpternlogd xmm9, xmm5, xmm6, 232
	vpaddq xmm3, xmm3, xmm8
	vpaddq xmm3, xmm3, xmm9
	vprorq xmm8, xmm7, 14
	vprorq xmm9, xmm7, 18
	vprorq xmm10, xmm7, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm7
	vpternlogd xmm9, xmm0, xmm1, 202
	vpaddq xmm2, xmm2, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm2, xmm2, xmm8
	vpaddq xmm6, xmm6, xmm2
	vprorq xmm8, xmm3, 28
	vprorq xmm9, xmm3, 34
	vprorq xmm10, xmm3, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm3
	vpternlogd xmm9, xmm4, xmm5, 232
	vpaddq xmm2, xmm2, xmm8
	vpaddq xmm2, xmm2, xmm9
	vmovdqu xmm12, XMMWORD PTR [rsi+48]
	vmovdqu xmm13, XMMWORD PTR [rcx+48]
	vinserti128 ymm12, ymm12, xmm13, 1
	vpshufb ymm12, ymm12, ymm15
	vpermq ymm12, ymm12, 216
	vmovdqu YMMWORD PTR [r8+r9*1+96], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+96]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm6, 14
	vprorq xmm9, xmm6, 18
	vprorq xmm10, xmm6, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm6
	vpternlogd xmm9, xmm7, xmm0, 202
	vpaddq xmm1, xmm1, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm1, xmm1, xmm8
	vpaddq xmm5, xmm5, xmm1
	vprorq xmm8, xmm2, 28
	vprorq xmm9, xmm2, 34
	vprorq xmm10, xmm2, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm2
	vpternlogd xmm9, xmm3, xmm4, 232
	vpaddq xmm1, xmm1, xmm8
	vpaddq xmm1, xmm1, xmm9
	vprorq xmm8, xmm5, 14
	vprorq xmm9, xmm5, 18
	vprorq xmm10, xmm5, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm5
	vpternlogd xmm9, xmm6, xmm7, 202
	vpaddq xmm0, xmm0, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm0, xmm0, xmm8
	vpaddq xmm4, xmm4, xmm0
	vprorq xmm8, xmm1, 28
	vprorq xmm9, xmm1, 34
	vprorq xmm10, xmm1, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm1
	vpternlogd xmm9, xmm2, xmm3, 232
	vpaddq xmm0, xmm0, xmm8
	vpaddq xmm0, xmm0, xmm9
	vmovdqu xmm12, XMMWORD PTR [rsi+64]
	vmovdqu xmm13, XMMWORD PTR [rcx+64]
	vinserti128 ymm12, ymm12, xmm13, 1
	vpshufb ymm12, ymm12, ymm15
	vpermq ymm12, ymm12, 216
	vmovdqu YMMWORD PTR [r8+r9*1+128], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+128]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm4, 14
	vprorq xmm9, xmm4, 18
	vprorq xmm10, xmm4, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm4
	vpternlogd xmm9, xmm5, xmm6, 202
	vpaddq xmm7, xmm7, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm7, xmm7, xmm8
	vpaddq xmm3, xmm3, xmm7
	vprorq xmm8, xmm0, 28
	vprorq xmm9, xmm0, 34
	vprorq xmm10, xmm0, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm0
	vpternlogd xmm9, xmm1, xmm2, 232
	vpaddq xmm7, xmm7, xmm8
	vpaddq xmm7, xmm7, xmm9
	vprorq xmm8, xmm3, 14
	vprorq xmm9, xmm3, 18
	vprorq xmm10, xmm3, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm3
	vpternlogd xmm9, xmm4, xmm5, 202
	vpaddq xmm6, xmm6, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm6, xmm6, xmm8
	vpaddq xmm2, xmm2, xmm6
	vprorq xmm8, xmm7, 28
	vprorq xmm9, xmm7, 34
	vprorq xmm10, xmm7, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm7
	vpternlogd xmm9, xmm0, xmm1, 232
	vpaddq xmm6, xmm6, xmm8
	vpaddq xmm6, xmm6, xmm9
	vmovdqu xmm12, XMMWORD PTR [rsi+80]
	vmovdqu xmm13, XMMWORD PTR [rcx+80]
	vinserti128 ymm12, ymm12, xmm13, 1
	vpshufb ymm12, ymm12, ymm15
	vpermq ymm12, ymm12, 216
	vmovdqu YMMWORD PTR [r8+r9*1+160], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+160]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm2, 14
	vprorq xmm9, xmm2, 18
	vprorq xmm10, xmm2, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm2
	vpternlogd xmm9, xmm3, xmm4, 202
	vpaddq xmm5, xmm5, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm5, xmm5, xmm8
	vpaddq xmm1, xmm1, xmm5
	vprorq xmm8, xmm6, 28
	vprorq xmm9, xmm6, 34
	vprorq xmm10, xmm6, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm6
	vpternlogd xmm9, xmm7, xmm0, 232
	vpaddq xmm5, xmm5, xmm8
	vpaddq xmm5, xmm5, xmm9
	vprorq xmm8, xmm1, 14
	vprorq xmm9, xmm1, 18
	vprorq xmm10, xmm1, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm1
	vpternlogd xmm9, xmm2, xmm3, 202
	vpaddq xmm4, xmm4, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm4, xmm4, xmm8
	vpaddq xmm0, xmm0, xmm4
	vprorq xmm8, xmm5, 28
	vprorq xmm9, xmm5, 34
	vprorq xmm10, xmm5, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm5
	vpternlogd xmm9, xmm6, xmm7, 232
	vpaddq xmm4, xmm4, xmm8
	vpaddq xmm4, xmm4, xmm9
	vmovdqu xmm12, XMMWORD PTR [rsi+96]
	vmovdqu xmm13, XMMWORD PTR [rcx+96]
	vinserti128 ymm12, ymm12, xmm13, 1
	vpshufb ymm12, ymm12, ymm15
	vpermq ymm12, ymm12, 216
	vmovdqu YMMWORD PTR [r8+r9*1+192], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+192]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm0, 14
	vprorq xmm9, xmm0, 18
	vprorq xmm10, xmm0, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm0
	vpternlogd xmm9, xmm1, xmm2, 202
	vpaddq xmm3, xmm3, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm3, xmm3, xmm8
	vpaddq xmm7, xmm7, xmm3
	vprorq xmm8, xmm4, 28
	vprorq xmm9, xmm4, 34
	vprorq xmm10, xmm4, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm4
	vpternlogd xmm9, xmm5, xmm6, 232
	vpaddq xmm3, xmm3, xmm8
	vpaddq xmm3, xmm3, xmm9
	vprorq xmm8, xmm7, 14
	vprorq xmm9, xmm7, 18
	vprorq xmm10, xmm7, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm7
	vpternlogd xmm9, xmm0, xmm1, 202
	vpaddq xmm2, xmm2, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm2, xmm2, xmm8
	vpaddq xmm6, xmm6, xmm2
	vprorq xmm8, xmm3, 28
	vprorq xmm9, xmm3, 34
	vprorq xmm10, xmm3, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm3
	vpternlogd xmm9, xmm4, xmm5, 232
	vpaddq xmm2, xmm2, xmm8
	vpaddq xmm2, xmm2, xmm9
	vmovdqu xmm12, XMMWORD PTR [rsi+112]
	vmovdqu xmm13, XMMWORD PTR [rcx+112]
	vinserti128 ymm12, ymm12, xmm13, 1
	vpshufb ymm12, ymm12, ymm15
	vpermq ymm12, ymm12, 216
	vmovdqu YMMWORD PTR [r8+r9*1+224], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+224]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm6, 14
	vprorq xmm9, xmm6, 18
	vprorq xmm10, xmm6, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm6
	vpternlogd xmm9, xmm7, xmm0, 202
	vpaddq xmm1, xmm1, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm1, xmm1, xmm8
	vpaddq xmm5, xmm5, xmm1
	vprorq xmm8, xmm2, 28
	vprorq xmm9, xmm2, 34
	vprorq xmm10, xmm2, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm2
	vpternlogd xmm9, xmm3, xmm4, 232
	vpaddq xmm1, xmm1, xmm8
	vpaddq xmm1, xmm1, xmm9
	vprorq xmm8, xmm5, 14
	vprorq xmm9, xmm5, 18
	vprorq xmm10, xmm5, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm5
	vpternlogd xmm9, xmm6, xmm7, 202
	vpaddq xmm0, xmm0, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm0, xmm0, xmm8
	vpaddq xmm4, xmm4, xmm0
	vprorq xmm8, xmm1, 28
	vprorq xmm9, xmm1, 34
	vprorq xmm10, xmm1, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm1
	vpternlogd xmm9, xmm2, xmm3, 232
	vpaddq xmm0, xmm0, xmm8
	vpaddq xmm0, xmm0, xmm9
	add r9, 256
	cmp r9, 1280
20:
	vmovdqu ymm12, YMMWORD PTR [r8+r9*1-240]
	vmovdqu ymm13, YMMWORD PTR [r8+r9*1-32]
	vprorq ymm8, ymm12, 1
	vprorq ymm9, ymm12, 8
	vpsrlq ymm12, ymm12, 7
	vpternlogd ymm12, ymm8, ymm9, 150
	vprorq ymm8, ymm13, 19
	vprorq ymm9, ymm13, 61
	vpsrlq ymm13, ymm13, 6
	vpternlogd ymm13, ymm8, ymm9, 150
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-256]
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-112]
	vpaddq ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [r8+r9*1], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm4, 14
	vprorq xmm9, xmm4, 18
	vprorq xmm10, xmm4, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm4
	vpternlogd xmm9, xmm5, xmm6, 202
	vpaddq xmm7, xmm7, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm7, xmm7, xmm8
	vpaddq xmm3, xmm3, xmm7
	vprorq xmm8, xmm0, 28
	vprorq xmm9, xmm0, 34
	vprorq xmm10, xmm0, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm0
	vpternlogd xmm9, xmm1, xmm2, 232
	vpaddq xmm7, xmm7, xmm8
	vpaddq xmm7, xmm7, xmm9
	vprorq xmm8, xmm3, 14
	vprorq xmm9, xmm3, 18
	vprorq xmm10, xmm3, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm3
	vpternlogd xmm9, xmm4, xmm5, 202
	vpaddq xmm6, xmm6, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm6, xmm6, xmm8
	vpaddq xmm2, xmm2, xmm6
	vprorq xmm8, xmm7, 28
	vprorq xmm9, xmm7, 34
	vprorq xmm10, xmm7, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm7
	vpternlogd xmm9, xmm0, xmm1, 232
	vpaddq xmm6, xmm6, xmm8
	vpaddq xmm6, xmm6, xmm9
	vmovdqu ymm12, YMMWORD PTR [r8+r9*1-208]
	vmovdqu ymm13, YMMWORD PTR [r8+r9*1]
	vprorq ymm8, ymm12, 1
	vprorq ymm9, ymm12, 8
	vpsrlq ymm12, ymm12, 7
	vpternlogd ymm12, ymm8, ymm9, 150
	vprorq ymm8, ymm13, 19
	vprorq ymm9, ymm13, 61
	vpsrlq ymm13, ymm13, 6
	vpternlogd ymm13, ymm8, ymm9, 150
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-224]
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-80]
	vpaddq ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [r8+r9*1+32], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+32]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm2, 14
	vprorq xmm9, xmm2, 18
	vprorq xmm10, xmm2, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm2
	vpternlogd xmm9, xmm3, xmm4, 202
	vpaddq xmm5, xmm5, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm5, xmm5, xmm8
	vpaddq xmm1, xmm1, xmm5
	vprorq xmm8, xmm6, 28
	vprorq xmm9, xmm6, 34
	vprorq xmm10, xmm6, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm6
	vpternlogd xmm9, xmm7, xmm0, 232
	vpaddq xmm5, xmm5, xmm8
	vpaddq xmm5, xmm5, xmm9
	vprorq xmm8, xmm1, 14
	vprorq xmm9, xmm1, 18
	vprorq xmm10, xmm1, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm1
	vpternlogd xmm9, xmm2, xmm3, 202
	vpaddq xmm4, xmm4, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm4, xmm4, xmm8
	vpaddq xmm0, xmm0, xmm4
	vprorq xmm8, xmm5, 28
	vprorq xmm9, xmm5, 34
	vprorq xmm10, xmm5, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm5
	vpternlogd xmm9, xmm6, xmm7, 232
	vpaddq xmm4, xmm4, xmm8
	vpaddq xmm4, xmm4, xmm9
	vmovdqu ymm12, YMMWORD PTR [r8+r9*1-176]
	vmovdqu ymm13, YMMWORD PTR [r8+r9*1+32]
	vprorq ymm8, ymm12, 1
	vprorq ymm9, ymm12, 8
	vpsrlq ymm12, ymm12, 7
	vpternlogd ymm12, ymm8, ymm9, 150
	vprorq ymm8, ymm13, 19
	vprorq ymm9, ymm13, 61
	vpsrlq ymm13, ymm13, 6
	vpternlogd ymm13, ymm8, ymm9, 150
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-192]
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-48]
	vpaddq ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [r8+r9*1+64], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+64]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm0, 14
	vprorq xmm9, xmm0, 18
	vprorq xmm10, xmm0, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm0
	vpternlogd xmm9, xmm1, xmm2, 202
	vpaddq xmm3, xmm3, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm3, xmm3, xmm8
	vpaddq xmm7, xmm7, xmm3
	vprorq xmm8, xmm4, 28
	vprorq xmm9, xmm4, 34
	vprorq xmm10, xmm4, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm4
	vpternlogd xmm9, xmm5, xmm6, 232
	vpaddq xmm3, xmm3, xmm8
	vpaddq xmm3, xmm3, xmm9
	vprorq xmm8, xmm7, 14
	vprorq xmm9, xmm7, 18
	vprorq xmm10, xmm7, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm7
	vpternlogd xmm9, xmm0, xmm1, 202
	vpaddq xmm2, xmm2, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm2, xmm2, xmm8
	vpaddq xmm6, xmm6, xmm2
	vprorq xmm8, xmm3, 28
	vprorq xmm9, xmm3, 34
	vprorq xmm10, xmm3, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm3
	vpternlogd xmm9, xmm4, xmm5, 232
	vpaddq xmm2, xmm2, xmm8
	vpaddq xmm2, xmm2, xmm9
	vmovdqu ymm12, YMMWORD PTR [r8+r9*1-144]
	vmovdqu ymm13, YMMWORD PTR [r8+r9*1+64]
	vprorq ymm8, ymm12, 1
	vprorq ymm9, ymm12, 8
	vpsrlq ymm12, ymm12, 7
	vpternlogd ymm12, ymm8, ymm9, 150
	vprorq ymm8, ymm13, 19
	vprorq ymm9, ymm13, 61
	vpsrlq ymm13, ymm13, 6
	vpternlogd ymm13, ymm8, ymm9, 150
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-160]
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-16]
	vpaddq ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [r8+r9*1+96], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+96]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm6, 14
	vprorq xmm9, xmm6, 18
	vprorq xmm10, xmm6, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm6
	vpternlogd xmm9, xmm7, xmm0, 202
	vpaddq xmm1, xmm1, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm1, xmm1, xmm8
	vpaddq xmm5, xmm5, xmm1
	vprorq xmm8, xmm2, 28
	vprorq xmm9, xmm2, 34
	vprorq xmm10, xmm2, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm2
	vpternlogd xmm9, xmm3, xmm4, 232
	vpaddq xmm1, xmm1, xmm8
	vpaddq xmm1, xmm1, xmm9
	vprorq xmm8, xmm5, 14
	vprorq xmm9, xmm5, 18
	vprorq xmm10, xmm5, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm5
	vpternlogd xmm9, xmm6, xmm7, 202
	vpaddq xmm0, xmm0, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm0, xmm0, xmm8
	vpaddq xmm4, xmm4, xmm0
	vprorq xmm8, xmm1, 28
	vprorq xmm9, xmm1, 34
	vprorq xmm10, xmm1, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm1
	vpternlogd xmm9, xmm2, xmm3, 232
	vpaddq xmm0, xmm0, xmm8
	vpaddq xmm0, xmm0, xmm9
	vmovdqu ymm12, YMMWORD PTR [r8+r9*1-112]
	vmovdqu ymm13, YMMWORD PTR [r8+r9*1+96]
	vprorq ymm8, ymm12, 1
	vprorq ymm9, ymm12, 8
	vpsrlq ymm12, ymm12, 7
	vpternlogd ymm12, ymm8, ymm9, 150
	vprorq ymm8, ymm13, 19
	vprorq ymm9, ymm13, 61
	vpsrlq ymm13, ymm13, 6
	vpternlogd ymm13, ymm8, ymm9, 150
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-128]
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1+16]
	vpaddq ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [r8+r9*1+128], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+128]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm4, 14
	vprorq xmm9, xmm4, 18
	vprorq xmm10, xmm4, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm4
	vpternlogd xmm9, xmm5, xmm6, 202
	vpaddq xmm7, xmm7, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm7, xmm7, xmm8
	vpaddq xmm3, xmm3, xmm7
	vprorq xmm8, xmm0, 28
	vprorq xmm9, xmm0, 34
	vprorq xmm10, xmm0, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm0
	vpternlogd xmm9, xmm1, xmm2, 232
	vpaddq xmm7, xmm7, xmm8
	vpaddq xmm7, xmm7, xmm9
	vprorq xmm8, xmm3, 14
	vprorq xmm9, xmm3, 18
	vprorq xmm10, xmm3, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm3
	vpternlogd xmm9, xmm4, xmm5, 202
	vpaddq xmm6, xmm6, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm6, xmm6, xmm8
	vpaddq xmm2, xmm2, xmm6
	vprorq xmm8, xmm7, 28
	vprorq xmm9, xmm7, 34
	vprorq xmm10, xmm7, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm7
	vpternlogd xmm9, xmm0, xmm1, 232
	vpaddq xmm6, xmm6, xmm8
	vpaddq xmm6, xmm6, xmm9
	vmovdqu ymm12, YMMWORD PTR [r8+r9*1-80]
	vmovdqu ymm13, YMMWORD PTR [r8+r9*1+128]
	vprorq ymm8, ymm12, 1
	vprorq ymm9, ymm12, 8
	vpsrlq ymm12, ymm12, 7
	vpternlogd ymm12, ymm8, ymm9, 150
	vprorq ymm8, ymm13, 19
	vprorq ymm9, ymm13, 61
	vpsrlq ymm13, ymm13, 6
	vpternlogd ymm13, ymm8, ymm9, 150
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-96]
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1+48]
	vpaddq ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [r8+r9*1+160], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+160]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm2, 14
	vprorq xmm9, xmm2, 18
	vprorq xmm10, xmm2, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm2
	vpternlogd xmm9, xmm3, xmm4, 202
	vpaddq xmm5, xmm5, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm5, xmm5, xmm8
	vpaddq xmm1, xmm1, xmm5
	vprorq xmm8, xmm6, 28
	vprorq xmm9, xmm6, 34
	vprorq xmm10, xmm6, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm6
	vpternlogd xmm9, xmm7, xmm0, 232
	vpaddq xmm5, xmm5, xmm8
	vpaddq xmm5, xmm5, xmm9
	vprorq xmm8, xmm1, 14
	vprorq xmm9, xmm1, 18
	vprorq xmm10, xmm1, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm1
	vpternlogd xmm9, xmm2, xmm3, 202
	vpaddq xmm4, xmm4, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm4, xmm4, xmm8
	vpaddq xmm0, xmm0, xmm4
	vprorq xmm8, xmm5, 28
	vprorq xmm9, xmm5, 34
	vprorq xmm10, xmm5, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm5
	vpternlogd xmm9, xmm6, xmm7, 232
	vpaddq xmm4, xmm4, xmm8
	vpaddq xmm4, xmm4, xmm9
	vmovdqu ymm12, YMMWORD PTR [r8+r9*1-48]
	vmovdqu ymm13, YMMWORD PTR [r8+r9*1+160]
	vprorq ymm8, ymm12, 1
	vprorq ymm9, ymm12, 8
	vpsrlq ymm12, ymm12, 7
	vpternlogd ymm12, ymm8, ymm9, 150
	vprorq ymm8, ymm13, 19
	vprorq ymm9, ymm13, 61
	vpsrlq ymm13, ymm13, 6
	vpternlogd ymm13, ymm8, ymm9, 150
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-64]
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1+80]
	vpaddq ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [r8+r9*1+192], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+192]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm0, 14
	vprorq xmm9, xmm0, 18
	vprorq xmm10, xmm0, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm0
	vpternlogd xmm9, xmm1, xmm2, 202
	vpaddq xmm3, xmm3, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm3, xmm3, xmm8
	vpaddq xmm7, xmm7, xmm3
	vprorq xmm8, xmm4, 28
	vprorq xmm9, xmm4, 34
	vprorq xmm10, xmm4, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm4
	vpternlogd xmm9, xmm5, xmm6, 232
	vpaddq xmm3, xmm3, xmm8
	vpaddq xmm3, xmm3, xmm9
	vprorq xmm8, xmm7, 14
	vprorq xmm9, xmm7, 18
	vprorq xmm10, xmm7, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm7
	vpternlogd xmm9, xmm0, xmm1, 202
	vpaddq xmm2, xmm2, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm2, xmm2, xmm8
	vpaddq xmm6, xmm6, xmm2
	vprorq xmm8, xmm3, 28
	vprorq xmm9, xmm3, 34
	vprorq xmm10, xmm3, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm3
	vpternlogd xmm9, xmm4, xmm5, 232
	vpaddq xmm2, xmm2, xmm8
	vpaddq xmm2, xmm2, xmm9
	vmovdqu ymm12, YMMWORD PTR [r8+r9*1-16]
	vmovdqu ymm13, YMMWORD PTR [r8+r9*1+192]
	vprorq ymm8, ymm12, 1
	vprorq ymm9, ymm12, 8
	vpsrlq ymm12, ymm12, 7
	vpternlogd ymm12, ymm8, ymm9, 150
	vprorq ymm8, ymm13, 19
	vprorq ymm9, ymm13, 61
	vpsrlq ymm13, ymm13, 6
	vpternlogd ymm13, ymm8, ymm9, 150
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1-32]
	vpaddq ymm12, ymm12, YMMWORD PTR [r8+r9*1+112]
	vpaddq ymm12, ymm12, ymm13
	vmovdqu YMMWORD PTR [r8+r9*1+224], ymm12
	vmovdqu ymm13, YMMWORD PTR [rax+r9*1+224]
	vpaddq ymm12, ymm12, ymm13
	vextracti128 xmm13, ymm12, 1
	vprorq xmm8, xmm6, 14
	vprorq xmm9, xmm6, 18
	vprorq xmm10, xmm6, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm6
	vpternlogd xmm9, xmm7, xmm0, 202
	vpaddq xmm1, xmm1, xmm12
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm1, xmm1, xmm8
	vpaddq xmm5, xmm5, xmm1
	vprorq xmm8, xmm2, 28
	vprorq xmm9, xmm2, 34
	vprorq xmm10, xmm2, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm2
	vpternlogd xmm9, xmm3, xmm4, 232
	vpaddq xmm1, xmm1, xmm8
	vpaddq xmm1, xmm1, xmm9
	vprorq xmm8, xmm5, 14
	vprorq xmm9, xmm5, 18
	vprorq xmm10, xmm5, 41
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm5
	vpternlogd xmm9, xmm6, xmm7, 202
	vpaddq xmm0, xmm0, xmm13
	vpaddq xmm8, xmm8, xmm9
	vpaddq xmm0, xmm0, xmm8
	vpaddq xmm4, xmm4, xmm0
	vprorq xmm8, xmm1, 28
	vprorq xmm9, xmm1, 34
	vprorq xmm10, xmm1, 39
	vpternlogd xmm8, xmm9, xmm10, 150
	vmovdqa xmm9, xmm1
	vpternlogd xmm9, xmm2, xmm3, 232
	vpaddq xmm0, xmm0, xmm8
	vpaddq xmm0, xmm0, xmm9
	add r9, 256
	cmp r9, 1280
	jne 20b
	vpunpcklqdq xmm8, xmm0, xmm1
	vpunpckhqdq xmm9, xmm0, xmm1
	vpaddq xmm8, xmm8, XMMWORD PTR [rdi]
	vpaddq xmm9, xmm9, XMMWORD PTR [rdx]
	vmovdqu XMMWORD PTR [rdi], xmm8
	vmovdqu XMMWORD PTR [rdx], xmm9
	vpunpcklqdq xmm8, xmm2, xmm3
	vpunpckhqdq xmm9, xmm2, xmm3
	vpaddq xmm8, xmm8, XMMWORD PTR [rdi+16]
	vpaddq xmm9, xmm9, XMMWORD PTR [rdx+16]
	vmovdqu XMMWORD PTR [rdi+16], xmm8
	vmovdqu XMMWORD PTR [rdx+16], xmm9
	vpunpcklqdq xmm8, xmm4, xmm5
	vpunpckhqdq xmm9, xmm4, xmm5
	vpaddq xmm8, xmm8, XMMWORD PTR [rdi+32]
	vpaddq xmm9, xmm9, XMMWORD PTR [rdx+32]
	vmovdqu XMMWORD PTR [rdi+32], xmm8
	vmovdqu XMMWORD PTR [rdx+32], xmm9
	vpunpcklqdq xmm8, xmm6, xmm7
	vpunpckhqdq xmm9, xmm6, xmm7
	vpaddq xmm8, xmm8, XMMWORD PTR [rdi+48]
	vpaddq xmm9, xmm9, XMMWORD PTR [rdx+48]
	vmovdqu XMMWORD PTR [rdi+48], xmm8
	vmovdqu XMMWORD PTR [rdx+48], xmm9
	vzeroupper
	ret
	.p2align 6
