// The functions of `src/internal/vg_sha512_compress_shani.rs` of `verified-garbage-asm-x86_64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress_shani:
	movabs rax, 283686952306183
	vmovq xmm8, rax
	movabs rax, 579005069656919567
	vmovq xmm11, rax
	vpunpcklqdq xmm8, xmm8, xmm11
	vinserti128 ymm8, ymm8, xmm8, 1
	lea rax, {VG_SHA512_K}
	vmovdqu ymm1, YMMWORD PTR [rdi]
	vmovdqu ymm2, YMMWORD PTR [rdi+32]
	vperm2i128 ymm7, ymm2, ymm1, 32
	vperm2i128 ymm2, ymm2, ymm1, 49
	vpermq ymm1, ymm7, 177
	vpermq ymm2, ymm2, 177
	test rdx, rdx
	je 20f
22:
	vmovdqa ymm9, ymm1
	vmovdqa ymm10, ymm2
	vmovdqu ymm3, YMMWORD PTR [rsi]
	vpshufb ymm3, ymm3, ymm8
	vmovdqu ymm0, YMMWORD PTR [rax]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vmovdqu ymm4, YMMWORD PTR [rsi+32]
	vpshufb ymm4, ymm4, ymm8
	vmovdqu ymm0, YMMWORD PTR [rax+32]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vmovdqu ymm5, YMMWORD PTR [rsi+64]
	vpshufb ymm5, ymm5, ymm8
	vmovdqu ymm0, YMMWORD PTR [rax+64]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vmovdqu ymm6, YMMWORD PTR [rsi+96]
	vpshufb ymm6, ymm6, ymm8
	vmovdqu ymm0, YMMWORD PTR [rax+96]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm3, xmm4
	vperm2i128 ymm7, ymm5, ymm6, 33
	vpalignr ymm7, ymm7, ymm5, 8
	vpaddq ymm3, ymm3, ymm7
	vsha512msg2 ymm3, ymm6
	vmovdqu ymm0, YMMWORD PTR [rax+128]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm4, xmm5
	vperm2i128 ymm7, ymm6, ymm3, 33
	vpalignr ymm7, ymm7, ymm6, 8
	vpaddq ymm4, ymm4, ymm7
	vsha512msg2 ymm4, ymm3
	vmovdqu ymm0, YMMWORD PTR [rax+160]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm5, xmm6
	vperm2i128 ymm7, ymm3, ymm4, 33
	vpalignr ymm7, ymm7, ymm3, 8
	vpaddq ymm5, ymm5, ymm7
	vsha512msg2 ymm5, ymm4
	vmovdqu ymm0, YMMWORD PTR [rax+192]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm6, xmm3
	vperm2i128 ymm7, ymm4, ymm5, 33
	vpalignr ymm7, ymm7, ymm4, 8
	vpaddq ymm6, ymm6, ymm7
	vsha512msg2 ymm6, ymm5
	vmovdqu ymm0, YMMWORD PTR [rax+224]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm3, xmm4
	vperm2i128 ymm7, ymm5, ymm6, 33
	vpalignr ymm7, ymm7, ymm5, 8
	vpaddq ymm3, ymm3, ymm7
	vsha512msg2 ymm3, ymm6
	vmovdqu ymm0, YMMWORD PTR [rax+256]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm4, xmm5
	vperm2i128 ymm7, ymm6, ymm3, 33
	vpalignr ymm7, ymm7, ymm6, 8
	vpaddq ymm4, ymm4, ymm7
	vsha512msg2 ymm4, ymm3
	vmovdqu ymm0, YMMWORD PTR [rax+288]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm5, xmm6
	vperm2i128 ymm7, ymm3, ymm4, 33
	vpalignr ymm7, ymm7, ymm3, 8
	vpaddq ymm5, ymm5, ymm7
	vsha512msg2 ymm5, ymm4
	vmovdqu ymm0, YMMWORD PTR [rax+320]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm6, xmm3
	vperm2i128 ymm7, ymm4, ymm5, 33
	vpalignr ymm7, ymm7, ymm4, 8
	vpaddq ymm6, ymm6, ymm7
	vsha512msg2 ymm6, ymm5
	vmovdqu ymm0, YMMWORD PTR [rax+352]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm3, xmm4
	vperm2i128 ymm7, ymm5, ymm6, 33
	vpalignr ymm7, ymm7, ymm5, 8
	vpaddq ymm3, ymm3, ymm7
	vsha512msg2 ymm3, ymm6
	vmovdqu ymm0, YMMWORD PTR [rax+384]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm4, xmm5
	vperm2i128 ymm7, ymm6, ymm3, 33
	vpalignr ymm7, ymm7, ymm6, 8
	vpaddq ymm4, ymm4, ymm7
	vsha512msg2 ymm4, ymm3
	vmovdqu ymm0, YMMWORD PTR [rax+416]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm5, xmm6
	vperm2i128 ymm7, ymm3, ymm4, 33
	vpalignr ymm7, ymm7, ymm3, 8
	vpaddq ymm5, ymm5, ymm7
	vsha512msg2 ymm5, ymm4
	vmovdqu ymm0, YMMWORD PTR [rax+448]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm6, xmm3
	vperm2i128 ymm7, ymm4, ymm5, 33
	vpalignr ymm7, ymm7, ymm4, 8
	vpaddq ymm6, ymm6, ymm7
	vsha512msg2 ymm6, ymm5
	vmovdqu ymm0, YMMWORD PTR [rax+480]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm3, xmm4
	vperm2i128 ymm7, ymm5, ymm6, 33
	vpalignr ymm7, ymm7, ymm5, 8
	vpaddq ymm3, ymm3, ymm7
	vsha512msg2 ymm3, ymm6
	vmovdqu ymm0, YMMWORD PTR [rax+512]
	vpaddq ymm0, ymm0, ymm3
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm4, xmm5
	vperm2i128 ymm7, ymm6, ymm3, 33
	vpalignr ymm7, ymm7, ymm6, 8
	vpaddq ymm4, ymm4, ymm7
	vsha512msg2 ymm4, ymm3
	vmovdqu ymm0, YMMWORD PTR [rax+544]
	vpaddq ymm0, ymm0, ymm4
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm5, xmm6
	vperm2i128 ymm7, ymm3, ymm4, 33
	vpalignr ymm7, ymm7, ymm3, 8
	vpaddq ymm5, ymm5, ymm7
	vsha512msg2 ymm5, ymm4
	vmovdqu ymm0, YMMWORD PTR [rax+576]
	vpaddq ymm0, ymm0, ymm5
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vsha512msg1 ymm6, xmm3
	vperm2i128 ymm7, ymm4, ymm5, 33
	vpalignr ymm7, ymm7, ymm4, 8
	vpaddq ymm6, ymm6, ymm7
	vsha512msg2 ymm6, ymm5
	vmovdqu ymm0, YMMWORD PTR [rax+608]
	vpaddq ymm0, ymm0, ymm6
	vsha512rnds2 ymm2, ymm1, xmm0
	vextracti128 xmm0, ymm0, 1
	vsha512rnds2 ymm1, ymm2, xmm0
	vpaddq ymm1, ymm1, ymm9
	vpaddq ymm2, ymm2, ymm10
	add rsi, 128
	sub rdx, 1
	jne 22b
	jmp 21f
20:
21:
	vpermq ymm1, ymm1, 177
	vpermq ymm2, ymm2, 177
	vperm2i128 ymm7, ymm1, ymm2, 49
	vperm2i128 ymm1, ymm1, ymm2, 32
	vmovdqu YMMWORD PTR [rdi], ymm7
	vmovdqu YMMWORD PTR [rdi+32], ymm1
	vzeroupper
	ret
	.p2align 6
