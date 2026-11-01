// The functions of `src/internal/vg_aes_expand_key_scratch_aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch_aes:
	.arch_extension aes
	movi v0.2d, #0
	sub x9, x1, #24
	sub x10, x1, #32
	cbz x9, 20f
	cbz x10, 22f
	ldr w4, [x0, #0]
	str w4, [x2, #0]
	ldr w5, [x0, #4]
	str w5, [x2, #4]
	ldr w6, [x0, #8]
	str w6, [x2, #8]
	ldr w7, [x0, #12]
	str w7, [x2, #12]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #1, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #16]
	eor w5, w5, w4
	str w5, [x2, #20]
	eor w6, w6, w5
	str w6, [x2, #24]
	eor w7, w7, w6
	str w7, [x2, #28]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #2, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #32]
	eor w5, w5, w4
	str w5, [x2, #36]
	eor w6, w6, w5
	str w6, [x2, #40]
	eor w7, w7, w6
	str w7, [x2, #44]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #4, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #48]
	eor w5, w5, w4
	str w5, [x2, #52]
	eor w6, w6, w5
	str w6, [x2, #56]
	eor w7, w7, w6
	str w7, [x2, #60]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #8, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #64]
	eor w5, w5, w4
	str w5, [x2, #68]
	eor w6, w6, w5
	str w6, [x2, #72]
	eor w7, w7, w6
	str w7, [x2, #76]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #16, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #80]
	eor w5, w5, w4
	str w5, [x2, #84]
	eor w6, w6, w5
	str w6, [x2, #88]
	eor w7, w7, w6
	str w7, [x2, #92]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #32, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #96]
	eor w5, w5, w4
	str w5, [x2, #100]
	eor w6, w6, w5
	str w6, [x2, #104]
	eor w7, w7, w6
	str w7, [x2, #108]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #64, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #112]
	eor w5, w5, w4
	str w5, [x2, #116]
	eor w6, w6, w5
	str w6, [x2, #120]
	eor w7, w7, w6
	str w7, [x2, #124]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #128, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #128]
	eor w5, w5, w4
	str w5, [x2, #132]
	eor w6, w6, w5
	str w6, [x2, #136]
	eor w7, w7, w6
	str w7, [x2, #140]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #27, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #144]
	eor w5, w5, w4
	str w5, [x2, #148]
	eor w6, w6, w5
	str w6, [x2, #152]
	eor w7, w7, w6
	str w7, [x2, #156]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #54, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #160]
	eor w5, w5, w4
	str w5, [x2, #164]
	eor w6, w6, w5
	str w6, [x2, #168]
	eor w7, w7, w6
	str w7, [x2, #172]
	b 23f
22:
	ldr w4, [x0, #0]
	str w4, [x2, #0]
	ldr w5, [x0, #4]
	str w5, [x2, #4]
	ldr w6, [x0, #8]
	str w6, [x2, #8]
	ldr w7, [x0, #12]
	str w7, [x2, #12]
	ldr w8, [x0, #16]
	str w8, [x2, #16]
	ldr w11, [x0, #20]
	str w11, [x2, #20]
	ldr w12, [x0, #24]
	str w12, [x2, #24]
	ldr w13, [x0, #28]
	str w13, [x2, #28]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #1, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #32]
	eor w5, w5, w4
	str w5, [x2, #36]
	eor w6, w6, w5
	str w6, [x2, #40]
	eor w7, w7, w6
	str w7, [x2, #44]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #48]
	eor w11, w11, w8
	str w11, [x2, #52]
	eor w12, w12, w11
	str w12, [x2, #56]
	eor w13, w13, w12
	str w13, [x2, #60]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #2, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #64]
	eor w5, w5, w4
	str w5, [x2, #68]
	eor w6, w6, w5
	str w6, [x2, #72]
	eor w7, w7, w6
	str w7, [x2, #76]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #80]
	eor w11, w11, w8
	str w11, [x2, #84]
	eor w12, w12, w11
	str w12, [x2, #88]
	eor w13, w13, w12
	str w13, [x2, #92]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #4, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #96]
	eor w5, w5, w4
	str w5, [x2, #100]
	eor w6, w6, w5
	str w6, [x2, #104]
	eor w7, w7, w6
	str w7, [x2, #108]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #112]
	eor w11, w11, w8
	str w11, [x2, #116]
	eor w12, w12, w11
	str w12, [x2, #120]
	eor w13, w13, w12
	str w13, [x2, #124]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #8, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #128]
	eor w5, w5, w4
	str w5, [x2, #132]
	eor w6, w6, w5
	str w6, [x2, #136]
	eor w7, w7, w6
	str w7, [x2, #140]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #144]
	eor w11, w11, w8
	str w11, [x2, #148]
	eor w12, w12, w11
	str w12, [x2, #152]
	eor w13, w13, w12
	str w13, [x2, #156]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #16, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #160]
	eor w5, w5, w4
	str w5, [x2, #164]
	eor w6, w6, w5
	str w6, [x2, #168]
	eor w7, w7, w6
	str w7, [x2, #172]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #176]
	eor w11, w11, w8
	str w11, [x2, #180]
	eor w12, w12, w11
	str w12, [x2, #184]
	eor w13, w13, w12
	str w13, [x2, #188]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #32, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #192]
	eor w5, w5, w4
	str w5, [x2, #196]
	eor w6, w6, w5
	str w6, [x2, #200]
	eor w7, w7, w6
	str w7, [x2, #204]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #208]
	eor w11, w11, w8
	str w11, [x2, #212]
	eor w12, w12, w11
	str w12, [x2, #216]
	eor w13, w13, w12
	str w13, [x2, #220]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #64, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #224]
	eor w5, w5, w4
	str w5, [x2, #228]
	eor w6, w6, w5
	str w6, [x2, #232]
	eor w7, w7, w6
	str w7, [x2, #236]
23:
	b 21f
20:
	ldr w4, [x0, #0]
	str w4, [x2, #0]
	ldr w5, [x0, #4]
	str w5, [x2, #4]
	ldr w6, [x0, #8]
	str w6, [x2, #8]
	ldr w7, [x0, #12]
	str w7, [x2, #12]
	ldr w8, [x0, #16]
	str w8, [x2, #16]
	ldr w11, [x0, #20]
	str w11, [x2, #20]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #1, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #24]
	eor w5, w5, w4
	str w5, [x2, #28]
	eor w6, w6, w5
	str w6, [x2, #32]
	eor w7, w7, w6
	str w7, [x2, #36]
	eor w8, w8, w7
	str w8, [x2, #40]
	eor w11, w11, w8
	str w11, [x2, #44]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #2, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #48]
	eor w5, w5, w4
	str w5, [x2, #52]
	eor w6, w6, w5
	str w6, [x2, #56]
	eor w7, w7, w6
	str w7, [x2, #60]
	eor w8, w8, w7
	str w8, [x2, #64]
	eor w11, w11, w8
	str w11, [x2, #68]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #4, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #72]
	eor w5, w5, w4
	str w5, [x2, #76]
	eor w6, w6, w5
	str w6, [x2, #80]
	eor w7, w7, w6
	str w7, [x2, #84]
	eor w8, w8, w7
	str w8, [x2, #88]
	eor w11, w11, w8
	str w11, [x2, #92]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #8, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #96]
	eor w5, w5, w4
	str w5, [x2, #100]
	eor w6, w6, w5
	str w6, [x2, #104]
	eor w7, w7, w6
	str w7, [x2, #108]
	eor w8, w8, w7
	str w8, [x2, #112]
	eor w11, w11, w8
	str w11, [x2, #116]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #16, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #120]
	eor w5, w5, w4
	str w5, [x2, #124]
	eor w6, w6, w5
	str w6, [x2, #128]
	eor w7, w7, w6
	str w7, [x2, #132]
	eor w8, w8, w7
	str w8, [x2, #136]
	eor w11, w11, w8
	str w11, [x2, #140]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #32, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #144]
	eor w5, w5, w4
	str w5, [x2, #148]
	eor w6, w6, w5
	str w6, [x2, #152]
	eor w7, w7, w6
	str w7, [x2, #156]
	eor w8, w8, w7
	str w8, [x2, #160]
	eor w11, w11, w8
	str w11, [x2, #164]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #64, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #168]
	eor w5, w5, w4
	str w5, [x2, #172]
	eor w6, w6, w5
	str w6, [x2, #176]
	eor w7, w7, w6
	str w7, [x2, #180]
	eor w8, w8, w7
	str w8, [x2, #184]
	eor w11, w11, w8
	str w11, [x2, #188]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #128, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #192]
	eor w5, w5, w4
	str w5, [x2, #196]
	eor w6, w6, w5
	str w6, [x2, #200]
	eor w7, w7, w6
	str w7, [x2, #204]
21:
	ret
	.arch_extension noaes
	.p2align 6
