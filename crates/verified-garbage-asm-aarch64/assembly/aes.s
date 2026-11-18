// The functions of `src/aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key:
	sub sp, sp, #512
	add x3, sp, #0
	adrp x6, {VG_AES_SBOX}
	add x6, x6, {VG_AES_SBOX}
	ldr q16, [x6, #0]
	ldr q17, [x6, #16]
	ldr q18, [x6, #32]
	ldr q19, [x6, #48]
	ldr q20, [x6, #64]
	ldr q21, [x6, #80]
	ldr q22, [x6, #96]
	ldr q23, [x6, #112]
	ldr q24, [x6, #128]
	ldr q25, [x6, #144]
	ldr q26, [x6, #160]
	ldr q27, [x6, #176]
	ldr q28, [x6, #192]
	ldr q29, [x6, #208]
	ldr q30, [x6, #224]
	ldr q31, [x6, #240]
	ldr q4, [x6, #256]
	ldr q5, [x6, #272]
	ldr q6, [x6, #288]
	ldr q7, [x6, #304]
	add x5, x3, #0
	str x19, [x5, #384]
	str x20, [x5, #392]
	str x21, [x5, #400]
	str x22, [x5, #408]
	str x23, [x5, #416]
	str x24, [x5, #424]
	str x25, [x5, #432]
	str x26, [x5, #440]
	str x27, [x5, #448]
	str x28, [x5, #456]
	add x4, x1, #0
20:
	ldr x6, [x0, #0]
	str x6, [x2, #0]
	add x0, x0, #8
	add x2, x2, #8
	sub x4, x4, #8
	cbnz x4, 20b
	lsr x6, x6, #32
	sub x0, x2, x1
	lsr x3, x1, #2
	movz x1, #0, lsl #0
	add x4, x3, x3
	add x4, x4, x3
	add x4, x4, #28
	movz x7, #1, lsl #0
	str x7, [x5, #472]
21:
	cbz x1, 22f
	sub x7, x1, #4
	sub x8, x3, #8
	orr x7, x7, x8
	cbz x7, 24f
	b 25f
24:
	mov v0.d[0], x6
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x6, v0.d[0]
25:
	b 23f
22:
	mov v0.d[0], x6
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x6, v0.d[0]
	ror w6, w6, #8
	ldr x7, [x5, #472]
	eor w6, w6, w7
	lsr x8, x7, #7
	movz x9, #27, lsl #0
	mul x8, x8, x9
	lsl x7, x7, #1
	eor x7, x7, x8
	movz x9, #255, lsl #0
	and x7, x7, x9
	str x7, [x5, #472]
23:
	ldr w7, [x0, #0]
	eor w6, w6, w7
	str w6, [x2, #0]
	add x0, x0, #4
	add x2, x2, #4
	add x1, x1, #1
	sub x7, x1, x3
	cbz x7, 26f
	b 27f
26:
	movz x1, #0, lsl #0
27:
	sub x4, x4, #1
	cbnz x4, 21b
	ldr x19, [x5, #384]
	ldr x20, [x5, #392]
	ldr x21, [x5, #400]
	ldr x22, [x5, #408]
	ldr x23, [x5, #416]
	ldr x24, [x5, #424]
	ldr x25, [x5, #432]
	ldr x26, [x5, #440]
	ldr x27, [x5, #448]
	ldr x28, [x5, #456]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add sp, sp, #512
	movz x6, #0, lsl #0
	movz x8, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	ret
	.p2align 6

vg_aes_expand_key_aes:
	sub sp, sp, #512
	add x3, sp, #0
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
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add sp, sp, #512
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movi v1.2d, #0
	ret
	.p2align 6
