// The functions of `src/internal/vg_mldsa_rej_ntt_poly2_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_ntt_poly2_sha3:
	.arch_extension sha3
	str x19, [x2, #7968]
	str x20, [x2, #7976]
	str x21, [x2, #7984]
	str x22, [x2, #7992]
	str x23, [x2, #8000]
	str x24, [x2, #8008]
	str x25, [x2, #8016]
	str x26, [x2, #8024]
	str x27, [x2, #8032]
	str x28, [x2, #8040]
	umov x8, v8.d[0]
	str x8, [x2, #8048]
	umov x8, v9.d[0]
	str x8, [x2, #8056]
	umov x8, v10.d[0]
	str x8, [x2, #8064]
	umov x8, v11.d[0]
	str x8, [x2, #8072]
	umov x8, v12.d[0]
	str x8, [x2, #8080]
	umov x8, v13.d[0]
	str x8, [x2, #8088]
	umov x8, v14.d[0]
	str x8, [x2, #8096]
	umov x8, v15.d[0]
	str x8, [x2, #8104]
	add x19, x2, #0
	add x20, x0, #0
	add x21, x1, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	str q0, [x19, #400]
	str q0, [x19, #416]
	str q0, [x19, #432]
	str q0, [x19, #448]
	str q0, [x19, #464]
	str q0, [x19, #480]
	str q0, [x19, #496]
	str q0, [x19, #512]
	str q0, [x19, #528]
	str q0, [x19, #544]
	str q0, [x19, #560]
	str q0, [x19, #576]
	str q0, [x19, #592]
	str q0, [x19, #608]
	str q0, [x19, #624]
	str q0, [x19, #640]
	str q0, [x19, #656]
	str q0, [x19, #672]
	str q0, [x19, #688]
	str q0, [x19, #704]
	str q0, [x19, #720]
	str q0, [x19, #736]
	str q0, [x19, #752]
	str q0, [x19, #768]
	str q0, [x19, #784]
	add x2, x19, #0
	add x3, x20, #0
	add x4, x3, #34
	ldr x6, [x3, #0]
	ldr x7, [x4, #0]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #0]
	ldr x6, [x3, #8]
	ldr x7, [x4, #8]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #16]
	ldr x6, [x3, #16]
	ldr x7, [x4, #16]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #32]
	ldr x6, [x3, #24]
	ldr x7, [x4, #24]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #48]
	ldrb w6, [x3, #32]
	ldrb w8, [x3, #33]
	lsl x8, x8, #8
	add x6, x6, x8
	ldrb w7, [x4, #32]
	ldrb w8, [x4, #33]
	lsl x8, x8, #8
	add x7, x7, x8
	movz x9, #31, lsl #16
	add x6, x6, x9
	add x7, x7, x9
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #64]
	movz x9, #32768, lsl #48
	dup v0.2d, x9
	str q0, [x2, #320]
	movz x4, #256, lsl #0
	str x4, [x19, #7904]
	str x4, [x19, #7912]
	add x22, x19, #0
	add x23, x19, #400
	add x24, x19, #840
	add x25, x19, #1848
	add x26, x19, #2856
	add x27, x19, #3864
	movz x28, #5, lsl #0
	ldr q0, [x22, #0]
	ldr q1, [x22, #16]
	ldr q2, [x22, #32]
	ldr q3, [x22, #48]
	ldr q4, [x22, #64]
	ldr q5, [x22, #80]
	ldr q6, [x22, #96]
	ldr q7, [x22, #112]
	ldr q8, [x22, #128]
	ldr q9, [x22, #144]
	ldr q10, [x22, #160]
	ldr q11, [x22, #176]
	ldr q12, [x22, #192]
	ldr q13, [x22, #208]
	ldr q14, [x22, #224]
	ldr q15, [x22, #240]
	ldr q16, [x22, #256]
	ldr q17, [x22, #272]
	ldr q18, [x22, #288]
	ldr q19, [x22, #304]
	ldr q20, [x22, #320]
	ldr q21, [x22, #336]
	ldr q22, [x22, #352]
	ldr q23, [x22, #368]
	ldr q24, [x22, #384]
	movz x28, #5, lsl #0
	add x15, x19, #3648
	add x15, x15, #3648
	movz x16, #1, lsl #0
	str x16, [x15, #0]
	str x16, [x15, #8]
	movz x16, #32898, lsl #0
	str x16, [x15, #16]
	str x16, [x15, #24]
	movz x16, #32906, lsl #0
	movk x16, #32768, lsl #48
	str x16, [x15, #32]
	str x16, [x15, #40]
	movz x16, #32768, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	str x16, [x15, #48]
	str x16, [x15, #56]
	movz x16, #32907, lsl #0
	str x16, [x15, #64]
	str x16, [x15, #72]
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
	str x16, [x15, #80]
	str x16, [x15, #88]
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	str x16, [x15, #96]
	str x16, [x15, #104]
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #48
	str x16, [x15, #112]
	str x16, [x15, #120]
	movz x16, #138, lsl #0
	str x16, [x15, #128]
	str x16, [x15, #136]
	movz x16, #136, lsl #0
	str x16, [x15, #144]
	str x16, [x15, #152]
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #16
	str x16, [x15, #160]
	str x16, [x15, #168]
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	str x16, [x15, #176]
	str x16, [x15, #184]
	movz x16, #32907, lsl #0
	movk x16, #32768, lsl #16
	str x16, [x15, #192]
	str x16, [x15, #200]
	movz x16, #139, lsl #0
	movk x16, #32768, lsl #48
	str x16, [x15, #208]
	str x16, [x15, #216]
	movz x16, #32905, lsl #0
	movk x16, #32768, lsl #48
	str x16, [x15, #224]
	str x16, [x15, #232]
	movz x16, #32771, lsl #0
	movk x16, #32768, lsl #48
	str x16, [x15, #240]
	str x16, [x15, #248]
	movz x16, #32770, lsl #0
	movk x16, #32768, lsl #48
	str x16, [x15, #256]
	str x16, [x15, #264]
	movz x16, #128, lsl #0
	movk x16, #32768, lsl #48
	str x16, [x15, #272]
	str x16, [x15, #280]
	movz x16, #32778, lsl #0
	str x16, [x15, #288]
	str x16, [x15, #296]
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	str x16, [x15, #304]
	str x16, [x15, #312]
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	str x16, [x15, #320]
	str x16, [x15, #328]
	movz x16, #32896, lsl #0
	movk x16, #32768, lsl #48
	str x16, [x15, #336]
	str x16, [x15, #344]
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
	str x16, [x15, #352]
	str x16, [x15, #360]
	movz x16, #32776, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	str x16, [x15, #368]
	str x16, [x15, #376]
20:
	movz x16, #24, lsl #0
21:
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	ldr q26, [x15, #0]
	eor v0.16b, v0.16b, v26.16b
	add x15, x15, #16
	sub x16, x16, #1
	cbnz x16, 21b
	sub x15, x15, #384
	trn1 v26.2d, v0.2d, v1.2d
	trn2 v27.2d, v0.2d, v1.2d
	str q26, [x24, #0]
	str q27, [x25, #0]
	trn1 v26.2d, v2.2d, v3.2d
	trn2 v27.2d, v2.2d, v3.2d
	str q26, [x24, #16]
	str q27, [x25, #16]
	trn1 v26.2d, v4.2d, v5.2d
	trn2 v27.2d, v4.2d, v5.2d
	str q26, [x24, #32]
	str q27, [x25, #32]
	trn1 v26.2d, v6.2d, v7.2d
	trn2 v27.2d, v6.2d, v7.2d
	str q26, [x24, #48]
	str q27, [x25, #48]
	trn1 v26.2d, v8.2d, v9.2d
	trn2 v27.2d, v8.2d, v9.2d
	str q26, [x24, #64]
	str q27, [x25, #64]
	trn1 v26.2d, v10.2d, v11.2d
	trn2 v27.2d, v10.2d, v11.2d
	str q26, [x24, #80]
	str q27, [x25, #80]
	trn1 v26.2d, v12.2d, v13.2d
	trn2 v27.2d, v12.2d, v13.2d
	str q26, [x24, #96]
	str q27, [x25, #96]
	trn1 v26.2d, v14.2d, v15.2d
	trn2 v27.2d, v14.2d, v15.2d
	str q26, [x24, #112]
	str q27, [x25, #112]
	trn1 v26.2d, v16.2d, v17.2d
	trn2 v27.2d, v16.2d, v17.2d
	str q26, [x24, #128]
	str q27, [x25, #128]
	trn1 v26.2d, v18.2d, v19.2d
	trn2 v27.2d, v18.2d, v19.2d
	str q26, [x24, #144]
	str q27, [x25, #144]
	umov x6, v20.d[0]
	umov x7, v20.d[1]
	str x6, [x24, #160]
	str x7, [x25, #160]
	add x24, x24, #168
	add x25, x25, #168
	sub x28, x28, #1
	cbnz x28, 20b
	str q0, [x22, #0]
	str q1, [x22, #16]
	str q2, [x22, #32]
	str q3, [x22, #48]
	str q4, [x22, #64]
	str q5, [x22, #80]
	str q6, [x22, #96]
	str q7, [x22, #112]
	str q8, [x22, #128]
	str q9, [x22, #144]
	str q10, [x22, #160]
	str q11, [x22, #176]
	str q12, [x22, #192]
	str q13, [x22, #208]
	str q14, [x22, #224]
	str q15, [x22, #240]
	str q16, [x22, #256]
	str q17, [x22, #272]
	str q18, [x22, #288]
	str q19, [x22, #304]
	str q20, [x22, #320]
	str q21, [x22, #336]
	str q22, [x22, #352]
	str q23, [x22, #368]
	str q24, [x22, #384]
	add x24, x19, #840
	add x25, x21, #0
	add x26, x19, #3952
	add x26, x26, #3952
	movz x27, #2, lsl #0
22:
	add x2, x24, #0
	add x3, x25, #0
	ldr x4, [x26, #0]
	movz x6, #256, lsl #0
	sub x6, x6, x4
	lsl x6, x6, #2
	add x3, x3, x6
	movz x5, #168, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
	movz x6, #256, lsl #0
	movk x6, #65282, lsl #16
	movk x6, #1027, lsl #32
	movk x6, #65285, lsl #48
	movz x7, #1798, lsl #0
	movk x7, #65288, lsl #16
	movk x7, #2569, lsl #32
	movk x7, #65291, lsl #48
	dup v3.2d, x6
	mov v3.d[1], x7
	movz x10, #65535, lsl #0
	movk x10, #127, lsl #16
	dup v4.4s, w10
	dup v5.4s, w9
	movz x12, #1, lsl #0
	movk x12, #1, lsl #32
	movz x17, #4, lsl #0
	movz x0, #0, lsl #0
	movz x17, #16, lsl #0
	subs x16, x4, x17
	csel x16, x5, x0, hs
	subs x16, x16, x17
	csel x16, x17, x0, hs
	cbz x16, 23f
25:
	dup v20.2d, x12
	add x6, x2, #0
	ldr q0, [x6, #0]
	tbl v16.16b, {v0.16b}, v3.16b
	and v16.16b, v16.16b, v4.16b
	sub v2.4s, v16.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	add x6, x2, #12
	ldr q0, [x6, #0]
	tbl v17.16b, {v0.16b}, v3.16b
	and v17.16b, v17.16b, v4.16b
	sub v2.4s, v17.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	add x6, x2, #24
	ldr q0, [x6, #0]
	tbl v18.16b, {v0.16b}, v3.16b
	and v18.16b, v18.16b, v4.16b
	sub v2.4s, v18.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	add x6, x2, #36
	ldr q0, [x6, #0]
	tbl v19.16b, {v0.16b}, v3.16b
	and v19.16b, v19.16b, v4.16b
	sub v2.4s, v19.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	umov x6, v20.d[0]
	umov x7, v20.d[1]
	and x6, x6, x7
	eor x6, x6, x12
	cbz x6, 26f
	umov w11, v16.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v16.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v16.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v16.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 27f
26:
	str q16, [x3, #0]
	str q17, [x3, #16]
	str q18, [x3, #32]
	str q19, [x3, #48]
	add x3, x3, #64
	sub x4, x4, #16
27:
	add x2, x2, #48
	sub x5, x5, #16
	subs x16, x4, x17
	csel x16, x5, x0, hs
	subs x16, x16, x17
	csel x16, x17, x0, hs
	cbnz x16, 25b
	b 24f
23:
24:
	movz x6, #256, lsl #0
	movk x6, #65282, lsl #16
	movk x6, #1027, lsl #32
	movk x6, #65285, lsl #48
	movz x7, #1798, lsl #0
	movk x7, #65288, lsl #16
	movk x7, #2569, lsl #32
	movk x7, #65291, lsl #48
	dup v3.2d, x6
	mov v3.d[1], x7
	movz x10, #65535, lsl #0
	movk x10, #127, lsl #16
	dup v4.4s, w10
	dup v5.4s, w9
	movz x12, #1, lsl #0
	movk x12, #1, lsl #32
	movz x17, #4, lsl #0
	movz x0, #0, lsl #0
	subs x16, x4, x17
	csel x16, x5, x0, hs
	cbz x16, 28f
210:
	ldr q0, [x2, #0]
	tbl v1.16b, {v0.16b}, v3.16b
	and v1.16b, v1.16b, v4.16b
	sub v2.4s, v1.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	umov x6, v2.d[0]
	umov x7, v2.d[1]
	and x6, x6, x7
	eor x6, x6, x12
	cbz x6, 211f
	umov w11, v1.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v1.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v1.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v1.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 212f
211:
	str q1, [x3, #0]
	add x3, x3, #16
	sub x4, x4, #4
212:
	add x2, x2, #12
	sub x5, x5, #4
	subs x16, x4, x17
	csel x16, x5, x0, hs
	cbnz x16, 210b
	b 29f
28:
29:
	mul x16, x4, x5
	cbz x16, 213f
215:
	ldr w11, [x2, #0]
	and x11, x11, x10
	add x2, x2, #3
	sub x5, x5, #1
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	mul x16, x4, x5
	cbnz x16, 215b
	b 214f
213:
214:
	str x4, [x26, #0]
	add x24, x24, #1008
	add x25, x25, #1024
	add x26, x26, #8
	sub x27, x27, #1
	cbnz x27, 22b
	add x24, x19, #1344
	add x25, x21, #0
	add x26, x19, #3952
	add x26, x26, #3952
	movz x27, #2, lsl #0
216:
	add x2, x24, #0
	add x3, x25, #0
	ldr x4, [x26, #0]
	movz x6, #256, lsl #0
	sub x6, x6, x4
	lsl x6, x6, #2
	add x3, x3, x6
	movz x5, #112, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
	movz x6, #256, lsl #0
	movk x6, #65282, lsl #16
	movk x6, #1027, lsl #32
	movk x6, #65285, lsl #48
	movz x7, #1798, lsl #0
	movk x7, #65288, lsl #16
	movk x7, #2569, lsl #32
	movk x7, #65291, lsl #48
	dup v3.2d, x6
	mov v3.d[1], x7
	movz x10, #65535, lsl #0
	movk x10, #127, lsl #16
	dup v4.4s, w10
	dup v5.4s, w9
	movz x12, #1, lsl #0
	movk x12, #1, lsl #32
	movz x17, #4, lsl #0
	movz x0, #0, lsl #0
	movz x17, #16, lsl #0
	subs x16, x4, x17
	csel x16, x5, x0, hs
	subs x16, x16, x17
	csel x16, x17, x0, hs
	cbz x16, 217f
219:
	dup v20.2d, x12
	add x6, x2, #0
	ldr q0, [x6, #0]
	tbl v16.16b, {v0.16b}, v3.16b
	and v16.16b, v16.16b, v4.16b
	sub v2.4s, v16.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	add x6, x2, #12
	ldr q0, [x6, #0]
	tbl v17.16b, {v0.16b}, v3.16b
	and v17.16b, v17.16b, v4.16b
	sub v2.4s, v17.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	add x6, x2, #24
	ldr q0, [x6, #0]
	tbl v18.16b, {v0.16b}, v3.16b
	and v18.16b, v18.16b, v4.16b
	sub v2.4s, v18.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	add x6, x2, #36
	ldr q0, [x6, #0]
	tbl v19.16b, {v0.16b}, v3.16b
	and v19.16b, v19.16b, v4.16b
	sub v2.4s, v19.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	umov x6, v20.d[0]
	umov x7, v20.d[1]
	and x6, x6, x7
	eor x6, x6, x12
	cbz x6, 220f
	umov w11, v16.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v16.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v16.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v16.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 221f
220:
	str q16, [x3, #0]
	str q17, [x3, #16]
	str q18, [x3, #32]
	str q19, [x3, #48]
	add x3, x3, #64
	sub x4, x4, #16
221:
	add x2, x2, #48
	sub x5, x5, #16
	subs x16, x4, x17
	csel x16, x5, x0, hs
	subs x16, x16, x17
	csel x16, x17, x0, hs
	cbnz x16, 219b
	b 218f
217:
218:
	movz x6, #256, lsl #0
	movk x6, #65282, lsl #16
	movk x6, #1027, lsl #32
	movk x6, #65285, lsl #48
	movz x7, #1798, lsl #0
	movk x7, #65288, lsl #16
	movk x7, #2569, lsl #32
	movk x7, #65291, lsl #48
	dup v3.2d, x6
	mov v3.d[1], x7
	movz x10, #65535, lsl #0
	movk x10, #127, lsl #16
	dup v4.4s, w10
	dup v5.4s, w9
	movz x12, #1, lsl #0
	movk x12, #1, lsl #32
	movz x17, #4, lsl #0
	movz x0, #0, lsl #0
	subs x16, x4, x17
	csel x16, x5, x0, hs
	cbz x16, 222f
224:
	ldr q0, [x2, #0]
	tbl v1.16b, {v0.16b}, v3.16b
	and v1.16b, v1.16b, v4.16b
	sub v2.4s, v1.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	umov x6, v2.d[0]
	umov x7, v2.d[1]
	and x6, x6, x7
	eor x6, x6, x12
	cbz x6, 225f
	umov w11, v1.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v1.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v1.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v1.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 226f
225:
	str q1, [x3, #0]
	add x3, x3, #16
	sub x4, x4, #4
226:
	add x2, x2, #12
	sub x5, x5, #4
	subs x16, x4, x17
	csel x16, x5, x0, hs
	cbnz x16, 224b
	b 223f
222:
223:
	mul x16, x4, x5
	cbz x16, 227f
229:
	ldr w11, [x2, #0]
	and x11, x11, x10
	add x2, x2, #3
	sub x5, x5, #1
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	mul x16, x4, x5
	cbnz x16, 229b
	b 228f
227:
228:
	str x4, [x26, #0]
	add x24, x24, #1008
	add x25, x25, #1024
	add x26, x26, #8
	sub x27, x27, #1
	cbnz x27, 216b
	ldr x27, [x19, #7904]
	ldr x6, [x19, #7912]
	orr x27, x27, x6
	cbz x27, 230f
	add x22, x19, #0
	add x23, x19, #400
	add x24, x19, #840
	add x25, x19, #1848
	add x26, x19, #2856
	add x27, x19, #3864
	add x24, x24, #840
	add x25, x25, #840
	add x26, x26, #840
	add x27, x27, #840
	movz x28, #1, lsl #0
232:
	add x1, x19, #2440
	add x1, x1, #2440
	str x30, [x1, #128]
	add x0, x22, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr q0, [x22, #0]
	ldr q1, [x22, #16]
	ldr q2, [x22, #32]
	ldr q3, [x22, #48]
	ldr q4, [x22, #64]
	ldr q5, [x22, #80]
	ldr q6, [x22, #96]
	ldr q7, [x22, #112]
	ldr q8, [x22, #128]
	ldr q9, [x22, #144]
	ldr q10, [x22, #160]
	ldr q11, [x22, #176]
	ldr q12, [x22, #192]
	ldr q13, [x22, #208]
	ldr q14, [x22, #224]
	ldr q15, [x22, #240]
	ldr q16, [x22, #256]
	ldr q17, [x22, #272]
	ldr q18, [x22, #288]
	ldr q19, [x22, #304]
	ldr q20, [x22, #320]
	ldr q21, [x22, #336]
	ldr q22, [x22, #352]
	ldr q23, [x22, #368]
	ldr q24, [x22, #384]
	trn1 v26.2d, v0.2d, v1.2d
	trn2 v27.2d, v0.2d, v1.2d
	str q26, [x24, #0]
	str q27, [x25, #0]
	trn1 v26.2d, v2.2d, v3.2d
	trn2 v27.2d, v2.2d, v3.2d
	str q26, [x24, #16]
	str q27, [x25, #16]
	trn1 v26.2d, v4.2d, v5.2d
	trn2 v27.2d, v4.2d, v5.2d
	str q26, [x24, #32]
	str q27, [x25, #32]
	trn1 v26.2d, v6.2d, v7.2d
	trn2 v27.2d, v6.2d, v7.2d
	str q26, [x24, #48]
	str q27, [x25, #48]
	trn1 v26.2d, v8.2d, v9.2d
	trn2 v27.2d, v8.2d, v9.2d
	str q26, [x24, #64]
	str q27, [x25, #64]
	trn1 v26.2d, v10.2d, v11.2d
	trn2 v27.2d, v10.2d, v11.2d
	str q26, [x24, #80]
	str q27, [x25, #80]
	trn1 v26.2d, v12.2d, v13.2d
	trn2 v27.2d, v12.2d, v13.2d
	str q26, [x24, #96]
	str q27, [x25, #96]
	trn1 v26.2d, v14.2d, v15.2d
	trn2 v27.2d, v14.2d, v15.2d
	str q26, [x24, #112]
	str q27, [x25, #112]
	trn1 v26.2d, v16.2d, v17.2d
	trn2 v27.2d, v16.2d, v17.2d
	str q26, [x24, #128]
	str q27, [x25, #128]
	trn1 v26.2d, v18.2d, v19.2d
	trn2 v27.2d, v18.2d, v19.2d
	str q26, [x24, #144]
	str q27, [x25, #144]
	umov x6, v20.d[0]
	umov x7, v20.d[1]
	str x6, [x24, #160]
	str x7, [x25, #160]
	add x24, x24, #168
	add x25, x25, #168
	add x26, x26, #168
	add x27, x27, #168
	sub x28, x28, #1
	cbnz x28, 232b
	add x24, x19, #1680
	add x25, x21, #0
	add x26, x19, #3952
	add x26, x26, #3952
	movz x27, #2, lsl #0
233:
	add x2, x24, #0
	add x3, x25, #0
	ldr x4, [x26, #0]
	movz x6, #256, lsl #0
	sub x6, x6, x4
	lsl x6, x6, #2
	add x3, x3, x6
	movz x5, #56, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
	movz x6, #256, lsl #0
	movk x6, #65282, lsl #16
	movk x6, #1027, lsl #32
	movk x6, #65285, lsl #48
	movz x7, #1798, lsl #0
	movk x7, #65288, lsl #16
	movk x7, #2569, lsl #32
	movk x7, #65291, lsl #48
	dup v3.2d, x6
	mov v3.d[1], x7
	movz x10, #65535, lsl #0
	movk x10, #127, lsl #16
	dup v4.4s, w10
	dup v5.4s, w9
	movz x12, #1, lsl #0
	movk x12, #1, lsl #32
	movz x17, #4, lsl #0
	movz x0, #0, lsl #0
	movz x17, #16, lsl #0
	subs x16, x4, x17
	csel x16, x5, x0, hs
	subs x16, x16, x17
	csel x16, x17, x0, hs
	cbz x16, 234f
236:
	dup v20.2d, x12
	add x6, x2, #0
	ldr q0, [x6, #0]
	tbl v16.16b, {v0.16b}, v3.16b
	and v16.16b, v16.16b, v4.16b
	sub v2.4s, v16.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	add x6, x2, #12
	ldr q0, [x6, #0]
	tbl v17.16b, {v0.16b}, v3.16b
	and v17.16b, v17.16b, v4.16b
	sub v2.4s, v17.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	add x6, x2, #24
	ldr q0, [x6, #0]
	tbl v18.16b, {v0.16b}, v3.16b
	and v18.16b, v18.16b, v4.16b
	sub v2.4s, v18.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	add x6, x2, #36
	ldr q0, [x6, #0]
	tbl v19.16b, {v0.16b}, v3.16b
	and v19.16b, v19.16b, v4.16b
	sub v2.4s, v19.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	and v20.16b, v20.16b, v2.16b
	umov x6, v20.d[0]
	umov x7, v20.d[1]
	and x6, x6, x7
	eor x6, x6, x12
	cbz x6, 237f
	umov w11, v16.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v16.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v16.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v16.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v17.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v18.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v19.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 238f
237:
	str q16, [x3, #0]
	str q17, [x3, #16]
	str q18, [x3, #32]
	str q19, [x3, #48]
	add x3, x3, #64
	sub x4, x4, #16
238:
	add x2, x2, #48
	sub x5, x5, #16
	subs x16, x4, x17
	csel x16, x5, x0, hs
	subs x16, x16, x17
	csel x16, x17, x0, hs
	cbnz x16, 236b
	b 235f
234:
235:
	movz x6, #256, lsl #0
	movk x6, #65282, lsl #16
	movk x6, #1027, lsl #32
	movk x6, #65285, lsl #48
	movz x7, #1798, lsl #0
	movk x7, #65288, lsl #16
	movk x7, #2569, lsl #32
	movk x7, #65291, lsl #48
	dup v3.2d, x6
	mov v3.d[1], x7
	movz x10, #65535, lsl #0
	movk x10, #127, lsl #16
	dup v4.4s, w10
	dup v5.4s, w9
	movz x12, #1, lsl #0
	movk x12, #1, lsl #32
	movz x17, #4, lsl #0
	movz x0, #0, lsl #0
	subs x16, x4, x17
	csel x16, x5, x0, hs
	cbz x16, 239f
241:
	ldr q0, [x2, #0]
	tbl v1.16b, {v0.16b}, v3.16b
	and v1.16b, v1.16b, v4.16b
	sub v2.4s, v1.4s, v5.4s
	ushr v2.4s, v2.4s, #31
	umov x6, v2.d[0]
	umov x7, v2.d[1]
	and x6, x6, x7
	eor x6, x6, x12
	cbz x6, 242f
	umov w11, v1.s[0]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v1.s[1]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v1.s[2]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	umov w11, v1.s[3]
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 243f
242:
	str q1, [x3, #0]
	add x3, x3, #16
	sub x4, x4, #4
243:
	add x2, x2, #12
	sub x5, x5, #4
	subs x16, x4, x17
	csel x16, x5, x0, hs
	cbnz x16, 241b
	b 240f
239:
240:
	mul x16, x4, x5
	cbz x16, 244f
246:
	ldr w11, [x2, #0]
	and x11, x11, x10
	add x2, x2, #3
	sub x5, x5, #1
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	mul x16, x4, x5
	cbnz x16, 246b
	b 245f
244:
245:
	str x4, [x26, #0]
	add x24, x24, #1008
	add x25, x25, #1024
	add x26, x26, #8
	sub x27, x27, #1
	cbnz x27, 233b
	ldr x27, [x19, #7904]
	ldr x6, [x19, #7912]
	orr x27, x27, x6
	b 231f
230:
231:
	cbz x27, 247f
	ldr x4, [x19, #7904]
	cbz x4, 249f
	add x3, x21, #0
	movz x6, #256, lsl #0
	sub x6, x6, x4
	lsl x6, x6, #2
	add x3, x3, x6
	add x6, x19, #840
	add x6, x6, #1005
	ldr w6, [x6, #0]
	movz x7, #65535, lsl #0
	movk x7, #127, lsl #16
	and x6, x6, x7
	movz x7, #57345, lsl #0
	movk x7, #127, lsl #16
	sub x6, x6, x7
	lsr x6, x6, #63
	movz x7, #1, lsl #0
	sub x6, x7, x6
	sub x4, x4, x6
	lsl x6, x6, #2
	add x3, x3, x6
	movz x9, #0, lsl #0
	cbz x4, 251f
253:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 253b
	b 252f
251:
252:
	b 250f
249:
250:
	ldr x4, [x19, #7912]
	cbz x4, 254f
	add x3, x21, #1024
	movz x6, #256, lsl #0
	sub x6, x6, x4
	lsl x6, x6, #2
	add x3, x3, x6
	add x6, x19, #1848
	add x6, x6, #1005
	ldr w6, [x6, #0]
	movz x7, #65535, lsl #0
	movk x7, #127, lsl #16
	and x6, x6, x7
	movz x7, #57345, lsl #0
	movk x7, #127, lsl #16
	sub x6, x6, x7
	lsr x6, x6, #63
	movz x7, #1, lsl #0
	sub x6, x7, x6
	sub x4, x4, x6
	lsl x6, x6, #2
	add x3, x3, x6
	movz x9, #0, lsl #0
	cbz x4, 256f
258:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 258b
	b 257f
256:
257:
	b 255f
254:
255:
	b 248f
247:
248:
	sub x27, x27, #1
	lsr x27, x27, #63
	add x0, x27, #0
	ldr x8, [x19, #8048]
	mov v8.d[0], x8
	ldr x8, [x19, #8056]
	mov v9.d[0], x8
	ldr x8, [x19, #8064]
	mov v10.d[0], x8
	ldr x8, [x19, #8072]
	mov v11.d[0], x8
	ldr x8, [x19, #8080]
	mov v12.d[0], x8
	ldr x8, [x19, #8088]
	mov v13.d[0], x8
	ldr x8, [x19, #8096]
	mov v14.d[0], x8
	ldr x8, [x19, #8104]
	mov v15.d[0], x8
	ldr x20, [x19, #7976]
	ldr x21, [x19, #7984]
	ldr x22, [x19, #7992]
	ldr x23, [x19, #8000]
	ldr x24, [x19, #8008]
	ldr x25, [x19, #8016]
	ldr x26, [x19, #8024]
	ldr x27, [x19, #8032]
	ldr x28, [x19, #8040]
	ldr x19, [x19, #7968]
	ret
	.arch_extension nosha3
	.p2align 6
