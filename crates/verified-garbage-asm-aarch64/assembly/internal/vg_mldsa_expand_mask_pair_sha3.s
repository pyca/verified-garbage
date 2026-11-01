// The functions of `src/internal/vg_mldsa_expand_mask_pair_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_expand_mask_pair_sha3:
	.arch_extension sha3
	str x19, [x4, #7968]
	str x20, [x4, #7976]
	str x21, [x4, #7984]
	str x22, [x4, #7992]
	str x23, [x4, #8000]
	str x24, [x4, #8008]
	str x25, [x4, #8016]
	str x26, [x4, #8024]
	str x27, [x4, #8032]
	str x28, [x4, #8040]
	umov x8, v8.d[0]
	str x8, [x4, #8048]
	umov x8, v9.d[0]
	str x8, [x4, #8056]
	umov x8, v10.d[0]
	str x8, [x4, #8064]
	umov x8, v11.d[0]
	str x8, [x4, #8072]
	umov x8, v12.d[0]
	str x8, [x4, #8080]
	umov x8, v13.d[0]
	str x8, [x4, #8088]
	umov x8, v14.d[0]
	str x8, [x4, #8096]
	umov x8, v15.d[0]
	str x8, [x4, #8104]
	str w1, [x4, #7904]
	add x19, x4, #0
	add x20, x0, #0
	add x21, x2, #0
	add x22, x3, #0
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
	add x2, x19, #0
	add x3, x20, #0
	add x4, x3, #66
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
	ldr x6, [x3, #32]
	ldr x7, [x4, #32]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #64]
	ldr x6, [x3, #40]
	ldr x7, [x4, #40]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #80]
	ldr x6, [x3, #48]
	ldr x7, [x4, #48]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #96]
	ldr x6, [x3, #56]
	ldr x7, [x4, #56]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #112]
	ldrb w6, [x3, #64]
	ldrb w8, [x3, #65]
	lsl x8, x8, #8
	add x6, x6, x8
	ldrb w7, [x4, #64]
	ldrb w8, [x4, #65]
	lsl x8, x8, #8
	add x7, x7, x8
	movz x9, #31, lsl #16
	add x6, x6, x9
	add x7, x7, x9
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #128]
	movz x9, #32768, lsl #48
	dup v0.2d, x9
	str q0, [x2, #256]
	add x23, x19, #0
	add x24, x19, #840
	add x25, x19, #1520
	ldr q0, [x23, #0]
	ldr q1, [x23, #16]
	ldr q2, [x23, #32]
	ldr q3, [x23, #48]
	ldr q4, [x23, #64]
	ldr q5, [x23, #80]
	ldr q6, [x23, #96]
	ldr q7, [x23, #112]
	ldr q8, [x23, #128]
	ldr q9, [x23, #144]
	ldr q10, [x23, #160]
	ldr q11, [x23, #176]
	ldr q12, [x23, #192]
	ldr q13, [x23, #208]
	ldr q14, [x23, #224]
	ldr q15, [x23, #240]
	ldr q16, [x23, #256]
	ldr q17, [x23, #272]
	ldr q18, [x23, #288]
	ldr q19, [x23, #304]
	ldr q20, [x23, #320]
	ldr q21, [x23, #336]
	ldr q22, [x23, #352]
	ldr q23, [x23, #368]
	ldr q24, [x23, #384]
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
	umov x6, v16.d[0]
	umov x7, v16.d[1]
	str x6, [x24, #128]
	str x7, [x25, #128]
	add x24, x24, #136
	add x25, x25, #136
	sub x28, x28, #1
	cbnz x28, 20b
	str q0, [x23, #0]
	str q1, [x23, #16]
	str q2, [x23, #32]
	str q3, [x23, #48]
	str q4, [x23, #64]
	str q5, [x23, #80]
	str q6, [x23, #96]
	str q7, [x23, #112]
	str q8, [x23, #128]
	str q9, [x23, #144]
	str q10, [x23, #160]
	str q11, [x23, #176]
	str q12, [x23, #192]
	str q13, [x23, #208]
	str q14, [x23, #224]
	str q15, [x23, #240]
	str q16, [x23, #256]
	str q17, [x23, #272]
	str q18, [x23, #288]
	str q19, [x23, #304]
	str q20, [x23, #320]
	str q21, [x23, #336]
	str q22, [x23, #352]
	str q23, [x23, #368]
	str q24, [x23, #384]
	ldr w27, [x19, #7904]
	lsr x9, x27, #18
	cbz x9, 22f
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #770, lsl #32
	movk x9, #65284, lsl #48
	dup v16.2d, x9
	movz x9, #1541, lsl #0
	movk x9, #65287, lsl #16
	movk x9, #2055, lsl #32
	movk x9, #65289, lsl #48
	mov v16.d[1], x9
	movz x9, #2826, lsl #0
	movk x9, #65292, lsl #16
	movk x9, #3340, lsl #32
	movk x9, #65294, lsl #48
	dup v17.2d, x9
	movz x9, #4111, lsl #0
	movk x9, #65297, lsl #16
	movk x9, #4625, lsl #32
	movk x9, #65299, lsl #48
	mov v17.d[1], x9
	movz x9, #5396, lsl #0
	movk x9, #65302, lsl #16
	movk x9, #5910, lsl #32
	movk x9, #65304, lsl #48
	dup v18.2d, x9
	movz x9, #6681, lsl #0
	movk x9, #65307, lsl #16
	movk x9, #7195, lsl #32
	movk x9, #65309, lsl #48
	mov v18.d[1], x9
	movz x9, #7966, lsl #0
	movk x9, #65320, lsl #16
	movk x9, #10536, lsl #32
	movk x9, #65322, lsl #48
	dup v19.2d, x9
	movz x9, #11307, lsl #0
	movk x9, #65325, lsl #16
	movk x9, #11821, lsl #32
	movk x9, #65327, lsl #48
	mov v19.d[1], x9
	movz x9, #16, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v23.4s, w9
	movz x9, #1, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v23.s[1], w9
	movz x9, #16, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v23.s[2], w9
	movz x9, #1, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v23.s[3], w9
	movz x9, #65535, lsl #0
	movk x9, #15, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v22.4s, w9
	movz x9, #65535, lsl #0
	movk x9, #15, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v22.s[1], w9
	movz x9, #65535, lsl #0
	movk x9, #15, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v22.s[2], w9
	movz x9, #65535, lsl #0
	movk x9, #15, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v22.s[3], w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v20.4s, w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v20.s[1], w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v20.s[2], w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v20.s[3], w9
	movz x9, #0, lsl #0
	movk x9, #8, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v21.4s, w9
	movz x9, #0, lsl #0
	movk x9, #8, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v21.s[1], w9
	movz x9, #0, lsl #0
	movk x9, #8, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v21.s[2], w9
	movz x9, #0, lsl #0
	movk x9, #8, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v21.s[3], w9
	movz x11, #16, lsl #0
	add x0, x19, #840
	add x4, x21, #0
	movz x11, #16, lsl #0
24:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	add x9, x0, #24
	ldr q2, [x9, #0]
	tbl v4.16b, {v0.16b, v1.16b, v2.16b}, v16.16b
	mul v4.4s, v4.4s, v23.4s
	ushr v4.4s, v4.4s, #4
	and v4.16b, v4.16b, v22.16b
	sub v4.4s, v21.4s, v4.4s
	sshr v24.4s, v4.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v4.4s, v4.4s, v24.4s
	str q4, [x4, #0]
	tbl v5.16b, {v0.16b, v1.16b, v2.16b}, v17.16b
	mul v5.4s, v5.4s, v23.4s
	ushr v5.4s, v5.4s, #4
	and v5.16b, v5.16b, v22.16b
	sub v5.4s, v21.4s, v5.4s
	sshr v24.4s, v5.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v5.4s, v5.4s, v24.4s
	str q5, [x4, #16]
	tbl v6.16b, {v0.16b, v1.16b, v2.16b}, v18.16b
	mul v6.4s, v6.4s, v23.4s
	ushr v6.4s, v6.4s, #4
	and v6.16b, v6.16b, v22.16b
	sub v6.4s, v21.4s, v6.4s
	sshr v24.4s, v6.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v6.4s, v6.4s, v24.4s
	str q6, [x4, #32]
	tbl v7.16b, {v0.16b, v1.16b, v2.16b}, v19.16b
	mul v7.4s, v7.4s, v23.4s
	ushr v7.4s, v7.4s, #4
	and v7.16b, v7.16b, v22.16b
	sub v7.4s, v21.4s, v7.4s
	sshr v24.4s, v7.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v7.4s, v7.4s, v24.4s
	str q7, [x4, #48]
	add x0, x0, #40
	add x4, x4, #64
	sub x11, x11, #1
	cbnz x11, 24b
	add x0, x19, #1520
	add x4, x22, #0
	movz x11, #16, lsl #0
25:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	add x9, x0, #24
	ldr q2, [x9, #0]
	tbl v4.16b, {v0.16b, v1.16b, v2.16b}, v16.16b
	mul v4.4s, v4.4s, v23.4s
	ushr v4.4s, v4.4s, #4
	and v4.16b, v4.16b, v22.16b
	sub v4.4s, v21.4s, v4.4s
	sshr v24.4s, v4.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v4.4s, v4.4s, v24.4s
	str q4, [x4, #0]
	tbl v5.16b, {v0.16b, v1.16b, v2.16b}, v17.16b
	mul v5.4s, v5.4s, v23.4s
	ushr v5.4s, v5.4s, #4
	and v5.16b, v5.16b, v22.16b
	sub v5.4s, v21.4s, v5.4s
	sshr v24.4s, v5.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v5.4s, v5.4s, v24.4s
	str q5, [x4, #16]
	tbl v6.16b, {v0.16b, v1.16b, v2.16b}, v18.16b
	mul v6.4s, v6.4s, v23.4s
	ushr v6.4s, v6.4s, #4
	and v6.16b, v6.16b, v22.16b
	sub v6.4s, v21.4s, v6.4s
	sshr v24.4s, v6.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v6.4s, v6.4s, v24.4s
	str q6, [x4, #32]
	tbl v7.16b, {v0.16b, v1.16b, v2.16b}, v19.16b
	mul v7.4s, v7.4s, v23.4s
	ushr v7.4s, v7.4s, #4
	and v7.16b, v7.16b, v22.16b
	sub v7.4s, v21.4s, v7.4s
	sshr v24.4s, v7.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v7.4s, v7.4s, v24.4s
	str q7, [x4, #48]
	add x0, x0, #40
	add x4, x4, #64
	sub x11, x11, #1
	cbnz x11, 25b
	b 23f
22:
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #770, lsl #32
	movk x9, #65284, lsl #48
	dup v16.2d, x9
	movz x9, #1284, lsl #0
	movk x9, #65286, lsl #16
	movk x9, #1798, lsl #32
	movk x9, #65288, lsl #48
	mov v16.d[1], x9
	movz x9, #2569, lsl #0
	movk x9, #65291, lsl #16
	movk x9, #3083, lsl #32
	movk x9, #65293, lsl #48
	dup v17.2d, x9
	movz x9, #3597, lsl #0
	movk x9, #65295, lsl #16
	movk x9, #4111, lsl #32
	movk x9, #65297, lsl #48
	mov v17.d[1], x9
	movz x9, #4882, lsl #0
	movk x9, #65300, lsl #16
	movk x9, #5396, lsl #32
	movk x9, #65302, lsl #48
	dup v18.2d, x9
	movz x9, #5910, lsl #0
	movk x9, #65304, lsl #16
	movk x9, #6424, lsl #32
	movk x9, #65306, lsl #48
	mov v18.d[1], x9
	movz x9, #7195, lsl #0
	movk x9, #65309, lsl #16
	movk x9, #7709, lsl #32
	movk x9, #65311, lsl #48
	dup v19.2d, x9
	movz x9, #11295, lsl #0
	movk x9, #65325, lsl #16
	movk x9, #11821, lsl #32
	movk x9, #65327, lsl #48
	mov v19.d[1], x9
	movz x9, #64, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v23.4s, w9
	movz x9, #16, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v23.s[1], w9
	movz x9, #4, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v23.s[2], w9
	movz x9, #1, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v23.s[3], w9
	movz x9, #65535, lsl #0
	movk x9, #3, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v22.4s, w9
	movz x9, #65535, lsl #0
	movk x9, #3, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v22.s[1], w9
	movz x9, #65535, lsl #0
	movk x9, #3, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v22.s[2], w9
	movz x9, #65535, lsl #0
	movk x9, #3, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v22.s[3], w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v20.4s, w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v20.s[1], w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v20.s[2], w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v20.s[3], w9
	movz x9, #0, lsl #0
	movk x9, #2, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v21.4s, w9
	movz x9, #0, lsl #0
	movk x9, #2, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v21.s[1], w9
	movz x9, #0, lsl #0
	movk x9, #2, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v21.s[2], w9
	movz x9, #0, lsl #0
	movk x9, #2, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	mov v21.s[3], w9
	movz x11, #16, lsl #0
	add x0, x19, #840
	add x4, x21, #0
	movz x11, #16, lsl #0
26:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	add x9, x0, #20
	ldr q2, [x9, #0]
	tbl v4.16b, {v0.16b, v1.16b, v2.16b}, v16.16b
	mul v4.4s, v4.4s, v23.4s
	ushr v4.4s, v4.4s, #6
	and v4.16b, v4.16b, v22.16b
	sub v4.4s, v21.4s, v4.4s
	sshr v24.4s, v4.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v4.4s, v4.4s, v24.4s
	str q4, [x4, #0]
	tbl v5.16b, {v0.16b, v1.16b, v2.16b}, v17.16b
	mul v5.4s, v5.4s, v23.4s
	ushr v5.4s, v5.4s, #6
	and v5.16b, v5.16b, v22.16b
	sub v5.4s, v21.4s, v5.4s
	sshr v24.4s, v5.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v5.4s, v5.4s, v24.4s
	str q5, [x4, #16]
	tbl v6.16b, {v0.16b, v1.16b, v2.16b}, v18.16b
	mul v6.4s, v6.4s, v23.4s
	ushr v6.4s, v6.4s, #6
	and v6.16b, v6.16b, v22.16b
	sub v6.4s, v21.4s, v6.4s
	sshr v24.4s, v6.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v6.4s, v6.4s, v24.4s
	str q6, [x4, #32]
	tbl v7.16b, {v0.16b, v1.16b, v2.16b}, v19.16b
	mul v7.4s, v7.4s, v23.4s
	ushr v7.4s, v7.4s, #6
	and v7.16b, v7.16b, v22.16b
	sub v7.4s, v21.4s, v7.4s
	sshr v24.4s, v7.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v7.4s, v7.4s, v24.4s
	str q7, [x4, #48]
	add x0, x0, #36
	add x4, x4, #64
	sub x11, x11, #1
	cbnz x11, 26b
	add x0, x19, #1520
	add x4, x22, #0
	movz x11, #16, lsl #0
27:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	add x9, x0, #20
	ldr q2, [x9, #0]
	tbl v4.16b, {v0.16b, v1.16b, v2.16b}, v16.16b
	mul v4.4s, v4.4s, v23.4s
	ushr v4.4s, v4.4s, #6
	and v4.16b, v4.16b, v22.16b
	sub v4.4s, v21.4s, v4.4s
	sshr v24.4s, v4.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v4.4s, v4.4s, v24.4s
	str q4, [x4, #0]
	tbl v5.16b, {v0.16b, v1.16b, v2.16b}, v17.16b
	mul v5.4s, v5.4s, v23.4s
	ushr v5.4s, v5.4s, #6
	and v5.16b, v5.16b, v22.16b
	sub v5.4s, v21.4s, v5.4s
	sshr v24.4s, v5.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v5.4s, v5.4s, v24.4s
	str q5, [x4, #16]
	tbl v6.16b, {v0.16b, v1.16b, v2.16b}, v18.16b
	mul v6.4s, v6.4s, v23.4s
	ushr v6.4s, v6.4s, #6
	and v6.16b, v6.16b, v22.16b
	sub v6.4s, v21.4s, v6.4s
	sshr v24.4s, v6.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v6.4s, v6.4s, v24.4s
	str q6, [x4, #32]
	tbl v7.16b, {v0.16b, v1.16b, v2.16b}, v19.16b
	mul v7.4s, v7.4s, v23.4s
	ushr v7.4s, v7.4s, #6
	and v7.16b, v7.16b, v22.16b
	sub v7.4s, v21.4s, v7.4s
	sshr v24.4s, v7.4s, #31
	and v24.16b, v24.16b, v20.16b
	add v7.4s, v7.4s, v24.4s
	str q7, [x4, #48]
	add x0, x0, #36
	add x4, x4, #64
	sub x11, x11, #1
	cbnz x11, 27b
23:
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
