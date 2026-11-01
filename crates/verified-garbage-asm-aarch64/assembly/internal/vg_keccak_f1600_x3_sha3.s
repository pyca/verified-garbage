// The functions of `src/internal/vg_keccak_f1600_x3_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600_x3_sha3:
	.arch_extension sha3
	sub sp, sp, #128
	str x19, [sp, #16]
	str x20, [sp, #24]
	str x21, [sp, #32]
	str x22, [sp, #40]
	str x23, [sp, #48]
	str x24, [sp, #56]
	str x25, [sp, #64]
	str x26, [sp, #72]
	str x27, [sp, #80]
	str x28, [sp, #88]
	str x30, [sp, #96]
	str x0, [sp, #104]
	str x1, [sp, #112]
	str x2, [sp, #120]
	str q8, [x2, #0]
	str q9, [x2, #16]
	str q10, [x2, #32]
	str q11, [x2, #48]
	str q12, [x2, #64]
	str q13, [x2, #80]
	str q14, [x2, #96]
	str q15, [x2, #112]
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	ldr q2, [x0, #32]
	ldr q3, [x0, #48]
	ldr q4, [x0, #64]
	ldr q5, [x0, #80]
	ldr q6, [x0, #96]
	ldr q7, [x0, #112]
	ldr q8, [x0, #128]
	ldr q9, [x0, #144]
	ldr q10, [x0, #160]
	ldr q11, [x0, #176]
	ldr q12, [x0, #192]
	ldr q13, [x0, #208]
	ldr q14, [x0, #224]
	ldr q15, [x0, #240]
	ldr q16, [x0, #256]
	ldr q17, [x0, #272]
	ldr q18, [x0, #288]
	ldr q19, [x0, #304]
	ldr q20, [x0, #320]
	ldr q21, [x0, #336]
	ldr q22, [x0, #352]
	ldr q23, [x0, #368]
	ldr q24, [x0, #384]
	add x30, x1, #0
	ldr x0, [x30, #0]
	ldr x1, [x30, #8]
	ldr x2, [x30, #16]
	ldr x3, [x30, #24]
	ldr x4, [x30, #32]
	ldr x5, [x30, #40]
	ldr x6, [x30, #48]
	ldr x7, [x30, #56]
	ldr x8, [x30, #64]
	ldr x9, [x30, #72]
	ldr x10, [x30, #80]
	ldr x11, [x30, #88]
	ldr x12, [x30, #96]
	ldr x13, [x30, #104]
	ldr x14, [x30, #112]
	ldr x15, [x30, #120]
	ldr x16, [x30, #128]
	ldr x17, [x30, #136]
	ldr x25, [x30, #144]
	ldr x19, [x30, #152]
	ldr x20, [x30, #160]
	ldr x21, [x30, #168]
	ldr x22, [x30, #176]
	ldr x23, [x30, #184]
	ldr x24, [x30, #192]
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #1, lsl #0
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32898, lsl #0
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32906, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32768, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32907, lsl #0
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #1, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32897, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32777, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #138, lsl #0
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #136, lsl #0
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32777, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #10, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32907, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #139, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32905, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32771, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32770, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #128, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32778, lsl #0
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #10, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32897, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32896, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #1, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor x26, x0, x5
	str x4, [sp, #0]
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	str x9, [sp, #8]
	eor x27, x1, x6
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor x28, x2, x7
	eor x30, x3, x8
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor x4, x4, x9
	eor x26, x26, x10
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor x27, x27, x11
	eor x28, x28, x12
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor x30, x30, x13
	eor x4, x4, x14
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor x26, x26, x15
	eor x27, x27, x16
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor x28, x28, x17
	eor x30, x30, x25
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor x4, x4, x19
	eor x26, x26, x20
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	eor x27, x27, x21
	eor x28, x28, x22
	rax1 v30.2d, v25.2d, v27.2d
	eor x30, x30, x23
	eor x4, x4, x24
	rax1 v31.2d, v26.2d, v28.2d
	eor x9, x26, x28, ror #63
	eor x1, x1, x9
	rax1 v27.2d, v27.2d, v29.2d
	eor x6, x6, x9
	eor x11, x11, x9
	rax1 v28.2d, v28.2d, v25.2d
	eor x16, x16, x9
	eor x21, x21, x9
	rax1 v29.2d, v29.2d, v26.2d
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	xar v25.2d, v1.2d, v30.2d, #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	xar v1.2d, v6.2d, v30.2d, #20
	eor x27, x2, x9
	eor x7, x7, x9
	xar v6.2d, v9.2d, v28.2d, #44
	eor x12, x12, x9
	eor x17, x17, x9
	xar v9.2d, v22.2d, v31.2d, #3
	eor x22, x22, x9
	eor x0, x0, x4
	xar v22.2d, v14.2d, v28.2d, #25
	eor x5, x5, x4
	eor x10, x10, x4
	xar v14.2d, v20.2d, v29.2d, #46
	eor x15, x15, x4
	eor x20, x20, x4
	xar v26.2d, v2.2d, v31.2d, #2
	ldr x4, [sp, #0]
	ldr x9, [sp, #8]
	xar v2.2d, v12.2d, v31.2d, #21
	eor x26, x3, x28
	eor x8, x8, x28
	xar v12.2d, v13.2d, v27.2d, #39
	eor x13, x13, x28
	eor x25, x25, x28
	xar v13.2d, v19.2d, v28.2d, #56
	eor x23, x23, x28
	eor x28, x4, x30
	xar v19.2d, v23.2d, v27.2d, #8
	eor x9, x9, x30
	eor x14, x14, x30
	xar v23.2d, v15.2d, v29.2d, #23
	eor x19, x19, x30
	eor x24, x24, x30
	xar v15.2d, v4.2d, v28.2d, #37
	add x30, x1, #0
	ror x1, x6, #20
	xar v28.2d, v24.2d, v28.2d, #50
	ror x2, x12, #21
	ror x3, x25, #43
	xar v24.2d, v21.2d, v30.2d, #62
	ror x4, x24, #50
	ror x6, x9, #44
	xar v8.2d, v8.2d, v27.2d, #9
	ror x12, x13, #39
	ror x25, x17, #49
	xar v4.2d, v16.2d, v30.2d, #19
	ror x24, x21, #62
	ror x9, x22, #3
	xar v16.2d, v5.2d, v29.2d, #28
	ror x13, x19, #56
	ror x17, x11, #54
	xar v5.2d, v3.2d, v27.2d, #36
	ror x21, x8, #9
	ror x22, x14, #25
	eor v0.16b, v0.16b, v29.16b
	ror x19, x23, #8
	ror x11, x7, #58
	xar v27.2d, v18.2d, v27.2d, #43
	ror x8, x16, #19
	ror x14, x20, #46
	xar v3.2d, v17.2d, v31.2d, #49
	ror x23, x15, #23
	ror x7, x10, #61
	xar v30.2d, v11.2d, v30.2d, #54
	ror x16, x5, #28
	ror x5, x26, #36
	xar v31.2d, v7.2d, v31.2d, #58
	ror x10, x30, #63
	ror x15, x28, #37
	xar v29.2d, v10.2d, v29.2d, #61
	ror x20, x27, #2
	bic x26, x2, x1, ror #0
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bic x27, x3, x2, ror #0
	bic x28, x0, x4, ror #0
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bic x30, x1, x0, ror #0
	eor x0, x0, x26
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bic x26, x4, x3, ror #0
	eor x1, x1, x27
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	eor x3, x3, x28
	eor x4, x4, x30
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	eor x2, x2, x26
	bic x26, x7, x6, ror #0
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bic x27, x8, x7, ror #0
	bic x28, x5, x9, ror #0
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bic x30, x6, x5, ror #0
	eor x5, x5, x26
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bic x26, x9, x8, ror #0
	eor x6, x6, x27
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	eor x8, x8, x28
	eor x9, x9, x30
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	eor x7, x7, x26
	bic x26, x12, x11, ror #0
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bic x27, x13, x12, ror #0
	bic x28, x10, x14, ror #0
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bic x30, x11, x10, ror #0
	eor x10, x10, x26
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bic x26, x14, x13, ror #0
	eor x11, x11, x27
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	eor x13, x13, x28
	eor x14, x14, x30
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	eor x12, x12, x26
	bic x26, x17, x16, ror #0
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bic x27, x25, x17, ror #0
	bic x28, x15, x19, ror #0
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bic x30, x16, x15, ror #0
	eor x15, x15, x26
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bic x26, x19, x25, ror #0
	eor x16, x16, x27
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	eor x25, x25, x28
	eor x19, x19, x30
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	eor x17, x17, x26
	bic x26, x22, x21, ror #0
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bic x27, x23, x22, ror #0
	bic x28, x20, x24, ror #0
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bic x30, x21, x20, ror #0
	eor x20, x20, x26
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bic x26, x24, x23, ror #0
	eor x21, x21, x27
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	eor x23, x23, x28
	eor x24, x24, x30
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	eor x22, x22, x26
	movz x26, #32776, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26
	dup v26.2d, x26
	eor v0.16b, v0.16b, v26.16b
	ldr x30, [sp, #112]
	str x0, [x30, #0]
	str x1, [x30, #8]
	str x2, [x30, #16]
	str x3, [x30, #24]
	str x4, [x30, #32]
	str x5, [x30, #40]
	str x6, [x30, #48]
	str x7, [x30, #56]
	str x8, [x30, #64]
	str x9, [x30, #72]
	str x10, [x30, #80]
	str x11, [x30, #88]
	str x12, [x30, #96]
	str x13, [x30, #104]
	str x14, [x30, #112]
	str x15, [x30, #120]
	str x16, [x30, #128]
	str x17, [x30, #136]
	str x25, [x30, #144]
	str x19, [x30, #152]
	str x20, [x30, #160]
	str x21, [x30, #168]
	str x22, [x30, #176]
	str x23, [x30, #184]
	str x24, [x30, #192]
	ldr x0, [sp, #104]
	str q0, [x0, #0]
	str q1, [x0, #16]
	str q2, [x0, #32]
	str q3, [x0, #48]
	str q4, [x0, #64]
	str q5, [x0, #80]
	str q6, [x0, #96]
	str q7, [x0, #112]
	str q8, [x0, #128]
	str q9, [x0, #144]
	str q10, [x0, #160]
	str q11, [x0, #176]
	str q12, [x0, #192]
	str q13, [x0, #208]
	str q14, [x0, #224]
	str q15, [x0, #240]
	str q16, [x0, #256]
	str q17, [x0, #272]
	str q18, [x0, #288]
	str q19, [x0, #304]
	str q20, [x0, #320]
	str q21, [x0, #336]
	str q22, [x0, #352]
	str q23, [x0, #368]
	str q24, [x0, #384]
	ldr x2, [sp, #120]
	ldr q8, [x2, #0]
	ldr q9, [x2, #16]
	ldr q10, [x2, #32]
	ldr q11, [x2, #48]
	ldr q12, [x2, #64]
	ldr q13, [x2, #80]
	ldr q14, [x2, #96]
	ldr q15, [x2, #112]
	ldr x19, [sp, #16]
	ldr x20, [sp, #24]
	ldr x21, [sp, #32]
	ldr x22, [sp, #40]
	ldr x23, [sp, #48]
	ldr x24, [sp, #56]
	ldr x25, [sp, #64]
	ldr x26, [sp, #72]
	ldr x27, [sp, #80]
	ldr x28, [sp, #88]
	ldr x30, [sp, #96]
	add sp, sp, #128
	ret
	.arch_extension nosha3
	.p2align 6
