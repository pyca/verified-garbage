// The functions of `src/internal/vg_keccak_f1600_x3_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600_x3_sha3:
	sub sp, sp, #128
	str q8, [x2, #0]
	str q9, [x2, #16]
	str q10, [x2, #32]
	str q11, [x2, #48]
	str q12, [x2, #64]
	str q13, [x2, #80]
	str q14, [x2, #96]
	str q15, [x2, #112]
	str x19, [sp, #0]
	str x20, [sp, #8]
	str x21, [sp, #16]
	str x22, [sp, #24]
	str x23, [sp, #32]
	str x24, [sp, #40]
	str x25, [sp, #48]
	str x26, [sp, #56]
	str x27, [sp, #64]
	str x28, [sp, #72]
	str x30, [sp, #80]
	str x0, [sp, #88]
	str x1, [sp, #96]
	str x2, [sp, #104]
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
	adrp x16, {VG_KECCAK_RC}
	add x16, x16, {VG_KECCAK_RC}
	ldr q31, [x16, #0]
	str q31, [x0, #32]
	ldr q31, [x16, #16]
	str q31, [x0, #48]
	ldr q31, [x16, #32]
	str q31, [x0, #64]
	ldr q31, [x16, #48]
	str q31, [x0, #80]
	ldr q31, [x16, #64]
	str q31, [x0, #96]
	ldr q31, [x16, #80]
	str q31, [x0, #112]
	ldr q31, [x16, #96]
	str q31, [x0, #128]
	ldr q31, [x16, #112]
	str q31, [x0, #144]
	ldr q31, [x16, #128]
	str q31, [x0, #160]
	ldr q31, [x16, #144]
	str q31, [x0, #176]
	ldr q31, [x16, #160]
	str q31, [x0, #192]
	ldr q31, [x16, #176]
	str q31, [x0, #208]
	movz x16, #12, lsl #0
	str x16, [sp, #112]
	add x30, x0, #0
	ldr x0, [x1, #0]
	ldr x2, [x1, #16]
	ldr x3, [x1, #24]
	ldr x4, [x1, #32]
	ldr x5, [x1, #40]
	ldr x6, [x1, #48]
	ldr x7, [x1, #56]
	ldr x8, [x1, #64]
	ldr x9, [x1, #72]
	ldr x10, [x1, #80]
	ldr x11, [x1, #88]
	ldr x12, [x1, #96]
	ldr x13, [x1, #104]
	ldr x14, [x1, #112]
	ldr x15, [x1, #120]
	ldr x19, [x1, #128]
	ldr x20, [x1, #136]
	ldr x21, [x1, #144]
	ldr x22, [x1, #152]
	ldr x23, [x1, #160]
	ldr x24, [x1, #168]
	ldr x25, [x1, #176]
	ldr x26, [x1, #184]
	ldr x27, [x1, #192]
	ldr x1, [x1, #8]
20:
	eor3 v25.16b, v0.16b, v5.16b, v10.16b
	eor x28, x1, x6
	eor x28, x28, x11
	eor3 v25.16b, v25.16b, v15.16b, v20.16b
	eor x28, x28, x19
	eor x28, x28, x24
	eor3 v26.16b, v1.16b, v6.16b, v11.16b
	eor x16, x0, x5
	eor x16, x16, x10
	eor3 v26.16b, v26.16b, v16.16b, v21.16b
	eor x16, x16, x15
	eor x16, x16, x23
	eor3 v27.16b, v2.16b, v7.16b, v12.16b
	eor x17, x2, x7
	eor x17, x17, x12
	eor3 v27.16b, v27.16b, v17.16b, v22.16b
	eor x17, x17, x20
	eor x17, x17, x25
	eor3 v28.16b, v3.16b, v8.16b, v13.16b
	str x1, [x30, #0]
	eor x1, x3, x8
	eor3 v28.16b, v28.16b, v18.16b, v23.16b
	eor x1, x1, x13
	eor x1, x1, x21
	eor3 v29.16b, v4.16b, v9.16b, v14.16b
	eor x1, x1, x26
	str x11, [x30, #8]
	eor3 v29.16b, v29.16b, v19.16b, v24.16b
	eor x11, x4, x9
	eor x11, x11, x14
	rax1 v30.2d, v29.2d, v26.2d
	eor x11, x11, x22
	eor x11, x11, x27
	rax1 v26.2d, v26.2d, v28.2d
	str x24, [x30, #16]
	eor x24, x11, x28, ror #63
	rax1 v28.2d, v28.2d, v25.2d
	eor x28, x28, x1, ror #63
	eor x1, x1, x16, ror #63
	rax1 v25.2d, v25.2d, v27.2d
	eor x16, x16, x17, ror #63
	eor x17, x17, x11, ror #63
	rax1 v27.2d, v27.2d, v29.2d
	eor x0, x0, x24
	eor x5, x5, x24
	eor v0.16b, v0.16b, v30.16b
	ror x5, x5, #28
	eor x10, x10, x24
	xar v5.2d, v5.2d, v30.2d, #28
	ror x10, x10, #61
	xar v10.2d, v10.2d, v30.2d, #61
	eor x15, x15, x24
	ror x15, x15, #23
	xar v15.2d, v15.2d, v30.2d, #23
	eor x23, x23, x24
	ror x23, x23, #46
	xar v20.2d, v20.2d, v30.2d, #46
	eor x2, x2, x28
	ror x2, x2, #2
	xar v2.2d, v2.2d, v26.2d, #2
	eor x7, x7, x28
	ror x7, x7, #58
	xar v7.2d, v7.2d, v26.2d, #58
	eor x12, x12, x28
	ror x12, x12, #21
	xar v12.2d, v12.2d, v26.2d, #21
	eor x20, x20, x28
	ror x20, x20, #49
	xar v17.2d, v17.2d, v26.2d, #49
	eor x25, x25, x28
	ror x25, x25, #3
	xar v22.2d, v22.2d, v26.2d, #3
	eor x3, x3, x17
	ror x3, x3, #36
	xar v4.2d, v4.2d, v28.2d, #37
	eor x8, x8, x17
	ror x8, x8, #9
	xar v9.2d, v9.2d, v28.2d, #44
	eor x13, x13, x17
	ror x13, x13, #39
	xar v14.2d, v14.2d, v28.2d, #25
	eor x21, x21, x17
	ror x21, x21, #43
	xar v19.2d, v19.2d, v28.2d, #56
	eor x26, x26, x17
	ror x26, x26, #8
	xar v24.2d, v24.2d, v28.2d, #50
	eor x4, x4, x1
	ror x4, x4, #37
	xar v29.2d, v6.2d, v25.2d, #20
	eor x9, x9, x1
	ror x9, x9, #44
	xar v31.2d, v18.2d, v27.2d, #43
	eor x14, x14, x1
	ror x14, x14, #25
	bcax v6.16b, v31.16b, v0.16b, v24.16b
	eor x22, x22, x1
	ror x22, x22, #56
	bcax v18.16b, v24.16b, v29.16b, v0.16b
	eor x27, x27, x1
	bcax v24.16b, v12.16b, v24.16b, v31.16b
	ror x27, x27, #50
	eor x11, x6, x16
	bcax v0.16b, v0.16b, v12.16b, v29.16b
	ror x11, x11, #20
	bic x24, x21, x12, ror #0
	bcax v12.16b, v29.16b, v31.16b, v12.16b
	bic x28, x27, x21, ror #0
	bic x6, x0, x27, ror #0
	xar v29.2d, v16.2d, v25.2d, #19
	eor x6, x21, x6
	bic x21, x11, x0, ror #0
	xar v31.2d, v3.2d, v27.2d, #36
	eor x21, x27, x21
	eor x27, x12, x28
	bcax v16.16b, v31.16b, v10.16b, v9.16b
	bic x28, x12, x11, ror #0
	eor x12, x11, x24
	bcax v3.16b, v9.16b, v29.16b, v10.16b
	eor x0, x0, x28
	eor x11, x19, x16
	bcax v9.16b, v22.16b, v9.16b, v31.16b
	ror x11, x11, #19
	bic x24, x3, x25, ror #0
	bcax v10.16b, v10.16b, v22.16b, v29.16b
	bic x28, x9, x3, ror #0
	bic x19, x10, x9, ror #0
	bcax v22.16b, v29.16b, v31.16b, v22.16b
	eor x19, x3, x19
	bic x3, x11, x10, ror #0
	xar v29.2d, v1.2d, v25.2d, #63
	eor x3, x9, x3
	eor x9, x25, x28
	xar v31.2d, v13.2d, v27.2d, #39
	bic x28, x25, x11, ror #0
	eor x25, x11, x24
	bcax v1.16b, v31.16b, v20.16b, v19.16b
	eor x10, x10, x28
	ldr x11, [x30, #0]
	bcax v13.16b, v19.16b, v29.16b, v20.16b
	eor x11, x11, x16
	ror x11, x11, #63
	bcax v19.16b, v7.16b, v19.16b, v31.16b
	bic x24, x13, x7, ror #0
	bic x28, x22, x13, ror #0
	bcax v20.16b, v20.16b, v7.16b, v29.16b
	bic x1, x23, x22, ror #0
	eor x1, x13, x1
	bcax v7.16b, v29.16b, v31.16b, v7.16b
	bic x13, x11, x23, ror #0
	xar v29.2d, v11.2d, v25.2d, #54
	eor x13, x22, x13
	eor x22, x7, x28
	xar v31.2d, v23.2d, v27.2d, #8
	bic x28, x7, x11, ror #0
	eor x7, x11, x24
	bcax v11.16b, v31.16b, v5.16b, v4.16b
	eor x23, x23, x28
	ldr x24, [x30, #8]
	bcax v23.16b, v4.16b, v29.16b, v5.16b
	eor x24, x24, x16
	ror x24, x24, #54
	bcax v4.16b, v17.16b, v4.16b, v31.16b
	bic x28, x26, x20, ror #0
	bic x17, x4, x26, ror #0
	bcax v5.16b, v5.16b, v17.16b, v29.16b
	bic x11, x5, x4, ror #0
	eor x11, x26, x11
	bcax v17.16b, v29.16b, v31.16b, v17.16b
	bic x26, x24, x5, ror #0
	eor x26, x4, x26
	xar v29.2d, v21.2d, v25.2d, #62
	eor x4, x20, x17
	bic x17, x20, x24, ror #0
	xar v31.2d, v8.2d, v27.2d, #9
	eor x20, x24, x28
	eor x5, x5, x17
	bcax v21.16b, v31.16b, v15.16b, v14.16b
	ldr x28, [x30, #16]
	eor x28, x28, x16
	bcax v8.16b, v14.16b, v29.16b, v15.16b
	ror x28, x28, #62
	bic x17, x8, x2, ror #0
	bcax v14.16b, v2.16b, v14.16b, v31.16b
	bic x16, x14, x8, ror #0
	bic x24, x15, x14, ror #0
	bcax v15.16b, v15.16b, v2.16b, v29.16b
	eor x24, x8, x24
	bic x8, x28, x15, ror #0
	bcax v2.16b, v29.16b, v31.16b, v2.16b
	eor x8, x14, x8
	eor x14, x2, x16
	ldr q31, [x30, #32]
	bic x16, x2, x28, ror #0
	eor x2, x28, x17
	trn1 v31.2d, v31.2d, v31.2d
	eor x15, x15, x16
	ldr x16, [x30, #32]
	eor v0.16b, v0.16b, v31.16b
	eor x0, x0, x16
	eor3 v25.16b, v0.16b, v16.16b, v7.16b
	eor x28, x12, x3
	eor x28, x28, x22
	eor3 v25.16b, v25.16b, v23.16b, v14.16b
	eor x28, x28, x5
	eor x28, x28, x24
	eor3 v26.16b, v12.16b, v3.16b, v19.16b
	eor x16, x0, x19
	eor x16, x16, x7
	eor3 v26.16b, v26.16b, v5.16b, v21.16b
	eor x16, x16, x26
	eor x16, x16, x14
	eor3 v27.16b, v24.16b, v10.16b, v1.16b
	eor x17, x27, x10
	eor x17, x17, x1
	eor3 v27.16b, v27.16b, v17.16b, v8.16b
	eor x17, x17, x20
	eor x17, x17, x8
	eor3 v28.16b, v6.16b, v22.16b, v13.16b
	str x12, [x30, #0]
	eor x12, x6, x25
	eor3 v28.16b, v28.16b, v4.16b, v15.16b
	eor x12, x12, x13
	eor x12, x12, x4
	eor3 v29.16b, v18.16b, v9.16b, v20.16b
	eor x12, x12, x15
	str x22, [x30, #8]
	eor3 v29.16b, v29.16b, v11.16b, v2.16b
	eor x22, x21, x9
	eor x22, x22, x23
	rax1 v30.2d, v29.2d, v26.2d
	eor x22, x22, x11
	eor x22, x22, x2
	rax1 v26.2d, v26.2d, v28.2d
	str x24, [x30, #16]
	eor x24, x22, x28, ror #63
	rax1 v28.2d, v28.2d, v25.2d
	eor x28, x28, x12, ror #63
	eor x12, x12, x16, ror #63
	rax1 v25.2d, v25.2d, v27.2d
	eor x16, x16, x17, ror #63
	eor x17, x17, x22, ror #63
	rax1 v27.2d, v27.2d, v29.2d
	eor x0, x0, x24
	eor x19, x19, x24
	eor v0.16b, v0.16b, v30.16b
	ror x19, x19, #28
	eor x7, x7, x24
	xar v16.2d, v16.2d, v30.2d, #28
	ror x7, x7, #61
	xar v7.2d, v7.2d, v30.2d, #61
	eor x26, x26, x24
	ror x26, x26, #23
	xar v23.2d, v23.2d, v30.2d, #23
	eor x14, x14, x24
	ror x14, x14, #46
	xar v14.2d, v14.2d, v30.2d, #46
	eor x27, x27, x28
	ror x27, x27, #2
	xar v24.2d, v24.2d, v26.2d, #2
	eor x10, x10, x28
	ror x10, x10, #58
	xar v10.2d, v10.2d, v26.2d, #58
	eor x1, x1, x28
	ror x1, x1, #21
	xar v1.2d, v1.2d, v26.2d, #21
	eor x20, x20, x28
	ror x20, x20, #49
	xar v17.2d, v17.2d, v26.2d, #49
	eor x8, x8, x28
	ror x8, x8, #3
	xar v8.2d, v8.2d, v26.2d, #3
	eor x6, x6, x17
	ror x6, x6, #36
	xar v18.2d, v18.2d, v28.2d, #37
	eor x25, x25, x17
	ror x25, x25, #9
	xar v9.2d, v9.2d, v28.2d, #44
	eor x13, x13, x17
	ror x13, x13, #39
	xar v20.2d, v20.2d, v28.2d, #25
	eor x4, x4, x17
	ror x4, x4, #43
	xar v11.2d, v11.2d, v28.2d, #56
	eor x15, x15, x17
	ror x15, x15, #8
	xar v2.2d, v2.2d, v28.2d, #50
	eor x21, x21, x12
	ror x21, x21, #37
	xar v29.2d, v3.2d, v25.2d, #20
	eor x9, x9, x12
	ror x9, x9, #44
	xar v31.2d, v4.2d, v27.2d, #43
	eor x23, x23, x12
	ror x23, x23, #25
	bcax v3.16b, v31.16b, v0.16b, v2.16b
	eor x11, x11, x12
	ror x11, x11, #56
	bcax v4.16b, v2.16b, v29.16b, v0.16b
	eor x2, x2, x12
	bcax v2.16b, v1.16b, v2.16b, v31.16b
	ror x2, x2, #50
	eor x22, x3, x16
	bcax v0.16b, v0.16b, v1.16b, v29.16b
	ror x22, x22, #20
	bic x24, x4, x1, ror #0
	bcax v1.16b, v29.16b, v31.16b, v1.16b
	bic x28, x2, x4, ror #0
	bic x3, x0, x2, ror #0
	xar v29.2d, v5.2d, v25.2d, #19
	eor x3, x4, x3
	bic x4, x22, x0, ror #0
	xar v31.2d, v6.2d, v27.2d, #36
	eor x4, x2, x4
	eor x2, x1, x28
	bcax v5.16b, v31.16b, v7.16b, v9.16b
	bic x28, x1, x22, ror #0
	eor x1, x22, x24
	bcax v6.16b, v9.16b, v29.16b, v7.16b
	eor x0, x0, x28
	eor x22, x5, x16
	bcax v9.16b, v8.16b, v9.16b, v31.16b
	ror x22, x22, #19
	bic x24, x6, x8, ror #0
	bcax v7.16b, v7.16b, v8.16b, v29.16b
	bic x28, x9, x6, ror #0
	bic x5, x7, x9, ror #0
	bcax v8.16b, v29.16b, v31.16b, v8.16b
	eor x5, x6, x5
	bic x6, x22, x7, ror #0
	xar v29.2d, v12.2d, v25.2d, #63
	eor x6, x9, x6
	eor x9, x8, x28
	xar v31.2d, v13.2d, v27.2d, #39
	bic x28, x8, x22, ror #0
	eor x8, x22, x24
	bcax v12.16b, v31.16b, v14.16b, v11.16b
	eor x7, x7, x28
	ldr x22, [x30, #0]
	bcax v13.16b, v11.16b, v29.16b, v14.16b
	eor x22, x22, x16
	ror x22, x22, #63
	bcax v11.16b, v10.16b, v11.16b, v31.16b
	bic x24, x13, x10, ror #0
	bic x28, x11, x13, ror #0
	bcax v14.16b, v14.16b, v10.16b, v29.16b
	bic x12, x14, x11, ror #0
	eor x12, x13, x12
	bcax v10.16b, v29.16b, v31.16b, v10.16b
	bic x13, x22, x14, ror #0
	xar v29.2d, v19.2d, v25.2d, #54
	eor x13, x11, x13
	eor x11, x10, x28
	xar v31.2d, v15.2d, v27.2d, #8
	bic x28, x10, x22, ror #0
	eor x10, x22, x24
	bcax v19.16b, v31.16b, v16.16b, v18.16b
	eor x14, x14, x28
	ldr x24, [x30, #8]
	bcax v15.16b, v18.16b, v29.16b, v16.16b
	eor x24, x24, x16
	ror x24, x24, #54
	bcax v18.16b, v17.16b, v18.16b, v31.16b
	bic x28, x15, x20, ror #0
	bic x17, x21, x15, ror #0
	bcax v16.16b, v16.16b, v17.16b, v29.16b
	bic x22, x19, x21, ror #0
	eor x22, x15, x22
	bcax v17.16b, v29.16b, v31.16b, v17.16b
	bic x15, x24, x19, ror #0
	eor x15, x21, x15
	xar v29.2d, v21.2d, v25.2d, #62
	eor x21, x20, x17
	bic x17, x20, x24, ror #0
	xar v31.2d, v22.2d, v27.2d, #9
	eor x20, x24, x28
	eor x19, x19, x17
	bcax v21.16b, v31.16b, v23.16b, v20.16b
	ldr x28, [x30, #16]
	eor x28, x28, x16
	bcax v22.16b, v20.16b, v29.16b, v23.16b
	ror x28, x28, #62
	bic x17, x25, x27, ror #0
	bcax v20.16b, v24.16b, v20.16b, v31.16b
	bic x16, x23, x25, ror #0
	bic x24, x26, x23, ror #0
	bcax v23.16b, v23.16b, v24.16b, v29.16b
	eor x24, x25, x24
	bic x25, x28, x26, ror #0
	bcax v24.16b, v29.16b, v31.16b, v24.16b
	eor x25, x23, x25
	eor x23, x27, x16
	ldr q31, [x30, #32]
	bic x16, x27, x28, ror #0
	eor x27, x28, x17
	trn2 v31.2d, v31.2d, v31.2d
	eor x26, x26, x16
	ldr x16, [x30, #40]
	eor v0.16b, v0.16b, v31.16b
	eor x0, x0, x16
	add x30, x30, #16
	ldr x16, [sp, #112]
	sub x16, x16, #1
	str x16, [sp, #112]
	cbnz x16, 20b
	ldr x16, [sp, #96]
	str x0, [x16, #0]
	str x1, [x16, #8]
	str x2, [x16, #16]
	str x3, [x16, #24]
	str x4, [x16, #32]
	str x5, [x16, #40]
	str x6, [x16, #48]
	str x7, [x16, #56]
	str x8, [x16, #64]
	str x9, [x16, #72]
	str x10, [x16, #80]
	str x11, [x16, #88]
	str x12, [x16, #96]
	str x13, [x16, #104]
	str x14, [x16, #112]
	str x15, [x16, #120]
	str x19, [x16, #128]
	str x20, [x16, #136]
	str x21, [x16, #144]
	str x22, [x16, #152]
	str x23, [x16, #160]
	str x24, [x16, #168]
	str x25, [x16, #176]
	str x26, [x16, #184]
	str x27, [x16, #192]
	ldr x0, [sp, #88]
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
	ldr x2, [sp, #104]
	ldr q8, [x2, #0]
	ldr q9, [x2, #16]
	ldr q10, [x2, #32]
	ldr q11, [x2, #48]
	ldr q12, [x2, #64]
	ldr q13, [x2, #80]
	ldr q14, [x2, #96]
	ldr q15, [x2, #112]
	ldr x19, [sp, #0]
	ldr x20, [sp, #8]
	ldr x21, [sp, #16]
	ldr x22, [sp, #24]
	ldr x23, [sp, #32]
	ldr x24, [sp, #40]
	ldr x25, [sp, #48]
	ldr x26, [sp, #56]
	ldr x27, [sp, #64]
	ldr x28, [sp, #72]
	ldr x30, [sp, #80]
	add sp, sp, #128
	ret
	.p2align 6
