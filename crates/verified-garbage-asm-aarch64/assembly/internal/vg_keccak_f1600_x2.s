// The functions of `src/internal/vg_keccak_f1600_x2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600_x2:
	str q8, [x1, #0]
	str q9, [x1, #16]
	str q10, [x1, #32]
	str q11, [x1, #48]
	str q12, [x1, #64]
	str q13, [x1, #80]
	str q14, [x1, #96]
	str q15, [x1, #112]
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
	movz x16, #1, lsl #0
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32898, lsl #0
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32906, lsl #0
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32768, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32907, lsl #0
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #138, lsl #0
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #136, lsl #0
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #16
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32907, lsl #0
	movk x16, #32768, lsl #16
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #139, lsl #0
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32905, lsl #0
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32771, lsl #0
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32770, lsl #0
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #128, lsl #0
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32778, lsl #0
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32896, lsl #0
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
	movz x16, #32776, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor v25.16b, v0.16b, v5.16b
	eor v25.16b, v25.16b, v10.16b
	eor v25.16b, v25.16b, v15.16b
	eor v25.16b, v25.16b, v20.16b
	eor v26.16b, v1.16b, v6.16b
	eor v26.16b, v26.16b, v11.16b
	eor v26.16b, v26.16b, v16.16b
	eor v26.16b, v26.16b, v21.16b
	eor v27.16b, v2.16b, v7.16b
	eor v27.16b, v27.16b, v12.16b
	eor v27.16b, v27.16b, v17.16b
	eor v27.16b, v27.16b, v22.16b
	eor v28.16b, v3.16b, v8.16b
	eor v28.16b, v28.16b, v13.16b
	eor v28.16b, v28.16b, v18.16b
	eor v28.16b, v28.16b, v23.16b
	eor v29.16b, v4.16b, v9.16b
	eor v29.16b, v29.16b, v14.16b
	eor v29.16b, v29.16b, v19.16b
	eor v29.16b, v29.16b, v24.16b
	ushr v30.2d, v26.2d, #63
	sli v30.2d, v26.2d, #1
	eor v30.16b, v29.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	eor v5.16b, v5.16b, v30.16b
	eor v10.16b, v10.16b, v30.16b
	eor v15.16b, v15.16b, v30.16b
	eor v20.16b, v20.16b, v30.16b
	ushr v30.2d, v27.2d, #63
	sli v30.2d, v27.2d, #1
	eor v30.16b, v25.16b, v30.16b
	eor v1.16b, v1.16b, v30.16b
	eor v6.16b, v6.16b, v30.16b
	eor v11.16b, v11.16b, v30.16b
	eor v16.16b, v16.16b, v30.16b
	eor v21.16b, v21.16b, v30.16b
	ushr v30.2d, v28.2d, #63
	sli v30.2d, v28.2d, #1
	eor v30.16b, v26.16b, v30.16b
	eor v2.16b, v2.16b, v30.16b
	eor v7.16b, v7.16b, v30.16b
	eor v12.16b, v12.16b, v30.16b
	eor v17.16b, v17.16b, v30.16b
	eor v22.16b, v22.16b, v30.16b
	ushr v30.2d, v29.2d, #63
	sli v30.2d, v29.2d, #1
	eor v30.16b, v27.16b, v30.16b
	eor v3.16b, v3.16b, v30.16b
	eor v8.16b, v8.16b, v30.16b
	eor v13.16b, v13.16b, v30.16b
	eor v18.16b, v18.16b, v30.16b
	eor v23.16b, v23.16b, v30.16b
	ushr v30.2d, v25.2d, #63
	sli v30.2d, v25.2d, #1
	eor v30.16b, v28.16b, v30.16b
	eor v4.16b, v4.16b, v30.16b
	eor v9.16b, v9.16b, v30.16b
	eor v14.16b, v14.16b, v30.16b
	eor v19.16b, v19.16b, v30.16b
	eor v24.16b, v24.16b, v30.16b
	mov v25.16b, v1.16b
	mov v26.16b, v10.16b
	ushr v10.2d, v25.2d, #63
	sli v10.2d, v25.2d, #1
	mov v25.16b, v26.16b
	mov v26.16b, v7.16b
	ushr v7.2d, v25.2d, #61
	sli v7.2d, v25.2d, #3
	mov v25.16b, v26.16b
	mov v26.16b, v11.16b
	ushr v11.2d, v25.2d, #58
	sli v11.2d, v25.2d, #6
	mov v25.16b, v26.16b
	mov v26.16b, v17.16b
	ushr v17.2d, v25.2d, #54
	sli v17.2d, v25.2d, #10
	mov v25.16b, v26.16b
	mov v26.16b, v18.16b
	ushr v18.2d, v25.2d, #49
	sli v18.2d, v25.2d, #15
	mov v25.16b, v26.16b
	mov v26.16b, v3.16b
	ushr v3.2d, v25.2d, #43
	sli v3.2d, v25.2d, #21
	mov v25.16b, v26.16b
	mov v26.16b, v5.16b
	ushr v5.2d, v25.2d, #36
	sli v5.2d, v25.2d, #28
	mov v25.16b, v26.16b
	mov v26.16b, v16.16b
	ushr v16.2d, v25.2d, #28
	sli v16.2d, v25.2d, #36
	mov v25.16b, v26.16b
	mov v26.16b, v8.16b
	ushr v8.2d, v25.2d, #19
	sli v8.2d, v25.2d, #45
	mov v25.16b, v26.16b
	mov v26.16b, v21.16b
	ushr v21.2d, v25.2d, #9
	sli v21.2d, v25.2d, #55
	mov v25.16b, v26.16b
	mov v26.16b, v24.16b
	ushr v24.2d, v25.2d, #62
	sli v24.2d, v25.2d, #2
	mov v25.16b, v26.16b
	mov v26.16b, v4.16b
	ushr v4.2d, v25.2d, #50
	sli v4.2d, v25.2d, #14
	mov v25.16b, v26.16b
	mov v26.16b, v15.16b
	ushr v15.2d, v25.2d, #37
	sli v15.2d, v25.2d, #27
	mov v25.16b, v26.16b
	mov v26.16b, v23.16b
	ushr v23.2d, v25.2d, #23
	sli v23.2d, v25.2d, #41
	mov v25.16b, v26.16b
	mov v26.16b, v19.16b
	ushr v19.2d, v25.2d, #8
	sli v19.2d, v25.2d, #56
	mov v25.16b, v26.16b
	mov v26.16b, v13.16b
	ushr v13.2d, v25.2d, #56
	sli v13.2d, v25.2d, #8
	mov v25.16b, v26.16b
	mov v26.16b, v12.16b
	ushr v12.2d, v25.2d, #39
	sli v12.2d, v25.2d, #25
	mov v25.16b, v26.16b
	mov v26.16b, v2.16b
	ushr v2.2d, v25.2d, #21
	sli v2.2d, v25.2d, #43
	mov v25.16b, v26.16b
	mov v26.16b, v20.16b
	ushr v20.2d, v25.2d, #2
	sli v20.2d, v25.2d, #62
	mov v25.16b, v26.16b
	mov v26.16b, v14.16b
	ushr v14.2d, v25.2d, #46
	sli v14.2d, v25.2d, #18
	mov v25.16b, v26.16b
	mov v26.16b, v22.16b
	ushr v22.2d, v25.2d, #25
	sli v22.2d, v25.2d, #39
	mov v25.16b, v26.16b
	mov v26.16b, v9.16b
	ushr v9.2d, v25.2d, #3
	sli v9.2d, v25.2d, #61
	mov v25.16b, v26.16b
	mov v26.16b, v6.16b
	ushr v6.2d, v25.2d, #44
	sli v6.2d, v25.2d, #20
	mov v25.16b, v26.16b
	mov v26.16b, v1.16b
	ushr v1.2d, v25.2d, #20
	sli v1.2d, v25.2d, #44
	mov v25.16b, v26.16b
	mov v25.16b, v0.16b
	mov v26.16b, v1.16b
	mov v27.16b, v2.16b
	mov v28.16b, v3.16b
	mov v29.16b, v4.16b
	bic v30.16b, v27.16b, v26.16b
	eor v0.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v1.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v2.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v3.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v4.16b, v29.16b, v30.16b
	mov v25.16b, v5.16b
	mov v26.16b, v6.16b
	mov v27.16b, v7.16b
	mov v28.16b, v8.16b
	mov v29.16b, v9.16b
	bic v30.16b, v27.16b, v26.16b
	eor v5.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v6.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v7.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v8.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v9.16b, v29.16b, v30.16b
	mov v25.16b, v10.16b
	mov v26.16b, v11.16b
	mov v27.16b, v12.16b
	mov v28.16b, v13.16b
	mov v29.16b, v14.16b
	bic v30.16b, v27.16b, v26.16b
	eor v10.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v11.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v12.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v13.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v14.16b, v29.16b, v30.16b
	mov v25.16b, v15.16b
	mov v26.16b, v16.16b
	mov v27.16b, v17.16b
	mov v28.16b, v18.16b
	mov v29.16b, v19.16b
	bic v30.16b, v27.16b, v26.16b
	eor v15.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v16.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v17.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v18.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v19.16b, v29.16b, v30.16b
	mov v25.16b, v20.16b
	mov v26.16b, v21.16b
	mov v27.16b, v22.16b
	mov v28.16b, v23.16b
	mov v29.16b, v24.16b
	bic v30.16b, v27.16b, v26.16b
	eor v20.16b, v25.16b, v30.16b
	bic v30.16b, v28.16b, v27.16b
	eor v21.16b, v26.16b, v30.16b
	bic v30.16b, v29.16b, v28.16b
	eor v22.16b, v27.16b, v30.16b
	bic v30.16b, v25.16b, v29.16b
	eor v23.16b, v28.16b, v30.16b
	bic v30.16b, v26.16b, v25.16b
	eor v24.16b, v29.16b, v30.16b
	dup v25.2d, x16
	eor v0.16b, v0.16b, v25.16b
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
	ldr q8, [x1, #0]
	ldr q9, [x1, #16]
	ldr q10, [x1, #32]
	ldr q11, [x1, #48]
	ldr q12, [x1, #64]
	ldr q13, [x1, #80]
	ldr q14, [x1, #96]
	ldr q15, [x1, #112]
	ret
	.p2align 6
