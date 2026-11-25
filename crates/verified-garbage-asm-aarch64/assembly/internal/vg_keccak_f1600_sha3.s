// The functions of `src/internal/vg_keccak_f1600_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600_sha3:
	str q8, [x1, #384]
	str q9, [x1, #400]
	str q10, [x1, #416]
	str q11, [x1, #432]
	str q12, [x1, #448]
	str q13, [x1, #464]
	str q14, [x1, #480]
	str q15, [x1, #496]
	adrp x16, {VG_KECCAK_RC_PAIRS}
	add x16, x16, {VG_KECCAK_RC_PAIRS}
	ldr q31, [x16, #0]
	str q31, [x1, #0]
	ldr q31, [x16, #16]
	str q31, [x1, #16]
	ldr q31, [x16, #32]
	str q31, [x1, #32]
	ldr q31, [x16, #48]
	str q31, [x1, #48]
	ldr q31, [x16, #64]
	str q31, [x1, #64]
	ldr q31, [x16, #80]
	str q31, [x1, #80]
	ldr q31, [x16, #96]
	str q31, [x1, #96]
	ldr q31, [x16, #112]
	str q31, [x1, #112]
	ldr q31, [x16, #128]
	str q31, [x1, #128]
	ldr q31, [x16, #144]
	str q31, [x1, #144]
	ldr q31, [x16, #160]
	str q31, [x1, #160]
	ldr q31, [x16, #176]
	str q31, [x1, #176]
	ldr q31, [x16, #192]
	str q31, [x1, #192]
	ldr q31, [x16, #208]
	str q31, [x1, #208]
	ldr q31, [x16, #224]
	str q31, [x1, #224]
	ldr q31, [x16, #240]
	str q31, [x1, #240]
	ldr q31, [x16, #256]
	str q31, [x1, #256]
	ldr q31, [x16, #272]
	str q31, [x1, #272]
	ldr q31, [x16, #288]
	str q31, [x1, #288]
	ldr q31, [x16, #304]
	str q31, [x1, #304]
	ldr q31, [x16, #320]
	str q31, [x1, #320]
	ldr q31, [x16, #336]
	str q31, [x1, #336]
	ldr q31, [x16, #352]
	str q31, [x1, #352]
	ldr q31, [x16, #368]
	str q31, [x1, #368]
	ldr q0, [x0, #0]
	ext v1.16b, v0.16b, v0.16b, #8
	ldr q2, [x0, #16]
	ext v3.16b, v2.16b, v2.16b, #8
	ldr q4, [x0, #32]
	ext v5.16b, v4.16b, v4.16b, #8
	ldr q6, [x0, #48]
	ext v7.16b, v6.16b, v6.16b, #8
	ldr q8, [x0, #64]
	ext v9.16b, v8.16b, v8.16b, #8
	ldr q10, [x0, #80]
	ext v11.16b, v10.16b, v10.16b, #8
	ldr q12, [x0, #96]
	ext v13.16b, v12.16b, v12.16b, #8
	ldr q14, [x0, #112]
	ext v15.16b, v14.16b, v14.16b, #8
	ldr q16, [x0, #128]
	ext v17.16b, v16.16b, v16.16b, #8
	ldr q18, [x0, #144]
	ext v19.16b, v18.16b, v18.16b, #8
	ldr q20, [x0, #160]
	ext v21.16b, v20.16b, v20.16b, #8
	ldr q22, [x0, #176]
	ext v23.16b, v22.16b, v22.16b, #8
	ldr x16, [x0, #192]
	dup v24.2d, x16
	add x16, x1, #0
	movz x17, #12, lsl #0
20:
	eor3 v25.16b, v0.16b, v5.16b, v10.16b
	eor3 v25.16b, v25.16b, v15.16b, v20.16b
	eor3 v26.16b, v1.16b, v6.16b, v11.16b
	eor3 v26.16b, v26.16b, v16.16b, v21.16b
	eor3 v27.16b, v2.16b, v7.16b, v12.16b
	eor3 v27.16b, v27.16b, v17.16b, v22.16b
	eor3 v28.16b, v3.16b, v8.16b, v13.16b
	eor3 v28.16b, v28.16b, v18.16b, v23.16b
	eor3 v29.16b, v4.16b, v9.16b, v14.16b
	eor3 v29.16b, v29.16b, v19.16b, v24.16b
	rax1 v30.2d, v29.2d, v26.2d
	rax1 v26.2d, v26.2d, v28.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v25.2d, v25.2d, v27.2d
	rax1 v27.2d, v27.2d, v29.2d
	eor v0.16b, v0.16b, v30.16b
	xar v5.2d, v5.2d, v30.2d, #28
	xar v10.2d, v10.2d, v30.2d, #61
	xar v15.2d, v15.2d, v30.2d, #23
	xar v20.2d, v20.2d, v30.2d, #46
	xar v2.2d, v2.2d, v26.2d, #2
	xar v7.2d, v7.2d, v26.2d, #58
	xar v12.2d, v12.2d, v26.2d, #21
	xar v17.2d, v17.2d, v26.2d, #49
	xar v22.2d, v22.2d, v26.2d, #3
	xar v4.2d, v4.2d, v28.2d, #37
	xar v9.2d, v9.2d, v28.2d, #44
	xar v14.2d, v14.2d, v28.2d, #25
	xar v19.2d, v19.2d, v28.2d, #56
	xar v24.2d, v24.2d, v28.2d, #50
	xar v29.2d, v6.2d, v25.2d, #20
	xar v31.2d, v18.2d, v27.2d, #43
	bcax v6.16b, v31.16b, v0.16b, v24.16b
	bcax v18.16b, v24.16b, v29.16b, v0.16b
	bcax v24.16b, v12.16b, v24.16b, v31.16b
	bcax v0.16b, v0.16b, v12.16b, v29.16b
	bcax v12.16b, v29.16b, v31.16b, v12.16b
	xar v29.2d, v16.2d, v25.2d, #19
	xar v31.2d, v3.2d, v27.2d, #36
	bcax v16.16b, v31.16b, v10.16b, v9.16b
	bcax v3.16b, v9.16b, v29.16b, v10.16b
	bcax v9.16b, v22.16b, v9.16b, v31.16b
	bcax v10.16b, v10.16b, v22.16b, v29.16b
	bcax v22.16b, v29.16b, v31.16b, v22.16b
	xar v29.2d, v1.2d, v25.2d, #63
	xar v31.2d, v13.2d, v27.2d, #39
	bcax v1.16b, v31.16b, v20.16b, v19.16b
	bcax v13.16b, v19.16b, v29.16b, v20.16b
	bcax v19.16b, v7.16b, v19.16b, v31.16b
	bcax v20.16b, v20.16b, v7.16b, v29.16b
	bcax v7.16b, v29.16b, v31.16b, v7.16b
	xar v29.2d, v11.2d, v25.2d, #54
	xar v31.2d, v23.2d, v27.2d, #8
	bcax v11.16b, v31.16b, v5.16b, v4.16b
	bcax v23.16b, v4.16b, v29.16b, v5.16b
	bcax v4.16b, v17.16b, v4.16b, v31.16b
	bcax v5.16b, v5.16b, v17.16b, v29.16b
	bcax v17.16b, v29.16b, v31.16b, v17.16b
	xar v29.2d, v21.2d, v25.2d, #62
	xar v31.2d, v8.2d, v27.2d, #9
	bcax v21.16b, v31.16b, v15.16b, v14.16b
	bcax v8.16b, v14.16b, v29.16b, v15.16b
	bcax v14.16b, v2.16b, v14.16b, v31.16b
	bcax v15.16b, v15.16b, v2.16b, v29.16b
	bcax v2.16b, v29.16b, v31.16b, v2.16b
	ldr q31, [x16, #0]
	eor v0.16b, v0.16b, v31.16b
	eor3 v25.16b, v0.16b, v16.16b, v7.16b
	eor3 v25.16b, v25.16b, v23.16b, v14.16b
	eor3 v26.16b, v12.16b, v3.16b, v19.16b
	eor3 v26.16b, v26.16b, v5.16b, v21.16b
	eor3 v27.16b, v24.16b, v10.16b, v1.16b
	eor3 v27.16b, v27.16b, v17.16b, v8.16b
	eor3 v28.16b, v6.16b, v22.16b, v13.16b
	eor3 v28.16b, v28.16b, v4.16b, v15.16b
	eor3 v29.16b, v18.16b, v9.16b, v20.16b
	eor3 v29.16b, v29.16b, v11.16b, v2.16b
	rax1 v30.2d, v29.2d, v26.2d
	rax1 v26.2d, v26.2d, v28.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v25.2d, v25.2d, v27.2d
	rax1 v27.2d, v27.2d, v29.2d
	eor v0.16b, v0.16b, v30.16b
	xar v16.2d, v16.2d, v30.2d, #28
	xar v7.2d, v7.2d, v30.2d, #61
	xar v23.2d, v23.2d, v30.2d, #23
	xar v14.2d, v14.2d, v30.2d, #46
	xar v24.2d, v24.2d, v26.2d, #2
	xar v10.2d, v10.2d, v26.2d, #58
	xar v1.2d, v1.2d, v26.2d, #21
	xar v17.2d, v17.2d, v26.2d, #49
	xar v8.2d, v8.2d, v26.2d, #3
	xar v18.2d, v18.2d, v28.2d, #37
	xar v9.2d, v9.2d, v28.2d, #44
	xar v20.2d, v20.2d, v28.2d, #25
	xar v11.2d, v11.2d, v28.2d, #56
	xar v2.2d, v2.2d, v28.2d, #50
	xar v29.2d, v3.2d, v25.2d, #20
	xar v31.2d, v4.2d, v27.2d, #43
	bcax v3.16b, v31.16b, v0.16b, v2.16b
	bcax v4.16b, v2.16b, v29.16b, v0.16b
	bcax v2.16b, v1.16b, v2.16b, v31.16b
	bcax v0.16b, v0.16b, v1.16b, v29.16b
	bcax v1.16b, v29.16b, v31.16b, v1.16b
	xar v29.2d, v5.2d, v25.2d, #19
	xar v31.2d, v6.2d, v27.2d, #36
	bcax v5.16b, v31.16b, v7.16b, v9.16b
	bcax v6.16b, v9.16b, v29.16b, v7.16b
	bcax v9.16b, v8.16b, v9.16b, v31.16b
	bcax v7.16b, v7.16b, v8.16b, v29.16b
	bcax v8.16b, v29.16b, v31.16b, v8.16b
	xar v29.2d, v12.2d, v25.2d, #63
	xar v31.2d, v13.2d, v27.2d, #39
	bcax v12.16b, v31.16b, v14.16b, v11.16b
	bcax v13.16b, v11.16b, v29.16b, v14.16b
	bcax v11.16b, v10.16b, v11.16b, v31.16b
	bcax v14.16b, v14.16b, v10.16b, v29.16b
	bcax v10.16b, v29.16b, v31.16b, v10.16b
	xar v29.2d, v19.2d, v25.2d, #54
	xar v31.2d, v15.2d, v27.2d, #8
	bcax v19.16b, v31.16b, v16.16b, v18.16b
	bcax v15.16b, v18.16b, v29.16b, v16.16b
	bcax v18.16b, v17.16b, v18.16b, v31.16b
	bcax v16.16b, v16.16b, v17.16b, v29.16b
	bcax v17.16b, v29.16b, v31.16b, v17.16b
	xar v29.2d, v21.2d, v25.2d, #62
	xar v31.2d, v22.2d, v27.2d, #9
	bcax v21.16b, v31.16b, v23.16b, v20.16b
	bcax v22.16b, v20.16b, v29.16b, v23.16b
	bcax v20.16b, v24.16b, v20.16b, v31.16b
	bcax v23.16b, v23.16b, v24.16b, v29.16b
	bcax v24.16b, v29.16b, v31.16b, v24.16b
	ldr q31, [x16, #16]
	eor v0.16b, v0.16b, v31.16b
	add x16, x16, #32
	sub x17, x17, #1
	cbnz x17, 20b
	zip1 v25.2d, v0.2d, v1.2d
	str q25, [x0, #0]
	zip1 v25.2d, v2.2d, v3.2d
	str q25, [x0, #16]
	zip1 v25.2d, v4.2d, v5.2d
	str q25, [x0, #32]
	zip1 v25.2d, v6.2d, v7.2d
	str q25, [x0, #48]
	zip1 v25.2d, v8.2d, v9.2d
	str q25, [x0, #64]
	zip1 v25.2d, v10.2d, v11.2d
	str q25, [x0, #80]
	zip1 v25.2d, v12.2d, v13.2d
	str q25, [x0, #96]
	zip1 v25.2d, v14.2d, v15.2d
	str q25, [x0, #112]
	zip1 v25.2d, v16.2d, v17.2d
	str q25, [x0, #128]
	zip1 v25.2d, v18.2d, v19.2d
	str q25, [x0, #144]
	zip1 v25.2d, v20.2d, v21.2d
	str q25, [x0, #160]
	zip1 v25.2d, v22.2d, v23.2d
	str q25, [x0, #176]
	umov x16, v24.d[0]
	str x16, [x0, #192]
	ldr q8, [x1, #384]
	ldr q9, [x1, #400]
	ldr q10, [x1, #416]
	ldr q11, [x1, #432]
	ldr q12, [x1, #448]
	ldr q13, [x1, #464]
	ldr q14, [x1, #480]
	ldr q15, [x1, #496]
	ret
	.p2align 6
