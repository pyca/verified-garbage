// The functions of `src/sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha3_224_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #144, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	str q8, [x1, #0]
	str q9, [x1, #16]
	str q10, [x1, #32]
	str q11, [x1, #48]
	str q12, [x1, #64]
	str q13, [x1, #80]
	str q14, [x1, #96]
	str q15, [x1, #112]
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
	ldr x17, [x0, #192]
	dup v24.2d, x17
24:
	sub x7, x6, #72
	cbz x7, 25f
	sub x7, x6, #104
	cbz x7, 27f
	sub x7, x6, #136
	cbz x7, 29f
	sub x7, x6, #144
	cbz x7, 211f
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
	ldr q25, [x3, #144]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v18.16b, v18.16b, v25.16b
	eor v19.16b, v19.16b, v26.16b
	ldr x17, [x3, #160]
	dup v25.2d, x17
	eor v20.16b, v20.16b, v25.16b
	b 212f
211:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
212:
	b 210f
29:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr x17, [x3, #128]
	dup v25.2d, x17
	eor v16.16b, v16.16b, v25.16b
210:
	b 28f
27:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr x17, [x3, #96]
	dup v25.2d, x17
	eor v12.16b, v12.16b, v25.16b
28:
	b 26f
25:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr x17, [x3, #64]
	dup v25.2d, x17
	eor v8.16b, v8.16b, v25.16b
26:
	movz x16, #1, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32898, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32906, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32768, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #138, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #136, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #139, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32905, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32771, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32770, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #128, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32778, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32896, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32776, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	add x3, x3, x6
	sub x4, x4, x6
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 24b
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
	umov x17, v24.d[0]
	str x17, [x0, #192]
	ldr q8, [x1, #0]
	ldr q9, [x1, #16]
	ldr q10, [x1, #32]
	ldr q11, [x1, #48]
	ldr q12, [x1, #64]
	ldr q13, [x1, #80]
	ldr q14, [x1, #96]
	ldr q15, [x1, #112]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 213f
215:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 216f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 217f
216:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
217:
	cbz x9, 218f
	b 219f
218:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
219:
	cbnz x24, 215b
	b 214f
213:
214:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
220:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 220b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_224_finalize_sha3:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #144, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x19, #0
	movz x1, #144, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #28, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_256_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	str q8, [x1, #0]
	str q9, [x1, #16]
	str q10, [x1, #32]
	str q11, [x1, #48]
	str q12, [x1, #64]
	str q13, [x1, #80]
	str q14, [x1, #96]
	str q15, [x1, #112]
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
	ldr x17, [x0, #192]
	dup v24.2d, x17
24:
	sub x7, x6, #72
	cbz x7, 25f
	sub x7, x6, #104
	cbz x7, 27f
	sub x7, x6, #136
	cbz x7, 29f
	sub x7, x6, #144
	cbz x7, 211f
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
	ldr q25, [x3, #144]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v18.16b, v18.16b, v25.16b
	eor v19.16b, v19.16b, v26.16b
	ldr x17, [x3, #160]
	dup v25.2d, x17
	eor v20.16b, v20.16b, v25.16b
	b 212f
211:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
212:
	b 210f
29:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr x17, [x3, #128]
	dup v25.2d, x17
	eor v16.16b, v16.16b, v25.16b
210:
	b 28f
27:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr x17, [x3, #96]
	dup v25.2d, x17
	eor v12.16b, v12.16b, v25.16b
28:
	b 26f
25:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr x17, [x3, #64]
	dup v25.2d, x17
	eor v8.16b, v8.16b, v25.16b
26:
	movz x16, #1, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32898, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32906, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32768, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #138, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #136, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #139, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32905, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32771, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32770, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #128, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32778, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32896, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32776, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	add x3, x3, x6
	sub x4, x4, x6
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 24b
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
	umov x17, v24.d[0]
	str x17, [x0, #192]
	ldr q8, [x1, #0]
	ldr q9, [x1, #16]
	ldr q10, [x1, #32]
	ldr q11, [x1, #48]
	ldr q12, [x1, #64]
	ldr q13, [x1, #80]
	ldr q14, [x1, #96]
	ldr q15, [x1, #112]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 213f
215:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 216f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 217f
216:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
217:
	cbz x9, 218f
	b 219f
218:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
219:
	cbnz x24, 215b
	b 214f
213:
214:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
220:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 220b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_256_finalize_sha3:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x19, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #32, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_384_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #104, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	str q8, [x1, #0]
	str q9, [x1, #16]
	str q10, [x1, #32]
	str q11, [x1, #48]
	str q12, [x1, #64]
	str q13, [x1, #80]
	str q14, [x1, #96]
	str q15, [x1, #112]
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
	ldr x17, [x0, #192]
	dup v24.2d, x17
24:
	sub x7, x6, #72
	cbz x7, 25f
	sub x7, x6, #104
	cbz x7, 27f
	sub x7, x6, #136
	cbz x7, 29f
	sub x7, x6, #144
	cbz x7, 211f
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
	ldr q25, [x3, #144]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v18.16b, v18.16b, v25.16b
	eor v19.16b, v19.16b, v26.16b
	ldr x17, [x3, #160]
	dup v25.2d, x17
	eor v20.16b, v20.16b, v25.16b
	b 212f
211:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
212:
	b 210f
29:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr x17, [x3, #128]
	dup v25.2d, x17
	eor v16.16b, v16.16b, v25.16b
210:
	b 28f
27:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr x17, [x3, #96]
	dup v25.2d, x17
	eor v12.16b, v12.16b, v25.16b
28:
	b 26f
25:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr x17, [x3, #64]
	dup v25.2d, x17
	eor v8.16b, v8.16b, v25.16b
26:
	movz x16, #1, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32898, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32906, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32768, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #138, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #136, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #139, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32905, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32771, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32770, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #128, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32778, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32896, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32776, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	add x3, x3, x6
	sub x4, x4, x6
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 24b
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
	umov x17, v24.d[0]
	str x17, [x0, #192]
	ldr q8, [x1, #0]
	ldr q9, [x1, #16]
	ldr q10, [x1, #32]
	ldr q11, [x1, #48]
	ldr q12, [x1, #64]
	ldr q13, [x1, #80]
	ldr q14, [x1, #96]
	ldr q15, [x1, #112]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 213f
215:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 216f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 217f
216:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
217:
	cbz x9, 218f
	b 219f
218:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
219:
	cbnz x24, 215b
	b 214f
213:
214:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
220:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 220b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_384_finalize_sha3:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #104, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x19, #0
	movz x1, #104, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #48, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_512_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #72, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	str q8, [x1, #0]
	str q9, [x1, #16]
	str q10, [x1, #32]
	str q11, [x1, #48]
	str q12, [x1, #64]
	str q13, [x1, #80]
	str q14, [x1, #96]
	str q15, [x1, #112]
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
	ldr x17, [x0, #192]
	dup v24.2d, x17
24:
	sub x7, x6, #72
	cbz x7, 25f
	sub x7, x6, #104
	cbz x7, 27f
	sub x7, x6, #136
	cbz x7, 29f
	sub x7, x6, #144
	cbz x7, 211f
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
	ldr q25, [x3, #144]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v18.16b, v18.16b, v25.16b
	eor v19.16b, v19.16b, v26.16b
	ldr x17, [x3, #160]
	dup v25.2d, x17
	eor v20.16b, v20.16b, v25.16b
	b 212f
211:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
212:
	b 210f
29:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr x17, [x3, #128]
	dup v25.2d, x17
	eor v16.16b, v16.16b, v25.16b
210:
	b 28f
27:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr x17, [x3, #96]
	dup v25.2d, x17
	eor v12.16b, v12.16b, v25.16b
28:
	b 26f
25:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr x17, [x3, #64]
	dup v25.2d, x17
	eor v8.16b, v8.16b, v25.16b
26:
	movz x16, #1, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32898, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32906, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32768, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #138, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #136, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #139, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32905, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32771, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32770, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #128, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32778, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32896, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32776, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	add x3, x3, x6
	sub x4, x4, x6
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 24b
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
	umov x17, v24.d[0]
	str x17, [x0, #192]
	ldr q8, [x1, #0]
	ldr q9, [x1, #16]
	ldr q10, [x1, #32]
	ldr q11, [x1, #48]
	ldr q12, [x1, #64]
	ldr q13, [x1, #80]
	ldr q14, [x1, #96]
	ldr q15, [x1, #112]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 213f
215:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 216f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 217f
216:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
217:
	cbz x9, 218f
	b 219f
218:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
219:
	cbnz x24, 215b
	b 214f
213:
214:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
220:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 220b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_512_finalize_sha3:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #72, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x19, #0
	movz x1, #72, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #64, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_shake128_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	str q8, [x1, #0]
	str q9, [x1, #16]
	str q10, [x1, #32]
	str q11, [x1, #48]
	str q12, [x1, #64]
	str q13, [x1, #80]
	str q14, [x1, #96]
	str q15, [x1, #112]
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
	ldr x17, [x0, #192]
	dup v24.2d, x17
24:
	sub x7, x6, #72
	cbz x7, 25f
	sub x7, x6, #104
	cbz x7, 27f
	sub x7, x6, #136
	cbz x7, 29f
	sub x7, x6, #144
	cbz x7, 211f
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
	ldr q25, [x3, #144]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v18.16b, v18.16b, v25.16b
	eor v19.16b, v19.16b, v26.16b
	ldr x17, [x3, #160]
	dup v25.2d, x17
	eor v20.16b, v20.16b, v25.16b
	b 212f
211:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
212:
	b 210f
29:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr x17, [x3, #128]
	dup v25.2d, x17
	eor v16.16b, v16.16b, v25.16b
210:
	b 28f
27:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr x17, [x3, #96]
	dup v25.2d, x17
	eor v12.16b, v12.16b, v25.16b
28:
	b 26f
25:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr x17, [x3, #64]
	dup v25.2d, x17
	eor v8.16b, v8.16b, v25.16b
26:
	movz x16, #1, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32898, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32906, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32768, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #138, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #136, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #139, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32905, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32771, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32770, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #128, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32778, lsl #0
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32896, lsl #0
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32776, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
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
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	add x3, x3, x6
	sub x4, x4, x6
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 24b
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
	umov x17, v24.d[0]
	str x17, [x0, #192]
	ldr q8, [x1, #0]
	ldr q9, [x1, #16]
	ldr q10, [x1, #32]
	ldr q11, [x1, #48]
	ldr q12, [x1, #64]
	ldr q13, [x1, #80]
	ldr q14, [x1, #96]
	ldr q15, [x1, #112]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 213f
215:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 216f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 217f
216:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
217:
	cbz x9, 218f
	b 219f
218:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
219:
	cbnz x24, 215b
	b 214f
213:
214:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
220:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 220b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake128_finalize_sha3:
	sub sp, sp, #640
	add x2, sp, #0
	add x4, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600_sha3}
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake128_squeeze_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
27:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 27b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake256_finalize_sha3:
	sub sp, sp, #640
	add x2, sp, #0
	add x4, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600_sha3}
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake256_squeeze_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
27:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 27b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_224_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #144, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	dup v29.2d, x30
	bl {vg_keccak_scalar_absorb_blocks}
	umov x30, v29.d[0]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
211:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 211b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_224_finalize:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #144, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch}
	add x0, x19, #0
	movz x1, #144, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #28, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_256_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	dup v29.2d, x30
	bl {vg_keccak_scalar_absorb_blocks}
	umov x30, v29.d[0]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
211:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 211b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_256_finalize:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch}
	add x0, x19, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #32, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_384_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #104, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	dup v29.2d, x30
	bl {vg_keccak_scalar_absorb_blocks}
	umov x30, v29.d[0]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
211:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 211b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_384_finalize:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #104, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch}
	add x0, x19, #0
	movz x1, #104, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #48, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_512_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #72, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	dup v29.2d, x30
	bl {vg_keccak_scalar_absorb_blocks}
	umov x30, v29.d[0]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
211:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 211b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_512_finalize:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #72, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch}
	add x0, x19, #0
	movz x1, #72, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #64, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_shake128_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	dup v29.2d, x30
	bl {vg_keccak_scalar_absorb_blocks}
	umov x30, v29.d[0]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
211:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 211b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake128_finalize:
	sub sp, sp, #640
	add x2, sp, #0
	add x4, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600}
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake128_squeeze:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
27:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 27b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake256_finalize:
	sub sp, sp, #640
	add x2, sp, #0
	add x4, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600}
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake256_squeeze:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
27:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 27b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6
