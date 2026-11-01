// The functions of `src/internal/vg_chacha20_xor_neon.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor_neon:
	lsr x5, x2, #6
	sub x5, x5, #8
	lsr x5, x5, #63
	cbnz x5, 20f
	str x20, [x3, #256]
	str x19, [x3, #264]
	str x26, [x3, #272]
	add x20, x3, #0
	str q8, [x3, #128]
	str q9, [x3, #144]
22:
	add x19, x2, #0
	add x26, x1, #0
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	ldr q2, [x0, #32]
	ldr q3, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #0
	mov v3.s[0], w4
	ldr q4, [x0, #0]
	ldr q5, [x0, #16]
	ldr q6, [x0, #32]
	ldr q7, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #1
	mov v7.s[0], w4
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #2
	mov v19.s[0], w4
	ldr q20, [x0, #0]
	ldr q21, [x0, #16]
	ldr q22, [x0, #32]
	ldr q23, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #3
	mov v23.s[0], w4
	ldr q24, [x0, #0]
	ldr q25, [x0, #16]
	ldr q26, [x0, #32]
	ldr q27, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #4
	mov v27.s[0], w4
	ldr q28, [x0, #0]
	ldr q29, [x0, #16]
	ldr q8, [x0, #32]
	ldr q9, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #5
	mov v9.s[0], w4
	movz x4, #3, lsl #0
	movk x4, #513, lsl #16
	movk x4, #1031, lsl #32
	movk x4, #1541, lsl #48
	dup v30.2d, x4
	movz x4, #2059, lsl #0
	movk x4, #2569, lsl #16
	movk x4, #3087, lsl #32
	movk x4, #3597, lsl #48
	mov v30.d[1], x4
	ldr w4, [x0, #48]
	add w4, w4, #6
	str w4, [x0, #48]
	ldr w2, [x0, #0]
	ldr w3, [x0, #4]
	ldr w4, [x0, #8]
	ldr w5, [x0, #12]
	ldr w6, [x0, #16]
	ldr w7, [x0, #20]
	ldr w8, [x0, #24]
	ldr w9, [x0, #28]
	ldr w10, [x0, #32]
	ldr w11, [x0, #36]
	ldr w12, [x0, #40]
	ldr w13, [x0, #44]
	ldr w14, [x0, #48]
	ldr w15, [x0, #52]
	ldr w16, [x0, #56]
	ldr w17, [x0, #60]
	movz x1, #5, lsl #0
23:
	add v0.4s, v0.4s, v1.4s
	add w2, w2, w6
	add v4.4s, v4.4s, v5.4s
	add w3, w3, w7
	add v16.4s, v16.4s, v17.4s
	add w4, w4, w8
	add v20.4s, v20.4s, v21.4s
	add w5, w5, w9
	add v24.4s, v24.4s, v25.4s
	eor w14, w14, w2
	ror w14, w14, #16
	add v28.4s, v28.4s, v29.4s
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v3.16b, v0.16b
	rev32 v3.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v7.16b, v4.16b
	rev32 v7.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	eor v31.16b, v19.16b, v16.16b
	rev32 v19.8h, v31.8h
	add w10, w10, w14
	eor v31.16b, v23.16b, v20.16b
	rev32 v23.8h, v31.8h
	add w11, w11, w15
	eor v31.16b, v27.16b, v24.16b
	rev32 v27.8h, v31.8h
	add w12, w12, w16
	eor v31.16b, v9.16b, v28.16b
	rev32 v9.8h, v31.8h
	add w13, w13, w17
	add v2.4s, v2.4s, v3.4s
	eor w6, w6, w10
	ror w6, w6, #20
	add v6.4s, v6.4s, v7.4s
	eor w7, w7, w11
	ror w7, w7, #20
	add v18.4s, v18.4s, v19.4s
	eor w8, w8, w12
	ror w8, w8, #20
	add v22.4s, v22.4s, v23.4s
	eor w9, w9, w13
	ror w9, w9, #20
	add v26.4s, v26.4s, v27.4s
	add w2, w2, w6
	add v8.4s, v8.4s, v9.4s
	add w3, w3, w7
	eor v31.16b, v1.16b, v2.16b
	ushr v1.4s, v31.4s, #20
	sli v1.4s, v31.4s, #12
	add w4, w4, w8
	eor v31.16b, v5.16b, v6.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	add w5, w5, w9
	eor v31.16b, v17.16b, v18.16b
	ushr v17.4s, v31.4s, #20
	sli v17.4s, v31.4s, #12
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v22.16b
	ushr v21.4s, v31.4s, #20
	sli v21.4s, v31.4s, #12
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v25.16b, v26.16b
	ushr v25.4s, v31.4s, #20
	sli v25.4s, v31.4s, #12
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v29.16b, v8.16b
	ushr v29.4s, v31.4s, #20
	sli v29.4s, v31.4s, #12
	eor w17, w17, w5
	ror w17, w17, #24
	add v0.4s, v0.4s, v1.4s
	add w10, w10, w14
	add v4.4s, v4.4s, v5.4s
	add w11, w11, w15
	add v16.4s, v16.4s, v17.4s
	add w12, w12, w16
	add v20.4s, v20.4s, v21.4s
	add w13, w13, w17
	add v24.4s, v24.4s, v25.4s
	eor w6, w6, w10
	ror w6, w6, #25
	add v28.4s, v28.4s, v29.4s
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v3.16b, v0.16b
	tbl v3.16b, {v31.16b}, v30.16b
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v4.16b
	tbl v7.16b, {v31.16b}, v30.16b
	eor w9, w9, w13
	ror w9, w9, #25
	eor v31.16b, v19.16b, v16.16b
	tbl v19.16b, {v31.16b}, v30.16b
	add w2, w2, w7
	eor v31.16b, v23.16b, v20.16b
	tbl v23.16b, {v31.16b}, v30.16b
	add w3, w3, w8
	eor v31.16b, v27.16b, v24.16b
	tbl v27.16b, {v31.16b}, v30.16b
	add w4, w4, w9
	eor v31.16b, v9.16b, v28.16b
	tbl v9.16b, {v31.16b}, v30.16b
	add w5, w5, w6
	add v2.4s, v2.4s, v3.4s
	eor w17, w17, w2
	ror w17, w17, #16
	add v6.4s, v6.4s, v7.4s
	eor w14, w14, w3
	ror w14, w14, #16
	add v18.4s, v18.4s, v19.4s
	eor w15, w15, w4
	ror w15, w15, #16
	add v22.4s, v22.4s, v23.4s
	eor w16, w16, w5
	ror w16, w16, #16
	add v26.4s, v26.4s, v27.4s
	add w12, w12, w17
	add v8.4s, v8.4s, v9.4s
	add w13, w13, w14
	eor v31.16b, v1.16b, v2.16b
	ushr v1.4s, v31.4s, #25
	sli v1.4s, v31.4s, #7
	add w10, w10, w15
	eor v31.16b, v5.16b, v6.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	add w11, w11, w16
	eor v31.16b, v17.16b, v18.16b
	ushr v17.4s, v31.4s, #25
	sli v17.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v21.16b, v22.16b
	ushr v21.4s, v31.4s, #25
	sli v21.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v25.16b, v26.16b
	ushr v25.4s, v31.4s, #25
	sli v25.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v29.16b, v8.16b
	ushr v29.4s, v31.4s, #25
	sli v29.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #20
	ext v1.16b, v1.16b, v1.16b, #4
	add w2, w2, w7
	ext v5.16b, v5.16b, v5.16b, #4
	add w3, w3, w8
	ext v17.16b, v17.16b, v17.16b, #4
	add w4, w4, w9
	ext v21.16b, v21.16b, v21.16b, #4
	add w5, w5, w6
	ext v25.16b, v25.16b, v25.16b, #4
	eor w17, w17, w2
	ror w17, w17, #24
	ext v29.16b, v29.16b, v29.16b, #4
	eor w14, w14, w3
	ror w14, w14, #24
	ext v2.16b, v2.16b, v2.16b, #8
	eor w15, w15, w4
	ror w15, w15, #24
	ext v6.16b, v6.16b, v6.16b, #8
	eor w16, w16, w5
	ror w16, w16, #24
	ext v18.16b, v18.16b, v18.16b, #8
	add w12, w12, w17
	ext v22.16b, v22.16b, v22.16b, #8
	add w13, w13, w14
	ext v26.16b, v26.16b, v26.16b, #8
	add w10, w10, w15
	ext v8.16b, v8.16b, v8.16b, #8
	add w11, w11, w16
	ext v3.16b, v3.16b, v3.16b, #12
	eor w7, w7, w12
	ror w7, w7, #25
	ext v7.16b, v7.16b, v7.16b, #12
	eor w8, w8, w13
	ror w8, w8, #25
	ext v19.16b, v19.16b, v19.16b, #12
	eor w9, w9, w10
	ror w9, w9, #25
	ext v23.16b, v23.16b, v23.16b, #12
	eor w6, w6, w11
	ror w6, w6, #25
	ext v27.16b, v27.16b, v27.16b, #12
	add w2, w2, w6
	ext v9.16b, v9.16b, v9.16b, #12
	add w3, w3, w7
	add v0.4s, v0.4s, v1.4s
	add w4, w4, w8
	add v4.4s, v4.4s, v5.4s
	add w5, w5, w9
	add v16.4s, v16.4s, v17.4s
	eor w14, w14, w2
	ror w14, w14, #16
	add v20.4s, v20.4s, v21.4s
	eor w15, w15, w3
	ror w15, w15, #16
	add v24.4s, v24.4s, v25.4s
	eor w16, w16, w4
	ror w16, w16, #16
	add v28.4s, v28.4s, v29.4s
	eor w17, w17, w5
	ror w17, w17, #16
	eor v31.16b, v3.16b, v0.16b
	rev32 v3.8h, v31.8h
	add w10, w10, w14
	eor v31.16b, v7.16b, v4.16b
	rev32 v7.8h, v31.8h
	add w11, w11, w15
	eor v31.16b, v19.16b, v16.16b
	rev32 v19.8h, v31.8h
	add w12, w12, w16
	eor v31.16b, v23.16b, v20.16b
	rev32 v23.8h, v31.8h
	add w13, w13, w17
	eor v31.16b, v27.16b, v24.16b
	rev32 v27.8h, v31.8h
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v9.16b, v28.16b
	rev32 v9.8h, v31.8h
	eor w7, w7, w11
	ror w7, w7, #20
	add v2.4s, v2.4s, v3.4s
	eor w8, w8, w12
	ror w8, w8, #20
	add v6.4s, v6.4s, v7.4s
	eor w9, w9, w13
	ror w9, w9, #20
	add v18.4s, v18.4s, v19.4s
	add w2, w2, w6
	add v22.4s, v22.4s, v23.4s
	add w3, w3, w7
	add v26.4s, v26.4s, v27.4s
	add w4, w4, w8
	add v8.4s, v8.4s, v9.4s
	add w5, w5, w9
	eor v31.16b, v1.16b, v2.16b
	ushr v1.4s, v31.4s, #20
	sli v1.4s, v31.4s, #12
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v5.16b, v6.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v17.16b, v18.16b
	ushr v17.4s, v31.4s, #20
	sli v17.4s, v31.4s, #12
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v21.16b, v22.16b
	ushr v21.4s, v31.4s, #20
	sli v21.4s, v31.4s, #12
	eor w17, w17, w5
	ror w17, w17, #24
	eor v31.16b, v25.16b, v26.16b
	ushr v25.4s, v31.4s, #20
	sli v25.4s, v31.4s, #12
	add w10, w10, w14
	eor v31.16b, v29.16b, v8.16b
	ushr v29.4s, v31.4s, #20
	sli v29.4s, v31.4s, #12
	add w11, w11, w15
	add v0.4s, v0.4s, v1.4s
	add w12, w12, w16
	add v4.4s, v4.4s, v5.4s
	add w13, w13, w17
	add v16.4s, v16.4s, v17.4s
	eor w6, w6, w10
	ror w6, w6, #25
	add v20.4s, v20.4s, v21.4s
	eor w7, w7, w11
	ror w7, w7, #25
	add v24.4s, v24.4s, v25.4s
	eor w8, w8, w12
	ror w8, w8, #25
	add v28.4s, v28.4s, v29.4s
	eor w9, w9, w13
	ror w9, w9, #25
	eor v31.16b, v3.16b, v0.16b
	tbl v3.16b, {v31.16b}, v30.16b
	add w2, w2, w7
	eor v31.16b, v7.16b, v4.16b
	tbl v7.16b, {v31.16b}, v30.16b
	add w3, w3, w8
	eor v31.16b, v19.16b, v16.16b
	tbl v19.16b, {v31.16b}, v30.16b
	add w4, w4, w9
	eor v31.16b, v23.16b, v20.16b
	tbl v23.16b, {v31.16b}, v30.16b
	add w5, w5, w6
	eor v31.16b, v27.16b, v24.16b
	tbl v27.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v9.16b, v28.16b
	tbl v9.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #16
	add v2.4s, v2.4s, v3.4s
	eor w15, w15, w4
	ror w15, w15, #16
	add v6.4s, v6.4s, v7.4s
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v19.4s
	add w12, w12, w17
	add v22.4s, v22.4s, v23.4s
	add w13, w13, w14
	add v26.4s, v26.4s, v27.4s
	add w10, w10, w15
	add v8.4s, v8.4s, v9.4s
	add w11, w11, w16
	eor v31.16b, v1.16b, v2.16b
	ushr v1.4s, v31.4s, #25
	sli v1.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v5.16b, v6.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v17.16b, v18.16b
	ushr v17.4s, v31.4s, #25
	sli v17.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v21.16b, v22.16b
	ushr v21.4s, v31.4s, #25
	sli v21.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #20
	eor v31.16b, v25.16b, v26.16b
	ushr v25.4s, v31.4s, #25
	sli v25.4s, v31.4s, #7
	add w2, w2, w7
	eor v31.16b, v29.16b, v8.16b
	ushr v29.4s, v31.4s, #25
	sli v29.4s, v31.4s, #7
	add w3, w3, w8
	ext v1.16b, v1.16b, v1.16b, #12
	add w4, w4, w9
	ext v5.16b, v5.16b, v5.16b, #12
	add w5, w5, w6
	ext v17.16b, v17.16b, v17.16b, #12
	eor w17, w17, w2
	ror w17, w17, #24
	ext v21.16b, v21.16b, v21.16b, #12
	eor w14, w14, w3
	ror w14, w14, #24
	ext v25.16b, v25.16b, v25.16b, #12
	eor w15, w15, w4
	ror w15, w15, #24
	ext v29.16b, v29.16b, v29.16b, #12
	eor w16, w16, w5
	ror w16, w16, #24
	ext v2.16b, v2.16b, v2.16b, #8
	add w12, w12, w17
	ext v6.16b, v6.16b, v6.16b, #8
	add w13, w13, w14
	ext v18.16b, v18.16b, v18.16b, #8
	add w10, w10, w15
	ext v22.16b, v22.16b, v22.16b, #8
	add w11, w11, w16
	ext v26.16b, v26.16b, v26.16b, #8
	eor w7, w7, w12
	ror w7, w7, #25
	ext v8.16b, v8.16b, v8.16b, #8
	eor w8, w8, w13
	ror w8, w8, #25
	ext v3.16b, v3.16b, v3.16b, #4
	eor w9, w9, w10
	ror w9, w9, #25
	ext v7.16b, v7.16b, v7.16b, #4
	eor w6, w6, w11
	ror w6, w6, #25
	ext v19.16b, v19.16b, v19.16b, #4
	ext v23.16b, v23.16b, v23.16b, #4
	ext v27.16b, v27.16b, v27.16b, #4
	ext v9.16b, v9.16b, v9.16b, #4
	sub x1, x1, #1
	cbnz x1, 23b
	add x1, x26, #0
	add x1, x20, #0
	str w2, [x1, #0]
	ldr w2, [x0, #4]
	add w3, w3, w2
	str w3, [x1, #4]
	ldr w2, [x0, #8]
	add w4, w4, w2
	str w4, [x1, #8]
	ldr w2, [x0, #12]
	add w5, w5, w2
	str w5, [x1, #12]
	ldr w2, [x0, #16]
	add w6, w6, w2
	str w6, [x1, #16]
	ldr w2, [x0, #20]
	add w7, w7, w2
	str w7, [x1, #20]
	ldr w2, [x0, #24]
	add w8, w8, w2
	str w8, [x1, #24]
	ldr w2, [x0, #28]
	add w9, w9, w2
	str w9, [x1, #28]
	ldr w2, [x0, #32]
	add w10, w10, w2
	str w10, [x1, #32]
	ldr w2, [x0, #36]
	add w11, w11, w2
	str w11, [x1, #36]
	ldr w2, [x0, #40]
	add w12, w12, w2
	str w12, [x1, #40]
	ldr w2, [x0, #44]
	add w13, w13, w2
	str w13, [x1, #44]
	ldr w2, [x0, #48]
	add w14, w14, w2
	str w14, [x1, #48]
	ldr w2, [x0, #52]
	add w15, w15, w2
	str w15, [x1, #52]
	ldr w2, [x0, #56]
	add w16, w16, w2
	str w16, [x1, #56]
	ldr w2, [x0, #60]
	add w17, w17, w2
	str w17, [x1, #60]
	ldr w2, [x0, #0]
	ldr w3, [x1, #0]
	add w2, w3, w2
	str w2, [x1, #0]
	ldr w4, [x0, #48]
	add w4, w4, #1
	str w4, [x0, #48]
	ldr w2, [x0, #0]
	ldr w3, [x0, #4]
	ldr w4, [x0, #8]
	ldr w5, [x0, #12]
	ldr w6, [x0, #16]
	ldr w7, [x0, #20]
	ldr w8, [x0, #24]
	ldr w9, [x0, #28]
	ldr w10, [x0, #32]
	ldr w11, [x0, #36]
	ldr w12, [x0, #40]
	ldr w13, [x0, #44]
	ldr w14, [x0, #48]
	ldr w15, [x0, #52]
	ldr w16, [x0, #56]
	ldr w17, [x0, #60]
	movz x1, #5, lsl #0
24:
	add v0.4s, v0.4s, v1.4s
	add w2, w2, w6
	add v4.4s, v4.4s, v5.4s
	add w3, w3, w7
	add v16.4s, v16.4s, v17.4s
	add w4, w4, w8
	add v20.4s, v20.4s, v21.4s
	add w5, w5, w9
	add v24.4s, v24.4s, v25.4s
	eor w14, w14, w2
	ror w14, w14, #16
	add v28.4s, v28.4s, v29.4s
	eor w15, w15, w3
	ror w15, w15, #16
	eor v31.16b, v3.16b, v0.16b
	rev32 v3.8h, v31.8h
	eor w16, w16, w4
	ror w16, w16, #16
	eor v31.16b, v7.16b, v4.16b
	rev32 v7.8h, v31.8h
	eor w17, w17, w5
	ror w17, w17, #16
	eor v31.16b, v19.16b, v16.16b
	rev32 v19.8h, v31.8h
	add w10, w10, w14
	eor v31.16b, v23.16b, v20.16b
	rev32 v23.8h, v31.8h
	add w11, w11, w15
	eor v31.16b, v27.16b, v24.16b
	rev32 v27.8h, v31.8h
	add w12, w12, w16
	eor v31.16b, v9.16b, v28.16b
	rev32 v9.8h, v31.8h
	add w13, w13, w17
	add v2.4s, v2.4s, v3.4s
	eor w6, w6, w10
	ror w6, w6, #20
	add v6.4s, v6.4s, v7.4s
	eor w7, w7, w11
	ror w7, w7, #20
	add v18.4s, v18.4s, v19.4s
	eor w8, w8, w12
	ror w8, w8, #20
	add v22.4s, v22.4s, v23.4s
	eor w9, w9, w13
	ror w9, w9, #20
	add v26.4s, v26.4s, v27.4s
	add w2, w2, w6
	add v8.4s, v8.4s, v9.4s
	add w3, w3, w7
	eor v31.16b, v1.16b, v2.16b
	ushr v1.4s, v31.4s, #20
	sli v1.4s, v31.4s, #12
	add w4, w4, w8
	eor v31.16b, v5.16b, v6.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	add w5, w5, w9
	eor v31.16b, v17.16b, v18.16b
	ushr v17.4s, v31.4s, #20
	sli v17.4s, v31.4s, #12
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v21.16b, v22.16b
	ushr v21.4s, v31.4s, #20
	sli v21.4s, v31.4s, #12
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v25.16b, v26.16b
	ushr v25.4s, v31.4s, #20
	sli v25.4s, v31.4s, #12
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v29.16b, v8.16b
	ushr v29.4s, v31.4s, #20
	sli v29.4s, v31.4s, #12
	eor w17, w17, w5
	ror w17, w17, #24
	add v0.4s, v0.4s, v1.4s
	add w10, w10, w14
	add v4.4s, v4.4s, v5.4s
	add w11, w11, w15
	add v16.4s, v16.4s, v17.4s
	add w12, w12, w16
	add v20.4s, v20.4s, v21.4s
	add w13, w13, w17
	add v24.4s, v24.4s, v25.4s
	eor w6, w6, w10
	ror w6, w6, #25
	add v28.4s, v28.4s, v29.4s
	eor w7, w7, w11
	ror w7, w7, #25
	eor v31.16b, v3.16b, v0.16b
	tbl v3.16b, {v31.16b}, v30.16b
	eor w8, w8, w12
	ror w8, w8, #25
	eor v31.16b, v7.16b, v4.16b
	tbl v7.16b, {v31.16b}, v30.16b
	eor w9, w9, w13
	ror w9, w9, #25
	eor v31.16b, v19.16b, v16.16b
	tbl v19.16b, {v31.16b}, v30.16b
	add w2, w2, w7
	eor v31.16b, v23.16b, v20.16b
	tbl v23.16b, {v31.16b}, v30.16b
	add w3, w3, w8
	eor v31.16b, v27.16b, v24.16b
	tbl v27.16b, {v31.16b}, v30.16b
	add w4, w4, w9
	eor v31.16b, v9.16b, v28.16b
	tbl v9.16b, {v31.16b}, v30.16b
	add w5, w5, w6
	add v2.4s, v2.4s, v3.4s
	eor w17, w17, w2
	ror w17, w17, #16
	add v6.4s, v6.4s, v7.4s
	eor w14, w14, w3
	ror w14, w14, #16
	add v18.4s, v18.4s, v19.4s
	eor w15, w15, w4
	ror w15, w15, #16
	add v22.4s, v22.4s, v23.4s
	eor w16, w16, w5
	ror w16, w16, #16
	add v26.4s, v26.4s, v27.4s
	add w12, w12, w17
	add v8.4s, v8.4s, v9.4s
	add w13, w13, w14
	eor v31.16b, v1.16b, v2.16b
	ushr v1.4s, v31.4s, #25
	sli v1.4s, v31.4s, #7
	add w10, w10, w15
	eor v31.16b, v5.16b, v6.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	add w11, w11, w16
	eor v31.16b, v17.16b, v18.16b
	ushr v17.4s, v31.4s, #25
	sli v17.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v21.16b, v22.16b
	ushr v21.4s, v31.4s, #25
	sli v21.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v25.16b, v26.16b
	ushr v25.4s, v31.4s, #25
	sli v25.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v29.16b, v8.16b
	ushr v29.4s, v31.4s, #25
	sli v29.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #20
	ext v1.16b, v1.16b, v1.16b, #4
	add w2, w2, w7
	ext v5.16b, v5.16b, v5.16b, #4
	add w3, w3, w8
	ext v17.16b, v17.16b, v17.16b, #4
	add w4, w4, w9
	ext v21.16b, v21.16b, v21.16b, #4
	add w5, w5, w6
	ext v25.16b, v25.16b, v25.16b, #4
	eor w17, w17, w2
	ror w17, w17, #24
	ext v29.16b, v29.16b, v29.16b, #4
	eor w14, w14, w3
	ror w14, w14, #24
	ext v2.16b, v2.16b, v2.16b, #8
	eor w15, w15, w4
	ror w15, w15, #24
	ext v6.16b, v6.16b, v6.16b, #8
	eor w16, w16, w5
	ror w16, w16, #24
	ext v18.16b, v18.16b, v18.16b, #8
	add w12, w12, w17
	ext v22.16b, v22.16b, v22.16b, #8
	add w13, w13, w14
	ext v26.16b, v26.16b, v26.16b, #8
	add w10, w10, w15
	ext v8.16b, v8.16b, v8.16b, #8
	add w11, w11, w16
	ext v3.16b, v3.16b, v3.16b, #12
	eor w7, w7, w12
	ror w7, w7, #25
	ext v7.16b, v7.16b, v7.16b, #12
	eor w8, w8, w13
	ror w8, w8, #25
	ext v19.16b, v19.16b, v19.16b, #12
	eor w9, w9, w10
	ror w9, w9, #25
	ext v23.16b, v23.16b, v23.16b, #12
	eor w6, w6, w11
	ror w6, w6, #25
	ext v27.16b, v27.16b, v27.16b, #12
	add w2, w2, w6
	ext v9.16b, v9.16b, v9.16b, #12
	add w3, w3, w7
	add v0.4s, v0.4s, v1.4s
	add w4, w4, w8
	add v4.4s, v4.4s, v5.4s
	add w5, w5, w9
	add v16.4s, v16.4s, v17.4s
	eor w14, w14, w2
	ror w14, w14, #16
	add v20.4s, v20.4s, v21.4s
	eor w15, w15, w3
	ror w15, w15, #16
	add v24.4s, v24.4s, v25.4s
	eor w16, w16, w4
	ror w16, w16, #16
	add v28.4s, v28.4s, v29.4s
	eor w17, w17, w5
	ror w17, w17, #16
	eor v31.16b, v3.16b, v0.16b
	rev32 v3.8h, v31.8h
	add w10, w10, w14
	eor v31.16b, v7.16b, v4.16b
	rev32 v7.8h, v31.8h
	add w11, w11, w15
	eor v31.16b, v19.16b, v16.16b
	rev32 v19.8h, v31.8h
	add w12, w12, w16
	eor v31.16b, v23.16b, v20.16b
	rev32 v23.8h, v31.8h
	add w13, w13, w17
	eor v31.16b, v27.16b, v24.16b
	rev32 v27.8h, v31.8h
	eor w6, w6, w10
	ror w6, w6, #20
	eor v31.16b, v9.16b, v28.16b
	rev32 v9.8h, v31.8h
	eor w7, w7, w11
	ror w7, w7, #20
	add v2.4s, v2.4s, v3.4s
	eor w8, w8, w12
	ror w8, w8, #20
	add v6.4s, v6.4s, v7.4s
	eor w9, w9, w13
	ror w9, w9, #20
	add v18.4s, v18.4s, v19.4s
	add w2, w2, w6
	add v22.4s, v22.4s, v23.4s
	add w3, w3, w7
	add v26.4s, v26.4s, v27.4s
	add w4, w4, w8
	add v8.4s, v8.4s, v9.4s
	add w5, w5, w9
	eor v31.16b, v1.16b, v2.16b
	ushr v1.4s, v31.4s, #20
	sli v1.4s, v31.4s, #12
	eor w14, w14, w2
	ror w14, w14, #24
	eor v31.16b, v5.16b, v6.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor w15, w15, w3
	ror w15, w15, #24
	eor v31.16b, v17.16b, v18.16b
	ushr v17.4s, v31.4s, #20
	sli v17.4s, v31.4s, #12
	eor w16, w16, w4
	ror w16, w16, #24
	eor v31.16b, v21.16b, v22.16b
	ushr v21.4s, v31.4s, #20
	sli v21.4s, v31.4s, #12
	eor w17, w17, w5
	ror w17, w17, #24
	eor v31.16b, v25.16b, v26.16b
	ushr v25.4s, v31.4s, #20
	sli v25.4s, v31.4s, #12
	add w10, w10, w14
	eor v31.16b, v29.16b, v8.16b
	ushr v29.4s, v31.4s, #20
	sli v29.4s, v31.4s, #12
	add w11, w11, w15
	add v0.4s, v0.4s, v1.4s
	add w12, w12, w16
	add v4.4s, v4.4s, v5.4s
	add w13, w13, w17
	add v16.4s, v16.4s, v17.4s
	eor w6, w6, w10
	ror w6, w6, #25
	add v20.4s, v20.4s, v21.4s
	eor w7, w7, w11
	ror w7, w7, #25
	add v24.4s, v24.4s, v25.4s
	eor w8, w8, w12
	ror w8, w8, #25
	add v28.4s, v28.4s, v29.4s
	eor w9, w9, w13
	ror w9, w9, #25
	eor v31.16b, v3.16b, v0.16b
	tbl v3.16b, {v31.16b}, v30.16b
	add w2, w2, w7
	eor v31.16b, v7.16b, v4.16b
	tbl v7.16b, {v31.16b}, v30.16b
	add w3, w3, w8
	eor v31.16b, v19.16b, v16.16b
	tbl v19.16b, {v31.16b}, v30.16b
	add w4, w4, w9
	eor v31.16b, v23.16b, v20.16b
	tbl v23.16b, {v31.16b}, v30.16b
	add w5, w5, w6
	eor v31.16b, v27.16b, v24.16b
	tbl v27.16b, {v31.16b}, v30.16b
	eor w17, w17, w2
	ror w17, w17, #16
	eor v31.16b, v9.16b, v28.16b
	tbl v9.16b, {v31.16b}, v30.16b
	eor w14, w14, w3
	ror w14, w14, #16
	add v2.4s, v2.4s, v3.4s
	eor w15, w15, w4
	ror w15, w15, #16
	add v6.4s, v6.4s, v7.4s
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v19.4s
	add w12, w12, w17
	add v22.4s, v22.4s, v23.4s
	add w13, w13, w14
	add v26.4s, v26.4s, v27.4s
	add w10, w10, w15
	add v8.4s, v8.4s, v9.4s
	add w11, w11, w16
	eor v31.16b, v1.16b, v2.16b
	ushr v1.4s, v31.4s, #25
	sli v1.4s, v31.4s, #7
	eor w7, w7, w12
	ror w7, w7, #20
	eor v31.16b, v5.16b, v6.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor w8, w8, w13
	ror w8, w8, #20
	eor v31.16b, v17.16b, v18.16b
	ushr v17.4s, v31.4s, #25
	sli v17.4s, v31.4s, #7
	eor w9, w9, w10
	ror w9, w9, #20
	eor v31.16b, v21.16b, v22.16b
	ushr v21.4s, v31.4s, #25
	sli v21.4s, v31.4s, #7
	eor w6, w6, w11
	ror w6, w6, #20
	eor v31.16b, v25.16b, v26.16b
	ushr v25.4s, v31.4s, #25
	sli v25.4s, v31.4s, #7
	add w2, w2, w7
	eor v31.16b, v29.16b, v8.16b
	ushr v29.4s, v31.4s, #25
	sli v29.4s, v31.4s, #7
	add w3, w3, w8
	ext v1.16b, v1.16b, v1.16b, #12
	add w4, w4, w9
	ext v5.16b, v5.16b, v5.16b, #12
	add w5, w5, w6
	ext v17.16b, v17.16b, v17.16b, #12
	eor w17, w17, w2
	ror w17, w17, #24
	ext v21.16b, v21.16b, v21.16b, #12
	eor w14, w14, w3
	ror w14, w14, #24
	ext v25.16b, v25.16b, v25.16b, #12
	eor w15, w15, w4
	ror w15, w15, #24
	ext v29.16b, v29.16b, v29.16b, #12
	eor w16, w16, w5
	ror w16, w16, #24
	ext v2.16b, v2.16b, v2.16b, #8
	add w12, w12, w17
	ext v6.16b, v6.16b, v6.16b, #8
	add w13, w13, w14
	ext v18.16b, v18.16b, v18.16b, #8
	add w10, w10, w15
	ext v22.16b, v22.16b, v22.16b, #8
	add w11, w11, w16
	ext v26.16b, v26.16b, v26.16b, #8
	eor w7, w7, w12
	ror w7, w7, #25
	ext v8.16b, v8.16b, v8.16b, #8
	eor w8, w8, w13
	ror w8, w8, #25
	ext v3.16b, v3.16b, v3.16b, #4
	eor w9, w9, w10
	ror w9, w9, #25
	ext v7.16b, v7.16b, v7.16b, #4
	eor w6, w6, w11
	ror w6, w6, #25
	ext v19.16b, v19.16b, v19.16b, #4
	ext v23.16b, v23.16b, v23.16b, #4
	ext v27.16b, v27.16b, v27.16b, #4
	ext v9.16b, v9.16b, v9.16b, #4
	sub x1, x1, #1
	cbnz x1, 24b
	add x1, x20, #0
	add x1, x20, #64
	str w2, [x1, #0]
	ldr w2, [x0, #4]
	add w3, w3, w2
	str w3, [x1, #4]
	ldr w2, [x0, #8]
	add w4, w4, w2
	str w4, [x1, #8]
	ldr w2, [x0, #12]
	add w5, w5, w2
	str w5, [x1, #12]
	ldr w2, [x0, #16]
	add w6, w6, w2
	str w6, [x1, #16]
	ldr w2, [x0, #20]
	add w7, w7, w2
	str w7, [x1, #20]
	ldr w2, [x0, #24]
	add w8, w8, w2
	str w8, [x1, #24]
	ldr w2, [x0, #28]
	add w9, w9, w2
	str w9, [x1, #28]
	ldr w2, [x0, #32]
	add w10, w10, w2
	str w10, [x1, #32]
	ldr w2, [x0, #36]
	add w11, w11, w2
	str w11, [x1, #36]
	ldr w2, [x0, #40]
	add w12, w12, w2
	str w12, [x1, #40]
	ldr w2, [x0, #44]
	add w13, w13, w2
	str w13, [x1, #44]
	ldr w2, [x0, #48]
	add w14, w14, w2
	str w14, [x1, #48]
	ldr w2, [x0, #52]
	add w15, w15, w2
	str w15, [x1, #52]
	ldr w2, [x0, #56]
	add w16, w16, w2
	str w16, [x1, #56]
	ldr w2, [x0, #60]
	add w17, w17, w2
	str w17, [x1, #60]
	ldr w2, [x0, #0]
	ldr w3, [x1, #0]
	add w2, w3, w2
	str w2, [x1, #0]
	add x1, x26, #0
	add x2, x19, #0
	add x3, x20, #0
	ldr w4, [x0, #48]
	sub w4, w4, #7
	str w4, [x0, #48]
	ldr q31, [x0, #0]
	add v0.4s, v0.4s, v31.4s
	add v4.4s, v4.4s, v31.4s
	add v16.4s, v16.4s, v31.4s
	add v20.4s, v20.4s, v31.4s
	add v24.4s, v24.4s, v31.4s
	add v28.4s, v28.4s, v31.4s
	ldr q31, [x0, #16]
	add v1.4s, v1.4s, v31.4s
	add v5.4s, v5.4s, v31.4s
	add v17.4s, v17.4s, v31.4s
	add v21.4s, v21.4s, v31.4s
	add v25.4s, v25.4s, v31.4s
	add v29.4s, v29.4s, v31.4s
	ldr q31, [x0, #32]
	add v2.4s, v2.4s, v31.4s
	add v6.4s, v6.4s, v31.4s
	add v18.4s, v18.4s, v31.4s
	add v22.4s, v22.4s, v31.4s
	add v26.4s, v26.4s, v31.4s
	add v8.4s, v8.4s, v31.4s
	ldr q31, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #0
	mov v31.s[0], w4
	add v3.4s, v3.4s, v31.4s
	ldr q31, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #1
	mov v31.s[0], w4
	add v7.4s, v7.4s, v31.4s
	ldr q31, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #2
	mov v31.s[0], w4
	add v19.4s, v19.4s, v31.4s
	ldr q31, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #3
	mov v31.s[0], w4
	add v23.4s, v23.4s, v31.4s
	ldr q31, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #4
	mov v31.s[0], w4
	add v27.4s, v27.4s, v31.4s
	ldr q31, [x0, #48]
	ldr w4, [x0, #48]
	add w4, w4, #5
	mov v31.s[0], w4
	add v9.4s, v9.4s, v31.4s
	ldr q31, [x1, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q31, [x1, #16]
	eor v31.16b, v31.16b, v1.16b
	str q31, [x1, #16]
	ldr q31, [x1, #32]
	eor v31.16b, v31.16b, v2.16b
	str q31, [x1, #32]
	ldr q31, [x1, #48]
	eor v31.16b, v31.16b, v3.16b
	str q31, [x1, #48]
	ldr q31, [x1, #64]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #64]
	ldr q31, [x1, #80]
	eor v31.16b, v31.16b, v5.16b
	str q31, [x1, #80]
	ldr q31, [x1, #96]
	eor v31.16b, v31.16b, v6.16b
	str q31, [x1, #96]
	ldr q31, [x1, #112]
	eor v31.16b, v31.16b, v7.16b
	str q31, [x1, #112]
	ldr q31, [x1, #128]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #128]
	ldr q31, [x1, #144]
	eor v31.16b, v31.16b, v17.16b
	str q31, [x1, #144]
	ldr q31, [x1, #160]
	eor v31.16b, v31.16b, v18.16b
	str q31, [x1, #160]
	ldr q31, [x1, #176]
	eor v31.16b, v31.16b, v19.16b
	str q31, [x1, #176]
	ldr q31, [x1, #192]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #192]
	ldr q31, [x1, #208]
	eor v31.16b, v31.16b, v21.16b
	str q31, [x1, #208]
	ldr q31, [x1, #224]
	eor v31.16b, v31.16b, v22.16b
	str q31, [x1, #224]
	ldr q31, [x1, #240]
	eor v31.16b, v31.16b, v23.16b
	str q31, [x1, #240]
	ldr q31, [x1, #256]
	eor v31.16b, v31.16b, v24.16b
	str q31, [x1, #256]
	ldr q31, [x1, #272]
	eor v31.16b, v31.16b, v25.16b
	str q31, [x1, #272]
	ldr q31, [x1, #288]
	eor v31.16b, v31.16b, v26.16b
	str q31, [x1, #288]
	ldr q31, [x1, #304]
	eor v31.16b, v31.16b, v27.16b
	str q31, [x1, #304]
	ldr q31, [x1, #320]
	eor v31.16b, v31.16b, v28.16b
	str q31, [x1, #320]
	ldr q31, [x1, #336]
	eor v31.16b, v31.16b, v29.16b
	str q31, [x1, #336]
	ldr q31, [x1, #352]
	eor v31.16b, v31.16b, v8.16b
	str q31, [x1, #352]
	ldr q31, [x1, #368]
	eor v31.16b, v31.16b, v9.16b
	str q31, [x1, #368]
	ldr q30, [x3, #0]
	ldr q31, [x1, #384]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #384]
	ldr q30, [x3, #16]
	ldr q31, [x1, #400]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #400]
	ldr q30, [x3, #32]
	ldr q31, [x1, #416]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #416]
	ldr q30, [x3, #48]
	ldr q31, [x1, #432]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #432]
	ldr q30, [x3, #64]
	ldr q31, [x1, #448]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #448]
	ldr q30, [x3, #80]
	ldr q31, [x1, #464]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #464]
	ldr q30, [x3, #96]
	ldr q31, [x1, #480]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #480]
	ldr q30, [x3, #112]
	ldr q31, [x1, #496]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #496]
	ldr w4, [x0, #48]
	add w4, w4, #8
	str w4, [x0, #48]
	add x1, x1, #512
	sub x2, x2, #512
	lsr x5, x2, #6
	sub x5, x5, #8
	lsr x5, x5, #63
	cbz x5, 22b
	ldr q8, [x3, #128]
	ldr q9, [x3, #144]
	ldr x20, [x3, #256]
	ldr x19, [x3, #264]
	ldr x26, [x3, #272]
	b 21f
20:
21:
	lsr x5, x2, #8
	cbz x5, 25f
27:
	ldr w4, [x0, #0]
	dup v0.4s, w4
	ldr w4, [x0, #4]
	dup v1.4s, w4
	ldr w4, [x0, #8]
	dup v2.4s, w4
	ldr w4, [x0, #12]
	dup v3.4s, w4
	ldr w4, [x0, #16]
	dup v4.4s, w4
	ldr w4, [x0, #20]
	dup v5.4s, w4
	ldr w4, [x0, #24]
	dup v6.4s, w4
	ldr w4, [x0, #28]
	dup v7.4s, w4
	ldr w4, [x0, #32]
	dup v16.4s, w4
	ldr w4, [x0, #36]
	dup v17.4s, w4
	ldr w4, [x0, #40]
	dup v18.4s, w4
	ldr w4, [x0, #44]
	dup v19.4s, w4
	ldr w4, [x0, #48]
	dup v20.4s, w4
	add w4, w4, #1
	mov v20.s[1], w4
	add w4, w4, #1
	mov v20.s[2], w4
	add w4, w4, #1
	mov v20.s[3], w4
	ldr w4, [x0, #52]
	dup v21.4s, w4
	ldr w4, [x0, #56]
	dup v22.4s, w4
	ldr w4, [x0, #60]
	dup v23.4s, w4
	movz x4, #3, lsl #0
	movk x4, #513, lsl #16
	movk x4, #1031, lsl #32
	movk x4, #1541, lsl #48
	dup v30.2d, x4
	movz x4, #2059, lsl #0
	movk x4, #2569, lsl #16
	movk x4, #3087, lsl #32
	movk x4, #3597, lsl #48
	mov v30.d[1], x4
	movz x4, #10, lsl #0
28:
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	sub x4, x4, #1
	cbnz x4, 28b
	ldr w4, [x0, #0]
	dup v31.4s, w4
	add v0.4s, v0.4s, v31.4s
	ldr w4, [x0, #4]
	dup v31.4s, w4
	add v1.4s, v1.4s, v31.4s
	ldr w4, [x0, #8]
	dup v31.4s, w4
	add v2.4s, v2.4s, v31.4s
	ldr w4, [x0, #12]
	dup v31.4s, w4
	add v3.4s, v3.4s, v31.4s
	ldr w4, [x0, #16]
	dup v31.4s, w4
	add v4.4s, v4.4s, v31.4s
	ldr w4, [x0, #20]
	dup v31.4s, w4
	add v5.4s, v5.4s, v31.4s
	ldr w4, [x0, #24]
	dup v31.4s, w4
	add v6.4s, v6.4s, v31.4s
	ldr w4, [x0, #28]
	dup v31.4s, w4
	add v7.4s, v7.4s, v31.4s
	ldr w4, [x0, #32]
	dup v31.4s, w4
	add v16.4s, v16.4s, v31.4s
	ldr w4, [x0, #36]
	dup v31.4s, w4
	add v17.4s, v17.4s, v31.4s
	ldr w4, [x0, #40]
	dup v31.4s, w4
	add v18.4s, v18.4s, v31.4s
	ldr w4, [x0, #44]
	dup v31.4s, w4
	add v19.4s, v19.4s, v31.4s
	ldr w4, [x0, #48]
	dup v31.4s, w4
	add w4, w4, #1
	mov v31.s[1], w4
	add w4, w4, #1
	mov v31.s[2], w4
	add w4, w4, #1
	mov v31.s[3], w4
	add v20.4s, v20.4s, v31.4s
	ldr w4, [x0, #52]
	dup v31.4s, w4
	add v21.4s, v21.4s, v31.4s
	ldr w4, [x0, #56]
	dup v31.4s, w4
	add v22.4s, v22.4s, v31.4s
	ldr w4, [x0, #60]
	dup v31.4s, w4
	add v23.4s, v23.4s, v31.4s
	zip1 v24.4s, v0.4s, v1.4s
	zip2 v25.4s, v0.4s, v1.4s
	zip1 v26.4s, v2.4s, v3.4s
	zip2 v27.4s, v2.4s, v3.4s
	zip1 v0.2d, v24.2d, v26.2d
	zip2 v1.2d, v24.2d, v26.2d
	zip1 v2.2d, v25.2d, v27.2d
	zip2 v3.2d, v25.2d, v27.2d
	ldr q31, [x1, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q31, [x1, #64]
	eor v31.16b, v31.16b, v1.16b
	str q31, [x1, #64]
	ldr q31, [x1, #128]
	eor v31.16b, v31.16b, v2.16b
	str q31, [x1, #128]
	ldr q31, [x1, #192]
	eor v31.16b, v31.16b, v3.16b
	str q31, [x1, #192]
	zip1 v24.4s, v4.4s, v5.4s
	zip2 v25.4s, v4.4s, v5.4s
	zip1 v26.4s, v6.4s, v7.4s
	zip2 v27.4s, v6.4s, v7.4s
	zip1 v4.2d, v24.2d, v26.2d
	zip2 v5.2d, v24.2d, v26.2d
	zip1 v6.2d, v25.2d, v27.2d
	zip2 v7.2d, v25.2d, v27.2d
	ldr q31, [x1, #16]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #16]
	ldr q31, [x1, #80]
	eor v31.16b, v31.16b, v5.16b
	str q31, [x1, #80]
	ldr q31, [x1, #144]
	eor v31.16b, v31.16b, v6.16b
	str q31, [x1, #144]
	ldr q31, [x1, #208]
	eor v31.16b, v31.16b, v7.16b
	str q31, [x1, #208]
	zip1 v24.4s, v16.4s, v17.4s
	zip2 v25.4s, v16.4s, v17.4s
	zip1 v26.4s, v18.4s, v19.4s
	zip2 v27.4s, v18.4s, v19.4s
	zip1 v16.2d, v24.2d, v26.2d
	zip2 v17.2d, v24.2d, v26.2d
	zip1 v18.2d, v25.2d, v27.2d
	zip2 v19.2d, v25.2d, v27.2d
	ldr q31, [x1, #32]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #32]
	ldr q31, [x1, #96]
	eor v31.16b, v31.16b, v17.16b
	str q31, [x1, #96]
	ldr q31, [x1, #160]
	eor v31.16b, v31.16b, v18.16b
	str q31, [x1, #160]
	ldr q31, [x1, #224]
	eor v31.16b, v31.16b, v19.16b
	str q31, [x1, #224]
	zip1 v24.4s, v20.4s, v21.4s
	zip2 v25.4s, v20.4s, v21.4s
	zip1 v26.4s, v22.4s, v23.4s
	zip2 v27.4s, v22.4s, v23.4s
	zip1 v20.2d, v24.2d, v26.2d
	zip2 v21.2d, v24.2d, v26.2d
	zip1 v22.2d, v25.2d, v27.2d
	zip2 v23.2d, v25.2d, v27.2d
	ldr q31, [x1, #48]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #48]
	ldr q31, [x1, #112]
	eor v31.16b, v31.16b, v21.16b
	str q31, [x1, #112]
	ldr q31, [x1, #176]
	eor v31.16b, v31.16b, v22.16b
	str q31, [x1, #176]
	ldr q31, [x1, #240]
	eor v31.16b, v31.16b, v23.16b
	str q31, [x1, #240]
	ldr w4, [x0, #48]
	add w4, w4, #4
	str w4, [x0, #48]
	add x1, x1, #256
	sub x2, x2, #256
	lsr x5, x2, #8
	cbnz x5, 27b
	b 26f
25:
26:
	lsr x5, x2, #7
	cbz x5, 29f
	lsr x5, x2, #6
	sub x5, x5, #3
	lsr x5, x5, #63
	cbnz x5, 211f
	ldr w4, [x0, #0]
	dup v0.4s, w4
	ldr w4, [x0, #4]
	dup v1.4s, w4
	ldr w4, [x0, #8]
	dup v2.4s, w4
	ldr w4, [x0, #12]
	dup v3.4s, w4
	ldr w4, [x0, #16]
	dup v4.4s, w4
	ldr w4, [x0, #20]
	dup v5.4s, w4
	ldr w4, [x0, #24]
	dup v6.4s, w4
	ldr w4, [x0, #28]
	dup v7.4s, w4
	ldr w4, [x0, #32]
	dup v16.4s, w4
	ldr w4, [x0, #36]
	dup v17.4s, w4
	ldr w4, [x0, #40]
	dup v18.4s, w4
	ldr w4, [x0, #44]
	dup v19.4s, w4
	ldr w4, [x0, #48]
	dup v20.4s, w4
	add w4, w4, #1
	mov v20.s[1], w4
	add w4, w4, #1
	mov v20.s[2], w4
	add w4, w4, #1
	mov v20.s[3], w4
	ldr w4, [x0, #52]
	dup v21.4s, w4
	ldr w4, [x0, #56]
	dup v22.4s, w4
	ldr w4, [x0, #60]
	dup v23.4s, w4
	movz x4, #3, lsl #0
	movk x4, #513, lsl #16
	movk x4, #1031, lsl #32
	movk x4, #1541, lsl #48
	dup v30.2d, x4
	movz x4, #2059, lsl #0
	movk x4, #2569, lsl #16
	movk x4, #3087, lsl #32
	movk x4, #3597, lsl #48
	mov v30.d[1], x4
	movz x4, #10, lsl #0
213:
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	sub x4, x4, #1
	cbnz x4, 213b
	ldr w4, [x0, #0]
	dup v31.4s, w4
	add v0.4s, v0.4s, v31.4s
	ldr w4, [x0, #4]
	dup v31.4s, w4
	add v1.4s, v1.4s, v31.4s
	ldr w4, [x0, #8]
	dup v31.4s, w4
	add v2.4s, v2.4s, v31.4s
	ldr w4, [x0, #12]
	dup v31.4s, w4
	add v3.4s, v3.4s, v31.4s
	ldr w4, [x0, #16]
	dup v31.4s, w4
	add v4.4s, v4.4s, v31.4s
	ldr w4, [x0, #20]
	dup v31.4s, w4
	add v5.4s, v5.4s, v31.4s
	ldr w4, [x0, #24]
	dup v31.4s, w4
	add v6.4s, v6.4s, v31.4s
	ldr w4, [x0, #28]
	dup v31.4s, w4
	add v7.4s, v7.4s, v31.4s
	ldr w4, [x0, #32]
	dup v31.4s, w4
	add v16.4s, v16.4s, v31.4s
	ldr w4, [x0, #36]
	dup v31.4s, w4
	add v17.4s, v17.4s, v31.4s
	ldr w4, [x0, #40]
	dup v31.4s, w4
	add v18.4s, v18.4s, v31.4s
	ldr w4, [x0, #44]
	dup v31.4s, w4
	add v19.4s, v19.4s, v31.4s
	ldr w4, [x0, #48]
	dup v31.4s, w4
	add w4, w4, #1
	mov v31.s[1], w4
	add w4, w4, #1
	mov v31.s[2], w4
	add w4, w4, #1
	mov v31.s[3], w4
	add v20.4s, v20.4s, v31.4s
	ldr w4, [x0, #52]
	dup v31.4s, w4
	add v21.4s, v21.4s, v31.4s
	ldr w4, [x0, #56]
	dup v31.4s, w4
	add v22.4s, v22.4s, v31.4s
	ldr w4, [x0, #60]
	dup v31.4s, w4
	add v23.4s, v23.4s, v31.4s
	zip1 v24.4s, v0.4s, v1.4s
	zip2 v25.4s, v0.4s, v1.4s
	zip1 v26.4s, v2.4s, v3.4s
	zip2 v27.4s, v2.4s, v3.4s
	zip1 v0.2d, v24.2d, v26.2d
	zip2 v1.2d, v24.2d, v26.2d
	zip1 v2.2d, v25.2d, v27.2d
	zip2 v3.2d, v25.2d, v27.2d
	ldr q31, [x1, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q31, [x1, #64]
	eor v31.16b, v31.16b, v1.16b
	str q31, [x1, #64]
	ldr q31, [x1, #128]
	eor v31.16b, v31.16b, v2.16b
	str q31, [x1, #128]
	zip1 v24.4s, v4.4s, v5.4s
	zip2 v25.4s, v4.4s, v5.4s
	zip1 v26.4s, v6.4s, v7.4s
	zip2 v27.4s, v6.4s, v7.4s
	zip1 v4.2d, v24.2d, v26.2d
	zip2 v5.2d, v24.2d, v26.2d
	zip1 v6.2d, v25.2d, v27.2d
	zip2 v7.2d, v25.2d, v27.2d
	ldr q31, [x1, #16]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #16]
	ldr q31, [x1, #80]
	eor v31.16b, v31.16b, v5.16b
	str q31, [x1, #80]
	ldr q31, [x1, #144]
	eor v31.16b, v31.16b, v6.16b
	str q31, [x1, #144]
	zip1 v24.4s, v16.4s, v17.4s
	zip2 v25.4s, v16.4s, v17.4s
	zip1 v26.4s, v18.4s, v19.4s
	zip2 v27.4s, v18.4s, v19.4s
	zip1 v16.2d, v24.2d, v26.2d
	zip2 v17.2d, v24.2d, v26.2d
	zip1 v18.2d, v25.2d, v27.2d
	zip2 v19.2d, v25.2d, v27.2d
	ldr q31, [x1, #32]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #32]
	ldr q31, [x1, #96]
	eor v31.16b, v31.16b, v17.16b
	str q31, [x1, #96]
	ldr q31, [x1, #160]
	eor v31.16b, v31.16b, v18.16b
	str q31, [x1, #160]
	zip1 v24.4s, v20.4s, v21.4s
	zip2 v25.4s, v20.4s, v21.4s
	zip1 v26.4s, v22.4s, v23.4s
	zip2 v27.4s, v22.4s, v23.4s
	zip1 v20.2d, v24.2d, v26.2d
	zip2 v21.2d, v24.2d, v26.2d
	zip1 v22.2d, v25.2d, v27.2d
	zip2 v23.2d, v25.2d, v27.2d
	ldr q31, [x1, #48]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #48]
	ldr q31, [x1, #112]
	eor v31.16b, v31.16b, v21.16b
	str q31, [x1, #112]
	ldr q31, [x1, #176]
	eor v31.16b, v31.16b, v22.16b
	str q31, [x1, #176]
	ldr w4, [x0, #48]
	add w4, w4, #3
	str w4, [x0, #48]
	add x1, x1, #192
	sub x2, x2, #192
	b 212f
211:
	ldr w4, [x0, #0]
	dup v0.4s, w4
	ldr w4, [x0, #4]
	dup v1.4s, w4
	ldr w4, [x0, #8]
	dup v2.4s, w4
	ldr w4, [x0, #12]
	dup v3.4s, w4
	ldr w4, [x0, #16]
	dup v4.4s, w4
	ldr w4, [x0, #20]
	dup v5.4s, w4
	ldr w4, [x0, #24]
	dup v6.4s, w4
	ldr w4, [x0, #28]
	dup v7.4s, w4
	ldr w4, [x0, #32]
	dup v16.4s, w4
	ldr w4, [x0, #36]
	dup v17.4s, w4
	ldr w4, [x0, #40]
	dup v18.4s, w4
	ldr w4, [x0, #44]
	dup v19.4s, w4
	ldr w4, [x0, #48]
	dup v20.4s, w4
	add w4, w4, #1
	mov v20.s[1], w4
	add w4, w4, #1
	mov v20.s[2], w4
	add w4, w4, #1
	mov v20.s[3], w4
	ldr w4, [x0, #52]
	dup v21.4s, w4
	ldr w4, [x0, #56]
	dup v22.4s, w4
	ldr w4, [x0, #60]
	dup v23.4s, w4
	movz x4, #3, lsl #0
	movk x4, #513, lsl #16
	movk x4, #1031, lsl #32
	movk x4, #1541, lsl #48
	dup v30.2d, x4
	movz x4, #2059, lsl #0
	movk x4, #2569, lsl #16
	movk x4, #3087, lsl #32
	movk x4, #3597, lsl #48
	mov v30.d[1], x4
	movz x4, #10, lsl #0
214:
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	eor v31.16b, v20.16b, v0.16b
	rev32 v20.8h, v31.8h
	eor v31.16b, v21.16b, v1.16b
	rev32 v21.8h, v31.8h
	eor v31.16b, v22.16b, v2.16b
	rev32 v22.8h, v31.8h
	eor v31.16b, v23.16b, v3.16b
	rev32 v23.8h, v31.8h
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	eor v31.16b, v20.16b, v0.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor v31.16b, v21.16b, v1.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor v31.16b, v22.16b, v2.16b
	tbl v22.16b, {v31.16b}, v30.16b
	eor v31.16b, v23.16b, v3.16b
	tbl v23.16b, {v31.16b}, v30.16b
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	eor v31.16b, v4.16b, v16.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	eor v31.16b, v5.16b, v17.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor v31.16b, v6.16b, v18.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor v31.16b, v7.16b, v19.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	eor v31.16b, v23.16b, v0.16b
	rev32 v23.8h, v31.8h
	eor v31.16b, v20.16b, v1.16b
	rev32 v20.8h, v31.8h
	eor v31.16b, v21.16b, v2.16b
	rev32 v21.8h, v31.8h
	eor v31.16b, v22.16b, v3.16b
	rev32 v22.8h, v31.8h
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #20
	sli v5.4s, v31.4s, #12
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #20
	sli v6.4s, v31.4s, #12
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #20
	sli v7.4s, v31.4s, #12
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #20
	sli v4.4s, v31.4s, #12
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	eor v31.16b, v23.16b, v0.16b
	tbl v23.16b, {v31.16b}, v30.16b
	eor v31.16b, v20.16b, v1.16b
	tbl v20.16b, {v31.16b}, v30.16b
	eor v31.16b, v21.16b, v2.16b
	tbl v21.16b, {v31.16b}, v30.16b
	eor v31.16b, v22.16b, v3.16b
	tbl v22.16b, {v31.16b}, v30.16b
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	eor v31.16b, v5.16b, v18.16b
	ushr v5.4s, v31.4s, #25
	sli v5.4s, v31.4s, #7
	eor v31.16b, v6.16b, v19.16b
	ushr v6.4s, v31.4s, #25
	sli v6.4s, v31.4s, #7
	eor v31.16b, v7.16b, v16.16b
	ushr v7.4s, v31.4s, #25
	sli v7.4s, v31.4s, #7
	eor v31.16b, v4.16b, v17.16b
	ushr v4.4s, v31.4s, #25
	sli v4.4s, v31.4s, #7
	sub x4, x4, #1
	cbnz x4, 214b
	ldr w4, [x0, #0]
	dup v31.4s, w4
	add v0.4s, v0.4s, v31.4s
	ldr w4, [x0, #4]
	dup v31.4s, w4
	add v1.4s, v1.4s, v31.4s
	ldr w4, [x0, #8]
	dup v31.4s, w4
	add v2.4s, v2.4s, v31.4s
	ldr w4, [x0, #12]
	dup v31.4s, w4
	add v3.4s, v3.4s, v31.4s
	ldr w4, [x0, #16]
	dup v31.4s, w4
	add v4.4s, v4.4s, v31.4s
	ldr w4, [x0, #20]
	dup v31.4s, w4
	add v5.4s, v5.4s, v31.4s
	ldr w4, [x0, #24]
	dup v31.4s, w4
	add v6.4s, v6.4s, v31.4s
	ldr w4, [x0, #28]
	dup v31.4s, w4
	add v7.4s, v7.4s, v31.4s
	ldr w4, [x0, #32]
	dup v31.4s, w4
	add v16.4s, v16.4s, v31.4s
	ldr w4, [x0, #36]
	dup v31.4s, w4
	add v17.4s, v17.4s, v31.4s
	ldr w4, [x0, #40]
	dup v31.4s, w4
	add v18.4s, v18.4s, v31.4s
	ldr w4, [x0, #44]
	dup v31.4s, w4
	add v19.4s, v19.4s, v31.4s
	ldr w4, [x0, #48]
	dup v31.4s, w4
	add w4, w4, #1
	mov v31.s[1], w4
	add w4, w4, #1
	mov v31.s[2], w4
	add w4, w4, #1
	mov v31.s[3], w4
	add v20.4s, v20.4s, v31.4s
	ldr w4, [x0, #52]
	dup v31.4s, w4
	add v21.4s, v21.4s, v31.4s
	ldr w4, [x0, #56]
	dup v31.4s, w4
	add v22.4s, v22.4s, v31.4s
	ldr w4, [x0, #60]
	dup v31.4s, w4
	add v23.4s, v23.4s, v31.4s
	zip1 v24.4s, v0.4s, v1.4s
	zip2 v25.4s, v0.4s, v1.4s
	zip1 v26.4s, v2.4s, v3.4s
	zip2 v27.4s, v2.4s, v3.4s
	zip1 v0.2d, v24.2d, v26.2d
	zip2 v1.2d, v24.2d, v26.2d
	zip1 v2.2d, v25.2d, v27.2d
	zip2 v3.2d, v25.2d, v27.2d
	ldr q31, [x1, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q31, [x1, #64]
	eor v31.16b, v31.16b, v1.16b
	str q31, [x1, #64]
	zip1 v24.4s, v4.4s, v5.4s
	zip2 v25.4s, v4.4s, v5.4s
	zip1 v26.4s, v6.4s, v7.4s
	zip2 v27.4s, v6.4s, v7.4s
	zip1 v4.2d, v24.2d, v26.2d
	zip2 v5.2d, v24.2d, v26.2d
	zip1 v6.2d, v25.2d, v27.2d
	zip2 v7.2d, v25.2d, v27.2d
	ldr q31, [x1, #16]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #16]
	ldr q31, [x1, #80]
	eor v31.16b, v31.16b, v5.16b
	str q31, [x1, #80]
	zip1 v24.4s, v16.4s, v17.4s
	zip2 v25.4s, v16.4s, v17.4s
	zip1 v26.4s, v18.4s, v19.4s
	zip2 v27.4s, v18.4s, v19.4s
	zip1 v16.2d, v24.2d, v26.2d
	zip2 v17.2d, v24.2d, v26.2d
	zip1 v18.2d, v25.2d, v27.2d
	zip2 v19.2d, v25.2d, v27.2d
	ldr q31, [x1, #32]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #32]
	ldr q31, [x1, #96]
	eor v31.16b, v31.16b, v17.16b
	str q31, [x1, #96]
	zip1 v24.4s, v20.4s, v21.4s
	zip2 v25.4s, v20.4s, v21.4s
	zip1 v26.4s, v22.4s, v23.4s
	zip2 v27.4s, v22.4s, v23.4s
	zip1 v20.2d, v24.2d, v26.2d
	zip2 v21.2d, v24.2d, v26.2d
	zip1 v22.2d, v25.2d, v27.2d
	zip2 v23.2d, v25.2d, v27.2d
	ldr q31, [x1, #48]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #48]
	ldr q31, [x1, #112]
	eor v31.16b, v31.16b, v21.16b
	str q31, [x1, #112]
	ldr w4, [x0, #48]
	add w4, w4, #2
	str w4, [x0, #48]
	add x1, x1, #128
	sub x2, x2, #128
212:
	str x19, [x3, #256]
	str x20, [x3, #264]
	str x30, [x3, #272]
	add x19, x1, #0
	add x20, x2, #0
	add x1, x3, #0
	cbz x20, 215f
217:
	bl {vg_chacha20_block}
	lsr x9, x20, #6
	add x2, x20, #0
	cbz x9, 218f
	movz x2, #64, lsl #0
	b 219f
218:
219:
	sub x20, x20, x2
	add x7, x1, #0
220:
	ldrb w6, [x19, #0]
	ldrb w8, [x7, #0]
	eor w6, w6, w8
	strb w6, [x19, #0]
	add x19, x19, #1
	add x7, x7, #1
	sub x2, x2, #1
	cbnz x2, 220b
	ldr w3, [x0, #48]
	add w3, w3, #1
	str w3, [x0, #48]
	cbnz x20, 217b
	b 216f
215:
216:
	ldr x19, [x1, #256]
	ldr x20, [x1, #264]
	ldr x30, [x1, #272]
	b 210f
29:
	str x19, [x3, #256]
	str x20, [x3, #264]
	str x30, [x3, #272]
	add x19, x1, #0
	add x20, x2, #0
	add x1, x3, #0
	cbz x20, 221f
223:
	bl {vg_chacha20_block}
	lsr x9, x20, #6
	add x2, x20, #0
	cbz x9, 224f
	movz x2, #64, lsl #0
	b 225f
224:
225:
	sub x20, x20, x2
	add x7, x1, #0
226:
	ldrb w6, [x19, #0]
	ldrb w8, [x7, #0]
	eor w6, w6, w8
	strb w6, [x19, #0]
	add x19, x19, #1
	add x7, x7, #1
	sub x2, x2, #1
	cbnz x2, 226b
	ldr w3, [x0, #48]
	add w3, w3, #1
	str w3, [x0, #48]
	cbnz x20, 223b
	b 222f
221:
222:
	ldr x19, [x1, #256]
	ldr x20, [x1, #264]
	ldr x30, [x1, #272]
210:
	ret
	.p2align 6
