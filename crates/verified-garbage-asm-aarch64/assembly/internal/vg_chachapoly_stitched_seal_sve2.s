// The functions of `src/internal/vg_chachapoly_stitched_seal_sve2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chachapoly_stitched_seal_sve2:
	mov v15.d[1], x30
	add x0, x21, #64
	add x1, x22, #0
	add x2, x23, #0
	add x3, x21, #128
	lsr x5, x2, #6
	sub x5, x5, #8
	lsr x5, x5, #63
	cbnz x5, 20f
	str x27, [x21, #32]
	str x28, [x21, #40]
	movz x24, #65535, lsl #0
	movk x24, #4095, lsl #16
	movk x24, #65532, lsl #32
	movk x24, #4095, lsl #48
	ldr x25, [x21, #472]
	and x25, x25, x24
	str x25, [x21, #288]
	movz x24, #65532, lsl #0
	movk x24, #4095, lsl #16
	movk x24, #65532, lsl #32
	movk x24, #4095, lsl #48
	ldr x25, [x21, #480]
	and x25, x25, x24
	str x25, [x21, #296]
	ldr x22, [x21, #456]
	ldr x23, [x21, #464]
	ldr x21, [x21, #448]
	add x4, x1, #0
	str x20, [x3, #256]
	str x19, [x3, #264]
	str x26, [x3, #272]
	str x27, [x3, #280]
	add x20, x3, #0
	str q8, [x3, #128]
	str q9, [x3, #144]
	add x27, x1, #0
	add x1, x4, #0
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
22:
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
	xar z3.s, z3.s, z0.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z7.s, z7.s, z4.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	xar z19.s, z19.s, z16.s, #16
	add w10, w10, w14
	xar z23.s, z23.s, z20.s, #16
	add w11, w11, w15
	xar z27.s, z27.s, z24.s, #16
	add w12, w12, w16
	xar z9.s, z9.s, z28.s, #16
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
	xar z1.s, z1.s, z2.s, #20
	add w4, w4, w8
	xar z5.s, z5.s, z6.s, #20
	add w5, w5, w9
	xar z17.s, z17.s, z18.s, #20
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z22.s, #20
	eor w15, w15, w3
	ror w15, w15, #24
	xar z25.s, z25.s, z26.s, #20
	eor w16, w16, w4
	ror w16, w16, #24
	xar z29.s, z29.s, z8.s, #20
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
	xar z3.s, z3.s, z0.s, #24
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z4.s, #24
	eor w9, w9, w13
	ror w9, w9, #25
	xar z19.s, z19.s, z16.s, #24
	add w2, w2, w7
	xar z23.s, z23.s, z20.s, #24
	add w3, w3, w8
	xar z27.s, z27.s, z24.s, #24
	add w4, w4, w9
	xar z9.s, z9.s, z28.s, #24
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
	xar z1.s, z1.s, z2.s, #25
	add w10, w10, w15
	xar z5.s, z5.s, z6.s, #25
	add w11, w11, w16
	xar z17.s, z17.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #20
	xar z21.s, z21.s, z22.s, #25
	eor w8, w8, w13
	ror w8, w8, #20
	xar z25.s, z25.s, z26.s, #25
	eor w9, w9, w10
	ror w9, w9, #20
	xar z29.s, z29.s, z8.s, #25
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
	xar z3.s, z3.s, z0.s, #16
	add w10, w10, w14
	xar z7.s, z7.s, z4.s, #16
	add w11, w11, w15
	xar z19.s, z19.s, z16.s, #16
	add w12, w12, w16
	xar z23.s, z23.s, z20.s, #16
	add w13, w13, w17
	xar z27.s, z27.s, z24.s, #16
	eor w6, w6, w10
	ror w6, w6, #20
	xar z9.s, z9.s, z28.s, #16
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
	xar z1.s, z1.s, z2.s, #20
	eor w14, w14, w2
	ror w14, w14, #24
	xar z5.s, z5.s, z6.s, #20
	eor w15, w15, w3
	ror w15, w15, #24
	xar z17.s, z17.s, z18.s, #20
	eor w16, w16, w4
	ror w16, w16, #24
	xar z21.s, z21.s, z22.s, #20
	eor w17, w17, w5
	ror w17, w17, #24
	xar z25.s, z25.s, z26.s, #20
	add w10, w10, w14
	xar z29.s, z29.s, z8.s, #20
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
	xar z3.s, z3.s, z0.s, #24
	add w2, w2, w7
	xar z7.s, z7.s, z4.s, #24
	add w3, w3, w8
	xar z19.s, z19.s, z16.s, #24
	add w4, w4, w9
	xar z23.s, z23.s, z20.s, #24
	add w5, w5, w6
	xar z27.s, z27.s, z24.s, #24
	eor w17, w17, w2
	ror w17, w17, #16
	xar z9.s, z9.s, z28.s, #24
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
	xar z1.s, z1.s, z2.s, #25
	eor w7, w7, w12
	ror w7, w7, #20
	xar z5.s, z5.s, z6.s, #25
	eor w8, w8, w13
	ror w8, w8, #20
	xar z17.s, z17.s, z18.s, #25
	eor w9, w9, w10
	ror w9, w9, #20
	xar z21.s, z21.s, z22.s, #25
	eor w6, w6, w11
	ror w6, w6, #20
	xar z25.s, z25.s, z26.s, #25
	add w2, w2, w7
	xar z29.s, z29.s, z8.s, #25
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
	cbnz x1, 22b
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
	xar z3.s, z3.s, z0.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z7.s, z7.s, z4.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	xar z19.s, z19.s, z16.s, #16
	add w10, w10, w14
	xar z23.s, z23.s, z20.s, #16
	add w11, w11, w15
	xar z27.s, z27.s, z24.s, #16
	add w12, w12, w16
	xar z9.s, z9.s, z28.s, #16
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
	xar z1.s, z1.s, z2.s, #20
	add w4, w4, w8
	xar z5.s, z5.s, z6.s, #20
	add w5, w5, w9
	xar z17.s, z17.s, z18.s, #20
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z22.s, #20
	eor w15, w15, w3
	ror w15, w15, #24
	xar z25.s, z25.s, z26.s, #20
	eor w16, w16, w4
	ror w16, w16, #24
	xar z29.s, z29.s, z8.s, #20
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
	xar z3.s, z3.s, z0.s, #24
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z4.s, #24
	eor w9, w9, w13
	ror w9, w9, #25
	xar z19.s, z19.s, z16.s, #24
	add w2, w2, w7
	xar z23.s, z23.s, z20.s, #24
	add w3, w3, w8
	xar z27.s, z27.s, z24.s, #24
	add w4, w4, w9
	xar z9.s, z9.s, z28.s, #24
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
	xar z1.s, z1.s, z2.s, #25
	add w10, w10, w15
	xar z5.s, z5.s, z6.s, #25
	add w11, w11, w16
	xar z17.s, z17.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #20
	xar z21.s, z21.s, z22.s, #25
	eor w8, w8, w13
	ror w8, w8, #20
	xar z25.s, z25.s, z26.s, #25
	eor w9, w9, w10
	ror w9, w9, #20
	xar z29.s, z29.s, z8.s, #25
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
	xar z3.s, z3.s, z0.s, #16
	add w10, w10, w14
	xar z7.s, z7.s, z4.s, #16
	add w11, w11, w15
	xar z19.s, z19.s, z16.s, #16
	add w12, w12, w16
	xar z23.s, z23.s, z20.s, #16
	add w13, w13, w17
	xar z27.s, z27.s, z24.s, #16
	eor w6, w6, w10
	ror w6, w6, #20
	xar z9.s, z9.s, z28.s, #16
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
	xar z1.s, z1.s, z2.s, #20
	eor w14, w14, w2
	ror w14, w14, #24
	xar z5.s, z5.s, z6.s, #20
	eor w15, w15, w3
	ror w15, w15, #24
	xar z17.s, z17.s, z18.s, #20
	eor w16, w16, w4
	ror w16, w16, #24
	xar z21.s, z21.s, z22.s, #20
	eor w17, w17, w5
	ror w17, w17, #24
	xar z25.s, z25.s, z26.s, #20
	add w10, w10, w14
	xar z29.s, z29.s, z8.s, #20
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
	xar z3.s, z3.s, z0.s, #24
	add w2, w2, w7
	xar z7.s, z7.s, z4.s, #24
	add w3, w3, w8
	xar z19.s, z19.s, z16.s, #24
	add w4, w4, w9
	xar z23.s, z23.s, z20.s, #24
	add w5, w5, w6
	xar z27.s, z27.s, z24.s, #24
	eor w17, w17, w2
	ror w17, w17, #16
	xar z9.s, z9.s, z28.s, #24
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
	xar z1.s, z1.s, z2.s, #25
	eor w7, w7, w12
	ror w7, w7, #20
	xar z5.s, z5.s, z6.s, #25
	eor w8, w8, w13
	ror w8, w8, #20
	xar z17.s, z17.s, z18.s, #25
	eor w9, w9, w10
	ror w9, w9, #20
	xar z21.s, z21.s, z22.s, #25
	eor w6, w6, w11
	ror w6, w6, #20
	xar z25.s, z25.s, z26.s, #25
	add w2, w2, w7
	xar z29.s, z29.s, z8.s, #25
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
	ldr q31, [x27, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q31, [x27, #16]
	eor v31.16b, v31.16b, v1.16b
	str q31, [x1, #16]
	ldr q31, [x27, #32]
	eor v31.16b, v31.16b, v2.16b
	str q31, [x1, #32]
	ldr q31, [x27, #48]
	eor v31.16b, v31.16b, v3.16b
	str q31, [x1, #48]
	ldr q31, [x27, #64]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #64]
	ldr q31, [x27, #80]
	eor v31.16b, v31.16b, v5.16b
	str q31, [x1, #80]
	ldr q31, [x27, #96]
	eor v31.16b, v31.16b, v6.16b
	str q31, [x1, #96]
	ldr q31, [x27, #112]
	eor v31.16b, v31.16b, v7.16b
	str q31, [x1, #112]
	ldr q31, [x27, #128]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #128]
	ldr q31, [x27, #144]
	eor v31.16b, v31.16b, v17.16b
	str q31, [x1, #144]
	ldr q31, [x27, #160]
	eor v31.16b, v31.16b, v18.16b
	str q31, [x1, #160]
	ldr q31, [x27, #176]
	eor v31.16b, v31.16b, v19.16b
	str q31, [x1, #176]
	ldr q31, [x27, #192]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #192]
	ldr q31, [x27, #208]
	eor v31.16b, v31.16b, v21.16b
	str q31, [x1, #208]
	ldr q31, [x27, #224]
	eor v31.16b, v31.16b, v22.16b
	str q31, [x1, #224]
	ldr q31, [x27, #240]
	eor v31.16b, v31.16b, v23.16b
	str q31, [x1, #240]
	ldr q31, [x27, #256]
	eor v31.16b, v31.16b, v24.16b
	str q31, [x1, #256]
	ldr q31, [x27, #272]
	eor v31.16b, v31.16b, v25.16b
	str q31, [x1, #272]
	ldr q31, [x27, #288]
	eor v31.16b, v31.16b, v26.16b
	str q31, [x1, #288]
	ldr q31, [x27, #304]
	eor v31.16b, v31.16b, v27.16b
	str q31, [x1, #304]
	ldr q31, [x27, #320]
	eor v31.16b, v31.16b, v28.16b
	str q31, [x1, #320]
	ldr q31, [x27, #336]
	eor v31.16b, v31.16b, v29.16b
	str q31, [x1, #336]
	ldr q31, [x27, #352]
	eor v31.16b, v31.16b, v8.16b
	str q31, [x1, #352]
	ldr q31, [x27, #368]
	eor v31.16b, v31.16b, v9.16b
	str q31, [x1, #368]
	ldr q30, [x3, #0]
	ldr q31, [x27, #384]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #384]
	ldr q30, [x3, #16]
	ldr q31, [x27, #400]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #400]
	ldr q30, [x3, #32]
	ldr q31, [x27, #416]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #416]
	ldr q30, [x3, #48]
	ldr q31, [x27, #432]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #432]
	ldr q30, [x3, #64]
	ldr q31, [x27, #448]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #448]
	ldr q30, [x3, #80]
	ldr q31, [x27, #464]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #464]
	ldr q30, [x3, #96]
	ldr q31, [x27, #480]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #480]
	ldr q30, [x3, #112]
	ldr q31, [x27, #496]
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
	add x27, x27, #512
	cbnz x5, 24f
26:
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
	sub x20, x26, #512
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	movz x1, #5, lsl #0
27:
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
	xar z3.s, z3.s, z0.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z7.s, z7.s, z4.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	xar z19.s, z19.s, z16.s, #16
	add w10, w10, w14
	xar z23.s, z23.s, z20.s, #16
	add w11, w11, w15
	xar z27.s, z27.s, z24.s, #16
	add w12, w12, w16
	xar z9.s, z9.s, z28.s, #16
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
	xar z1.s, z1.s, z2.s, #20
	add w4, w4, w8
	xar z5.s, z5.s, z6.s, #20
	add w5, w5, w9
	xar z17.s, z17.s, z18.s, #20
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z22.s, #20
	eor w15, w15, w3
	ror w15, w15, #24
	xar z25.s, z25.s, z26.s, #20
	eor w16, w16, w4
	ror w16, w16, #24
	xar z29.s, z29.s, z8.s, #20
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
	xar z3.s, z3.s, z0.s, #24
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z4.s, #24
	eor w9, w9, w13
	ror w9, w9, #25
	xar z19.s, z19.s, z16.s, #24
	add w2, w2, w7
	xar z23.s, z23.s, z20.s, #24
	add w3, w3, w8
	xar z27.s, z27.s, z24.s, #24
	add w4, w4, w9
	xar z9.s, z9.s, z28.s, #24
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
	xar z1.s, z1.s, z2.s, #25
	add w10, w10, w15
	xar z5.s, z5.s, z6.s, #25
	add w11, w11, w16
	xar z17.s, z17.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #20
	xar z21.s, z21.s, z22.s, #25
	eor w8, w8, w13
	ror w8, w8, #20
	xar z25.s, z25.s, z26.s, #25
	eor w9, w9, w10
	ror w9, w9, #20
	xar z29.s, z29.s, z8.s, #25
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
	xar z3.s, z3.s, z0.s, #16
	add w10, w10, w14
	xar z7.s, z7.s, z4.s, #16
	add w11, w11, w15
	xar z19.s, z19.s, z16.s, #16
	add w12, w12, w16
	xar z23.s, z23.s, z20.s, #16
	add w13, w13, w17
	xar z27.s, z27.s, z24.s, #16
	eor w6, w6, w10
	ror w6, w6, #20
	xar z9.s, z9.s, z28.s, #16
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
	xar z1.s, z1.s, z2.s, #20
	eor w14, w14, w2
	ror w14, w14, #24
	xar z5.s, z5.s, z6.s, #20
	eor w15, w15, w3
	ror w15, w15, #24
	xar z17.s, z17.s, z18.s, #20
	eor w16, w16, w4
	ror w16, w16, #24
	xar z21.s, z21.s, z22.s, #20
	eor w17, w17, w5
	ror w17, w17, #24
	xar z25.s, z25.s, z26.s, #20
	add w10, w10, w14
	xar z29.s, z29.s, z8.s, #20
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
	xar z3.s, z3.s, z0.s, #24
	add w2, w2, w7
	xar z7.s, z7.s, z4.s, #24
	add w3, w3, w8
	xar z19.s, z19.s, z16.s, #24
	add w4, w4, w9
	xar z23.s, z23.s, z20.s, #24
	add w5, w5, w6
	xar z27.s, z27.s, z24.s, #24
	eor w17, w17, w2
	ror w17, w17, #16
	xar z9.s, z9.s, z28.s, #24
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
	xar z1.s, z1.s, z2.s, #25
	eor w7, w7, w12
	ror w7, w7, #20
	xar z5.s, z5.s, z6.s, #25
	eor w8, w8, w13
	ror w8, w8, #20
	xar z17.s, z17.s, z18.s, #25
	eor w9, w9, w10
	ror w9, w9, #20
	xar z21.s, z21.s, z22.s, #25
	eor w6, w6, w11
	ror w6, w6, #20
	xar z25.s, z25.s, z26.s, #25
	add w2, w2, w7
	xar z29.s, z29.s, z8.s, #25
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
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	sub x1, x1, #1
	cbnz x1, 27b
	add x27, x26, #0
	add x20, x0, #64
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
	sub x20, x26, #256
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	movz x1, #5, lsl #0
28:
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
	xar z3.s, z3.s, z0.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z7.s, z7.s, z4.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	xar z19.s, z19.s, z16.s, #16
	add w10, w10, w14
	xar z23.s, z23.s, z20.s, #16
	add w11, w11, w15
	xar z27.s, z27.s, z24.s, #16
	add w12, w12, w16
	xar z9.s, z9.s, z28.s, #16
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
	xar z1.s, z1.s, z2.s, #20
	add w4, w4, w8
	xar z5.s, z5.s, z6.s, #20
	add w5, w5, w9
	xar z17.s, z17.s, z18.s, #20
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z22.s, #20
	eor w15, w15, w3
	ror w15, w15, #24
	xar z25.s, z25.s, z26.s, #20
	eor w16, w16, w4
	ror w16, w16, #24
	xar z29.s, z29.s, z8.s, #20
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
	xar z3.s, z3.s, z0.s, #24
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z4.s, #24
	eor w9, w9, w13
	ror w9, w9, #25
	xar z19.s, z19.s, z16.s, #24
	add w2, w2, w7
	xar z23.s, z23.s, z20.s, #24
	add w3, w3, w8
	xar z27.s, z27.s, z24.s, #24
	add w4, w4, w9
	xar z9.s, z9.s, z28.s, #24
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
	xar z1.s, z1.s, z2.s, #25
	add w10, w10, w15
	xar z5.s, z5.s, z6.s, #25
	add w11, w11, w16
	xar z17.s, z17.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #20
	xar z21.s, z21.s, z22.s, #25
	eor w8, w8, w13
	ror w8, w8, #20
	xar z25.s, z25.s, z26.s, #25
	eor w9, w9, w10
	ror w9, w9, #20
	xar z29.s, z29.s, z8.s, #25
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
	xar z3.s, z3.s, z0.s, #16
	add w10, w10, w14
	xar z7.s, z7.s, z4.s, #16
	add w11, w11, w15
	xar z19.s, z19.s, z16.s, #16
	add w12, w12, w16
	xar z23.s, z23.s, z20.s, #16
	add w13, w13, w17
	xar z27.s, z27.s, z24.s, #16
	eor w6, w6, w10
	ror w6, w6, #20
	xar z9.s, z9.s, z28.s, #16
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
	xar z1.s, z1.s, z2.s, #20
	eor w14, w14, w2
	ror w14, w14, #24
	xar z5.s, z5.s, z6.s, #20
	eor w15, w15, w3
	ror w15, w15, #24
	xar z17.s, z17.s, z18.s, #20
	eor w16, w16, w4
	ror w16, w16, #24
	xar z21.s, z21.s, z22.s, #20
	eor w17, w17, w5
	ror w17, w17, #24
	xar z25.s, z25.s, z26.s, #20
	add w10, w10, w14
	xar z29.s, z29.s, z8.s, #20
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
	xar z3.s, z3.s, z0.s, #24
	add w2, w2, w7
	xar z7.s, z7.s, z4.s, #24
	add w3, w3, w8
	xar z19.s, z19.s, z16.s, #24
	add w4, w4, w9
	xar z23.s, z23.s, z20.s, #24
	add w5, w5, w6
	xar z27.s, z27.s, z24.s, #24
	eor w17, w17, w2
	ror w17, w17, #16
	xar z9.s, z9.s, z28.s, #24
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
	xar z1.s, z1.s, z2.s, #25
	eor w7, w7, w12
	ror w7, w7, #20
	xar z5.s, z5.s, z6.s, #25
	eor w8, w8, w13
	ror w8, w8, #20
	xar z17.s, z17.s, z18.s, #25
	eor w9, w9, w10
	ror w9, w9, #20
	xar z21.s, z21.s, z22.s, #25
	eor w6, w6, w11
	ror w6, w6, #20
	xar z25.s, z25.s, z26.s, #25
	add w2, w2, w7
	xar z29.s, z29.s, z8.s, #25
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
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	sub x1, x1, #1
	cbnz x1, 28b
	add x27, x26, #0
	add x20, x0, #64
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
	ldr q31, [x27, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q31, [x27, #16]
	eor v31.16b, v31.16b, v1.16b
	str q31, [x1, #16]
	ldr q31, [x27, #32]
	eor v31.16b, v31.16b, v2.16b
	str q31, [x1, #32]
	ldr q31, [x27, #48]
	eor v31.16b, v31.16b, v3.16b
	str q31, [x1, #48]
	ldr q31, [x27, #64]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #64]
	ldr q31, [x27, #80]
	eor v31.16b, v31.16b, v5.16b
	str q31, [x1, #80]
	ldr q31, [x27, #96]
	eor v31.16b, v31.16b, v6.16b
	str q31, [x1, #96]
	ldr q31, [x27, #112]
	eor v31.16b, v31.16b, v7.16b
	str q31, [x1, #112]
	ldr q31, [x27, #128]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #128]
	ldr q31, [x27, #144]
	eor v31.16b, v31.16b, v17.16b
	str q31, [x1, #144]
	ldr q31, [x27, #160]
	eor v31.16b, v31.16b, v18.16b
	str q31, [x1, #160]
	ldr q31, [x27, #176]
	eor v31.16b, v31.16b, v19.16b
	str q31, [x1, #176]
	ldr q31, [x27, #192]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #192]
	ldr q31, [x27, #208]
	eor v31.16b, v31.16b, v21.16b
	str q31, [x1, #208]
	ldr q31, [x27, #224]
	eor v31.16b, v31.16b, v22.16b
	str q31, [x1, #224]
	ldr q31, [x27, #240]
	eor v31.16b, v31.16b, v23.16b
	str q31, [x1, #240]
	ldr q31, [x27, #256]
	eor v31.16b, v31.16b, v24.16b
	str q31, [x1, #256]
	ldr q31, [x27, #272]
	eor v31.16b, v31.16b, v25.16b
	str q31, [x1, #272]
	ldr q31, [x27, #288]
	eor v31.16b, v31.16b, v26.16b
	str q31, [x1, #288]
	ldr q31, [x27, #304]
	eor v31.16b, v31.16b, v27.16b
	str q31, [x1, #304]
	ldr q31, [x27, #320]
	eor v31.16b, v31.16b, v28.16b
	str q31, [x1, #320]
	ldr q31, [x27, #336]
	eor v31.16b, v31.16b, v29.16b
	str q31, [x1, #336]
	ldr q31, [x27, #352]
	eor v31.16b, v31.16b, v8.16b
	str q31, [x1, #352]
	ldr q31, [x27, #368]
	eor v31.16b, v31.16b, v9.16b
	str q31, [x1, #368]
	ldr q30, [x3, #0]
	ldr q31, [x27, #384]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #384]
	ldr q30, [x3, #16]
	ldr q31, [x27, #400]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #400]
	ldr q30, [x3, #32]
	ldr q31, [x27, #416]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #416]
	ldr q30, [x3, #48]
	ldr q31, [x27, #432]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #432]
	ldr q30, [x3, #64]
	ldr q31, [x27, #448]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #448]
	ldr q30, [x3, #80]
	ldr q31, [x27, #464]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #464]
	ldr q30, [x3, #96]
	ldr q31, [x27, #480]
	eor v31.16b, v31.16b, v30.16b
	str q31, [x1, #480]
	ldr q30, [x3, #112]
	ldr q31, [x27, #496]
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
	add x27, x27, #512
	cbz x5, 26b
	b 25f
24:
25:
	add x4, x1, #0
	add x1, x27, #0
	ldr q8, [x3, #128]
	ldr q9, [x3, #144]
	ldr x20, [x3, #256]
	ldr x19, [x3, #264]
	ldr x26, [x3, #272]
	ldr x27, [x3, #280]
	add x4, x21, #0
	add x5, x22, #0
	add x6, x23, #0
	movz x13, #5, lsl #0
	movz x14, #0, lsl #0
	adds x9, x4, x13
	adcs x10, x5, x14
	adc x11, x6, x14
	lsr x12, x11, #2
	movz x14, #0, lsl #0
	sub x12, x14, x12
	movz x14, #3, lsl #0
	and x11, x11, x14
	eor x13, x9, x4
	and x13, x13, x12
	eor x4, x4, x13
	eor x13, x10, x5
	and x13, x13, x12
	eor x5, x5, x13
	eor x13, x11, x6
	and x13, x13, x12
	eor x6, x6, x13
	sub x21, x0, #64
	str x4, [x21, #448]
	str x5, [x21, #456]
	str x6, [x21, #464]
	ldr x27, [x21, #32]
	ldr x28, [x21, #40]
	sub x22, x1, #512
	add x23, x2, #512
	cbz x2, 29f
	add x8, x20, #0
	add x20, x22, #0
	add x7, x1, #0
	str x27, [x21, #32]
	str x28, [x21, #40]
	movz x24, #65535, lsl #0
	movk x24, #4095, lsl #16
	movk x24, #65532, lsl #32
	movk x24, #4095, lsl #48
	ldr x25, [x21, #472]
	and x25, x25, x24
	str x25, [x21, #288]
	movz x24, #65532, lsl #0
	movk x24, #4095, lsl #16
	movk x24, #65532, lsl #32
	movk x24, #4095, lsl #48
	ldr x25, [x21, #480]
	and x25, x25, x24
	str x25, [x21, #296]
	ldr x22, [x21, #456]
	ldr x23, [x21, #464]
	ldr x21, [x21, #448]
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
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	movz x4, #10, lsl #0
211:
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	xar z20.s, z20.s, z0.s, #16
	xar z21.s, z21.s, z1.s, #16
	xar z22.s, z22.s, z2.s, #16
	xar z23.s, z23.s, z3.s, #16
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	xar z4.s, z4.s, z16.s, #20
	xar z5.s, z5.s, z17.s, #20
	xar z6.s, z6.s, z18.s, #20
	xar z7.s, z7.s, z19.s, #20
	add v0.4s, v0.4s, v4.4s
	add v1.4s, v1.4s, v5.4s
	add v2.4s, v2.4s, v6.4s
	add v3.4s, v3.4s, v7.4s
	xar z20.s, z20.s, z0.s, #24
	xar z21.s, z21.s, z1.s, #24
	xar z22.s, z22.s, z2.s, #24
	xar z23.s, z23.s, z3.s, #24
	add v16.4s, v16.4s, v20.4s
	add v17.4s, v17.4s, v21.4s
	add v18.4s, v18.4s, v22.4s
	add v19.4s, v19.4s, v23.4s
	xar z4.s, z4.s, z16.s, #25
	xar z5.s, z5.s, z17.s, #25
	xar z6.s, z6.s, z18.s, #25
	xar z7.s, z7.s, z19.s, #25
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	xar z23.s, z23.s, z0.s, #16
	xar z20.s, z20.s, z1.s, #16
	xar z21.s, z21.s, z2.s, #16
	xar z22.s, z22.s, z3.s, #16
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	xar z5.s, z5.s, z18.s, #20
	xar z6.s, z6.s, z19.s, #20
	xar z7.s, z7.s, z16.s, #20
	xar z4.s, z4.s, z17.s, #20
	add v0.4s, v0.4s, v5.4s
	add v1.4s, v1.4s, v6.4s
	add v2.4s, v2.4s, v7.4s
	add v3.4s, v3.4s, v4.4s
	xar z23.s, z23.s, z0.s, #24
	xar z20.s, z20.s, z1.s, #24
	xar z21.s, z21.s, z2.s, #24
	xar z22.s, z22.s, z3.s, #24
	add v18.4s, v18.4s, v23.4s
	add v19.4s, v19.4s, v20.4s
	add v16.4s, v16.4s, v21.4s
	add v17.4s, v17.4s, v22.4s
	xar z5.s, z5.s, z18.s, #25
	xar z6.s, z6.s, z19.s, #25
	xar z7.s, z7.s, z16.s, #25
	xar z4.s, z4.s, z17.s, #25
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	ldr x25, [x20, #0]
	ldr x27, [x20, #8]
	movz x28, #1, lsl #0
	adds x21, x21, x25
	adcs x22, x22, x27
	adc x23, x23, x28
	ldr x24, [x0, #224]
	mul x25, x21, x24
	umulh x27, x21, x24
	mul x28, x22, x24
	umulh x30, x22, x24
	adds x27, x27, x28
	mul x28, x23, x24
	adc x28, x28, x30
	ldr x24, [x0, #232]
	mul x30, x21, x24
	umulh x21, x21, x24
	adds x27, x27, x30
	mul x30, x22, x24
	umulh x22, x22, x24
	adcs x30, x30, x21
	mul x23, x23, x24
	adc x23, x23, x22
	adds x28, x28, x30
	movz x22, #0, lsl #0
	adc x30, x23, x22
	movz x21, #3, lsl #0
	and x23, x28, x21
	sub x21, x28, x23
	extr x28, x30, x28, #2
	adds x21, x21, x25
	lsr x25, x30, #2
	adc x22, x30, x25
	adds x21, x21, x28
	adcs x22, x22, x27
	movz x25, #0, lsl #0
	adc x23, x23, x25
	add x20, x20, #16
	sub x4, x4, #1
	cbnz x4, 211b
	eor v28.16b, v28.16b, v28.16b
	str q28, [x3, #0]
	str q28, [x3, #16]
	str q28, [x3, #32]
	str q28, [x3, #48]
	str q28, [x3, #64]
	str q28, [x3, #80]
	str q28, [x3, #96]
	str q28, [x3, #112]
	str q28, [x3, #128]
	str q28, [x3, #144]
	str q28, [x3, #160]
	str q28, [x3, #176]
	str q28, [x3, #192]
	str q28, [x3, #208]
	str q28, [x3, #224]
	str q28, [x3, #240]
	add x1, x3, #0
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
	add x4, x21, #0
	add x5, x22, #0
	add x6, x23, #0
	movz x13, #5, lsl #0
	movz x14, #0, lsl #0
	adds x9, x4, x13
	adcs x10, x5, x14
	adc x11, x6, x14
	lsr x12, x11, #2
	movz x14, #0, lsl #0
	sub x12, x14, x12
	movz x14, #3, lsl #0
	and x11, x11, x14
	eor x13, x9, x4
	and x13, x13, x12
	eor x4, x4, x13
	eor x13, x10, x5
	and x13, x13, x12
	eor x5, x5, x13
	eor x13, x11, x6
	and x13, x13, x12
	eor x6, x6, x13
	sub x21, x0, #64
	str x4, [x21, #448]
	str x5, [x21, #456]
	str x6, [x21, #464]
	ldr x27, [x21, #32]
	ldr x28, [x21, #40]
	add x22, x1, #0
	add x23, x2, #0
	add x22, x7, #0
	add x20, x8, #0
	ldr w4, [x0, #48]
	add w4, w4, #4
	str w4, [x0, #48]
	lsr x9, x2, #8
	cbz x9, 212f
	movz x23, #256, lsl #0
	b 213f
212:
	add x23, x2, #0
213:
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 214f
216:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 216b
	b 215f
214:
215:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 217f
219:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 219b
	b 218f
217:
218:
	add x1, x22, x23
	sub x2, x2, x23
	add x23, x2, x23
	add x0, x21, #64
	add x3, x21, #128
	b 210f
29:
210:
	b 21f
20:
21:
	umov x30, v15.d[1]
	ret
	.p2align 6
