// The functions of `src/internal/vg_chacha20_poly1305_seal_core_sve2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_poly1305_seal_core_sve2:
	sub sp, sp, #1280
	add x7, sp, #0
	sub x9, x5, #1
	sub x10, x5, #1
	orr x9, x9, x10
	orr x9, x9, x5
	lsr x9, x9, #9
	cbz x9, 20f
	movz x10, #0, lsl #0
	movz x10, #0, lsl #0
	movz x10, #0, lsl #0
	movz x10, #0, lsl #0
	sub x9, x5, #705
	lsr x9, x9, #63
	sub x10, x5, #513
	lsr x10, x10, #63
	sub x10, x10, x9
	add x10, x10, #1
	lsl x9, x5, #55
	lsr x9, x9, #55
	sub x9, x9, #257
	lsr x9, x9, #9
	cbz x9, 22f
	cbz x10, 24f
	str x22, [x7, #584]
	str x23, [x7, #592]
	str x24, [x7, #600]
	str x25, [x7, #608]
	str x30, [x7, #616]
	str x6, [x7, #624]
	str x21, [x7, #576]
	add x21, x7, #0
	add x24, x2, #0
	add x25, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	movz w9, #30821, lsl #0
	movk w9, #24944, lsl #16
	str w9, [x21, #64]
	movz w9, #25710, lsl #0
	movk w9, #13088, lsl #16
	str w9, [x21, #68]
	movz w9, #11570, lsl #0
	movk w9, #31074, lsl #16
	str w9, [x21, #72]
	movz w9, #25972, lsl #0
	movk w9, #27424, lsl #16
	str w9, [x21, #76]
	ldr w9, [x0, #0]
	str w9, [x21, #80]
	ldr w9, [x0, #4]
	str w9, [x21, #84]
	ldr w9, [x0, #8]
	str w9, [x21, #88]
	ldr w9, [x0, #12]
	str w9, [x21, #92]
	ldr w9, [x0, #16]
	str w9, [x21, #96]
	ldr w9, [x0, #20]
	str w9, [x21, #100]
	ldr w9, [x0, #24]
	str w9, [x21, #104]
	ldr w9, [x0, #28]
	str w9, [x21, #108]
	movz w9, #0, lsl #0
	str w9, [x21, #112]
	ldr w9, [x1, #0]
	str w9, [x21, #116]
	ldr w9, [x1, #4]
	str w9, [x21, #120]
	ldr w9, [x1, #8]
	str w9, [x21, #124]
	add x0, x21, #64
	add x1, x21, #128
	bl {vg_chacha20_block}
	add x0, x21, #448
	add x1, x21, #128
	bl {vg_poly1305_init}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 26f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
28:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 28b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 27f
26:
27:
	str x25, [x21, #0]
	str x23, [x21, #8]
	movz w9, #1, lsl #0
	str w9, [x21, #112]
	add x0, x21, #64
	add x1, x22, #0
	add x2, x23, #0
	add x3, x21, #128
	lsr x5, x2, #6
	sub x5, x5, #8
	lsr x5, x5, #63
	cbnz x5, 29f
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
211:
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
	cbnz x1, 211b
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
212:
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
	cbnz x1, 212b
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
	cbnz x5, 213f
215:
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
216:
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
	cbnz x1, 216b
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
217:
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
	cbnz x1, 217b
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
	cbz x5, 215b
	b 214f
213:
214:
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
	cbz x2, 218f
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
220:
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
	cbnz x4, 220b
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
	cbz x9, 221f
	movz x23, #256, lsl #0
	b 222f
221:
	add x23, x2, #0
222:
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 223f
225:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 225b
	b 224f
223:
224:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 226f
228:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 228b
	b 227f
226:
227:
	add x1, x22, x23
	sub x2, x2, x23
	add x23, x2, x23
	add x0, x21, #64
	add x3, x21, #128
	b 219f
218:
219:
	b 210f
29:
210:
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 229f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
231:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 231b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 230f
229:
230:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
25:
	b 23f
22:
	str x22, [x7, #584]
	str x23, [x7, #592]
	str x24, [x7, #600]
	str x25, [x7, #608]
	str x30, [x7, #616]
	str x6, [x7, #624]
	str x21, [x7, #576]
	add x21, x7, #0
	add x24, x2, #0
	add x25, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	movz w9, #30821, lsl #0
	movk w9, #24944, lsl #16
	str w9, [x21, #0]
	movz w9, #25710, lsl #0
	movk w9, #13088, lsl #16
	str w9, [x21, #4]
	movz w9, #11570, lsl #0
	movk w9, #31074, lsl #16
	str w9, [x21, #8]
	movz w9, #25972, lsl #0
	movk w9, #27424, lsl #16
	str w9, [x21, #12]
	ldr w9, [x0, #0]
	str w9, [x21, #16]
	ldr w9, [x0, #4]
	str w9, [x21, #20]
	ldr w9, [x0, #8]
	str w9, [x21, #24]
	ldr w9, [x0, #12]
	str w9, [x21, #28]
	ldr w9, [x0, #16]
	str w9, [x21, #32]
	ldr w9, [x0, #20]
	str w9, [x21, #36]
	ldr w9, [x0, #24]
	str w9, [x21, #40]
	ldr w9, [x0, #28]
	str w9, [x21, #44]
	movz w9, #0, lsl #0
	str w9, [x21, #48]
	ldr w9, [x1, #0]
	str w9, [x21, #52]
	ldr w9, [x1, #4]
	str w9, [x21, #56]
	ldr w9, [x1, #8]
	str w9, [x21, #60]
	eor v0.16b, v0.16b, v0.16b
	str q0, [x21, #64]
	str q0, [x21, #80]
	str q0, [x21, #96]
	str q0, [x21, #112]
	str q0, [x21, #128]
	str q0, [x21, #144]
	str q0, [x21, #160]
	str q0, [x21, #176]
	str q0, [x21, #192]
	str q0, [x21, #208]
	str q0, [x21, #224]
	str q0, [x21, #240]
	str q0, [x21, #256]
	str q0, [x21, #272]
	str q0, [x21, #288]
	str q0, [x21, #304]
	str q0, [x21, #320]
	str q0, [x21, #336]
	str q0, [x21, #352]
	str q0, [x21, #368]
	str x19, [x21, #632]
	str x20, [x21, #640]
	str x26, [x21, #648]
	add x0, x21, #0
	add x1, x21, #64
	add x3, x21, #384
	add x20, x3, #0
	add x19, x2, #0
	add x26, x1, #0
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
	ldr w4, [x0, #48]
	add w4, w4, #4
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
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
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
	add x1, x26, #0
	add x2, x19, #0
	add x3, x20, #0
	ldr w4, [x0, #48]
	sub w4, w4, #4
	str w4, [x0, #48]
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
	add x1, x1, #256
	ldr q0, [x3, #0]
	ldr q31, [x1, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q4, [x3, #16]
	ldr q31, [x1, #16]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #16]
	ldr q16, [x3, #32]
	ldr q31, [x1, #32]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #32]
	ldr q20, [x3, #48]
	ldr q31, [x1, #48]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #48]
	sub x1, x1, #256
	ldr x19, [x21, #632]
	ldr x20, [x21, #640]
	ldr x26, [x21, #648]
	add x0, x21, #448
	add x1, x21, #64
	bl {vg_poly1305_init}
	ldr w9, [x21, #0]
	str w9, [x21, #64]
	ldr w9, [x21, #4]
	str w9, [x21, #68]
	ldr w9, [x21, #8]
	str w9, [x21, #72]
	ldr w9, [x21, #12]
	str w9, [x21, #76]
	ldr w9, [x21, #16]
	str w9, [x21, #80]
	ldr w9, [x21, #20]
	str w9, [x21, #84]
	ldr w9, [x21, #24]
	str w9, [x21, #88]
	ldr w9, [x21, #28]
	str w9, [x21, #92]
	ldr w9, [x21, #32]
	str w9, [x21, #96]
	ldr w9, [x21, #36]
	str w9, [x21, #100]
	ldr w9, [x21, #40]
	str w9, [x21, #104]
	ldr w9, [x21, #44]
	str w9, [x21, #108]
	movz w9, #5, lsl #0
	str w9, [x21, #112]
	ldr w9, [x21, #52]
	str w9, [x21, #116]
	ldr w9, [x21, #56]
	str w9, [x21, #120]
	ldr w9, [x21, #60]
	str w9, [x21, #124]
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 257f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
259:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 259b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 258f
257:
258:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x14, x23, #0
	movz x23, #256, lsl #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 260f
262:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 262b
	b 261f
260:
261:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 263f
265:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 265b
	b 264f
263:
264:
	add x23, x14, #0
	add x0, x21, #448
	add x1, x22, #0
	movz x2, #16, lsl #0
	bl {vg_poly1305_blocks}
	add x22, x22, #256
	sub x23, x23, #256
	add x0, x21, #64
	add x1, x22, #0
	add x2, x23, #0
	add x3, x21, #128
	lsr x5, x2, #6
	sub x5, x5, #8
	lsr x5, x5, #63
	cbnz x5, 266f
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
268:
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
	cbnz x1, 268b
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
269:
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
	cbnz x1, 269b
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
	cbnz x5, 270f
272:
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
273:
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
	cbnz x1, 273b
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
274:
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
	cbnz x1, 274b
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
	cbz x5, 272b
	b 271f
270:
271:
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
	cbz x2, 275f
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
277:
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
	cbnz x4, 277b
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
	cbz x9, 278f
	movz x23, #256, lsl #0
	b 279f
278:
	add x23, x2, #0
279:
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 280f
282:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 282b
	b 281f
280:
281:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 283f
285:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 285b
	b 284f
283:
284:
	add x1, x22, x23
	sub x2, x2, x23
	add x23, x2, x23
	add x0, x21, #64
	add x3, x21, #128
	b 276f
275:
276:
	b 267f
266:
267:
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 286f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
288:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 288b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 287f
286:
287:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
23:
	b 21f
20:
	add x9, x5, #191
	lsr x9, x9, #9
	cbz x9, 289f
	str x22, [x7, #584]
	str x23, [x7, #592]
	str x24, [x7, #600]
	str x25, [x7, #608]
	str x30, [x7, #616]
	str x6, [x7, #624]
	str x21, [x7, #576]
	add x21, x7, #0
	add x24, x2, #0
	add x25, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	movz w9, #30821, lsl #0
	movk w9, #24944, lsl #16
	str w9, [x21, #64]
	movz w9, #25710, lsl #0
	movk w9, #13088, lsl #16
	str w9, [x21, #68]
	movz w9, #11570, lsl #0
	movk w9, #31074, lsl #16
	str w9, [x21, #72]
	movz w9, #25972, lsl #0
	movk w9, #27424, lsl #16
	str w9, [x21, #76]
	ldr w9, [x0, #0]
	str w9, [x21, #80]
	ldr w9, [x0, #4]
	str w9, [x21, #84]
	ldr w9, [x0, #8]
	str w9, [x21, #88]
	ldr w9, [x0, #12]
	str w9, [x21, #92]
	ldr w9, [x0, #16]
	str w9, [x21, #96]
	ldr w9, [x0, #20]
	str w9, [x21, #100]
	ldr w9, [x0, #24]
	str w9, [x21, #104]
	ldr w9, [x0, #28]
	str w9, [x21, #108]
	movz w9, #0, lsl #0
	str w9, [x21, #112]
	ldr w9, [x1, #0]
	str w9, [x21, #116]
	ldr w9, [x1, #4]
	str w9, [x21, #120]
	ldr w9, [x1, #8]
	str w9, [x21, #124]
	add x0, x21, #64
	add x1, x21, #128
	bl {vg_chacha20_block}
	add x0, x21, #448
	add x1, x21, #128
	bl {vg_poly1305_init}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 291f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
293:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 293b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 292f
291:
292:
	str x25, [x21, #0]
	str x23, [x21, #8]
	eor v0.16b, v0.16b, v0.16b
	str q0, [x21, #768]
	str q0, [x21, #784]
	str q0, [x21, #800]
	str q0, [x21, #816]
	str q0, [x21, #832]
	str q0, [x21, #848]
	str q0, [x21, #864]
	str q0, [x21, #880]
	str q0, [x21, #896]
	str q0, [x21, #912]
	str q0, [x21, #928]
	str q0, [x21, #944]
	str q0, [x21, #960]
	str q0, [x21, #976]
	str q0, [x21, #992]
	str q0, [x21, #1008]
	str q0, [x21, #1024]
	str q0, [x21, #1040]
	str q0, [x21, #1056]
	str q0, [x21, #1072]
	str q0, [x21, #1088]
	str q0, [x21, #1104]
	str q0, [x21, #1120]
	str q0, [x21, #1136]
	str q0, [x21, #1152]
	str q0, [x21, #1168]
	str q0, [x21, #1184]
	str q0, [x21, #1200]
	str q0, [x21, #1216]
	str q0, [x21, #1232]
	str q0, [x21, #1248]
	str q0, [x21, #1264]
	movz w9, #1, lsl #0
	str w9, [x21, #112]
	add x0, x21, #64
	add x1, x21, #768
	movz x2, #512, lsl #0
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #768
	lsr x11, x23, #4
	cbz x11, 294f
296:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 296b
	b 295f
294:
295:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 297f
299:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 299b
	b 298f
297:
298:
	eor v0.16b, v0.16b, v0.16b
	str q0, [x21, #768]
	str q0, [x21, #784]
	str q0, [x21, #800]
	str q0, [x21, #816]
	str q0, [x21, #832]
	str q0, [x21, #848]
	str q0, [x21, #864]
	str q0, [x21, #880]
	str q0, [x21, #896]
	str q0, [x21, #912]
	str q0, [x21, #928]
	str q0, [x21, #944]
	str q0, [x21, #960]
	str q0, [x21, #976]
	str q0, [x21, #992]
	str q0, [x21, #1008]
	str q0, [x21, #1024]
	str q0, [x21, #1040]
	str q0, [x21, #1056]
	str q0, [x21, #1072]
	str q0, [x21, #1088]
	str q0, [x21, #1104]
	str q0, [x21, #1120]
	str q0, [x21, #1136]
	str q0, [x21, #1152]
	str q0, [x21, #1168]
	str q0, [x21, #1184]
	str q0, [x21, #1200]
	str q0, [x21, #1216]
	str q0, [x21, #1232]
	str q0, [x21, #1248]
	str q0, [x21, #1264]
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 2100f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
2102:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 2102b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 2101f
2100:
2101:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 290f
289:
	str x22, [x7, #584]
	str x23, [x7, #592]
	str x24, [x7, #600]
	str x25, [x7, #608]
	str x30, [x7, #616]
	str x6, [x7, #624]
	str x21, [x7, #576]
	add x21, x7, #0
	add x24, x2, #0
	add x25, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	movz w9, #30821, lsl #0
	movk w9, #24944, lsl #16
	str w9, [x21, #0]
	movz w9, #25710, lsl #0
	movk w9, #13088, lsl #16
	str w9, [x21, #4]
	movz w9, #11570, lsl #0
	movk w9, #31074, lsl #16
	str w9, [x21, #8]
	movz w9, #25972, lsl #0
	movk w9, #27424, lsl #16
	str w9, [x21, #12]
	ldr w9, [x0, #0]
	str w9, [x21, #16]
	ldr w9, [x0, #4]
	str w9, [x21, #20]
	ldr w9, [x0, #8]
	str w9, [x21, #24]
	ldr w9, [x0, #12]
	str w9, [x21, #28]
	ldr w9, [x0, #16]
	str w9, [x21, #32]
	ldr w9, [x0, #20]
	str w9, [x21, #36]
	ldr w9, [x0, #24]
	str w9, [x21, #40]
	ldr w9, [x0, #28]
	str w9, [x21, #44]
	movz w9, #0, lsl #0
	str w9, [x21, #48]
	ldr w9, [x1, #0]
	str w9, [x21, #52]
	ldr w9, [x1, #4]
	str w9, [x21, #56]
	ldr w9, [x1, #8]
	str w9, [x21, #60]
	eor v0.16b, v0.16b, v0.16b
	str q0, [x21, #64]
	str q0, [x21, #80]
	str q0, [x21, #96]
	str q0, [x21, #112]
	str q0, [x21, #128]
	str q0, [x21, #144]
	str q0, [x21, #160]
	str q0, [x21, #176]
	str q0, [x21, #192]
	str q0, [x21, #208]
	str q0, [x21, #224]
	str q0, [x21, #240]
	str q0, [x21, #256]
	str q0, [x21, #272]
	str q0, [x21, #288]
	str q0, [x21, #304]
	str q0, [x21, #320]
	str q0, [x21, #336]
	str q0, [x21, #352]
	str q0, [x21, #368]
	str x19, [x21, #632]
	str x20, [x21, #640]
	str x26, [x21, #648]
	add x0, x21, #0
	add x1, x21, #64
	add x3, x21, #384
	add x20, x3, #0
	add x19, x2, #0
	add x26, x1, #0
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
	ldr w4, [x0, #48]
	add w4, w4, #4
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
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #16
	eor w14, w14, w2
	ror w14, w14, #16
	xar z21.s, z21.s, z1.s, #16
	eor w15, w15, w3
	ror w15, w15, #16
	xar z22.s, z22.s, z2.s, #16
	eor w16, w16, w4
	ror w16, w16, #16
	xar z23.s, z23.s, z3.s, #16
	eor w17, w17, w5
	ror w17, w17, #16
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #20
	eor w6, w6, w10
	ror w6, w6, #20
	xar z5.s, z5.s, z17.s, #20
	eor w7, w7, w11
	ror w7, w7, #20
	xar z6.s, z6.s, z18.s, #20
	eor w8, w8, w12
	ror w8, w8, #20
	xar z7.s, z7.s, z19.s, #20
	eor w9, w9, w13
	ror w9, w9, #20
	add v0.4s, v0.4s, v4.4s
	add w2, w2, w6
	add v1.4s, v1.4s, v5.4s
	add w3, w3, w7
	add v2.4s, v2.4s, v6.4s
	add w4, w4, w8
	add v3.4s, v3.4s, v7.4s
	add w5, w5, w9
	xar z20.s, z20.s, z0.s, #24
	eor w14, w14, w2
	ror w14, w14, #24
	xar z21.s, z21.s, z1.s, #24
	eor w15, w15, w3
	ror w15, w15, #24
	xar z22.s, z22.s, z2.s, #24
	eor w16, w16, w4
	ror w16, w16, #24
	xar z23.s, z23.s, z3.s, #24
	eor w17, w17, w5
	ror w17, w17, #24
	add v16.4s, v16.4s, v20.4s
	add w10, w10, w14
	add v17.4s, v17.4s, v21.4s
	add w11, w11, w15
	add v18.4s, v18.4s, v22.4s
	add w12, w12, w16
	add v19.4s, v19.4s, v23.4s
	add w13, w13, w17
	xar z4.s, z4.s, z16.s, #25
	eor w6, w6, w10
	ror w6, w6, #25
	xar z5.s, z5.s, z17.s, #25
	eor w7, w7, w11
	ror w7, w7, #25
	xar z6.s, z6.s, z18.s, #25
	eor w8, w8, w12
	ror w8, w8, #25
	xar z7.s, z7.s, z19.s, #25
	eor w9, w9, w13
	ror w9, w9, #25
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #16
	eor w17, w17, w2
	ror w17, w17, #16
	xar z20.s, z20.s, z1.s, #16
	eor w14, w14, w3
	ror w14, w14, #16
	xar z21.s, z21.s, z2.s, #16
	eor w15, w15, w4
	ror w15, w15, #16
	xar z22.s, z22.s, z3.s, #16
	eor w16, w16, w5
	ror w16, w16, #16
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #20
	eor w7, w7, w12
	ror w7, w7, #20
	xar z6.s, z6.s, z19.s, #20
	eor w8, w8, w13
	ror w8, w8, #20
	xar z7.s, z7.s, z16.s, #20
	eor w9, w9, w10
	ror w9, w9, #20
	xar z4.s, z4.s, z17.s, #20
	eor w6, w6, w11
	ror w6, w6, #20
	add v0.4s, v0.4s, v5.4s
	add w2, w2, w7
	add v1.4s, v1.4s, v6.4s
	add w3, w3, w8
	add v2.4s, v2.4s, v7.4s
	add w4, w4, w9
	add v3.4s, v3.4s, v4.4s
	add w5, w5, w6
	xar z23.s, z23.s, z0.s, #24
	eor w17, w17, w2
	ror w17, w17, #24
	xar z20.s, z20.s, z1.s, #24
	eor w14, w14, w3
	ror w14, w14, #24
	xar z21.s, z21.s, z2.s, #24
	eor w15, w15, w4
	ror w15, w15, #24
	xar z22.s, z22.s, z3.s, #24
	eor w16, w16, w5
	ror w16, w16, #24
	add v18.4s, v18.4s, v23.4s
	add w12, w12, w17
	add v19.4s, v19.4s, v20.4s
	add w13, w13, w14
	add v16.4s, v16.4s, v21.4s
	add w10, w10, w15
	add v17.4s, v17.4s, v22.4s
	add w11, w11, w16
	xar z5.s, z5.s, z18.s, #25
	eor w7, w7, w12
	ror w7, w7, #25
	xar z6.s, z6.s, z19.s, #25
	eor w8, w8, w13
	ror w8, w8, #25
	xar z7.s, z7.s, z16.s, #25
	eor w9, w9, w10
	ror w9, w9, #25
	xar z4.s, z4.s, z17.s, #25
	eor w6, w6, w11
	ror w6, w6, #25
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
	add x1, x26, #0
	add x2, x19, #0
	add x3, x20, #0
	ldr w4, [x0, #48]
	sub w4, w4, #4
	str w4, [x0, #48]
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
	add x1, x1, #256
	ldr q0, [x3, #0]
	ldr q31, [x1, #0]
	eor v31.16b, v31.16b, v0.16b
	str q31, [x1, #0]
	ldr q4, [x3, #16]
	ldr q31, [x1, #16]
	eor v31.16b, v31.16b, v4.16b
	str q31, [x1, #16]
	ldr q16, [x3, #32]
	ldr q31, [x1, #32]
	eor v31.16b, v31.16b, v16.16b
	str q31, [x1, #32]
	ldr q20, [x3, #48]
	ldr q31, [x1, #48]
	eor v31.16b, v31.16b, v20.16b
	str q31, [x1, #48]
	sub x1, x1, #256
	ldr x19, [x21, #632]
	ldr x20, [x21, #640]
	ldr x26, [x21, #648]
	add x0, x21, #448
	add x1, x21, #64
	bl {vg_poly1305_init}
	sub x9, x23, #1
	lsr x9, x9, #8
	cbz x9, 2103f
	ldr w9, [x21, #0]
	str w9, [x21, #64]
	ldr w9, [x21, #4]
	str w9, [x21, #68]
	ldr w9, [x21, #8]
	str w9, [x21, #72]
	ldr w9, [x21, #12]
	str w9, [x21, #76]
	ldr w9, [x21, #16]
	str w9, [x21, #80]
	ldr w9, [x21, #20]
	str w9, [x21, #84]
	ldr w9, [x21, #24]
	str w9, [x21, #88]
	ldr w9, [x21, #28]
	str w9, [x21, #92]
	ldr w9, [x21, #32]
	str w9, [x21, #96]
	ldr w9, [x21, #36]
	str w9, [x21, #100]
	ldr w9, [x21, #40]
	str w9, [x21, #104]
	ldr w9, [x21, #44]
	str w9, [x21, #108]
	movz w9, #5, lsl #0
	str w9, [x21, #112]
	ldr w9, [x21, #52]
	str w9, [x21, #116]
	ldr w9, [x21, #56]
	str w9, [x21, #120]
	ldr w9, [x21, #60]
	str w9, [x21, #124]
	add x14, x23, #0
	movz x23, #256, lsl #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 2105f
2107:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 2107b
	b 2106f
2105:
2106:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 2108f
2110:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 2110b
	b 2109f
2108:
2109:
	add x23, x14, #0
	add x0, x21, #64
	add x1, x22, #256
	sub x2, x23, #256
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 2111f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
2113:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 2113b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 2112f
2111:
2112:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 2114f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
2116:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 2116b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 2115f
2114:
2115:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 2104f
2103:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 2117f
2119:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 2119b
	b 2118f
2117:
2118:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 2120f
2122:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 2122b
	b 2121f
2120:
2121:
	add x0, x21, #448
	movz x16, #65535, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x7, [x0, #24]
	and x7, x7, x16
	movz x16, #65532, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x8, [x0, #32]
	and x8, x8, x16
	lsr x17, x8, #2
	add x17, x17, x8
	ldr x4, [x0, #0]
	ldr x5, [x0, #8]
	ldr x6, [x0, #16]
	add x1, x24, #0
	lsr x2, x25, #4
	cbz x2, 2123f
2125:
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 2125b
	b 2124f
2123:
2124:
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 2126f
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
2128:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 2128b
	add x1, x21, #16
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	b 2127f
2126:
2127:
	add x1, x22, #0
	lsr x2, x23, #4
	cbz x2, 2129f
2131:
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 2131b
	b 2130f
2129:
2130:
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 2132f
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
2134:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 2134b
	add x1, x21, #16
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	b 2133f
2132:
2133:
	add x1, x21, #0
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
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
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
2104:
290:
21:
	ldr x2, [x21, #624]
	add x0, x21, #448
	movz x1, #0, lsl #0
	add x3, x21, #632
	bl {vg_poly1305_finalize_scratch}
	ldr x22, [x21, #584]
	ldr x23, [x21, #592]
	ldr x24, [x21, #600]
	ldr x25, [x21, #608]
	ldr x30, [x21, #616]
	ldr x6, [x21, #624]
	ldr x21, [x21, #576]
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
	add x16, sp, #512
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
	add sp, sp, #1280
	ret
24:
	str x22, [x7, #584]
	str x23, [x7, #592]
	str x24, [x7, #600]
	str x25, [x7, #608]
	str x30, [x7, #616]
	str x6, [x7, #624]
	str x21, [x7, #576]
	add x21, x7, #0
	add x24, x2, #0
	add x25, x3, #0
	add x22, x4, #0
	add x23, x5, #0
	movz w9, #30821, lsl #0
	movk w9, #24944, lsl #16
	str w9, [x21, #64]
	movz w9, #25710, lsl #0
	movk w9, #13088, lsl #16
	str w9, [x21, #68]
	movz w9, #11570, lsl #0
	movk w9, #31074, lsl #16
	str w9, [x21, #72]
	movz w9, #25972, lsl #0
	movk w9, #27424, lsl #16
	str w9, [x21, #76]
	ldr w9, [x0, #0]
	str w9, [x21, #80]
	ldr w9, [x0, #4]
	str w9, [x21, #84]
	ldr w9, [x0, #8]
	str w9, [x21, #88]
	ldr w9, [x0, #12]
	str w9, [x21, #92]
	ldr w9, [x0, #16]
	str w9, [x21, #96]
	ldr w9, [x0, #20]
	str w9, [x21, #100]
	ldr w9, [x0, #24]
	str w9, [x21, #104]
	ldr w9, [x0, #28]
	str w9, [x21, #108]
	movz w9, #0, lsl #0
	str w9, [x21, #112]
	ldr w9, [x1, #0]
	str w9, [x21, #116]
	ldr w9, [x1, #4]
	str w9, [x21, #120]
	ldr w9, [x1, #8]
	str w9, [x21, #124]
	add x0, x21, #64
	add x1, x21, #128
	ldr w9, [x21, #64]
	str w9, [x21, #640]
	ldr w9, [x21, #68]
	str w9, [x21, #644]
	ldr w9, [x21, #72]
	str w9, [x21, #648]
	ldr w9, [x21, #76]
	str w9, [x21, #652]
	ldr w9, [x21, #80]
	str w9, [x21, #656]
	ldr w9, [x21, #84]
	str w9, [x21, #660]
	ldr w9, [x21, #88]
	str w9, [x21, #664]
	ldr w9, [x21, #92]
	str w9, [x21, #668]
	ldr w9, [x21, #96]
	str w9, [x21, #672]
	ldr w9, [x21, #100]
	str w9, [x21, #676]
	ldr w9, [x21, #104]
	str w9, [x21, #680]
	ldr w9, [x21, #108]
	str w9, [x21, #684]
	ldr w9, [x21, #112]
	str w9, [x21, #688]
	ldr w9, [x21, #116]
	str w9, [x21, #692]
	ldr w9, [x21, #120]
	str w9, [x21, #696]
	ldr w9, [x21, #124]
	str w9, [x21, #700]
	eor v0.16b, v0.16b, v0.16b
	str q0, [x21, #768]
	str q0, [x21, #784]
	str q0, [x21, #800]
	str q0, [x21, #816]
	str q0, [x21, #832]
	str q0, [x21, #848]
	str q0, [x21, #864]
	str q0, [x21, #880]
	str q0, [x21, #896]
	str q0, [x21, #912]
	str q0, [x21, #928]
	str q0, [x21, #944]
	str q0, [x21, #960]
	str q0, [x21, #976]
	str q0, [x21, #992]
	str q0, [x21, #1008]
	str q0, [x21, #1024]
	str q0, [x21, #1040]
	str q0, [x21, #1056]
	str q0, [x21, #1072]
	str q0, [x21, #1088]
	str q0, [x21, #1104]
	str q0, [x21, #1120]
	str q0, [x21, #1136]
	str q0, [x21, #1152]
	str q0, [x21, #1168]
	str q0, [x21, #1184]
	str q0, [x21, #1200]
	str q0, [x21, #1216]
	str q0, [x21, #1232]
	str q0, [x21, #1248]
	str q0, [x21, #1264]
	add x0, x21, #640
	add x1, x21, #768
	movz x2, #512, lsl #0
	add x3, x21, #128
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	add x0, x21, #448
	add x1, x21, #768
	bl {vg_poly1305_init}
	add x0, x21, #448
	add x1, x24, #0
	lsr x2, x25, #4
	bl {vg_poly1305_blocks}
	lsl x10, x25, #60
	lsr x10, x10, #60
	cbz x10, 232f
	sub x9, x25, x10
	add x1, x24, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
234:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 234b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 233f
232:
233:
	str x25, [x21, #0]
	str x23, [x21, #8]
	add x14, x23, #0
	movz x23, #448, lsl #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #832
	lsr x11, x23, #4
	cbz x11, 235f
237:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 237b
	b 236f
235:
236:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 238f
240:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 240b
	b 239f
238:
239:
	add x23, x14, #0
	movz w9, #8, lsl #0
	str w9, [x21, #112]
	add x0, x21, #64
	add x3, x21, #128
	add x2, x23, #0
	movz x23, #448, lsl #0
	add x8, x20, #0
	add x20, x22, #0
	add x7, x22, #0
	lsr x6, x23, #4
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
	movz x4, #10, lsl #0
241:
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
	cbz x6, 242f
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
	sub x6, x6, #1
	b 243f
242:
243:
	cbz x6, 244f
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
	sub x6, x6, #1
	b 245f
244:
245:
	cbz x6, 246f
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
	sub x6, x6, #1
	b 247f
246:
247:
	sub x4, x4, #1
	cbnz x4, 241b
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
	add x22, x20, #0
	add x23, x7, x2
	sub x23, x23, x20
	add x20, x8, #0
	add x24, x7, #0
	add x25, x2, #0
	add x9, x22, #0
	add x15, x9, #0
	add x10, x21, #128
	lsr x11, x23, #4
	cbz x11, 248f
250:
	ldr q0, [x9, #0]
	ldr q1, [x10, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x15, #0]
	add x9, x9, #16
	add x10, x10, #16
	add x15, x15, #16
	sub x11, x11, #1
	cbnz x11, 250b
	b 249f
248:
249:
	lsl x11, x23, #60
	lsr x11, x11, #60
	cbz x11, 251f
253:
	ldrb w12, [x9, #0]
	ldrb w13, [x10, #0]
	eor w12, w12, w13
	strb w12, [x15, #0]
	add x9, x9, #1
	add x10, x10, #1
	add x15, x15, #1
	sub x11, x11, #1
	cbnz x11, 253b
	b 252f
251:
252:
	add x0, x21, #448
	add x1, x22, #0
	lsr x2, x23, #4
	bl {vg_poly1305_blocks}
	lsl x10, x23, #60
	lsr x10, x10, #60
	cbz x10, 254f
	sub x9, x23, x10
	add x1, x22, x9
	movz x11, #0, lsl #0
	str x11, [x21, #16]
	str x11, [x21, #24]
	add x9, x21, #16
256:
	ldrb w11, [x1, #0]
	strb w11, [x9, #0]
	add x1, x1, #1
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 256b
	add x0, x21, #448
	add x1, x21, #16
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	b 255f
254:
255:
	add x0, x21, #448
	add x1, x21, #0
	movz x2, #1, lsl #0
	bl {vg_poly1305_blocks}
	eor v0.16b, v0.16b, v0.16b
	str q0, [x21, #768]
	str q0, [x21, #784]
	str q0, [x21, #800]
	str q0, [x21, #816]
	str q0, [x21, #832]
	str q0, [x21, #848]
	str q0, [x21, #864]
	str q0, [x21, #880]
	str q0, [x21, #896]
	str q0, [x21, #912]
	str q0, [x21, #928]
	str q0, [x21, #944]
	str q0, [x21, #960]
	str q0, [x21, #976]
	str q0, [x21, #992]
	str q0, [x21, #1008]
	str q0, [x21, #1024]
	str q0, [x21, #1040]
	str q0, [x21, #1056]
	str q0, [x21, #1072]
	str q0, [x21, #1088]
	str q0, [x21, #1104]
	str q0, [x21, #1120]
	str q0, [x21, #1136]
	str q0, [x21, #1152]
	str q0, [x21, #1168]
	str q0, [x21, #1184]
	str q0, [x21, #1200]
	str q0, [x21, #1216]
	str q0, [x21, #1232]
	str q0, [x21, #1248]
	str q0, [x21, #1264]
	b 25b
	.p2align 6
