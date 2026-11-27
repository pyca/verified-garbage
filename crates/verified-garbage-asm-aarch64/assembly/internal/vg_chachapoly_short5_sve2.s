// The functions of `src/internal/vg_chachapoly_short5_sve2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chachapoly_short5_sve2:
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
	ret
	.p2align 6
