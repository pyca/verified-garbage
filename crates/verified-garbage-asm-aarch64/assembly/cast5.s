// The functions of `src/cast5.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_expand_key:
	movz x9, #0, lsl #0
	str x9, [x3, #16]
	str x9, [x3, #24]
	add x4, x3, #16
20:
	ldrb w9, [x0, #0]
	strb w9, [x4, #0]
	add x0, x0, #1
	add x4, x4, #1
	sub x1, x1, #1
	cbnz x1, 20b
	movz x1, #2, lsl #0
21:
	ldrb w9, [x3, #26]
	mov v0.s[0], w9
	ldrb w9, [x3, #24]
	mov v0.s[1], w9
	ldrb w9, [x3, #27]
	mov v0.s[2], w9
	ldrb w9, [x3, #25]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
22:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 22b
	mov v6.16b, v1.16b
	ldrb w9, [x3, #30]
	mov v0.s[0], w9
	ldrb w9, [x3, #28]
	mov v0.s[1], w9
	ldrb w9, [x3, #31]
	mov v0.s[2], w9
	ldrb w9, [x3, #29]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
23:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 23b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[1]
	eor w0, w0, w9
	ldr w9, [x3, #16]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #32]
	ldrb w9, [x3, #35]
	mov v0.s[0], w9
	ldrb w9, [x3, #33]
	mov v0.s[1], w9
	ldrb w9, [x3, #34]
	mov v0.s[2], w9
	ldrb w9, [x3, #32]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
24:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 24b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[0]
	eor w0, w0, w9
	ldr w9, [x3, #24]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #36]
	ldrb w9, [x3, #36]
	mov v0.s[0], w9
	ldrb w9, [x3, #37]
	mov v0.s[1], w9
	ldrb w9, [x3, #38]
	mov v0.s[2], w9
	ldrb w9, [x3, #39]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
25:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 25b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[3]
	eor w0, w0, w9
	ldr w9, [x3, #28]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #40]
	ldrb w9, [x3, #40]
	mov v0.s[0], w9
	ldrb w9, [x3, #43]
	mov v0.s[1], w9
	ldrb w9, [x3, #41]
	mov v0.s[2], w9
	ldrb w9, [x3, #42]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
26:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 26b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[2]
	eor w0, w0, w9
	ldr w9, [x3, #20]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #44]
	ldrb w9, [x3, #44]
	mov v0.s[0], w9
	ldrb w9, [x3, #41]
	mov v0.s[1], w9
	ldrb w9, [x3, #38]
	mov v0.s[2], w9
	ldrb w9, [x3, #34]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
27:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 27b
	mov v6.16b, v1.16b
	ldrb w9, [x3, #38]
	mov v0.s[0], w9
	ldrb w9, [x3, #39]
	mov v0.s[1], w9
	ldrb w9, [x3, #41]
	mov v0.s[2], w9
	ldrb w9, [x3, #40]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
28:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 28b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[3]
	eor w0, w0, w9
	str w0, [x2, #0]
	ldrb w9, [x3, #36]
	mov v0.s[0], w9
	ldrb w9, [x3, #37]
	mov v0.s[1], w9
	ldrb w9, [x3, #43]
	mov v0.s[2], w9
	ldrb w9, [x3, #42]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
29:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 29b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[2]
	eor w0, w0, w9
	str w0, [x2, #4]
	ldrb w9, [x3, #34]
	mov v0.s[0], w9
	ldrb w9, [x3, #35]
	mov v0.s[1], w9
	ldrb w9, [x3, #45]
	mov v0.s[2], w9
	ldrb w9, [x3, #44]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
210:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 210b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[1]
	eor w0, w0, w9
	str w0, [x2, #8]
	ldrb w9, [x3, #32]
	mov v0.s[0], w9
	ldrb w9, [x3, #33]
	mov v0.s[1], w9
	ldrb w9, [x3, #47]
	mov v0.s[2], w9
	ldrb w9, [x3, #46]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
211:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 211b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[0]
	eor w0, w0, w9
	str w0, [x2, #12]
	ldrb w9, [x3, #34]
	mov v0.s[0], w9
	ldrb w9, [x3, #32]
	mov v0.s[1], w9
	ldrb w9, [x3, #35]
	mov v0.s[2], w9
	ldrb w9, [x3, #33]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
212:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 212b
	mov v6.16b, v1.16b
	ldrb w9, [x3, #38]
	mov v0.s[0], w9
	ldrb w9, [x3, #36]
	mov v0.s[1], w9
	ldrb w9, [x3, #39]
	mov v0.s[2], w9
	ldrb w9, [x3, #37]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
213:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 213b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[1]
	eor w0, w0, w9
	ldr w9, [x3, #40]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #16]
	ldrb w9, [x3, #19]
	mov v0.s[0], w9
	ldrb w9, [x3, #17]
	mov v0.s[1], w9
	ldrb w9, [x3, #18]
	mov v0.s[2], w9
	ldrb w9, [x3, #16]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
214:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 214b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[0]
	eor w0, w0, w9
	ldr w9, [x3, #32]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #20]
	ldrb w9, [x3, #20]
	mov v0.s[0], w9
	ldrb w9, [x3, #21]
	mov v0.s[1], w9
	ldrb w9, [x3, #22]
	mov v0.s[2], w9
	ldrb w9, [x3, #23]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
215:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 215b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[3]
	eor w0, w0, w9
	ldr w9, [x3, #36]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #24]
	ldrb w9, [x3, #24]
	mov v0.s[0], w9
	ldrb w9, [x3, #27]
	mov v0.s[1], w9
	ldrb w9, [x3, #25]
	mov v0.s[2], w9
	ldrb w9, [x3, #26]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
216:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 216b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[2]
	eor w0, w0, w9
	ldr w9, [x3, #44]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #28]
	ldrb w9, [x3, #23]
	mov v0.s[0], w9
	ldrb w9, [x3, #19]
	mov v0.s[1], w9
	ldrb w9, [x3, #29]
	mov v0.s[2], w9
	ldrb w9, [x3, #24]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
217:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 217b
	mov v6.16b, v1.16b
	ldrb w9, [x3, #29]
	mov v0.s[0], w9
	ldrb w9, [x3, #28]
	mov v0.s[1], w9
	ldrb w9, [x3, #18]
	mov v0.s[2], w9
	ldrb w9, [x3, #19]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
218:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 218b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[3]
	eor w0, w0, w9
	str w0, [x2, #16]
	ldrb w9, [x3, #31]
	mov v0.s[0], w9
	ldrb w9, [x3, #30]
	mov v0.s[1], w9
	ldrb w9, [x3, #16]
	mov v0.s[2], w9
	ldrb w9, [x3, #17]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
219:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 219b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[2]
	eor w0, w0, w9
	str w0, [x2, #20]
	ldrb w9, [x3, #25]
	mov v0.s[0], w9
	ldrb w9, [x3, #24]
	mov v0.s[1], w9
	ldrb w9, [x3, #22]
	mov v0.s[2], w9
	ldrb w9, [x3, #23]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
220:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 220b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[1]
	eor w0, w0, w9
	str w0, [x2, #24]
	ldrb w9, [x3, #27]
	mov v0.s[0], w9
	ldrb w9, [x3, #26]
	mov v0.s[1], w9
	ldrb w9, [x3, #20]
	mov v0.s[2], w9
	ldrb w9, [x3, #21]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
221:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 221b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[0]
	eor w0, w0, w9
	str w0, [x2, #28]
	ldrb w9, [x3, #26]
	mov v0.s[0], w9
	ldrb w9, [x3, #24]
	mov v0.s[1], w9
	ldrb w9, [x3, #27]
	mov v0.s[2], w9
	ldrb w9, [x3, #25]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
222:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 222b
	mov v6.16b, v1.16b
	ldrb w9, [x3, #30]
	mov v0.s[0], w9
	ldrb w9, [x3, #28]
	mov v0.s[1], w9
	ldrb w9, [x3, #31]
	mov v0.s[2], w9
	ldrb w9, [x3, #29]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
223:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 223b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[1]
	eor w0, w0, w9
	ldr w9, [x3, #16]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #32]
	ldrb w9, [x3, #35]
	mov v0.s[0], w9
	ldrb w9, [x3, #33]
	mov v0.s[1], w9
	ldrb w9, [x3, #34]
	mov v0.s[2], w9
	ldrb w9, [x3, #32]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
224:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 224b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[0]
	eor w0, w0, w9
	ldr w9, [x3, #24]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #36]
	ldrb w9, [x3, #36]
	mov v0.s[0], w9
	ldrb w9, [x3, #37]
	mov v0.s[1], w9
	ldrb w9, [x3, #38]
	mov v0.s[2], w9
	ldrb w9, [x3, #39]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
225:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 225b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[3]
	eor w0, w0, w9
	ldr w9, [x3, #28]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #40]
	ldrb w9, [x3, #40]
	mov v0.s[0], w9
	ldrb w9, [x3, #43]
	mov v0.s[1], w9
	ldrb w9, [x3, #41]
	mov v0.s[2], w9
	ldrb w9, [x3, #42]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
226:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 226b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[2]
	eor w0, w0, w9
	ldr w9, [x3, #20]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #44]
	ldrb w9, [x3, #38]
	mov v0.s[0], w9
	ldrb w9, [x3, #34]
	mov v0.s[1], w9
	ldrb w9, [x3, #44]
	mov v0.s[2], w9
	ldrb w9, [x3, #41]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
227:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 227b
	mov v6.16b, v1.16b
	ldrb w9, [x3, #45]
	mov v0.s[0], w9
	ldrb w9, [x3, #44]
	mov v0.s[1], w9
	ldrb w9, [x3, #34]
	mov v0.s[2], w9
	ldrb w9, [x3, #35]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
228:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 228b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[3]
	eor w0, w0, w9
	str w0, [x2, #32]
	ldrb w9, [x3, #47]
	mov v0.s[0], w9
	ldrb w9, [x3, #46]
	mov v0.s[1], w9
	ldrb w9, [x3, #32]
	mov v0.s[2], w9
	ldrb w9, [x3, #33]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
229:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 229b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[2]
	eor w0, w0, w9
	str w0, [x2, #36]
	ldrb w9, [x3, #41]
	mov v0.s[0], w9
	ldrb w9, [x3, #40]
	mov v0.s[1], w9
	ldrb w9, [x3, #38]
	mov v0.s[2], w9
	ldrb w9, [x3, #39]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
230:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 230b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[1]
	eor w0, w0, w9
	str w0, [x2, #40]
	ldrb w9, [x3, #43]
	mov v0.s[0], w9
	ldrb w9, [x3, #42]
	mov v0.s[1], w9
	ldrb w9, [x3, #36]
	mov v0.s[2], w9
	ldrb w9, [x3, #37]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
231:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 231b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[0]
	eor w0, w0, w9
	str w0, [x2, #44]
	ldrb w9, [x3, #34]
	mov v0.s[0], w9
	ldrb w9, [x3, #32]
	mov v0.s[1], w9
	ldrb w9, [x3, #35]
	mov v0.s[2], w9
	ldrb w9, [x3, #33]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
232:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 232b
	mov v6.16b, v1.16b
	ldrb w9, [x3, #38]
	mov v0.s[0], w9
	ldrb w9, [x3, #36]
	mov v0.s[1], w9
	ldrb w9, [x3, #39]
	mov v0.s[2], w9
	ldrb w9, [x3, #37]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
233:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 233b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[1]
	eor w0, w0, w9
	ldr w9, [x3, #40]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #16]
	ldrb w9, [x3, #19]
	mov v0.s[0], w9
	ldrb w9, [x3, #17]
	mov v0.s[1], w9
	ldrb w9, [x3, #18]
	mov v0.s[2], w9
	ldrb w9, [x3, #16]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
234:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 234b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[0]
	eor w0, w0, w9
	ldr w9, [x3, #32]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #20]
	ldrb w9, [x3, #20]
	mov v0.s[0], w9
	ldrb w9, [x3, #21]
	mov v0.s[1], w9
	ldrb w9, [x3, #22]
	mov v0.s[2], w9
	ldrb w9, [x3, #23]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
235:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 235b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[3]
	eor w0, w0, w9
	ldr w9, [x3, #36]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #24]
	ldrb w9, [x3, #24]
	mov v0.s[0], w9
	ldrb w9, [x3, #27]
	mov v0.s[1], w9
	ldrb w9, [x3, #25]
	mov v0.s[2], w9
	ldrb w9, [x3, #26]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
236:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 236b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[2]
	eor w0, w0, w9
	ldr w9, [x3, #44]
	rev w9, w9
	eor w0, w0, w9
	rev w9, w0
	str w9, [x3, #28]
	ldrb w9, [x3, #29]
	mov v0.s[0], w9
	ldrb w9, [x3, #24]
	mov v0.s[1], w9
	ldrb w9, [x3, #23]
	mov v0.s[2], w9
	ldrb w9, [x3, #19]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
237:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 237b
	mov v6.16b, v1.16b
	ldrb w9, [x3, #22]
	mov v0.s[0], w9
	ldrb w9, [x3, #23]
	mov v0.s[1], w9
	ldrb w9, [x3, #25]
	mov v0.s[2], w9
	ldrb w9, [x3, #24]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
238:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 238b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[3]
	eor w0, w0, w9
	str w0, [x2, #48]
	ldrb w9, [x3, #20]
	mov v0.s[0], w9
	ldrb w9, [x3, #21]
	mov v0.s[1], w9
	ldrb w9, [x3, #27]
	mov v0.s[2], w9
	ldrb w9, [x3, #26]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
239:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 239b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[2]
	eor w0, w0, w9
	str w0, [x2, #52]
	ldrb w9, [x3, #18]
	mov v0.s[0], w9
	ldrb w9, [x3, #19]
	mov v0.s[1], w9
	ldrb w9, [x3, #29]
	mov v0.s[2], w9
	ldrb w9, [x3, #28]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
240:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 240b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[1]
	eor w0, w0, w9
	str w0, [x2, #56]
	ldrb w9, [x3, #16]
	mov v0.s[0], w9
	ldrb w9, [x3, #17]
	mov v0.s[1], w9
	ldrb w9, [x3, #31]
	mov v0.s[2], w9
	ldrb w9, [x3, #30]
	mov v0.s[3], w9
	adrp x10, {VG_CAST5_S5678}
	add x10, x10, {VG_CAST5_S5678}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
241:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 241b
	umov w0, v1.s[0]
	umov w9, v1.s[1]
	eor w0, w0, w9
	umov w9, v1.s[2]
	eor w0, w0, w9
	umov w9, v1.s[3]
	eor w0, w0, w9
	umov w9, v6.s[0]
	eor w0, w0, w9
	str w0, [x2, #60]
	add x2, x2, #64
	sub x1, x1, #1
	cbnz x1, 21b
	ret
	.p2align 6

vg_cast5_ecb_encrypt:
	cbz x3, 20f
22:
	ldr w5, [x2, #0]
	rev w5, w5
	ldr w6, [x2, #4]
	rev w6, w6
	add x12, x0, #0
	lsr x7, x1, #2
	add x7, x7, #1
	sub x8, x1, #16
23:
	ldr w9, [x12, #0]
	add w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
24:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 24b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	eor w4, w9, w14
	sub w4, w4, w15
	add w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
	ldr w9, [x12, #0]
	eor w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
25:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 25b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	sub w4, w9, w14
	add w4, w4, w15
	eor w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
	ldr w9, [x12, #0]
	sub w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
26:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 26b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	add w4, w9, w14
	eor w4, w4, w15
	sub w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
	sub x7, x7, #1
	cbnz x7, 23b
	cbz x8, 27f
	b 28f
27:
	ldr w9, [x12, #0]
	add w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
29:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 29b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	eor w4, w9, w14
	sub w4, w4, w15
	add w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
28:
	rev w6, w6
	str w6, [x2, #0]
	rev w5, w5
	str w5, [x2, #4]
	add x2, x2, #8
	sub x3, x3, #1
	cbnz x3, 22b
	b 21f
20:
21:
	ret
	.p2align 6

vg_cast5_ecb_decrypt:
	cbz x3, 20f
22:
	ldr w5, [x2, #0]
	rev w5, w5
	ldr w6, [x2, #4]
	rev w6, w6
	lsl x12, x1, #2
	add x12, x12, x0
	sub x12, x12, #4
	lsr x7, x1, #2
	add x7, x7, #1
	sub x8, x1, #16
	cbz x8, 23f
	b 24f
23:
	ldr w9, [x12, #0]
	add w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
25:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 25b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	eor w4, w9, w14
	sub w4, w4, w15
	add w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	sub x12, x12, #4
24:
26:
	ldr w9, [x12, #0]
	sub w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
27:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 27b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	add w4, w9, w14
	eor w4, w4, w15
	sub w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	sub x12, x12, #4
	ldr w9, [x12, #0]
	eor w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
28:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 28b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	sub w4, w9, w14
	add w4, w4, w15
	eor w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	sub x12, x12, #4
	ldr w9, [x12, #0]
	add w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
29:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 29b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	eor w4, w9, w14
	sub w4, w4, w15
	add w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	sub x12, x12, #4
	sub x7, x7, #1
	cbnz x7, 26b
	rev w6, w6
	str w6, [x2, #0]
	rev w5, w5
	str w5, [x2, #4]
	add x2, x2, #8
	sub x3, x3, #1
	cbnz x3, 22b
	b 21f
20:
21:
	ret
	.p2align 6
