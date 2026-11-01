// The functions of `src/internal/vg_mldsa_simple_bit_pack.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_simple_bit_pack:
	sub x9, x3, #128
	cbz x9, 20f
	sub x9, x3, #192
	cbz x9, 22f
	sub x9, x3, #320
	cbz x9, 24f
	sub x9, x3, #128
	cbz x9, 26f
	sub x9, x3, #192
	cbz x9, 28f
	movz x11, #64, lsl #0
210:
	movz x9, #0, lsl #0
	ldr w10, [x0, #0]
	add x9, x9, x10
	strb w9, [x2, #0]
	lsr x9, x9, #8
	ldr w10, [x0, #4]
	lsl x10, x10, #2
	add x9, x9, x10
	strb w9, [x2, #1]
	lsr x9, x9, #8
	ldr w10, [x0, #8]
	lsl x10, x10, #4
	add x9, x9, x10
	strb w9, [x2, #2]
	lsr x9, x9, #8
	ldr w10, [x0, #12]
	lsl x10, x10, #6
	add x9, x9, x10
	strb w9, [x2, #3]
	lsr x9, x9, #8
	strb w9, [x2, #4]
	lsr x9, x9, #8
	add x0, x0, #16
	add x2, x2, #5
	sub x11, x11, #1
	cbnz x11, 210b
	b 29f
28:
	movz x11, #64, lsl #0
211:
	movz x9, #0, lsl #0
	ldr w10, [x0, #0]
	add x9, x9, x10
	ldr w10, [x0, #4]
	lsl x10, x10, #6
	add x9, x9, x10
	strb w9, [x2, #0]
	lsr x9, x9, #8
	ldr w10, [x0, #8]
	lsl x10, x10, #4
	add x9, x9, x10
	strb w9, [x2, #1]
	lsr x9, x9, #8
	ldr w10, [x0, #12]
	lsl x10, x10, #2
	add x9, x9, x10
	strb w9, [x2, #2]
	lsr x9, x9, #8
	add x0, x0, #16
	add x2, x2, #3
	sub x11, x11, #1
	cbnz x11, 211b
29:
	b 27f
26:
	movz x11, #128, lsl #0
212:
	movz x9, #0, lsl #0
	ldr w10, [x0, #0]
	add x9, x9, x10
	ldr w10, [x0, #4]
	lsl x10, x10, #4
	add x9, x9, x10
	strb w9, [x2, #0]
	lsr x9, x9, #8
	add x0, x0, #8
	add x2, x2, #1
	sub x11, x11, #1
	cbnz x11, 212b
27:
	b 25f
24:
	movz x15, #32, lsl #0
213:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	umov w10, v0.s[0]
	add x9, x10, #0
	umov w10, v0.s[1]
	lsl x11, x10, #10
	orr x9, x9, x11
	umov w10, v0.s[2]
	lsl x11, x10, #20
	orr x9, x9, x11
	umov w10, v0.s[3]
	lsl x11, x10, #30
	orr x9, x9, x11
	umov w10, v1.s[0]
	lsl x11, x10, #40
	orr x9, x9, x11
	umov w10, v1.s[1]
	lsl x11, x10, #50
	orr x9, x9, x11
	umov w10, v1.s[2]
	lsl x11, x10, #60
	orr x9, x9, x11
	str x9, [x2, #0]
	lsr x9, x10, #4
	umov w10, v1.s[3]
	lsl x11, x10, #6
	orr x9, x9, x11
	strb w9, [x2, #8]
	lsr x9, x9, #8
	strb w9, [x2, #9]
	lsr x9, x9, #8
	add x0, x0, #32
	add x2, x2, #10
	sub x15, x15, #1
	cbnz x15, 213b
25:
	b 23f
22:
	movz x15, #32, lsl #0
214:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	umov w10, v0.s[0]
	add x9, x10, #0
	umov w10, v0.s[1]
	lsl x11, x10, #6
	orr x9, x9, x11
	umov w10, v0.s[2]
	lsl x11, x10, #12
	orr x9, x9, x11
	umov w10, v0.s[3]
	lsl x11, x10, #18
	orr x9, x9, x11
	umov w10, v1.s[0]
	lsl x11, x10, #24
	orr x9, x9, x11
	umov w10, v1.s[1]
	lsl x11, x10, #30
	orr x9, x9, x11
	umov w10, v1.s[2]
	lsl x11, x10, #36
	orr x9, x9, x11
	umov w10, v1.s[3]
	lsl x11, x10, #42
	orr x9, x9, x11
	str w9, [x2, #0]
	lsr x9, x9, #32
	strb w9, [x2, #4]
	lsr x9, x9, #8
	strb w9, [x2, #5]
	lsr x9, x9, #8
	add x0, x0, #32
	add x2, x2, #6
	sub x15, x15, #1
	cbnz x15, 214b
23:
	b 21f
20:
	movz x9, #1024, lsl #0
	movk x9, #3080, lsl #16
	movk x9, #5136, lsl #32
	movk x9, #7192, lsl #48
	movz x10, #9248, lsl #0
	movk x10, #11304, lsl #16
	movk x10, #13360, lsl #32
	movk x10, #15416, lsl #48
	dup v18.2d, x9
	mov v18.d[1], x10
	movz x9, #256, lsl #0
	movk x9, #1284, lsl #16
	movk x9, #2312, lsl #32
	movk x9, #3340, lsl #48
	movz x10, #65535, lsl #0
	movk x10, #65535, lsl #16
	movk x10, #65535, lsl #32
	movk x10, #65535, lsl #48
	dup v19.2d, x9
	mov v19.d[1], x10
	movz x9, #255, lsl #0
	movk x9, #255, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v20.4s, w9
	movz x15, #16, lsl #0
215:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	ldr q2, [x0, #32]
	ldr q3, [x0, #48]
	tbl v0.16b, {v0.16b, v1.16b, v2.16b, v3.16b}, v18.16b
	ushr v1.4s, v0.4s, #4
	orr v0.16b, v0.16b, v1.16b
	and v0.16b, v0.16b, v20.16b
	ushr v1.4s, v0.4s, #8
	orr v0.16b, v0.16b, v1.16b
	tbl v0.16b, {v0.16b}, v19.16b
	umov x9, v0.d[0]
	str x9, [x2, #0]
	add x0, x0, #64
	add x2, x2, #8
	sub x15, x15, #1
	cbnz x15, 215b
21:
	ret
	.p2align 6
