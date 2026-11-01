// The functions of `src/internal/vg_mldsa_bit_pack.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_bit_pack:
	sub x9, x4, #96
	cbz x9, 20f
	sub x9, x4, #128
	cbz x9, 22f
	sub x9, x4, #416
	cbz x9, 24f
	sub x9, x4, #576
	cbz x9, 26f
	sub x9, x4, #640
	cbz x9, 28f
	add x2, x3, #0
	movz x13, #57345, lsl #0
	movk x13, #127, lsl #16
	movk x13, #0, lsl #32
	movk x13, #0, lsl #48
	sub x9, x4, #96
	cbz x9, 210f
	sub x9, x4, #128
	cbz x9, 212f
	sub x9, x4, #416
	cbz x9, 214f
	sub x9, x4, #576
	cbz x9, 216f
	movz x12, #0, lsl #0
	movk x12, #8, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x11, #128, lsl #0
218:
	movz x9, #0, lsl #0
	ldr w10, [x0, #0]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	add x9, x9, x10
	strb w9, [x2, #0]
	lsr x9, x9, #8
	strb w9, [x2, #1]
	lsr x9, x9, #8
	ldr w10, [x0, #4]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #4
	add x9, x9, x10
	strb w9, [x2, #2]
	lsr x9, x9, #8
	strb w9, [x2, #3]
	lsr x9, x9, #8
	strb w9, [x2, #4]
	lsr x9, x9, #8
	add x0, x0, #8
	add x2, x2, #5
	sub x11, x11, #1
	cbnz x11, 218b
	b 217f
216:
	movz x12, #0, lsl #0
	movk x12, #2, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x11, #64, lsl #0
219:
	movz x9, #0, lsl #0
	ldr w10, [x0, #0]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	add x9, x9, x10
	strb w9, [x2, #0]
	lsr x9, x9, #8
	strb w9, [x2, #1]
	lsr x9, x9, #8
	ldr w10, [x0, #4]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #2
	add x9, x9, x10
	strb w9, [x2, #2]
	lsr x9, x9, #8
	strb w9, [x2, #3]
	lsr x9, x9, #8
	ldr w10, [x0, #8]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #4
	add x9, x9, x10
	strb w9, [x2, #4]
	lsr x9, x9, #8
	strb w9, [x2, #5]
	lsr x9, x9, #8
	ldr w10, [x0, #12]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #6
	add x9, x9, x10
	strb w9, [x2, #6]
	lsr x9, x9, #8
	strb w9, [x2, #7]
	lsr x9, x9, #8
	strb w9, [x2, #8]
	lsr x9, x9, #8
	add x0, x0, #16
	add x2, x2, #9
	sub x11, x11, #1
	cbnz x11, 219b
217:
	b 215f
214:
	movz x12, #4096, lsl #0
	movk x12, #0, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x11, #32, lsl #0
220:
	movz x9, #0, lsl #0
	ldr w10, [x0, #0]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	add x9, x9, x10
	strb w9, [x2, #0]
	lsr x9, x9, #8
	ldr w10, [x0, #4]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #5
	add x9, x9, x10
	strb w9, [x2, #1]
	lsr x9, x9, #8
	strb w9, [x2, #2]
	lsr x9, x9, #8
	ldr w10, [x0, #8]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #2
	add x9, x9, x10
	strb w9, [x2, #3]
	lsr x9, x9, #8
	ldr w10, [x0, #12]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #7
	add x9, x9, x10
	strb w9, [x2, #4]
	lsr x9, x9, #8
	strb w9, [x2, #5]
	lsr x9, x9, #8
	ldr w10, [x0, #16]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #4
	add x9, x9, x10
	strb w9, [x2, #6]
	lsr x9, x9, #8
	strb w9, [x2, #7]
	lsr x9, x9, #8
	ldr w10, [x0, #20]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #1
	add x9, x9, x10
	strb w9, [x2, #8]
	lsr x9, x9, #8
	ldr w10, [x0, #24]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #6
	add x9, x9, x10
	strb w9, [x2, #9]
	lsr x9, x9, #8
	strb w9, [x2, #10]
	lsr x9, x9, #8
	ldr w10, [x0, #28]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #3
	add x9, x9, x10
	strb w9, [x2, #11]
	lsr x9, x9, #8
	strb w9, [x2, #12]
	lsr x9, x9, #8
	add x0, x0, #32
	add x2, x2, #13
	sub x11, x11, #1
	cbnz x11, 220b
215:
	b 213f
212:
	movz x12, #4, lsl #0
	movk x12, #0, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x11, #128, lsl #0
221:
	movz x9, #0, lsl #0
	ldr w10, [x0, #0]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	add x9, x9, x10
	ldr w10, [x0, #4]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #4
	add x9, x9, x10
	strb w9, [x2, #0]
	lsr x9, x9, #8
	add x0, x0, #8
	add x2, x2, #1
	sub x11, x11, #1
	cbnz x11, 221b
213:
	b 211f
210:
	movz x12, #2, lsl #0
	movk x12, #0, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x11, #32, lsl #0
222:
	movz x9, #0, lsl #0
	ldr w10, [x0, #0]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	add x9, x9, x10
	ldr w10, [x0, #4]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #3
	add x9, x9, x10
	ldr w10, [x0, #8]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #6
	add x9, x9, x10
	strb w9, [x2, #0]
	lsr x9, x9, #8
	ldr w10, [x0, #12]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #1
	add x9, x9, x10
	ldr w10, [x0, #16]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #4
	add x9, x9, x10
	ldr w10, [x0, #20]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #7
	add x9, x9, x10
	strb w9, [x2, #1]
	lsr x9, x9, #8
	ldr w10, [x0, #24]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #2
	add x9, x9, x10
	ldr w10, [x0, #28]
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	lsl x10, x10, #5
	add x9, x9, x10
	strb w9, [x2, #2]
	lsr x9, x9, #8
	add x0, x0, #32
	add x2, x2, #3
	sub x11, x11, #1
	cbnz x11, 222b
211:
	b 29f
28:
	add x2, x3, #0
	movz x9, #0, lsl #0
	movk x9, #8, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x15, #64, lsl #0
223:
	ldr q0, [x0, #0]
	sub v0.4s, v16.4s, v0.4s
	sshr v4.4s, v0.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v0.4s, v0.4s, v4.4s
	umov w10, v0.s[0]
	add x9, x10, #0
	umov w10, v0.s[1]
	lsl x11, x10, #20
	orr x9, x9, x11
	umov w10, v0.s[2]
	lsl x11, x10, #40
	orr x9, x9, x11
	umov w10, v0.s[3]
	lsl x11, x10, #60
	orr x9, x9, x11
	str x9, [x2, #0]
	lsr x9, x10, #4
	strb w9, [x2, #8]
	lsr x9, x9, #8
	strb w9, [x2, #9]
	lsr x9, x9, #8
	add x0, x0, #16
	add x2, x2, #10
	sub x15, x15, #1
	cbnz x15, 223b
29:
	b 27f
26:
	add x2, x3, #0
	movz x9, #0, lsl #0
	movk x9, #2, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x15, #64, lsl #0
224:
	ldr q0, [x0, #0]
	sub v0.4s, v16.4s, v0.4s
	sshr v4.4s, v0.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v0.4s, v0.4s, v4.4s
	umov w10, v0.s[0]
	add x9, x10, #0
	umov w10, v0.s[1]
	lsl x11, x10, #18
	orr x9, x9, x11
	umov w10, v0.s[2]
	lsl x11, x10, #36
	orr x9, x9, x11
	umov w10, v0.s[3]
	lsl x11, x10, #54
	orr x9, x9, x11
	str x9, [x2, #0]
	lsr x9, x10, #10
	strb w9, [x2, #8]
	add x0, x0, #16
	add x2, x2, #9
	sub x15, x15, #1
	cbnz x15, 224b
27:
	b 25f
24:
	add x2, x3, #0
	movz x9, #4096, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x15, #32, lsl #0
225:
	ldr q0, [x0, #0]
	sub v0.4s, v16.4s, v0.4s
	sshr v4.4s, v0.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v0.4s, v0.4s, v4.4s
	ldr q1, [x0, #16]
	sub v1.4s, v16.4s, v1.4s
	sshr v4.4s, v1.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v1.4s, v1.4s, v4.4s
	umov w10, v0.s[0]
	add x9, x10, #0
	umov w10, v0.s[1]
	lsl x11, x10, #13
	orr x9, x9, x11
	umov w10, v0.s[2]
	lsl x11, x10, #26
	orr x9, x9, x11
	umov w10, v0.s[3]
	lsl x11, x10, #39
	orr x9, x9, x11
	umov w10, v1.s[0]
	lsl x11, x10, #52
	orr x9, x9, x11
	str x9, [x2, #0]
	lsr x9, x10, #12
	umov w10, v1.s[1]
	lsl x11, x10, #1
	orr x9, x9, x11
	umov w10, v1.s[2]
	lsl x11, x10, #14
	orr x9, x9, x11
	umov w10, v1.s[3]
	lsl x11, x10, #27
	orr x9, x9, x11
	str w9, [x2, #8]
	lsr x9, x9, #32
	strb w9, [x2, #12]
	add x0, x0, #32
	add x2, x2, #13
	sub x15, x15, #1
	cbnz x15, 225b
25:
	b 23f
22:
	add x2, x3, #0
	movz x9, #4, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
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
226:
	ldr q0, [x0, #0]
	sub v0.4s, v16.4s, v0.4s
	sshr v4.4s, v0.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v0.4s, v0.4s, v4.4s
	ldr q1, [x0, #16]
	sub v1.4s, v16.4s, v1.4s
	sshr v4.4s, v1.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v1.4s, v1.4s, v4.4s
	ldr q2, [x0, #32]
	sub v2.4s, v16.4s, v2.4s
	sshr v4.4s, v2.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v2.4s, v2.4s, v4.4s
	ldr q3, [x0, #48]
	sub v3.4s, v16.4s, v3.4s
	sshr v4.4s, v3.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v3.4s, v3.4s, v4.4s
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
	cbnz x15, 226b
23:
	b 21f
20:
	add x2, x3, #0
	movz x9, #2, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x15, #32, lsl #0
227:
	ldr q0, [x0, #0]
	sub v0.4s, v16.4s, v0.4s
	sshr v4.4s, v0.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v0.4s, v0.4s, v4.4s
	ldr q1, [x0, #16]
	sub v1.4s, v16.4s, v1.4s
	sshr v4.4s, v1.4s, #31
	and v4.16b, v4.16b, v17.16b
	add v1.4s, v1.4s, v4.4s
	umov w10, v0.s[0]
	add x9, x10, #0
	umov w10, v0.s[1]
	lsl x11, x10, #3
	orr x9, x9, x11
	umov w10, v0.s[2]
	lsl x11, x10, #6
	orr x9, x9, x11
	umov w10, v0.s[3]
	lsl x11, x10, #9
	orr x9, x9, x11
	umov w10, v1.s[0]
	lsl x11, x10, #12
	orr x9, x9, x11
	umov w10, v1.s[1]
	lsl x11, x10, #15
	orr x9, x9, x11
	umov w10, v1.s[2]
	lsl x11, x10, #18
	orr x9, x9, x11
	umov w10, v1.s[3]
	lsl x11, x10, #21
	orr x9, x9, x11
	strb w9, [x2, #0]
	lsr x9, x9, #8
	strb w9, [x2, #1]
	lsr x9, x9, #8
	strb w9, [x2, #2]
	add x0, x0, #32
	add x2, x2, #3
	sub x15, x15, #1
	cbnz x15, 227b
21:
	ret
	.p2align 6
