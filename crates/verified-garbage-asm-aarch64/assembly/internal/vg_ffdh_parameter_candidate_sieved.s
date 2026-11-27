// The functions of `src/internal/vg_ffdh_parameter_candidate_sieved.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_parameter_candidate_sieved:
	str x0, [x7, #128]
	str x1, [x7, #144]
	str x1, [x7, #168]
	str x1, [x7, #216]
	str x2, [x7, #136]
	str x3, [x7, #152]
	add w4, w4, #0
	str x4, [x7, #160]
	str x5, [x7, #192]
	str x6, [x7, #200]
	add x0, x7, #0
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
20:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 20b
	ldr x3, [x0, #200]
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 21f
	ldr x3, [x0, #152]
	add x4, x3, #7
	lsr x4, x4, #3
	str x4, [x0, #144]
	add x6, x3, #63
	lsr x6, x6, #6
	lsl x6, x6, #6
	add x8, x3, #64
	sub x6, x8, x6
	movz x5, #64, lsl #0
	movz x9, #128, lsl #0
	movz x8, #2049, lsl #0
	subs x8, x3, x8
	csel x5, x9, x5, hs
	str x5, [x0, #0]
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
	add x3, x12, #2
	lsl x3, x3, #3
	add x4, x0, #256
	str x4, [x0, #64]
	add x4, x4, x3
	str x4, [x0, #72]
	add x4, x4, x3
	str x4, [x0, #80]
	add x4, x4, x3
	str x4, [x0, #88]
	add x4, x4, x3
	str x4, [x0, #96]
	add x4, x4, x3
	str x4, [x0, #104]
	add x4, x4, x3
	str x4, [x0, #112]
	add x4, x4, x3
	str x4, [x0, #120]
	add x4, x4, x3
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	movz x9, #0, lsl #0
23:
	add x9, x9, x9
	add x9, x9, #1
	sub x6, x6, #1
	cbnz x6, 23b
	str x9, [x0, #16]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
24:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 24b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #192]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
25:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 26f
	b 27f
26:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
27:
	cbnz x2, 25b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x16, #0]
	ldr x6, [x5, #0]
	movz x9, #1, lsl #0
	orr x3, x3, x9
	and x6, x6, x4
	lsr x9, x4, #1
	add x9, x9, #1
	orr x6, x6, x9
	str x3, [x16, #0]
	str x6, [x5, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x2, [x16, #0]
	add x14, x12, #0
	movz x3, #0, lsl #0
28:
	ldr x5, [x16, #0]
	lsr x4, x5, #32
	lsl x6, x4, #32
	sub x5, x5, x6
	add x3, x3, x4
	add x3, x3, x5
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 28b
	movz x7, #39322, lsl #0
	movk x7, #39321, lsl #16
	movk x7, #39321, lsl #32
	movk x7, #6553, lsl #48
	movz x6, #43691, lsl #0
	movk x6, #43690, lsl #16
	movk x6, #43690, lsl #32
	movk x6, #2730, lsl #48
	ldr x9, [x0, #160]
	movz x10, #3, lsl #0
	subs x8, x9, x10
	csel x7, x7, x6, hs
	movz x13, #10, lsl #0
	movz x6, #24, lsl #0
	csel x13, x13, x6, hs
	movz x4, #7, lsl #0
	and x2, x2, x4
	movz x4, #105, lsl #0
	mul x2, x2, x4
	movz x4, #16, lsl #0
	mul x3, x3, x4
	add x3, x3, x2
	umulh x4, x3, x7
	mul x4, x4, x13
	sub x3, x3, x4
	ldr x9, [x0, #160]
	movz x6, #3, lsl #0
	subs x8, x9, x6
	movz x4, #4, lsl #0
	orr x5, x3, x4
	csel x5, x5, x3, hs
	movz x6, #7, lsl #0
	movz x7, #11, lsl #0
	csel x6, x6, x7, hs
	eor x5, x5, x6
	str x5, [x0, #32]
	ldr x5, [x0, #32]
	cbz x5, 29f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 210f
29:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	add x4, x30, #0
	bl {vg_prime_table_write}
	add x30, x4, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	movz x10, #4, lsl #0
	movz x1, #0, lsl #0
	movz x7, #0, lsl #0
	sub x8, x7, #1
211:
	ldr x17, [x9, #0]
	add x9, x9, #8
	add x3, x17, #0
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
212:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 212b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #16
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
213:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 213b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #32
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
214:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #48
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
215:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 215b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	sub x10, x10, #1
	eor x3, x1, x8
	and x10, x10, x3
	cbnz x10, 211b
	ldr x5, [x0, #32]
	orr x5, x5, x1
	str x5, [x0, #32]
	ldr x5, [x0, #32]
	cbz x5, 216f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 217f
216:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x16, #0
	movz x7, #0, lsl #0
	sub x15, x7, #1
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
218:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 218b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x5, [x0, #32]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	eor x3, x3, x4
	orr x5, x5, x3
	str x5, [x0, #32]
	ldr x5, [x0, #32]
	cbz x5, 219f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 220f
219:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	movz x3, #128, lsl #0
	movz x4, #256, lsl #0
	movz x5, #17, lsl #0
	subs x6, x12, x5
	csel x10, x4, x3, hs
	movz x1, #0, lsl #0
	movz x7, #0, lsl #0
	sub x8, x7, #1
221:
	ldr x17, [x9, #0]
	add x9, x9, #8
	add x3, x17, #0
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
222:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 222b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #16
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
223:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 223b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #32
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
224:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 224b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #48
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
225:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 225b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	sub x10, x10, #1
	eor x3, x1, x8
	and x10, x10, x3
	cbnz x10, 221b
	ldr x5, [x0, #32]
	orr x5, x5, x1
	str x5, [x0, #32]
	ldr x5, [x0, #32]
	cbz x5, 226f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 227f
226:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
228:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 228b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #192]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
229:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 230f
	b 231f
230:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
231:
	cbnz x2, 229b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x16, #0]
	ldr x6, [x5, #0]
	movz x9, #1, lsl #0
	orr x3, x3, x9
	and x6, x6, x4
	lsr x9, x4, #1
	add x9, x9, #1
	orr x6, x6, x9
	str x3, [x16, #0]
	str x6, [x5, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	movz x3, #128, lsl #0
	movz x4, #256, lsl #0
	movz x5, #17, lsl #0
	subs x6, x12, x5
	csel x10, x4, x3, hs
	movz x1, #0, lsl #0
	movz x7, #0, lsl #0
	sub x8, x7, #1
232:
	ldr x17, [x9, #0]
	add x9, x9, #8
	add x3, x17, #0
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
233:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 233b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #16
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
234:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 234b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #32
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
235:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 235b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #48
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
236:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 236b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	sub x10, x10, #1
	eor x3, x1, x8
	and x10, x10, x3
	cbnz x10, 232b
	ldr x5, [x0, #32]
	orr x5, x5, x1
	str x5, [x0, #32]
	ldr x5, [x0, #32]
	cbz x5, 237f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 238f
237:
	ldr x3, [x0, #152]
	add x4, x3, #7
	lsr x4, x4, #3
	str x4, [x0, #144]
	add x6, x3, #63
	lsr x6, x6, #6
	lsl x6, x6, #6
	add x8, x3, #64
	sub x6, x8, x6
	movz x5, #64, lsl #0
	movz x9, #128, lsl #0
	movz x8, #2049, lsl #0
	subs x8, x3, x8
	csel x5, x9, x5, hs
	str x5, [x0, #0]
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
	add x3, x12, #2
	lsl x3, x3, #3
	add x4, x0, #256
	str x4, [x0, #64]
	add x4, x4, x3
	str x4, [x0, #72]
	add x4, x4, x3
	str x4, [x0, #80]
	add x4, x4, x3
	str x4, [x0, #88]
	add x4, x4, x3
	str x4, [x0, #96]
	add x4, x4, x3
	str x4, [x0, #104]
	add x4, x4, x3
	str x4, [x0, #112]
	add x4, x4, x3
	str x4, [x0, #120]
	add x4, x4, x3
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	movz x9, #0, lsl #0
239:
	add x9, x9, x9
	add x9, x9, #1
	sub x6, x6, #1
	cbnz x6, 239b
	str x9, [x0, #16]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
240:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 240b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #192]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
241:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 242f
	b 243f
242:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
243:
	cbnz x2, 241b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x16, #0]
	ldr x6, [x5, #0]
	movz x9, #1, lsl #0
	orr x3, x3, x9
	and x6, x6, x4
	lsr x9, x4, #1
	add x9, x9, #1
	orr x6, x6, x9
	str x3, [x16, #0]
	str x6, [x5, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #0]
	ldr x8, [x0, #64]
	ldr x3, [x8, #0]
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	str x15, [x0, #56]
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
244:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 244b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 245f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
247:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 247b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
248:
	lsr x3, x2, #63
	lsl x2, x2, #1
	orr x2, x2, x4
	subs x15, x2, x5
	adc x16, x7, x7
	orr x16, x16, x3
	tst x16, x16
	csel x2, x15, x2, ne
	add x10, x10, x10
	add x10, x10, x16
	sub x13, x13, #1
	cbnz x13, 248b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
249:
	ldr x9, [x0, #64]
	ldr x11, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #8
	add x14, x9, x13
	ldr x5, [x14, #0]
	add x16, x11, x13
	ldr x2, [x16, #0]
	sub x16, x16, #8
	ldr x3, [x16, #0]
	sub x4, x5, x2
	ldr x17, [x6, #0]
	mul x13, x17, x2
	umulh x14, x17, x2
	adds x13, x13, x3
	adc x14, x14, x2
	add x14, x14, #1
	mul x15, x14, x5
	sub x15, x3, x15
	sub x16, x14, #1
	add x17, x15, x5
	subs x3, x13, x15
	csel x14, x16, x14, lo
	csel x15, x17, x15, lo
	subs x3, x15, x5
	adc x14, x14, x7
	movz x16, #0, lsl #0
	sub x16, x16, #1
	tst x4, x4
	csel x1, x16, x14, eq
	lsl x13, x12, #3
	sub x13, x13, #24
	add x16, x11, x13
	ldr x3, [x16, #8]
	ldr x4, [x16, #0]
	add x17, x9, x13
	ldr x15, [x17, #8]
	sub x14, x12, #2
	tst x14, x14
	csel x4, x14, x4, eq
	mul x13, x1, x15
	umulh x14, x1, x15
	mul x16, x1, x5
	umulh x17, x1, x5
	adds x14, x14, x16
	adc x17, x17, x7
	subs x4, x4, x13
	sbcs x3, x3, x14
	sbc x2, x2, x17
	adds x4, x4, x15
	adcs x3, x3, x5
	adc x16, x2, x7
	sub x17, x1, #1
	tst x2, x2
	csel x1, x17, x1, mi
	csel x2, x16, x2, mi
	lsr x2, x2, #63
	sub x1, x1, x2
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	add x2, x7, #0
	movz x15, #0, lsl #0
	sub x15, x15, #1
	add x13, x15, #0
	adds x3, x7, x7
250:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x13
	eor x13, x3, x15
	eor x4, x4, x15
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 250b
	adc x4, x13, x2
	eor x4, x4, x15
	str x4, [x16, #0]
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
251:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 251b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 249b
	b 246f
245:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 252f
254:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 254b
	b 253f
252:
253:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
255:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 255b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
256:
	ldr x5, [x0, #96]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
257:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 257b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
258:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 258b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
259:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 259b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 256b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
260:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 260b
246:
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
261:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 261b
	add x13, x12, #0
262:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
263:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 263b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
264:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 264b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 262b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
265:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 265b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
266:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 266b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
267:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 267b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
268:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 268b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x5, [x16, #0]
	movz x4, #1, lsl #0
	eor x5, x5, x4
	add x16, x16, #8
	sub x14, x12, #1
	movz x7, #0, lsl #0
	sub x8, x7, #1
269:
	ldr x3, [x16, #0]
	subs x6, x5, x4
	csel x6, x7, x8, hs
	and x3, x3, x6
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 269b
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	sub x6, x7, x5
	and x6, x6, x5
	lsl x9, x12, #3
	add x9, x10, x9
	str x6, [x9, #0]
	add x15, x8, #0
	add x17, x10, #0
	add x16, x0, #256
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
270:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 270b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #56797, lsl #0
	movk x4, #56797, lsl #16
	movk x4, #56797, lsl #32
	movk x4, #56797, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
271:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 271b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #39321, lsl #0
	movk x4, #39321, lsl #16
	movk x4, #39321, lsl #32
	movk x4, #39321, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
272:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 272b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #4369, lsl #0
	movk x4, #4369, lsl #16
	movk x4, #4369, lsl #32
	movk x4, #4369, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
273:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 273b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x3, #0, lsl #0
	str x3, [x0, #24]
274:
	ldr x3, [x0, #200]
	ldr x4, [x0, #216]
	sub x3, x3, x4
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 275f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
277:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 277b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #192]
	ldr x3, [x0, #216]
	add x1, x1, x3
	ldr x2, [x0, #144]
	add x3, x3, x2
	str x3, [x0, #216]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
278:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 279f
	b 280f
279:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
280:
	cbnz x2, 278b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x5, #0]
	and x3, x3, x4
	str x3, [x5, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	ldr x5, [x16, #0]
	lsr x5, x5, #1
	add x16, x16, #8
	sub x14, x12, #1
281:
	ldr x3, [x16, #0]
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 281b
	movz x7, #0, lsl #0
	sub x8, x7, #1
	movz x4, #1, lsl #0
	subs x3, x5, x4
	csel x9, x8, x7, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
	ldr x3, [x16, #0]
	orr x3, x3, x4
	ldr x4, [x17, #0]
	subs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x12, #1
282:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 282b
	csel x15, x7, x8, hs
	and x9, x9, x15
	cbz x9, 283f
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
285:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 285b
	add x13, x12, #0
286:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
287:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 287b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
288:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 288b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 286b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
289:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 289b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
290:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 290b
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	str x19, [x2, #0]
	str x30, [x2, #8]
	add x19, x0, #0
	ldr x1, [x0, #48]
	add x1, x1, #2
	movz x4, #28, lsl #0
	mul x1, x1, x4
	add x1, x1, #32
	bl {vg_miller_rabin_round}
	add w3, w0, #0
	add x0, x19, #0
	movz x4, #0, lsl #0
	sub x3, x4, x3
	str x3, [x0, #184]
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	ldr x30, [x2, #8]
	ldr x19, [x2, #0]
	ldr x3, [x0, #184]
	cbz x3, 291f
	ldr x3, [x0, #24]
	ldr x4, [x0, #0]
	add x3, x3, #1
	subs x5, x3, x4
	movz x6, #4, lsl #0
	movz x7, #1, lsl #0
	csel x5, x7, x6, hs
	str x3, [x0, #24]
	str x5, [x0, #248]
	b 292f
291:
	movz x3, #2, lsl #0
	str x3, [x0, #248]
292:
	b 284f
283:
	movz x3, #4, lsl #0
	str x3, [x0, #248]
284:
	b 276f
275:
	movz x3, #0, lsl #0
	str x3, [x0, #248]
276:
	ldr x3, [x0, #248]
	sub x3, x3, #4
	cbz x3, 274b
	ldr x3, [x0, #248]
	sub x3, x3, #1
	cbz x3, 293f
	ldr x3, [x0, #248]
	cbz x3, 295f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 296f
295:
	movz x3, #0, lsl #0
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #0, lsl #0
296:
	b 294f
293:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x16, #0
	movz x7, #0, lsl #0
	sub x15, x7, #1
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
297:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 297b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x5, [x0, #32]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	eor x3, x3, x4
	orr x5, x5, x3
	str x5, [x0, #32]
	ldr x3, [x0, #152]
	sub x3, x3, #1
	add x4, x3, #7
	lsr x4, x4, #3
	str x4, [x0, #144]
	add x6, x3, #63
	lsr x6, x6, #6
	lsl x6, x6, #6
	add x8, x3, #64
	sub x6, x8, x6
	movz x5, #64, lsl #0
	movz x9, #128, lsl #0
	movz x8, #2049, lsl #0
	subs x8, x3, x8
	csel x5, x9, x5, hs
	str x5, [x0, #0]
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
	add x3, x12, #2
	lsl x3, x3, #3
	add x4, x0, #256
	str x4, [x0, #64]
	add x4, x4, x3
	str x4, [x0, #72]
	add x4, x4, x3
	str x4, [x0, #80]
	add x4, x4, x3
	str x4, [x0, #88]
	add x4, x4, x3
	str x4, [x0, #96]
	add x4, x4, x3
	str x4, [x0, #104]
	add x4, x4, x3
	str x4, [x0, #112]
	add x4, x4, x3
	str x4, [x0, #120]
	add x4, x4, x3
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	movz x9, #0, lsl #0
298:
	add x9, x9, x9
	add x9, x9, #1
	sub x6, x6, #1
	cbnz x6, 298b
	str x9, [x0, #16]
	ldr x8, [x0, #64]
	ldr x3, [x8, #0]
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	str x15, [x0, #56]
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
299:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 299b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2100f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2102:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2102b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2103:
	lsr x3, x2, #63
	lsl x2, x2, #1
	orr x2, x2, x4
	subs x15, x2, x5
	adc x16, x7, x7
	orr x16, x16, x3
	tst x16, x16
	csel x2, x15, x2, ne
	add x10, x10, x10
	add x10, x10, x16
	sub x13, x13, #1
	cbnz x13, 2103b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2104:
	ldr x9, [x0, #64]
	ldr x11, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #8
	add x14, x9, x13
	ldr x5, [x14, #0]
	add x16, x11, x13
	ldr x2, [x16, #0]
	sub x16, x16, #8
	ldr x3, [x16, #0]
	sub x4, x5, x2
	ldr x17, [x6, #0]
	mul x13, x17, x2
	umulh x14, x17, x2
	adds x13, x13, x3
	adc x14, x14, x2
	add x14, x14, #1
	mul x15, x14, x5
	sub x15, x3, x15
	sub x16, x14, #1
	add x17, x15, x5
	subs x3, x13, x15
	csel x14, x16, x14, lo
	csel x15, x17, x15, lo
	subs x3, x15, x5
	adc x14, x14, x7
	movz x16, #0, lsl #0
	sub x16, x16, #1
	tst x4, x4
	csel x1, x16, x14, eq
	lsl x13, x12, #3
	sub x13, x13, #24
	add x16, x11, x13
	ldr x3, [x16, #8]
	ldr x4, [x16, #0]
	add x17, x9, x13
	ldr x15, [x17, #8]
	sub x14, x12, #2
	tst x14, x14
	csel x4, x14, x4, eq
	mul x13, x1, x15
	umulh x14, x1, x15
	mul x16, x1, x5
	umulh x17, x1, x5
	adds x14, x14, x16
	adc x17, x17, x7
	subs x4, x4, x13
	sbcs x3, x3, x14
	sbc x2, x2, x17
	adds x4, x4, x15
	adcs x3, x3, x5
	adc x16, x2, x7
	sub x17, x1, #1
	tst x2, x2
	csel x1, x17, x1, mi
	csel x2, x16, x2, mi
	lsr x2, x2, #63
	sub x1, x1, x2
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	add x2, x7, #0
	movz x15, #0, lsl #0
	sub x15, x15, #1
	add x13, x15, #0
	adds x3, x7, x7
2105:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x13
	eor x13, x3, x15
	eor x4, x4, x15
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2105b
	adc x4, x13, x2
	eor x4, x4, x15
	str x4, [x16, #0]
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2106:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2106b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2104b
	b 2101f
2100:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2107f
2109:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2109b
	b 2108f
2107:
2108:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2110:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2110b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2111:
	ldr x5, [x0, #96]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2112:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2112b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2113:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2113b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2114:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2114b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2111b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2115:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2115b
2101:
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2116:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2116b
	add x13, x12, #0
2117:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2118:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2118b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
2119:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2119b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2117b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2120:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2120b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2121:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2121b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2122:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2122b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
2123:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2123b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x5, [x16, #0]
	movz x4, #1, lsl #0
	eor x5, x5, x4
	add x16, x16, #8
	sub x14, x12, #1
	movz x7, #0, lsl #0
	sub x8, x7, #1
2124:
	ldr x3, [x16, #0]
	subs x6, x5, x4
	csel x6, x7, x8, hs
	and x3, x3, x6
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2124b
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	sub x6, x7, x5
	and x6, x6, x5
	lsl x9, x12, #3
	add x9, x10, x9
	str x6, [x9, #0]
	add x15, x8, #0
	add x17, x10, #0
	add x16, x0, #256
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2125:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2125b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #56797, lsl #0
	movk x4, #56797, lsl #16
	movk x4, #56797, lsl #32
	movk x4, #56797, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2126:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2126b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #39321, lsl #0
	movk x4, #39321, lsl #16
	movk x4, #39321, lsl #32
	movk x4, #39321, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2127:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2127b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #4369, lsl #0
	movk x4, #4369, lsl #16
	movk x4, #4369, lsl #32
	movk x4, #4369, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2128:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2128b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x3, #0, lsl #0
	str x3, [x0, #24]
2129:
	ldr x3, [x0, #200]
	ldr x4, [x0, #216]
	sub x3, x3, x4
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2130f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2132:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2132b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #192]
	ldr x3, [x0, #216]
	add x1, x1, x3
	ldr x2, [x0, #144]
	add x3, x3, x2
	str x3, [x0, #216]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2133:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2134f
	b 2135f
2134:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2135:
	cbnz x2, 2133b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x5, #0]
	and x3, x3, x4
	str x3, [x5, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	ldr x5, [x16, #0]
	lsr x5, x5, #1
	add x16, x16, #8
	sub x14, x12, #1
2136:
	ldr x3, [x16, #0]
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2136b
	movz x7, #0, lsl #0
	sub x8, x7, #1
	movz x4, #1, lsl #0
	subs x3, x5, x4
	csel x9, x8, x7, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
	ldr x3, [x16, #0]
	orr x3, x3, x4
	ldr x4, [x17, #0]
	subs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x12, #1
2137:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2137b
	csel x15, x7, x8, hs
	and x9, x9, x15
	cbz x9, 2138f
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2140:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	add x13, x12, #0
2141:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2142:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2142b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
2143:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2143b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2141b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2144:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2144b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2145:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2145b
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	str x19, [x2, #0]
	str x30, [x2, #8]
	add x19, x0, #0
	ldr x1, [x0, #48]
	add x1, x1, #2
	movz x4, #28, lsl #0
	mul x1, x1, x4
	add x1, x1, #32
	bl {vg_miller_rabin_round}
	add w3, w0, #0
	add x0, x19, #0
	movz x4, #0, lsl #0
	sub x3, x4, x3
	str x3, [x0, #184]
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	ldr x30, [x2, #8]
	ldr x19, [x2, #0]
	ldr x3, [x0, #184]
	cbz x3, 2146f
	ldr x3, [x0, #24]
	ldr x4, [x0, #0]
	add x3, x3, #1
	subs x5, x3, x4
	movz x6, #4, lsl #0
	movz x7, #1, lsl #0
	csel x5, x7, x6, hs
	str x3, [x0, #24]
	str x5, [x0, #248]
	b 2147f
2146:
	movz x3, #2, lsl #0
	str x3, [x0, #248]
2147:
	b 2139f
2138:
	movz x3, #4, lsl #0
	str x3, [x0, #248]
2139:
	b 2131f
2130:
	movz x3, #0, lsl #0
	str x3, [x0, #248]
2131:
	ldr x3, [x0, #248]
	sub x3, x3, #4
	cbz x3, 2129b
	ldr x3, [x0, #248]
	sub x3, x3, #1
	cbz x3, 2148f
	ldr x3, [x0, #248]
	cbz x3, 2150f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 2151f
2150:
	movz x3, #0, lsl #0
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #0, lsl #0
2151:
	b 2149f
2148:
	ldr x3, [x0, #152]
	add x4, x3, #7
	lsr x4, x4, #3
	str x4, [x0, #144]
	add x6, x3, #63
	lsr x6, x6, #6
	lsl x6, x6, #6
	add x8, x3, #64
	sub x6, x8, x6
	movz x5, #64, lsl #0
	movz x9, #128, lsl #0
	movz x8, #2049, lsl #0
	subs x8, x3, x8
	csel x5, x9, x5, hs
	str x5, [x0, #0]
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
	add x3, x12, #2
	lsl x3, x3, #3
	add x4, x0, #256
	str x4, [x0, #64]
	add x4, x4, x3
	str x4, [x0, #72]
	add x4, x4, x3
	str x4, [x0, #80]
	add x4, x4, x3
	str x4, [x0, #88]
	add x4, x4, x3
	str x4, [x0, #96]
	add x4, x4, x3
	str x4, [x0, #104]
	add x4, x4, x3
	str x4, [x0, #112]
	add x4, x4, x3
	str x4, [x0, #120]
	add x4, x4, x3
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	movz x9, #0, lsl #0
2152:
	add x9, x9, x9
	add x9, x9, #1
	sub x6, x6, #1
	cbnz x6, 2152b
	str x9, [x0, #16]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2153:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2153b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #192]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2154:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2155f
	b 2156f
2155:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2156:
	cbnz x2, 2154b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x16, #0]
	ldr x6, [x5, #0]
	movz x9, #1, lsl #0
	orr x3, x3, x9
	and x6, x6, x4
	lsr x9, x4, #1
	add x9, x9, #1
	orr x6, x6, x9
	str x3, [x16, #0]
	str x6, [x5, #0]
	ldr x3, [x0, #0]
	sub x3, x3, #1
	str x3, [x0, #0]
	ldr x8, [x0, #64]
	ldr x3, [x8, #0]
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	str x15, [x0, #56]
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2157:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2157b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 2158f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
2160:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2160b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
2161:
	lsr x3, x2, #63
	lsl x2, x2, #1
	orr x2, x2, x4
	subs x15, x2, x5
	adc x16, x7, x7
	orr x16, x16, x3
	tst x16, x16
	csel x2, x15, x2, ne
	add x10, x10, x10
	add x10, x10, x16
	sub x13, x13, #1
	cbnz x13, 2161b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
2162:
	ldr x9, [x0, #64]
	ldr x11, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #8
	add x14, x9, x13
	ldr x5, [x14, #0]
	add x16, x11, x13
	ldr x2, [x16, #0]
	sub x16, x16, #8
	ldr x3, [x16, #0]
	sub x4, x5, x2
	ldr x17, [x6, #0]
	mul x13, x17, x2
	umulh x14, x17, x2
	adds x13, x13, x3
	adc x14, x14, x2
	add x14, x14, #1
	mul x15, x14, x5
	sub x15, x3, x15
	sub x16, x14, #1
	add x17, x15, x5
	subs x3, x13, x15
	csel x14, x16, x14, lo
	csel x15, x17, x15, lo
	subs x3, x15, x5
	adc x14, x14, x7
	movz x16, #0, lsl #0
	sub x16, x16, #1
	tst x4, x4
	csel x1, x16, x14, eq
	lsl x13, x12, #3
	sub x13, x13, #24
	add x16, x11, x13
	ldr x3, [x16, #8]
	ldr x4, [x16, #0]
	add x17, x9, x13
	ldr x15, [x17, #8]
	sub x14, x12, #2
	tst x14, x14
	csel x4, x14, x4, eq
	mul x13, x1, x15
	umulh x14, x1, x15
	mul x16, x1, x5
	umulh x17, x1, x5
	adds x14, x14, x16
	adc x17, x17, x7
	subs x4, x4, x13
	sbcs x3, x3, x14
	sbc x2, x2, x17
	adds x4, x4, x15
	adcs x3, x3, x5
	adc x16, x2, x7
	sub x17, x1, #1
	tst x2, x2
	csel x1, x17, x1, mi
	csel x2, x16, x2, mi
	lsr x2, x2, #63
	sub x1, x1, x2
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	add x2, x7, #0
	movz x15, #0, lsl #0
	sub x15, x15, #1
	add x13, x15, #0
	adds x3, x7, x7
2163:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x13
	eor x13, x3, x15
	eor x4, x4, x15
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2163b
	adc x4, x13, x2
	eor x4, x4, x15
	str x4, [x16, #0]
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2164:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2164b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2162b
	b 2159f
2158:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2165f
2167:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2167b
	b 2166f
2165:
2166:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2168:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2168b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2169:
	ldr x5, [x0, #96]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2170:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2170b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2171:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2171b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2172:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2172b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2169b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2173:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2173b
2159:
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2174:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2174b
	add x13, x12, #0
2175:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2176:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2176b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
2177:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2177b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2175b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2178:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2178b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2179:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2179b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2180:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2180b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
2181:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2181b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x5, [x16, #0]
	movz x4, #1, lsl #0
	eor x5, x5, x4
	add x16, x16, #8
	sub x14, x12, #1
	movz x7, #0, lsl #0
	sub x8, x7, #1
2182:
	ldr x3, [x16, #0]
	subs x6, x5, x4
	csel x6, x7, x8, hs
	and x3, x3, x6
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2182b
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	sub x6, x7, x5
	and x6, x6, x5
	lsl x9, x12, #3
	add x9, x10, x9
	str x6, [x9, #0]
	add x15, x8, #0
	add x17, x10, #0
	add x16, x0, #256
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2183:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2183b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #56797, lsl #0
	movk x4, #56797, lsl #16
	movk x4, #56797, lsl #32
	movk x4, #56797, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2184:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2184b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #39321, lsl #0
	movk x4, #39321, lsl #16
	movk x4, #39321, lsl #32
	movk x4, #39321, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2185:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2185b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #4369, lsl #0
	movk x4, #4369, lsl #16
	movk x4, #4369, lsl #32
	movk x4, #4369, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2186:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2186b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x3, #0, lsl #0
	str x3, [x0, #24]
2187:
	ldr x3, [x0, #200]
	ldr x4, [x0, #216]
	sub x3, x3, x4
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2188f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2190:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2190b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #192]
	ldr x3, [x0, #216]
	add x1, x1, x3
	ldr x2, [x0, #144]
	add x3, x3, x2
	str x3, [x0, #216]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2191:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2192f
	b 2193f
2192:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2193:
	cbnz x2, 2191b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x5, #0]
	and x3, x3, x4
	str x3, [x5, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	ldr x5, [x16, #0]
	lsr x5, x5, #1
	add x16, x16, #8
	sub x14, x12, #1
2194:
	ldr x3, [x16, #0]
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2194b
	movz x7, #0, lsl #0
	sub x8, x7, #1
	movz x4, #1, lsl #0
	subs x3, x5, x4
	csel x9, x8, x7, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
	ldr x3, [x16, #0]
	orr x3, x3, x4
	ldr x4, [x17, #0]
	subs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x12, #1
2195:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2195b
	csel x15, x7, x8, hs
	and x9, x9, x15
	cbz x9, 2196f
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2198:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2198b
	add x13, x12, #0
2199:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2200:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2200b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
2201:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2201b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2199b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2202:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2202b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2203:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2203b
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	str x19, [x2, #0]
	str x30, [x2, #8]
	add x19, x0, #0
	ldr x1, [x0, #48]
	add x1, x1, #2
	movz x4, #28, lsl #0
	mul x1, x1, x4
	add x1, x1, #32
	bl {vg_miller_rabin_round}
	add w3, w0, #0
	add x0, x19, #0
	movz x4, #0, lsl #0
	sub x3, x4, x3
	str x3, [x0, #184]
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	ldr x30, [x2, #8]
	ldr x19, [x2, #0]
	ldr x3, [x0, #184]
	cbz x3, 2204f
	ldr x3, [x0, #24]
	ldr x4, [x0, #0]
	add x3, x3, #1
	subs x5, x3, x4
	movz x6, #4, lsl #0
	movz x7, #1, lsl #0
	csel x5, x7, x6, hs
	str x3, [x0, #24]
	str x5, [x0, #248]
	b 2205f
2204:
	movz x3, #2, lsl #0
	str x3, [x0, #248]
2205:
	b 2197f
2196:
	movz x3, #4, lsl #0
	str x3, [x0, #248]
2197:
	b 2189f
2188:
	movz x3, #0, lsl #0
	str x3, [x0, #248]
2189:
	ldr x3, [x0, #248]
	sub x3, x3, #4
	cbz x3, 2187b
	ldr x3, [x0, #248]
	cbz x3, 2206f
	sub x3, x3, #1
	cbz x3, 2208f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 2209f
2208:
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2210:
	and x5, x2, x6
	cbz x5, 2211f
	b 2212f
2211:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2212:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2210b
	movz x0, #1, lsl #0
2209:
	b 2207f
2206:
	movz x3, #0, lsl #0
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #0, lsl #0
2207:
2149:
294:
238:
227:
220:
217:
210:
	b 22f
21:
	movz x3, #0, lsl #0
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #0, lsl #0
22:
	ret
	.p2align 6
