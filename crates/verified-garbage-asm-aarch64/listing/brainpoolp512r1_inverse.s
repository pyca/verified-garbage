// The functions of `src/brainpoolp512r1_inverse.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_inv_mod_p:
	str x19, [x0, #5080]
	str x21, [x0, #5088]
	str x22, [x0, #5096]
	str x23, [x0, #5104]
	str x24, [x0, #5112]
	str x25, [x0, #5120]
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #23, lsl #0
	ldr x2, [x0, #64]
	str x2, [x0, #4504]
	ldr x2, [x0, #72]
	str x2, [x0, #4512]
	ldr x2, [x0, #80]
	str x2, [x0, #4520]
	ldr x2, [x0, #88]
	str x2, [x0, #4528]
	ldr x2, [x0, #96]
	str x2, [x0, #4536]
	ldr x2, [x0, #104]
	str x2, [x0, #4544]
	ldr x2, [x0, #112]
	str x2, [x0, #4552]
	ldr x2, [x0, #120]
	str x2, [x0, #4560]
	str x12, [x0, #4568]
	ldr x2, [x0, #1088]
	str x2, [x0, #4576]
	ldr x2, [x0, #1096]
	str x2, [x0, #4584]
	ldr x2, [x0, #1104]
	str x2, [x0, #4592]
	ldr x2, [x0, #1112]
	str x2, [x0, #4600]
	ldr x2, [x0, #1120]
	str x2, [x0, #4608]
	ldr x2, [x0, #1128]
	str x2, [x0, #4616]
	ldr x2, [x0, #1136]
	str x2, [x0, #4624]
	ldr x2, [x0, #1144]
	str x2, [x0, #4632]
	str x12, [x0, #4640]
	str x12, [x0, #4648]
	str x12, [x0, #4656]
	str x12, [x0, #4664]
	str x12, [x0, #4672]
	str x12, [x0, #4680]
	str x12, [x0, #4688]
	str x12, [x0, #4696]
	str x12, [x0, #4704]
	str x12, [x0, #4712]
	str x12, [x0, #4720]
	str x12, [x0, #4728]
	str x12, [x0, #4736]
	str x12, [x0, #4744]
	str x12, [x0, #4752]
	str x12, [x0, #4760]
	str x12, [x0, #4768]
	str x12, [x0, #4776]
	str x12, [x0, #4784]
	str x11, [x0, #4720]
20:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #4504]
	ldr x3, [x0, #4576]
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #1, lsl #0
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x12, #0, lsl #0
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #4504]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #4936]
	ldr x2, [x0, #4512]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4944]
	ldr x2, [x0, #4520]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4952]
	ldr x2, [x0, #4528]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4960]
	ldr x2, [x0, #4536]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4968]
	ldr x2, [x0, #4544]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4976]
	ldr x2, [x0, #4552]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4984]
	ldr x2, [x0, #4560]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4992]
	ldr x2, [x0, #4568]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5000]
	movz x10, #0, lsl #0
	ldr x2, [x0, #4576]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #4584]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #4592]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #4600]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #4608]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #4616]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #4624]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #4632]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x2, [x0, #4640]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5000]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4504]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4512]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4520]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4528]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4536]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4544]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4552]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4560]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4576]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4584]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4592]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4600]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4608]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4616]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4624]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4632]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x2, [x0, #4936]
	ldr x3, [x0, #4944]
	extr x8, x3, x2, #59
	str x8, [x0, #4792]
	ldr x2, [x0, #4944]
	ldr x3, [x0, #4952]
	extr x8, x3, x2, #59
	str x8, [x0, #4800]
	ldr x2, [x0, #4952]
	ldr x3, [x0, #4960]
	extr x8, x3, x2, #59
	str x8, [x0, #4808]
	ldr x2, [x0, #4960]
	ldr x3, [x0, #4968]
	extr x8, x3, x2, #59
	str x8, [x0, #4816]
	ldr x2, [x0, #4968]
	ldr x3, [x0, #4976]
	extr x8, x3, x2, #59
	str x8, [x0, #4824]
	ldr x2, [x0, #4976]
	ldr x3, [x0, #4984]
	extr x8, x3, x2, #59
	str x8, [x0, #4832]
	ldr x2, [x0, #4984]
	ldr x3, [x0, #4992]
	extr x8, x3, x2, #59
	str x8, [x0, #4840]
	ldr x2, [x0, #4992]
	ldr x3, [x0, #5000]
	extr x8, x3, x2, #59
	str x8, [x0, #4848]
	ldr x3, [x0, #5000]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #4856]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #4504]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #4936]
	ldr x2, [x0, #4512]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4944]
	ldr x2, [x0, #4520]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4952]
	ldr x2, [x0, #4528]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4960]
	ldr x2, [x0, #4536]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4968]
	ldr x2, [x0, #4544]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4976]
	ldr x2, [x0, #4552]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4984]
	ldr x2, [x0, #4560]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4992]
	ldr x2, [x0, #4568]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5000]
	movz x10, #0, lsl #0
	ldr x2, [x0, #4576]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #4584]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #4592]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #4600]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #4608]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #4616]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #4624]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #4632]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x2, [x0, #4640]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5000]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4504]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4512]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4520]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4528]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4536]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4544]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4552]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4560]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4576]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4584]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4592]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4600]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4608]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4616]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4624]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4632]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x2, [x0, #4936]
	ldr x3, [x0, #4944]
	extr x8, x3, x2, #59
	str x8, [x0, #4864]
	ldr x2, [x0, #4944]
	ldr x3, [x0, #4952]
	extr x8, x3, x2, #59
	str x8, [x0, #4872]
	ldr x2, [x0, #4952]
	ldr x3, [x0, #4960]
	extr x8, x3, x2, #59
	str x8, [x0, #4880]
	ldr x2, [x0, #4960]
	ldr x3, [x0, #4968]
	extr x8, x3, x2, #59
	str x8, [x0, #4888]
	ldr x2, [x0, #4968]
	ldr x3, [x0, #4976]
	extr x8, x3, x2, #59
	str x8, [x0, #4896]
	ldr x2, [x0, #4976]
	ldr x3, [x0, #4984]
	extr x8, x3, x2, #59
	str x8, [x0, #4904]
	ldr x2, [x0, #4984]
	ldr x3, [x0, #4992]
	extr x8, x3, x2, #59
	str x8, [x0, #4912]
	ldr x2, [x0, #4992]
	ldr x3, [x0, #5000]
	extr x8, x3, x2, #59
	str x8, [x0, #4920]
	ldr x3, [x0, #5000]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #4928]
	ldr x2, [x0, #4792]
	str x2, [x0, #4504]
	ldr x2, [x0, #4800]
	str x2, [x0, #4512]
	ldr x2, [x0, #4808]
	str x2, [x0, #4520]
	ldr x2, [x0, #4816]
	str x2, [x0, #4528]
	ldr x2, [x0, #4824]
	str x2, [x0, #4536]
	ldr x2, [x0, #4832]
	str x2, [x0, #4544]
	ldr x2, [x0, #4840]
	str x2, [x0, #4552]
	ldr x2, [x0, #4848]
	str x2, [x0, #4560]
	ldr x2, [x0, #4856]
	str x2, [x0, #4568]
	ldr x2, [x0, #4864]
	str x2, [x0, #4576]
	ldr x2, [x0, #4872]
	str x2, [x0, #4584]
	ldr x2, [x0, #4880]
	str x2, [x0, #4592]
	ldr x2, [x0, #4888]
	str x2, [x0, #4600]
	ldr x2, [x0, #4896]
	str x2, [x0, #4608]
	ldr x2, [x0, #4904]
	str x2, [x0, #4616]
	ldr x2, [x0, #4912]
	str x2, [x0, #4624]
	ldr x2, [x0, #4920]
	str x2, [x0, #4632]
	ldr x2, [x0, #4928]
	str x2, [x0, #4640]
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #4648]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #4936]
	ldr x2, [x0, #4656]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4944]
	ldr x2, [x0, #4664]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4952]
	ldr x2, [x0, #4672]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4960]
	ldr x2, [x0, #4680]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4968]
	ldr x2, [x0, #4688]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4976]
	ldr x2, [x0, #4696]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4984]
	ldr x2, [x0, #4704]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4992]
	ldr x2, [x0, #4712]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5000]
	movz x10, #0, lsl #0
	ldr x2, [x0, #4720]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #4728]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #4736]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #4744]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #4752]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #4760]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #4768]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #4776]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x2, [x0, #4784]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5000]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4648]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4656]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4664]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4672]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4680]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4688]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4696]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4704]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4720]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4728]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4736]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4744]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4752]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4760]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4768]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4776]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x2, [x0, #4936]
	movz x17, #61381, lsl #0
	movk x17, #32137, lsl #16
	movk x17, #12832, lsl #32
	movk x17, #33691, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #5000]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #5008]
	movz x10, #0, lsl #0
	ldr x2, [x0, #64]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #72]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #80]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #88]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #96]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #104]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #112]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #120]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	adds x3, x3, x10
	str x3, [x0, #5000]
	ldr x3, [x0, #5008]
	adcs x3, x3, x12
	str x3, [x0, #5008]
	ldr x2, [x0, #4944]
	str x2, [x0, #4792]
	ldr x2, [x0, #4952]
	str x2, [x0, #4800]
	ldr x2, [x0, #4960]
	str x2, [x0, #4808]
	ldr x2, [x0, #4968]
	str x2, [x0, #4816]
	ldr x2, [x0, #4976]
	str x2, [x0, #4824]
	ldr x2, [x0, #4984]
	str x2, [x0, #4832]
	ldr x2, [x0, #4992]
	str x2, [x0, #4840]
	ldr x2, [x0, #5000]
	str x2, [x0, #4848]
	ldr x2, [x0, #5008]
	str x2, [x0, #4856]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #4648]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #4936]
	ldr x2, [x0, #4656]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4944]
	ldr x2, [x0, #4664]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4952]
	ldr x2, [x0, #4672]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4960]
	ldr x2, [x0, #4680]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4968]
	ldr x2, [x0, #4688]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4976]
	ldr x2, [x0, #4696]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4984]
	ldr x2, [x0, #4704]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4992]
	ldr x2, [x0, #4712]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5000]
	movz x10, #0, lsl #0
	ldr x2, [x0, #4720]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #4728]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #4736]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #4744]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #4752]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #4760]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #4768]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #4776]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x2, [x0, #4784]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5000]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4648]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4656]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4664]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4672]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4680]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4688]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4696]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4704]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4720]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4728]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4736]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4744]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4752]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4760]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4768]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4776]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x2, [x0, #4936]
	movz x17, #61381, lsl #0
	movk x17, #32137, lsl #16
	movk x17, #12832, lsl #32
	movk x17, #33691, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #5000]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #5008]
	movz x10, #0, lsl #0
	ldr x2, [x0, #64]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #72]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #80]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #88]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #96]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #104]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #112]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #120]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	adds x3, x3, x10
	str x3, [x0, #5000]
	ldr x3, [x0, #5008]
	adcs x3, x3, x12
	str x3, [x0, #5008]
	ldr x2, [x0, #4944]
	str x2, [x0, #4720]
	ldr x2, [x0, #4952]
	str x2, [x0, #4728]
	ldr x2, [x0, #4960]
	str x2, [x0, #4736]
	ldr x2, [x0, #4968]
	str x2, [x0, #4744]
	ldr x2, [x0, #4976]
	str x2, [x0, #4752]
	ldr x2, [x0, #4984]
	str x2, [x0, #4760]
	ldr x2, [x0, #4992]
	str x2, [x0, #4768]
	ldr x2, [x0, #5000]
	str x2, [x0, #4776]
	ldr x2, [x0, #5008]
	str x2, [x0, #4784]
	ldr x2, [x0, #4792]
	str x2, [x0, #4648]
	ldr x2, [x0, #4800]
	str x2, [x0, #4656]
	ldr x2, [x0, #4808]
	str x2, [x0, #4664]
	ldr x2, [x0, #4816]
	str x2, [x0, #4672]
	ldr x2, [x0, #4824]
	str x2, [x0, #4680]
	ldr x2, [x0, #4832]
	str x2, [x0, #4688]
	ldr x2, [x0, #4840]
	str x2, [x0, #4696]
	ldr x2, [x0, #4848]
	str x2, [x0, #4704]
	ldr x2, [x0, #4856]
	str x2, [x0, #4712]
	cbnz x19, 20b
	movz x12, #0, lsl #0
	ldr x3, [x0, #4712]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #4648]
	ldr x2, [x0, #64]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #4648]
	ldr x3, [x0, #4656]
	ldr x2, [x0, #72]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4656]
	ldr x3, [x0, #4664]
	ldr x2, [x0, #80]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4664]
	ldr x3, [x0, #4672]
	ldr x2, [x0, #88]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4672]
	ldr x3, [x0, #4680]
	ldr x2, [x0, #96]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4680]
	ldr x3, [x0, #4688]
	ldr x2, [x0, #104]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4688]
	ldr x3, [x0, #4696]
	ldr x2, [x0, #112]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4696]
	ldr x3, [x0, #4704]
	ldr x2, [x0, #120]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4704]
	ldr x3, [x0, #4712]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #4712]
	ldr x3, [x0, #4648]
	ldr x2, [x0, #64]
	subs x3, x3, x2
	str x3, [x0, #4648]
	ldr x3, [x0, #4656]
	ldr x2, [x0, #72]
	sbcs x3, x3, x2
	str x3, [x0, #4656]
	ldr x3, [x0, #4664]
	ldr x2, [x0, #80]
	sbcs x3, x3, x2
	str x3, [x0, #4664]
	ldr x3, [x0, #4672]
	ldr x2, [x0, #88]
	sbcs x3, x3, x2
	str x3, [x0, #4672]
	ldr x3, [x0, #4680]
	ldr x2, [x0, #96]
	sbcs x3, x3, x2
	str x3, [x0, #4680]
	ldr x3, [x0, #4688]
	ldr x2, [x0, #104]
	sbcs x3, x3, x2
	str x3, [x0, #4688]
	ldr x3, [x0, #4696]
	ldr x2, [x0, #112]
	sbcs x3, x3, x2
	str x3, [x0, #4696]
	ldr x3, [x0, #4704]
	ldr x2, [x0, #120]
	sbcs x3, x3, x2
	str x3, [x0, #4704]
	ldr x3, [x0, #4712]
	add x2, x12, x12
	sbcs x3, x3, x2
	str x3, [x0, #4712]
	ldr x3, [x0, #4712]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #4648]
	ldr x2, [x0, #64]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #4648]
	ldr x3, [x0, #4656]
	ldr x2, [x0, #72]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4656]
	ldr x3, [x0, #4664]
	ldr x2, [x0, #80]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4664]
	ldr x3, [x0, #4672]
	ldr x2, [x0, #88]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4672]
	ldr x3, [x0, #4680]
	ldr x2, [x0, #96]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4680]
	ldr x3, [x0, #4688]
	ldr x2, [x0, #104]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4688]
	ldr x3, [x0, #4696]
	ldr x2, [x0, #112]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4696]
	ldr x3, [x0, #4704]
	ldr x2, [x0, #120]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4704]
	ldr x3, [x0, #4712]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #4712]
	movz x12, #0, lsl #0
	ldr x3, [x0, #4504]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #34685, lsl #0
	movk x2, #44018, lsl #16
	movk x2, #38156, lsl #32
	movk x2, #6656, lsl #48
	movz x3, #49526, lsl #0
	movk x3, #44103, lsl #16
	movk x3, #52041, lsl #32
	movk x3, #3753, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4792]
	movz x2, #39275, lsl #0
	movk x2, #40930, lsl #16
	movk x2, #7840, lsl #32
	movk x2, #21676, lsl #48
	movz x3, #11546, lsl #0
	movk x3, #36256, lsl #16
	movk x3, #57486, lsl #32
	movk x3, #54229, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4800]
	movz x2, #23347, lsl #0
	movk x2, #1907, lsl #16
	movk x2, #57135, lsl #32
	movk x2, #56016, lsl #48
	movz x3, #9650, lsl #0
	movk x3, #57136, lsl #16
	movk x3, #49659, lsl #32
	movk x3, #54268, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4808]
	movz x2, #38788, lsl #0
	movk x2, #3175, lsl #16
	movk x2, #35369, lsl #32
	movk x2, #9503, lsl #48
	movz x3, #53437, lsl #0
	movk x3, #36702, lsl #16
	movk x3, #4311, lsl #32
	movk x3, #22574, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4816]
	movz x2, #33548, lsl #0
	movk x2, #60585, lsl #16
	movk x2, #9257, lsl #32
	movk x2, #15685, lsl #48
	movz x3, #34149, lsl #0
	movk x3, #33673, lsl #16
	movk x3, #30880, lsl #32
	movk x3, #39198, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4824]
	movz x2, #33545, lsl #0
	movk x2, #27792, lsl #16
	movk x2, #20903, lsl #32
	movk x2, #8287, lsl #48
	movz x3, #20229, lsl #0
	movk x3, #18233, lsl #16
	movk x3, #15372, lsl #32
	movk x3, #43729, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4832]
	movz x2, #32088, lsl #0
	movk x2, #4946, lsl #16
	movk x2, #65180, lsl #32
	movk x2, #20363, lsl #48
	movz x3, #32431, lsl #0
	movk x3, #8311, lsl #16
	movk x3, #59410, lsl #32
	movk x3, #61512, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4840]
	movz x2, #15631, lsl #0
	movk x2, #1530, lsl #16
	movk x2, #52069, lsl #32
	movk x2, #9061, lsl #48
	movz x3, #34683, lsl #0
	movk x3, #54767, lsl #16
	movk x3, #53843, lsl #32
	movk x3, #34679, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4848]
	movz x7, #0, lsl #0
	ldr x4, [x0, #4792]
	ldr x5, [x0, #4800]
	ldr x16, [x0, #4808]
	ldr x17, [x0, #4816]
	movz x6, #61381, lsl #0
	movk x6, #32137, lsl #16
	movk x6, #12832, lsl #32
	movk x6, #33691, lsl #48
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x21, #0, lsl #0
	movz x22, #0, lsl #0
	ldr x1, [x0, #4648]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x21, x21, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x21, x21, x7
	mul x1, x8, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x21, x21, x7
	adcs x22, x22, x7
	ldr x1, [x0, #4656]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x22, x22, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	mul x1, x9, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x8, x8, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	adcs x8, x8, x7
	ldr x1, [x0, #4664]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #4672]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x1, [x0, #4680]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x21, x21, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	mul x1, x12, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x1, [x0, #4688]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x21, x21, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x11, x11, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x21, x21, x2
	umulh x2, x1, x17
	adcs x22, x22, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	mul x1, x13, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x14, x14, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	ldr x1, [x0, #4696]
	mul x2, x1, x4
	adds x14, x14, x2
	mul x2, x1, x5
	adcs x15, x15, x2
	mul x2, x1, x16
	adcs x21, x21, x2
	mul x2, x1, x17
	adcs x22, x22, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x12, x12, x2
	umulh x2, x1, x4
	adds x15, x15, x2
	umulh x2, x1, x5
	adcs x21, x21, x2
	umulh x2, x1, x16
	adcs x22, x22, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	mul x1, x14, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x14, x14, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x15, x15, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #4704]
	mul x2, x1, x4
	adds x15, x15, x2
	mul x2, x1, x5
	adcs x21, x21, x2
	mul x2, x1, x16
	adcs x22, x22, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x21, x21, x2
	umulh x2, x1, x5
	adcs x22, x22, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x15, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x15, x15, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x21, x21, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x14, x14, x7
	ldr x2, [x0, #64]
	subs x1, x21, x2
	ldr x2, [x0, #72]
	sbcs x3, x22, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	ldr x2, [x0, #96]
	sbcs x6, x10, x2
	ldr x2, [x0, #104]
	sbcs x16, x11, x2
	ldr x2, [x0, #112]
	sbcs x17, x12, x2
	ldr x2, [x0, #120]
	sbcs x24, x13, x2
	sbcs x2, x14, x7
	csel x21, x1, x21, hs
	csel x22, x3, x22, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	csel x11, x16, x11, hs
	csel x12, x17, x12, hs
	csel x13, x24, x13, hs
	str x21, [x0, #1920]
	str x22, [x0, #1928]
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	ldr x19, [x0, #5080]
	ldr x21, [x0, #5088]
	ldr x22, [x0, #5096]
	ldr x23, [x0, #5104]
	ldr x24, [x0, #5112]
	ldr x25, [x0, #5120]
	ret
	.p2align 6

vg_brainpoolp512r1_inv_mod_n:
	str x19, [x0, #5080]
	str x21, [x0, #5088]
	str x22, [x0, #5096]
	str x23, [x0, #5104]
	str x24, [x0, #5112]
	str x25, [x0, #5120]
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #23, lsl #0
	ldr x2, [x0, #128]
	str x2, [x0, #4504]
	ldr x2, [x0, #136]
	str x2, [x0, #4512]
	ldr x2, [x0, #144]
	str x2, [x0, #4520]
	ldr x2, [x0, #152]
	str x2, [x0, #4528]
	ldr x2, [x0, #160]
	str x2, [x0, #4536]
	ldr x2, [x0, #168]
	str x2, [x0, #4544]
	ldr x2, [x0, #176]
	str x2, [x0, #4552]
	ldr x2, [x0, #184]
	str x2, [x0, #4560]
	str x12, [x0, #4568]
	ldr x2, [x0, #2432]
	str x2, [x0, #4576]
	ldr x2, [x0, #2440]
	str x2, [x0, #4584]
	ldr x2, [x0, #2448]
	str x2, [x0, #4592]
	ldr x2, [x0, #2456]
	str x2, [x0, #4600]
	ldr x2, [x0, #2464]
	str x2, [x0, #4608]
	ldr x2, [x0, #2472]
	str x2, [x0, #4616]
	ldr x2, [x0, #2480]
	str x2, [x0, #4624]
	ldr x2, [x0, #2488]
	str x2, [x0, #4632]
	str x12, [x0, #4640]
	str x12, [x0, #4648]
	str x12, [x0, #4656]
	str x12, [x0, #4664]
	str x12, [x0, #4672]
	str x12, [x0, #4680]
	str x12, [x0, #4688]
	str x12, [x0, #4696]
	str x12, [x0, #4704]
	str x12, [x0, #4712]
	str x12, [x0, #4720]
	str x12, [x0, #4728]
	str x12, [x0, #4736]
	str x12, [x0, #4744]
	str x12, [x0, #4752]
	str x12, [x0, #4760]
	str x12, [x0, #4768]
	str x12, [x0, #4776]
	str x12, [x0, #4784]
	str x11, [x0, #4720]
20:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #4504]
	ldr x3, [x0, #4576]
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #1, lsl #0
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x12, #0, lsl #0
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #4504]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #4936]
	ldr x2, [x0, #4512]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4944]
	ldr x2, [x0, #4520]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4952]
	ldr x2, [x0, #4528]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4960]
	ldr x2, [x0, #4536]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4968]
	ldr x2, [x0, #4544]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4976]
	ldr x2, [x0, #4552]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4984]
	ldr x2, [x0, #4560]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4992]
	ldr x2, [x0, #4568]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5000]
	movz x10, #0, lsl #0
	ldr x2, [x0, #4576]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #4584]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #4592]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #4600]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #4608]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #4616]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #4624]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #4632]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x2, [x0, #4640]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5000]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4504]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4512]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4520]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4528]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4536]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4544]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4552]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4560]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4576]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4584]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4592]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4600]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4608]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4616]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4624]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4632]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x2, [x0, #4936]
	ldr x3, [x0, #4944]
	extr x8, x3, x2, #59
	str x8, [x0, #4792]
	ldr x2, [x0, #4944]
	ldr x3, [x0, #4952]
	extr x8, x3, x2, #59
	str x8, [x0, #4800]
	ldr x2, [x0, #4952]
	ldr x3, [x0, #4960]
	extr x8, x3, x2, #59
	str x8, [x0, #4808]
	ldr x2, [x0, #4960]
	ldr x3, [x0, #4968]
	extr x8, x3, x2, #59
	str x8, [x0, #4816]
	ldr x2, [x0, #4968]
	ldr x3, [x0, #4976]
	extr x8, x3, x2, #59
	str x8, [x0, #4824]
	ldr x2, [x0, #4976]
	ldr x3, [x0, #4984]
	extr x8, x3, x2, #59
	str x8, [x0, #4832]
	ldr x2, [x0, #4984]
	ldr x3, [x0, #4992]
	extr x8, x3, x2, #59
	str x8, [x0, #4840]
	ldr x2, [x0, #4992]
	ldr x3, [x0, #5000]
	extr x8, x3, x2, #59
	str x8, [x0, #4848]
	ldr x3, [x0, #5000]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #4856]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #4504]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #4936]
	ldr x2, [x0, #4512]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4944]
	ldr x2, [x0, #4520]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4952]
	ldr x2, [x0, #4528]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4960]
	ldr x2, [x0, #4536]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4968]
	ldr x2, [x0, #4544]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4976]
	ldr x2, [x0, #4552]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4984]
	ldr x2, [x0, #4560]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4992]
	ldr x2, [x0, #4568]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5000]
	movz x10, #0, lsl #0
	ldr x2, [x0, #4576]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #4584]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #4592]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #4600]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #4608]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #4616]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #4624]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #4632]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x2, [x0, #4640]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5000]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4504]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4512]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4520]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4528]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4536]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4544]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4552]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4560]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4576]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4584]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4592]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4600]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4608]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4616]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4624]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4632]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x2, [x0, #4936]
	ldr x3, [x0, #4944]
	extr x8, x3, x2, #59
	str x8, [x0, #4864]
	ldr x2, [x0, #4944]
	ldr x3, [x0, #4952]
	extr x8, x3, x2, #59
	str x8, [x0, #4872]
	ldr x2, [x0, #4952]
	ldr x3, [x0, #4960]
	extr x8, x3, x2, #59
	str x8, [x0, #4880]
	ldr x2, [x0, #4960]
	ldr x3, [x0, #4968]
	extr x8, x3, x2, #59
	str x8, [x0, #4888]
	ldr x2, [x0, #4968]
	ldr x3, [x0, #4976]
	extr x8, x3, x2, #59
	str x8, [x0, #4896]
	ldr x2, [x0, #4976]
	ldr x3, [x0, #4984]
	extr x8, x3, x2, #59
	str x8, [x0, #4904]
	ldr x2, [x0, #4984]
	ldr x3, [x0, #4992]
	extr x8, x3, x2, #59
	str x8, [x0, #4912]
	ldr x2, [x0, #4992]
	ldr x3, [x0, #5000]
	extr x8, x3, x2, #59
	str x8, [x0, #4920]
	ldr x3, [x0, #5000]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #4928]
	ldr x2, [x0, #4792]
	str x2, [x0, #4504]
	ldr x2, [x0, #4800]
	str x2, [x0, #4512]
	ldr x2, [x0, #4808]
	str x2, [x0, #4520]
	ldr x2, [x0, #4816]
	str x2, [x0, #4528]
	ldr x2, [x0, #4824]
	str x2, [x0, #4536]
	ldr x2, [x0, #4832]
	str x2, [x0, #4544]
	ldr x2, [x0, #4840]
	str x2, [x0, #4552]
	ldr x2, [x0, #4848]
	str x2, [x0, #4560]
	ldr x2, [x0, #4856]
	str x2, [x0, #4568]
	ldr x2, [x0, #4864]
	str x2, [x0, #4576]
	ldr x2, [x0, #4872]
	str x2, [x0, #4584]
	ldr x2, [x0, #4880]
	str x2, [x0, #4592]
	ldr x2, [x0, #4888]
	str x2, [x0, #4600]
	ldr x2, [x0, #4896]
	str x2, [x0, #4608]
	ldr x2, [x0, #4904]
	str x2, [x0, #4616]
	ldr x2, [x0, #4912]
	str x2, [x0, #4624]
	ldr x2, [x0, #4920]
	str x2, [x0, #4632]
	ldr x2, [x0, #4928]
	str x2, [x0, #4640]
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #4648]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #4936]
	ldr x2, [x0, #4656]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4944]
	ldr x2, [x0, #4664]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4952]
	ldr x2, [x0, #4672]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4960]
	ldr x2, [x0, #4680]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4968]
	ldr x2, [x0, #4688]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4976]
	ldr x2, [x0, #4696]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4984]
	ldr x2, [x0, #4704]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4992]
	ldr x2, [x0, #4712]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5000]
	movz x10, #0, lsl #0
	ldr x2, [x0, #4720]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #4728]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #4736]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #4744]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #4752]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #4760]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #4768]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #4776]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x2, [x0, #4784]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5000]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4648]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4656]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4664]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4672]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4680]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4688]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4696]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4704]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4720]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4728]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4736]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4744]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4752]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4760]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4768]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4776]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x2, [x0, #4936]
	movz x17, #28711, lsl #0
	movk x17, #3867, lsl #16
	movk x17, #21535, lsl #32
	movk x17, #44361, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #5000]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #5008]
	movz x10, #0, lsl #0
	ldr x2, [x0, #128]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #136]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #144]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #152]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #160]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #168]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #176]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #184]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	adds x3, x3, x10
	str x3, [x0, #5000]
	ldr x3, [x0, #5008]
	adcs x3, x3, x12
	str x3, [x0, #5008]
	ldr x2, [x0, #4944]
	str x2, [x0, #4792]
	ldr x2, [x0, #4952]
	str x2, [x0, #4800]
	ldr x2, [x0, #4960]
	str x2, [x0, #4808]
	ldr x2, [x0, #4968]
	str x2, [x0, #4816]
	ldr x2, [x0, #4976]
	str x2, [x0, #4824]
	ldr x2, [x0, #4984]
	str x2, [x0, #4832]
	ldr x2, [x0, #4992]
	str x2, [x0, #4840]
	ldr x2, [x0, #5000]
	str x2, [x0, #4848]
	ldr x2, [x0, #5008]
	str x2, [x0, #4856]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #4648]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #4936]
	ldr x2, [x0, #4656]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4944]
	ldr x2, [x0, #4664]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4952]
	ldr x2, [x0, #4672]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4960]
	ldr x2, [x0, #4680]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4968]
	ldr x2, [x0, #4688]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4976]
	ldr x2, [x0, #4696]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4984]
	ldr x2, [x0, #4704]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #4992]
	ldr x2, [x0, #4712]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5000]
	movz x10, #0, lsl #0
	ldr x2, [x0, #4720]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #4728]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #4736]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #4744]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #4752]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #4760]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #4768]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #4776]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x2, [x0, #4784]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5000]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4648]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4656]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4664]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4672]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4680]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4688]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4696]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4704]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x3, [x0, #4944]
	ldr x2, [x0, #4720]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #4944]
	ldr x3, [x0, #4952]
	ldr x2, [x0, #4728]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4952]
	ldr x3, [x0, #4960]
	ldr x2, [x0, #4736]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4960]
	ldr x3, [x0, #4968]
	ldr x2, [x0, #4744]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4968]
	ldr x3, [x0, #4976]
	ldr x2, [x0, #4752]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4976]
	ldr x3, [x0, #4984]
	ldr x2, [x0, #4760]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4984]
	ldr x3, [x0, #4992]
	ldr x2, [x0, #4768]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	ldr x2, [x0, #4776]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5000]
	ldr x2, [x0, #4936]
	movz x17, #28711, lsl #0
	movk x17, #3867, lsl #16
	movk x17, #21535, lsl #32
	movk x17, #44361, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #5000]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #5008]
	movz x10, #0, lsl #0
	ldr x2, [x0, #128]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4936]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4936]
	ldr x2, [x0, #136]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4944]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4944]
	ldr x2, [x0, #144]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4952]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4952]
	ldr x2, [x0, #152]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4960]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4960]
	ldr x2, [x0, #160]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4968]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4968]
	ldr x2, [x0, #168]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4976]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4976]
	ldr x2, [x0, #176]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4984]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4984]
	ldr x2, [x0, #184]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #4992]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #4992]
	ldr x3, [x0, #5000]
	adds x3, x3, x10
	str x3, [x0, #5000]
	ldr x3, [x0, #5008]
	adcs x3, x3, x12
	str x3, [x0, #5008]
	ldr x2, [x0, #4944]
	str x2, [x0, #4720]
	ldr x2, [x0, #4952]
	str x2, [x0, #4728]
	ldr x2, [x0, #4960]
	str x2, [x0, #4736]
	ldr x2, [x0, #4968]
	str x2, [x0, #4744]
	ldr x2, [x0, #4976]
	str x2, [x0, #4752]
	ldr x2, [x0, #4984]
	str x2, [x0, #4760]
	ldr x2, [x0, #4992]
	str x2, [x0, #4768]
	ldr x2, [x0, #5000]
	str x2, [x0, #4776]
	ldr x2, [x0, #5008]
	str x2, [x0, #4784]
	ldr x2, [x0, #4792]
	str x2, [x0, #4648]
	ldr x2, [x0, #4800]
	str x2, [x0, #4656]
	ldr x2, [x0, #4808]
	str x2, [x0, #4664]
	ldr x2, [x0, #4816]
	str x2, [x0, #4672]
	ldr x2, [x0, #4824]
	str x2, [x0, #4680]
	ldr x2, [x0, #4832]
	str x2, [x0, #4688]
	ldr x2, [x0, #4840]
	str x2, [x0, #4696]
	ldr x2, [x0, #4848]
	str x2, [x0, #4704]
	ldr x2, [x0, #4856]
	str x2, [x0, #4712]
	cbnz x19, 20b
	movz x12, #0, lsl #0
	ldr x3, [x0, #4712]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #4648]
	ldr x2, [x0, #128]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #4648]
	ldr x3, [x0, #4656]
	ldr x2, [x0, #136]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4656]
	ldr x3, [x0, #4664]
	ldr x2, [x0, #144]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4664]
	ldr x3, [x0, #4672]
	ldr x2, [x0, #152]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4672]
	ldr x3, [x0, #4680]
	ldr x2, [x0, #160]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4680]
	ldr x3, [x0, #4688]
	ldr x2, [x0, #168]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4688]
	ldr x3, [x0, #4696]
	ldr x2, [x0, #176]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4696]
	ldr x3, [x0, #4704]
	ldr x2, [x0, #184]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4704]
	ldr x3, [x0, #4712]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #4712]
	ldr x3, [x0, #4648]
	ldr x2, [x0, #128]
	subs x3, x3, x2
	str x3, [x0, #4648]
	ldr x3, [x0, #4656]
	ldr x2, [x0, #136]
	sbcs x3, x3, x2
	str x3, [x0, #4656]
	ldr x3, [x0, #4664]
	ldr x2, [x0, #144]
	sbcs x3, x3, x2
	str x3, [x0, #4664]
	ldr x3, [x0, #4672]
	ldr x2, [x0, #152]
	sbcs x3, x3, x2
	str x3, [x0, #4672]
	ldr x3, [x0, #4680]
	ldr x2, [x0, #160]
	sbcs x3, x3, x2
	str x3, [x0, #4680]
	ldr x3, [x0, #4688]
	ldr x2, [x0, #168]
	sbcs x3, x3, x2
	str x3, [x0, #4688]
	ldr x3, [x0, #4696]
	ldr x2, [x0, #176]
	sbcs x3, x3, x2
	str x3, [x0, #4696]
	ldr x3, [x0, #4704]
	ldr x2, [x0, #184]
	sbcs x3, x3, x2
	str x3, [x0, #4704]
	ldr x3, [x0, #4712]
	add x2, x12, x12
	sbcs x3, x3, x2
	str x3, [x0, #4712]
	ldr x3, [x0, #4712]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #4648]
	ldr x2, [x0, #128]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #4648]
	ldr x3, [x0, #4656]
	ldr x2, [x0, #136]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4656]
	ldr x3, [x0, #4664]
	ldr x2, [x0, #144]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4664]
	ldr x3, [x0, #4672]
	ldr x2, [x0, #152]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4672]
	ldr x3, [x0, #4680]
	ldr x2, [x0, #160]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4680]
	ldr x3, [x0, #4688]
	ldr x2, [x0, #168]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4688]
	ldr x3, [x0, #4696]
	ldr x2, [x0, #176]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4696]
	ldr x3, [x0, #4704]
	ldr x2, [x0, #184]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #4704]
	ldr x3, [x0, #4712]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #4712]
	movz x12, #0, lsl #0
	ldr x3, [x0, #4504]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #3770, lsl #0
	movk x2, #44615, lsl #16
	movk x2, #13182, lsl #32
	movk x2, #32561, lsl #48
	movz x3, #61871, lsl #0
	movk x3, #61025, lsl #16
	movk x3, #25347, lsl #32
	movk x3, #13910, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4792]
	movz x2, #14320, lsl #0
	movk x2, #12019, lsl #16
	movk x2, #37910, lsl #32
	movk x2, #26436, lsl #48
	movz x3, #41709, lsl #0
	movk x3, #55658, lsl #16
	movk x3, #16234, lsl #32
	movk x3, #46701, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4800]
	movz x2, #46375, lsl #0
	movk x2, #7697, lsl #16
	movk x2, #18598, lsl #32
	movk x2, #37747, lsl #48
	movz x3, #23327, lsl #0
	movk x3, #24986, lsl #16
	movk x3, #6259, lsl #32
	movk x3, #44563, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4808]
	movz x2, #36888, lsl #0
	movk x2, #55242, lsl #16
	movk x2, #29638, lsl #32
	movk x2, #50868, lsl #48
	movz x3, #38400, lsl #0
	movk x3, #29918, lsl #16
	movk x3, #59514, lsl #32
	movk x3, #36489, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4816]
	movz x2, #58404, lsl #0
	movk x2, #63910, lsl #16
	movk x2, #7585, lsl #32
	movk x2, #25393, lsl #48
	movz x3, #9291, lsl #0
	movk x3, #30348, lsl #16
	movk x3, #32552, lsl #32
	movk x3, #29490, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4824]
	movz x2, #58339, lsl #0
	movk x2, #17515, lsl #16
	movk x2, #14601, lsl #32
	movk x2, #36291, lsl #48
	movz x3, #60971, lsl #0
	movk x3, #28509, lsl #16
	movk x3, #21674, lsl #32
	movk x3, #15725, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4832]
	movz x2, #4872, lsl #0
	movk x2, #12418, lsl #16
	movk x2, #60170, lsl #32
	movk x2, #35661, lsl #48
	movz x3, #59647, lsl #0
	movk x3, #839, lsl #16
	movk x3, #64420, lsl #32
	movk x3, #46214, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4840]
	movz x2, #13920, lsl #0
	movk x2, #53987, lsl #16
	movk x2, #27569, lsl #32
	movk x2, #25397, lsl #48
	movz x3, #36394, lsl #0
	movk x3, #2310, lsl #16
	movk x3, #12807, lsl #32
	movk x3, #18344, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #4848]
	movz x7, #0, lsl #0
	ldr x4, [x0, #4792]
	ldr x5, [x0, #4800]
	ldr x16, [x0, #4808]
	ldr x17, [x0, #4816]
	movz x6, #28711, lsl #0
	movk x6, #3867, lsl #16
	movk x6, #21535, lsl #32
	movk x6, #44361, lsl #48
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x21, #0, lsl #0
	movz x22, #0, lsl #0
	ldr x1, [x0, #4648]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x21, x21, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x21, x21, x7
	mul x1, x8, x6
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x21, x21, x7
	adcs x22, x22, x7
	ldr x1, [x0, #4656]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x22, x22, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	mul x1, x9, x6
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x8, x8, x7
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	adcs x8, x8, x7
	ldr x1, [x0, #4664]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #4672]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x1, [x0, #4680]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x21, x21, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	mul x1, x12, x6
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x1, [x0, #4688]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x21, x21, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x11, x11, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x21, x21, x2
	umulh x2, x1, x17
	adcs x22, x22, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	mul x1, x13, x6
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adds x14, x14, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	ldr x1, [x0, #4696]
	mul x2, x1, x4
	adds x14, x14, x2
	mul x2, x1, x5
	adcs x15, x15, x2
	mul x2, x1, x16
	adcs x21, x21, x2
	mul x2, x1, x17
	adcs x22, x22, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x12, x12, x2
	umulh x2, x1, x4
	adds x15, x15, x2
	umulh x2, x1, x5
	adcs x21, x21, x2
	umulh x2, x1, x16
	adcs x22, x22, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	mul x1, x14, x6
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adds x14, x14, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adds x15, x15, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #4704]
	mul x2, x1, x4
	adds x15, x15, x2
	mul x2, x1, x5
	adcs x21, x21, x2
	mul x2, x1, x16
	adcs x22, x22, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #4824]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4832]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4840]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4848]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4848]
	umulh x2, x1, x3
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x21, x21, x2
	umulh x2, x1, x5
	adcs x22, x22, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	ldr x3, [x0, #4824]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4832]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4840]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x15, x6
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adds x15, x15, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adds x21, x21, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x14, x14, x7
	ldr x2, [x0, #128]
	subs x1, x21, x2
	ldr x2, [x0, #136]
	sbcs x3, x22, x2
	ldr x2, [x0, #144]
	sbcs x4, x8, x2
	ldr x2, [x0, #152]
	sbcs x5, x9, x2
	ldr x2, [x0, #160]
	sbcs x6, x10, x2
	ldr x2, [x0, #168]
	sbcs x16, x11, x2
	ldr x2, [x0, #176]
	sbcs x17, x12, x2
	ldr x2, [x0, #184]
	sbcs x24, x13, x2
	sbcs x2, x14, x7
	csel x21, x1, x21, hs
	csel x22, x3, x22, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	csel x11, x16, x11, hs
	csel x12, x17, x12, hs
	csel x13, x24, x13, hs
	str x21, [x0, #1920]
	str x22, [x0, #1928]
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	ldr x19, [x0, #5080]
	ldr x21, [x0, #5088]
	ldr x22, [x0, #5096]
	ldr x23, [x0, #5104]
	ldr x24, [x0, #5112]
	ldr x25, [x0, #5120]
	ret
	.p2align 6
