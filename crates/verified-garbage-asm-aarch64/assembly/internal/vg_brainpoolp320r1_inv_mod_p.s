// The functions of `src/internal/vg_brainpoolp320r1_inv_mod_p.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_inv_mod_p:
	str x19, [x0, #3208]
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #15, lsl #0
	ldr x2, [x0, #64]
	str x2, [x0, #2848]
	ldr x2, [x0, #72]
	str x2, [x0, #2856]
	ldr x2, [x0, #80]
	str x2, [x0, #2864]
	ldr x2, [x0, #88]
	str x2, [x0, #2872]
	ldr x2, [x0, #96]
	str x2, [x0, #2880]
	str x12, [x0, #2888]
	ldr x2, [x0, #704]
	str x2, [x0, #2896]
	ldr x2, [x0, #712]
	str x2, [x0, #2904]
	ldr x2, [x0, #720]
	str x2, [x0, #2912]
	ldr x2, [x0, #728]
	str x2, [x0, #2920]
	ldr x2, [x0, #736]
	str x2, [x0, #2928]
	str x12, [x0, #2936]
	str x12, [x0, #2944]
	str x12, [x0, #2952]
	str x12, [x0, #2960]
	str x12, [x0, #2968]
	str x12, [x0, #2976]
	str x12, [x0, #2984]
	str x12, [x0, #2992]
	str x12, [x0, #3000]
	str x12, [x0, #3008]
	str x12, [x0, #3016]
	str x12, [x0, #3024]
	str x12, [x0, #3032]
	str x11, [x0, #2992]
20:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #2848]
	ldr x3, [x0, #2896]
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
	ldr x2, [x0, #2848]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #3136]
	ldr x2, [x0, #2856]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3144]
	ldr x2, [x0, #2864]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3152]
	ldr x2, [x0, #2872]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3160]
	ldr x2, [x0, #2880]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3168]
	ldr x2, [x0, #2888]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3176]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2896]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3136]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3136]
	ldr x2, [x0, #2904]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3144]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3144]
	ldr x2, [x0, #2912]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3152]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3152]
	ldr x2, [x0, #2920]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3160]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3160]
	ldr x2, [x0, #2928]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3168]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3168]
	ldr x2, [x0, #2936]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3176]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3176]
	ldr x3, [x0, #3144]
	ldr x2, [x0, #2848]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #3144]
	ldr x3, [x0, #3152]
	ldr x2, [x0, #2856]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3152]
	ldr x3, [x0, #3160]
	ldr x2, [x0, #2864]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3160]
	ldr x3, [x0, #3168]
	ldr x2, [x0, #2872]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	ldr x2, [x0, #2880]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3176]
	ldr x3, [x0, #3144]
	ldr x2, [x0, #2896]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #3144]
	ldr x3, [x0, #3152]
	ldr x2, [x0, #2904]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3152]
	ldr x3, [x0, #3160]
	ldr x2, [x0, #2912]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3160]
	ldr x3, [x0, #3168]
	ldr x2, [x0, #2920]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	ldr x2, [x0, #2928]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3176]
	ldr x2, [x0, #3136]
	ldr x3, [x0, #3144]
	extr x8, x3, x2, #59
	str x8, [x0, #3040]
	ldr x2, [x0, #3144]
	ldr x3, [x0, #3152]
	extr x8, x3, x2, #59
	str x8, [x0, #3048]
	ldr x2, [x0, #3152]
	ldr x3, [x0, #3160]
	extr x8, x3, x2, #59
	str x8, [x0, #3056]
	ldr x2, [x0, #3160]
	ldr x3, [x0, #3168]
	extr x8, x3, x2, #59
	str x8, [x0, #3064]
	ldr x2, [x0, #3168]
	ldr x3, [x0, #3176]
	extr x8, x3, x2, #59
	str x8, [x0, #3072]
	ldr x3, [x0, #3176]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #3080]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #2848]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #3136]
	ldr x2, [x0, #2856]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3144]
	ldr x2, [x0, #2864]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3152]
	ldr x2, [x0, #2872]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3160]
	ldr x2, [x0, #2880]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3168]
	ldr x2, [x0, #2888]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3176]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2896]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3136]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3136]
	ldr x2, [x0, #2904]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3144]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3144]
	ldr x2, [x0, #2912]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3152]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3152]
	ldr x2, [x0, #2920]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3160]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3160]
	ldr x2, [x0, #2928]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3168]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3168]
	ldr x2, [x0, #2936]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3176]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3176]
	ldr x3, [x0, #3144]
	ldr x2, [x0, #2848]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #3144]
	ldr x3, [x0, #3152]
	ldr x2, [x0, #2856]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3152]
	ldr x3, [x0, #3160]
	ldr x2, [x0, #2864]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3160]
	ldr x3, [x0, #3168]
	ldr x2, [x0, #2872]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	ldr x2, [x0, #2880]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3176]
	ldr x3, [x0, #3144]
	ldr x2, [x0, #2896]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #3144]
	ldr x3, [x0, #3152]
	ldr x2, [x0, #2904]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3152]
	ldr x3, [x0, #3160]
	ldr x2, [x0, #2912]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3160]
	ldr x3, [x0, #3168]
	ldr x2, [x0, #2920]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	ldr x2, [x0, #2928]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3176]
	ldr x2, [x0, #3136]
	ldr x3, [x0, #3144]
	extr x8, x3, x2, #59
	str x8, [x0, #3088]
	ldr x2, [x0, #3144]
	ldr x3, [x0, #3152]
	extr x8, x3, x2, #59
	str x8, [x0, #3096]
	ldr x2, [x0, #3152]
	ldr x3, [x0, #3160]
	extr x8, x3, x2, #59
	str x8, [x0, #3104]
	ldr x2, [x0, #3160]
	ldr x3, [x0, #3168]
	extr x8, x3, x2, #59
	str x8, [x0, #3112]
	ldr x2, [x0, #3168]
	ldr x3, [x0, #3176]
	extr x8, x3, x2, #59
	str x8, [x0, #3120]
	ldr x3, [x0, #3176]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #3128]
	ldr x2, [x0, #3040]
	str x2, [x0, #2848]
	ldr x2, [x0, #3048]
	str x2, [x0, #2856]
	ldr x2, [x0, #3056]
	str x2, [x0, #2864]
	ldr x2, [x0, #3064]
	str x2, [x0, #2872]
	ldr x2, [x0, #3072]
	str x2, [x0, #2880]
	ldr x2, [x0, #3080]
	str x2, [x0, #2888]
	ldr x2, [x0, #3088]
	str x2, [x0, #2896]
	ldr x2, [x0, #3096]
	str x2, [x0, #2904]
	ldr x2, [x0, #3104]
	str x2, [x0, #2912]
	ldr x2, [x0, #3112]
	str x2, [x0, #2920]
	ldr x2, [x0, #3120]
	str x2, [x0, #2928]
	ldr x2, [x0, #3128]
	str x2, [x0, #2936]
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #2944]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #3136]
	ldr x2, [x0, #2952]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3144]
	ldr x2, [x0, #2960]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3152]
	ldr x2, [x0, #2968]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3160]
	ldr x2, [x0, #2976]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3168]
	ldr x2, [x0, #2984]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3176]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2992]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3136]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3136]
	ldr x2, [x0, #3000]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3144]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3144]
	ldr x2, [x0, #3008]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3152]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3152]
	ldr x2, [x0, #3016]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3160]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3160]
	ldr x2, [x0, #3024]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3168]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3168]
	ldr x2, [x0, #3032]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3176]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3176]
	ldr x3, [x0, #3144]
	ldr x2, [x0, #2944]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #3144]
	ldr x3, [x0, #3152]
	ldr x2, [x0, #2952]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3152]
	ldr x3, [x0, #3160]
	ldr x2, [x0, #2960]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3160]
	ldr x3, [x0, #3168]
	ldr x2, [x0, #2968]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	ldr x2, [x0, #2976]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3176]
	ldr x3, [x0, #3144]
	ldr x2, [x0, #2992]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #3144]
	ldr x3, [x0, #3152]
	ldr x2, [x0, #3000]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3152]
	ldr x3, [x0, #3160]
	ldr x2, [x0, #3008]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3160]
	ldr x3, [x0, #3168]
	ldr x2, [x0, #3016]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	ldr x2, [x0, #3024]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3176]
	ldr x2, [x0, #3136]
	movz x17, #40553, lsl #0
	movk x17, #10890, lsl #16
	movk x17, #39842, lsl #32
	movk x17, #15646, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #3176]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #3184]
	movz x10, #0, lsl #0
	ldr x2, [x0, #64]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3136]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3136]
	ldr x2, [x0, #72]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3144]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3144]
	ldr x2, [x0, #80]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3152]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3152]
	ldr x2, [x0, #88]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3160]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3160]
	ldr x2, [x0, #96]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3168]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	adds x3, x3, x10
	str x3, [x0, #3176]
	ldr x3, [x0, #3184]
	adcs x3, x3, x12
	str x3, [x0, #3184]
	ldr x2, [x0, #3144]
	str x2, [x0, #3040]
	ldr x2, [x0, #3152]
	str x2, [x0, #3048]
	ldr x2, [x0, #3160]
	str x2, [x0, #3056]
	ldr x2, [x0, #3168]
	str x2, [x0, #3064]
	ldr x2, [x0, #3176]
	str x2, [x0, #3072]
	ldr x2, [x0, #3184]
	str x2, [x0, #3080]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #2944]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #3136]
	ldr x2, [x0, #2952]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3144]
	ldr x2, [x0, #2960]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3152]
	ldr x2, [x0, #2968]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3160]
	ldr x2, [x0, #2976]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3168]
	ldr x2, [x0, #2984]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3176]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2992]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3136]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3136]
	ldr x2, [x0, #3000]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3144]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3144]
	ldr x2, [x0, #3008]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3152]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3152]
	ldr x2, [x0, #3016]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3160]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3160]
	ldr x2, [x0, #3024]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3168]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3168]
	ldr x2, [x0, #3032]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3176]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3176]
	ldr x3, [x0, #3144]
	ldr x2, [x0, #2944]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #3144]
	ldr x3, [x0, #3152]
	ldr x2, [x0, #2952]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3152]
	ldr x3, [x0, #3160]
	ldr x2, [x0, #2960]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3160]
	ldr x3, [x0, #3168]
	ldr x2, [x0, #2968]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	ldr x2, [x0, #2976]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3176]
	ldr x3, [x0, #3144]
	ldr x2, [x0, #2992]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #3144]
	ldr x3, [x0, #3152]
	ldr x2, [x0, #3000]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3152]
	ldr x3, [x0, #3160]
	ldr x2, [x0, #3008]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3160]
	ldr x3, [x0, #3168]
	ldr x2, [x0, #3016]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	ldr x2, [x0, #3024]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3176]
	ldr x2, [x0, #3136]
	movz x17, #40553, lsl #0
	movk x17, #10890, lsl #16
	movk x17, #39842, lsl #32
	movk x17, #15646, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #3176]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #3184]
	movz x10, #0, lsl #0
	ldr x2, [x0, #64]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3136]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3136]
	ldr x2, [x0, #72]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3144]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3144]
	ldr x2, [x0, #80]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3152]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3152]
	ldr x2, [x0, #88]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3160]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3160]
	ldr x2, [x0, #96]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3168]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3168]
	ldr x3, [x0, #3176]
	adds x3, x3, x10
	str x3, [x0, #3176]
	ldr x3, [x0, #3184]
	adcs x3, x3, x12
	str x3, [x0, #3184]
	ldr x2, [x0, #3144]
	str x2, [x0, #2992]
	ldr x2, [x0, #3152]
	str x2, [x0, #3000]
	ldr x2, [x0, #3160]
	str x2, [x0, #3008]
	ldr x2, [x0, #3168]
	str x2, [x0, #3016]
	ldr x2, [x0, #3176]
	str x2, [x0, #3024]
	ldr x2, [x0, #3184]
	str x2, [x0, #3032]
	ldr x2, [x0, #3040]
	str x2, [x0, #2944]
	ldr x2, [x0, #3048]
	str x2, [x0, #2952]
	ldr x2, [x0, #3056]
	str x2, [x0, #2960]
	ldr x2, [x0, #3064]
	str x2, [x0, #2968]
	ldr x2, [x0, #3072]
	str x2, [x0, #2976]
	ldr x2, [x0, #3080]
	str x2, [x0, #2984]
	cbnz x19, 20b
	movz x12, #0, lsl #0
	ldr x3, [x0, #2984]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #2944]
	ldr x2, [x0, #64]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #2944]
	ldr x3, [x0, #2952]
	ldr x2, [x0, #72]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2952]
	ldr x3, [x0, #2960]
	ldr x2, [x0, #80]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2960]
	ldr x3, [x0, #2968]
	ldr x2, [x0, #88]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2968]
	ldr x3, [x0, #2976]
	ldr x2, [x0, #96]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2976]
	ldr x3, [x0, #2984]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #2984]
	ldr x3, [x0, #2944]
	ldr x2, [x0, #64]
	subs x3, x3, x2
	str x3, [x0, #2944]
	ldr x3, [x0, #2952]
	ldr x2, [x0, #72]
	sbcs x3, x3, x2
	str x3, [x0, #2952]
	ldr x3, [x0, #2960]
	ldr x2, [x0, #80]
	sbcs x3, x3, x2
	str x3, [x0, #2960]
	ldr x3, [x0, #2968]
	ldr x2, [x0, #88]
	sbcs x3, x3, x2
	str x3, [x0, #2968]
	ldr x3, [x0, #2976]
	ldr x2, [x0, #96]
	sbcs x3, x3, x2
	str x3, [x0, #2976]
	ldr x3, [x0, #2984]
	add x2, x12, x12
	sbcs x3, x3, x2
	str x3, [x0, #2984]
	ldr x3, [x0, #2984]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #2944]
	ldr x2, [x0, #64]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #2944]
	ldr x3, [x0, #2952]
	ldr x2, [x0, #72]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2952]
	ldr x3, [x0, #2960]
	ldr x2, [x0, #80]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2960]
	ldr x3, [x0, #2968]
	ldr x2, [x0, #88]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2968]
	ldr x3, [x0, #2976]
	ldr x2, [x0, #96]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2976]
	ldr x3, [x0, #2984]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #2984]
	movz x12, #0, lsl #0
	ldr x3, [x0, #2848]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #30403, lsl #0
	movk x2, #7588, lsl #16
	movk x2, #56998, lsl #32
	movk x2, #36635, lsl #48
	movz x3, #46948, lsl #0
	movk x3, #54286, lsl #16
	movk x3, #13323, lsl #32
	movk x3, #28088, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3040]
	movz x2, #10890, lsl #0
	movk x2, #60430, lsl #16
	movk x2, #61675, lsl #32
	movk x2, #53270, lsl #48
	movz x3, #49566, lsl #0
	movk x3, #35973, lsl #16
	movk x3, #51456, lsl #32
	movk x3, #32635, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3048]
	movz x2, #52812, lsl #0
	movk x2, #18610, lsl #16
	movk x2, #17883, lsl #32
	movk x2, #42154, lsl #48
	movz x3, #16290, lsl #0
	movk x3, #44609, lsl #16
	movk x3, #35275, lsl #32
	movk x3, #21733, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3056]
	movz x2, #35927, lsl #0
	movk x2, #23083, lsl #16
	movk x2, #65502, lsl #32
	movk x2, #20774, lsl #48
	movz x3, #21518, lsl #0
	movk x3, #30678, lsl #16
	movk x3, #30848, lsl #32
	movk x3, #36885, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3064]
	movz x2, #60996, lsl #0
	movk x2, #9277, lsl #16
	movk x2, #14459, lsl #32
	movk x2, #17545, lsl #48
	movz x3, #24947, lsl #0
	movk x3, #4734, lsl #16
	movk x3, #3749, lsl #32
	movk x3, #36565, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3072]
	movz x7, #0, lsl #0
	ldr x4, [x0, #3040]
	ldr x5, [x0, #3048]
	ldr x16, [x0, #3056]
	ldr x17, [x0, #3064]
	movz x6, #40553, lsl #0
	movk x6, #10890, lsl #16
	movk x6, #39842, lsl #32
	movk x6, #15646, lsl #48
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	ldr x1, [x0, #2944]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x0, #3072]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #3072]
	umulh x2, x1, x3
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	adcs x13, x13, x7
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
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
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
	adcs x13, x13, x7
	adcs x14, x14, x7
	ldr x1, [x0, #2952]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #3072]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3072]
	umulh x2, x1, x3
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	adcs x14, x14, x7
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
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x14, x14, x2
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
	adcs x14, x14, x7
	adcs x8, x8, x7
	ldr x1, [x0, #2960]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #3072]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3072]
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
	ldr x3, [x0, #96]
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
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #2968]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #3072]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #3072]
	umulh x2, x1, x3
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
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
	adcs x8, x8, x2
	ldr x3, [x0, #96]
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
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x1, [x0, #2976]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #3072]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #3072]
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
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
	adcs x8, x8, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #96]
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
	adcs x8, x8, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x2, [x0, #64]
	subs x1, x13, x2
	ldr x2, [x0, #72]
	sbcs x3, x14, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	ldr x2, [x0, #96]
	sbcs x6, x10, x2
	sbcs x2, x11, x7
	csel x13, x1, x13, hs
	csel x14, x3, x14, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	str x13, [x0, #1224]
	str x14, [x0, #1232]
	str x8, [x0, #1240]
	str x9, [x0, #1248]
	str x10, [x0, #1256]
	ldr x19, [x0, #3208]
	ret
	.p2align 6
