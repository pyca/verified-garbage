// The functions of `src/internal/vg_p384_inv_mod_n.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_inv_mod_n:
	str x19, [x0, #3832]
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #15, lsl #0
	ldr x2, [x0, #112]
	str x2, [x0, #3400]
	ldr x2, [x0, #120]
	str x2, [x0, #3408]
	ldr x2, [x0, #128]
	str x2, [x0, #3416]
	ldr x2, [x0, #136]
	str x2, [x0, #3424]
	ldr x2, [x0, #144]
	str x2, [x0, #3432]
	ldr x2, [x0, #152]
	str x2, [x0, #3440]
	str x12, [x0, #3448]
	ldr x2, [x0, #1840]
	str x2, [x0, #3456]
	ldr x2, [x0, #1848]
	str x2, [x0, #3464]
	ldr x2, [x0, #1856]
	str x2, [x0, #3472]
	ldr x2, [x0, #1864]
	str x2, [x0, #3480]
	ldr x2, [x0, #1872]
	str x2, [x0, #3488]
	ldr x2, [x0, #1880]
	str x2, [x0, #3496]
	str x12, [x0, #3504]
	str x12, [x0, #3512]
	str x12, [x0, #3520]
	str x12, [x0, #3528]
	str x12, [x0, #3536]
	str x12, [x0, #3544]
	str x12, [x0, #3552]
	str x12, [x0, #3560]
	str x12, [x0, #3568]
	str x12, [x0, #3576]
	str x12, [x0, #3584]
	str x12, [x0, #3592]
	str x12, [x0, #3600]
	str x12, [x0, #3608]
	str x12, [x0, #3616]
	str x11, [x0, #3568]
20:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #3400]
	ldr x3, [x0, #3456]
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
	ldr x2, [x0, #3400]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #3736]
	ldr x2, [x0, #3408]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3744]
	ldr x2, [x0, #3416]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3752]
	ldr x2, [x0, #3424]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3760]
	ldr x2, [x0, #3432]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3768]
	ldr x2, [x0, #3440]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3776]
	ldr x2, [x0, #3448]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3784]
	movz x10, #0, lsl #0
	ldr x2, [x0, #3456]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3736]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3736]
	ldr x2, [x0, #3464]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3744]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3744]
	ldr x2, [x0, #3472]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3752]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3752]
	ldr x2, [x0, #3480]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3760]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3760]
	ldr x2, [x0, #3488]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3768]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3768]
	ldr x2, [x0, #3496]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3776]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3776]
	ldr x2, [x0, #3504]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3784]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3784]
	ldr x3, [x0, #3744]
	ldr x2, [x0, #3400]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #3744]
	ldr x3, [x0, #3752]
	ldr x2, [x0, #3408]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3752]
	ldr x3, [x0, #3760]
	ldr x2, [x0, #3416]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3760]
	ldr x3, [x0, #3768]
	ldr x2, [x0, #3424]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3768]
	ldr x3, [x0, #3776]
	ldr x2, [x0, #3432]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	ldr x2, [x0, #3440]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3784]
	ldr x3, [x0, #3744]
	ldr x2, [x0, #3456]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #3744]
	ldr x3, [x0, #3752]
	ldr x2, [x0, #3464]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3752]
	ldr x3, [x0, #3760]
	ldr x2, [x0, #3472]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3760]
	ldr x3, [x0, #3768]
	ldr x2, [x0, #3480]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3768]
	ldr x3, [x0, #3776]
	ldr x2, [x0, #3488]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	ldr x2, [x0, #3496]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3784]
	ldr x2, [x0, #3736]
	ldr x3, [x0, #3744]
	extr x8, x3, x2, #59
	str x8, [x0, #3624]
	ldr x2, [x0, #3744]
	ldr x3, [x0, #3752]
	extr x8, x3, x2, #59
	str x8, [x0, #3632]
	ldr x2, [x0, #3752]
	ldr x3, [x0, #3760]
	extr x8, x3, x2, #59
	str x8, [x0, #3640]
	ldr x2, [x0, #3760]
	ldr x3, [x0, #3768]
	extr x8, x3, x2, #59
	str x8, [x0, #3648]
	ldr x2, [x0, #3768]
	ldr x3, [x0, #3776]
	extr x8, x3, x2, #59
	str x8, [x0, #3656]
	ldr x2, [x0, #3776]
	ldr x3, [x0, #3784]
	extr x8, x3, x2, #59
	str x8, [x0, #3664]
	ldr x3, [x0, #3784]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #3672]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #3400]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #3736]
	ldr x2, [x0, #3408]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3744]
	ldr x2, [x0, #3416]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3752]
	ldr x2, [x0, #3424]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3760]
	ldr x2, [x0, #3432]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3768]
	ldr x2, [x0, #3440]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3776]
	ldr x2, [x0, #3448]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3784]
	movz x10, #0, lsl #0
	ldr x2, [x0, #3456]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3736]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3736]
	ldr x2, [x0, #3464]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3744]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3744]
	ldr x2, [x0, #3472]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3752]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3752]
	ldr x2, [x0, #3480]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3760]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3760]
	ldr x2, [x0, #3488]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3768]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3768]
	ldr x2, [x0, #3496]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3776]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3776]
	ldr x2, [x0, #3504]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3784]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3784]
	ldr x3, [x0, #3744]
	ldr x2, [x0, #3400]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #3744]
	ldr x3, [x0, #3752]
	ldr x2, [x0, #3408]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3752]
	ldr x3, [x0, #3760]
	ldr x2, [x0, #3416]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3760]
	ldr x3, [x0, #3768]
	ldr x2, [x0, #3424]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3768]
	ldr x3, [x0, #3776]
	ldr x2, [x0, #3432]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	ldr x2, [x0, #3440]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3784]
	ldr x3, [x0, #3744]
	ldr x2, [x0, #3456]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #3744]
	ldr x3, [x0, #3752]
	ldr x2, [x0, #3464]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3752]
	ldr x3, [x0, #3760]
	ldr x2, [x0, #3472]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3760]
	ldr x3, [x0, #3768]
	ldr x2, [x0, #3480]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3768]
	ldr x3, [x0, #3776]
	ldr x2, [x0, #3488]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	ldr x2, [x0, #3496]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3784]
	ldr x2, [x0, #3736]
	ldr x3, [x0, #3744]
	extr x8, x3, x2, #59
	str x8, [x0, #3680]
	ldr x2, [x0, #3744]
	ldr x3, [x0, #3752]
	extr x8, x3, x2, #59
	str x8, [x0, #3688]
	ldr x2, [x0, #3752]
	ldr x3, [x0, #3760]
	extr x8, x3, x2, #59
	str x8, [x0, #3696]
	ldr x2, [x0, #3760]
	ldr x3, [x0, #3768]
	extr x8, x3, x2, #59
	str x8, [x0, #3704]
	ldr x2, [x0, #3768]
	ldr x3, [x0, #3776]
	extr x8, x3, x2, #59
	str x8, [x0, #3712]
	ldr x2, [x0, #3776]
	ldr x3, [x0, #3784]
	extr x8, x3, x2, #59
	str x8, [x0, #3720]
	ldr x3, [x0, #3784]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #3728]
	ldr x2, [x0, #3624]
	str x2, [x0, #3400]
	ldr x2, [x0, #3632]
	str x2, [x0, #3408]
	ldr x2, [x0, #3640]
	str x2, [x0, #3416]
	ldr x2, [x0, #3648]
	str x2, [x0, #3424]
	ldr x2, [x0, #3656]
	str x2, [x0, #3432]
	ldr x2, [x0, #3664]
	str x2, [x0, #3440]
	ldr x2, [x0, #3672]
	str x2, [x0, #3448]
	ldr x2, [x0, #3680]
	str x2, [x0, #3456]
	ldr x2, [x0, #3688]
	str x2, [x0, #3464]
	ldr x2, [x0, #3696]
	str x2, [x0, #3472]
	ldr x2, [x0, #3704]
	str x2, [x0, #3480]
	ldr x2, [x0, #3712]
	str x2, [x0, #3488]
	ldr x2, [x0, #3720]
	str x2, [x0, #3496]
	ldr x2, [x0, #3728]
	str x2, [x0, #3504]
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #3512]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #3736]
	ldr x2, [x0, #3520]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3744]
	ldr x2, [x0, #3528]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3752]
	ldr x2, [x0, #3536]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3760]
	ldr x2, [x0, #3544]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3768]
	ldr x2, [x0, #3552]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3776]
	ldr x2, [x0, #3560]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3784]
	movz x10, #0, lsl #0
	ldr x2, [x0, #3568]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3736]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3736]
	ldr x2, [x0, #3576]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3744]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3744]
	ldr x2, [x0, #3584]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3752]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3752]
	ldr x2, [x0, #3592]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3760]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3760]
	ldr x2, [x0, #3600]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3768]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3768]
	ldr x2, [x0, #3608]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3776]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3776]
	ldr x2, [x0, #3616]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3784]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3784]
	ldr x3, [x0, #3744]
	ldr x2, [x0, #3512]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #3744]
	ldr x3, [x0, #3752]
	ldr x2, [x0, #3520]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3752]
	ldr x3, [x0, #3760]
	ldr x2, [x0, #3528]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3760]
	ldr x3, [x0, #3768]
	ldr x2, [x0, #3536]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3768]
	ldr x3, [x0, #3776]
	ldr x2, [x0, #3544]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	ldr x2, [x0, #3552]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3784]
	ldr x3, [x0, #3744]
	ldr x2, [x0, #3568]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #3744]
	ldr x3, [x0, #3752]
	ldr x2, [x0, #3576]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3752]
	ldr x3, [x0, #3760]
	ldr x2, [x0, #3584]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3760]
	ldr x3, [x0, #3768]
	ldr x2, [x0, #3592]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3768]
	ldr x3, [x0, #3776]
	ldr x2, [x0, #3600]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	ldr x2, [x0, #3608]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3784]
	ldr x2, [x0, #3736]
	movz x17, #56389, lsl #0
	movk x17, #59535, lsl #16
	movk x17, #24713, lsl #32
	movk x17, #28372, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #3784]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #3792]
	movz x10, #0, lsl #0
	ldr x2, [x0, #112]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3736]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3736]
	ldr x2, [x0, #120]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3744]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3744]
	ldr x2, [x0, #128]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3752]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3752]
	ldr x2, [x0, #136]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3760]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3760]
	ldr x2, [x0, #144]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3768]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3768]
	ldr x2, [x0, #152]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3776]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	adds x3, x3, x10
	str x3, [x0, #3784]
	ldr x3, [x0, #3792]
	adcs x3, x3, x12
	str x3, [x0, #3792]
	ldr x2, [x0, #3744]
	str x2, [x0, #3624]
	ldr x2, [x0, #3752]
	str x2, [x0, #3632]
	ldr x2, [x0, #3760]
	str x2, [x0, #3640]
	ldr x2, [x0, #3768]
	str x2, [x0, #3648]
	ldr x2, [x0, #3776]
	str x2, [x0, #3656]
	ldr x2, [x0, #3784]
	str x2, [x0, #3664]
	ldr x2, [x0, #3792]
	str x2, [x0, #3672]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #3512]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #3736]
	ldr x2, [x0, #3520]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3744]
	ldr x2, [x0, #3528]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3752]
	ldr x2, [x0, #3536]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3760]
	ldr x2, [x0, #3544]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3768]
	ldr x2, [x0, #3552]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3776]
	ldr x2, [x0, #3560]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #3784]
	movz x10, #0, lsl #0
	ldr x2, [x0, #3568]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3736]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3736]
	ldr x2, [x0, #3576]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3744]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3744]
	ldr x2, [x0, #3584]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3752]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3752]
	ldr x2, [x0, #3592]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3760]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3760]
	ldr x2, [x0, #3600]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3768]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3768]
	ldr x2, [x0, #3608]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3776]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3776]
	ldr x2, [x0, #3616]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3784]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3784]
	ldr x3, [x0, #3744]
	ldr x2, [x0, #3512]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #3744]
	ldr x3, [x0, #3752]
	ldr x2, [x0, #3520]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3752]
	ldr x3, [x0, #3760]
	ldr x2, [x0, #3528]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3760]
	ldr x3, [x0, #3768]
	ldr x2, [x0, #3536]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3768]
	ldr x3, [x0, #3776]
	ldr x2, [x0, #3544]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	ldr x2, [x0, #3552]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #3784]
	ldr x3, [x0, #3744]
	ldr x2, [x0, #3568]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #3744]
	ldr x3, [x0, #3752]
	ldr x2, [x0, #3576]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3752]
	ldr x3, [x0, #3760]
	ldr x2, [x0, #3584]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3760]
	ldr x3, [x0, #3768]
	ldr x2, [x0, #3592]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3768]
	ldr x3, [x0, #3776]
	ldr x2, [x0, #3600]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	ldr x2, [x0, #3608]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #3784]
	ldr x2, [x0, #3736]
	movz x17, #56389, lsl #0
	movk x17, #59535, lsl #16
	movk x17, #24713, lsl #32
	movk x17, #28372, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #3784]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #3792]
	movz x10, #0, lsl #0
	ldr x2, [x0, #112]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3736]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3736]
	ldr x2, [x0, #120]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3744]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3744]
	ldr x2, [x0, #128]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3752]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3752]
	ldr x2, [x0, #136]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3760]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3760]
	ldr x2, [x0, #144]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3768]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3768]
	ldr x2, [x0, #152]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #3776]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #3776]
	ldr x3, [x0, #3784]
	adds x3, x3, x10
	str x3, [x0, #3784]
	ldr x3, [x0, #3792]
	adcs x3, x3, x12
	str x3, [x0, #3792]
	ldr x2, [x0, #3744]
	str x2, [x0, #3568]
	ldr x2, [x0, #3752]
	str x2, [x0, #3576]
	ldr x2, [x0, #3760]
	str x2, [x0, #3584]
	ldr x2, [x0, #3768]
	str x2, [x0, #3592]
	ldr x2, [x0, #3776]
	str x2, [x0, #3600]
	ldr x2, [x0, #3784]
	str x2, [x0, #3608]
	ldr x2, [x0, #3792]
	str x2, [x0, #3616]
	ldr x2, [x0, #3624]
	str x2, [x0, #3512]
	ldr x2, [x0, #3632]
	str x2, [x0, #3520]
	ldr x2, [x0, #3640]
	str x2, [x0, #3528]
	ldr x2, [x0, #3648]
	str x2, [x0, #3536]
	ldr x2, [x0, #3656]
	str x2, [x0, #3544]
	ldr x2, [x0, #3664]
	str x2, [x0, #3552]
	ldr x2, [x0, #3672]
	str x2, [x0, #3560]
	cbnz x19, 20b
	movz x12, #0, lsl #0
	ldr x3, [x0, #3560]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #3512]
	ldr x2, [x0, #112]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #3512]
	ldr x3, [x0, #3520]
	ldr x2, [x0, #120]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3520]
	ldr x3, [x0, #3528]
	ldr x2, [x0, #128]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3528]
	ldr x3, [x0, #3536]
	ldr x2, [x0, #136]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3536]
	ldr x3, [x0, #3544]
	ldr x2, [x0, #144]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3544]
	ldr x3, [x0, #3552]
	ldr x2, [x0, #152]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3552]
	ldr x3, [x0, #3560]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #3560]
	ldr x3, [x0, #3512]
	ldr x2, [x0, #112]
	subs x3, x3, x2
	str x3, [x0, #3512]
	ldr x3, [x0, #3520]
	ldr x2, [x0, #120]
	sbcs x3, x3, x2
	str x3, [x0, #3520]
	ldr x3, [x0, #3528]
	ldr x2, [x0, #128]
	sbcs x3, x3, x2
	str x3, [x0, #3528]
	ldr x3, [x0, #3536]
	ldr x2, [x0, #136]
	sbcs x3, x3, x2
	str x3, [x0, #3536]
	ldr x3, [x0, #3544]
	ldr x2, [x0, #144]
	sbcs x3, x3, x2
	str x3, [x0, #3544]
	ldr x3, [x0, #3552]
	ldr x2, [x0, #152]
	sbcs x3, x3, x2
	str x3, [x0, #3552]
	ldr x3, [x0, #3560]
	add x2, x12, x12
	sbcs x3, x3, x2
	str x3, [x0, #3560]
	ldr x3, [x0, #3560]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #3512]
	ldr x2, [x0, #112]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #3512]
	ldr x3, [x0, #3520]
	ldr x2, [x0, #120]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3520]
	ldr x3, [x0, #3528]
	ldr x2, [x0, #128]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3528]
	ldr x3, [x0, #3536]
	ldr x2, [x0, #136]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3536]
	ldr x3, [x0, #3544]
	ldr x2, [x0, #144]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3544]
	ldr x3, [x0, #3552]
	ldr x2, [x0, #152]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #3552]
	ldr x3, [x0, #3560]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #3560]
	movz x12, #0, lsl #0
	ldr x3, [x0, #3400]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #63550, lsl #0
	movk x2, #52244, lsl #16
	movk x2, #38868, lsl #32
	movk x2, #34797, lsl #48
	movz x3, #12597, lsl #0
	movk x3, #176, lsl #16
	movk x3, #33174, lsl #32
	movk x3, #25854, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3624]
	movz x2, #54274, lsl #0
	movk x2, #64189, lsl #16
	movk x2, #59932, lsl #32
	movk x2, #14053, lsl #48
	movz x3, #54136, lsl #0
	movk x3, #19954, lsl #16
	movk x3, #9109, lsl #32
	movk x3, #8500, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3632]
	movz x2, #37596, lsl #0
	movk x2, #38489, lsl #16
	movk x2, #50264, lsl #32
	movk x2, #30263, lsl #48
	movz x3, #39683, lsl #0
	movk x3, #24029, lsl #16
	movk x3, #35113, lsl #32
	movk x3, #20779, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3640]
	movz x2, #28761, lsl #0
	movk x2, #36679, lsl #16
	movk x2, #64716, lsl #32
	movk x2, #44787, lsl #48
	movz x3, #36774, lsl #0
	movk x3, #28856, lsl #16
	movk x3, #819, lsl #32
	movk x3, #20748, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3648]
	movz x2, #45530, lsl #0
	movk x2, #42101, lsl #16
	movk x2, #3949, lsl #32
	movk x2, #59898, lsl #48
	movz x3, #20005, lsl #0
	movk x3, #23434, lsl #16
	movk x3, #61586, lsl #32
	movk x3, #5637, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3656]
	movz x2, #56045, lsl #0
	movk x2, #4875, lsl #16
	movk x2, #15529, lsl #32
	movk x2, #33803, lsl #48
	movz x3, #9490, lsl #0
	movk x3, #60660, lsl #16
	movk x3, #50006, lsl #32
	movk x3, #31732, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #3664]
	movz x7, #0, lsl #0
	ldr x4, [x0, #3624]
	ldr x5, [x0, #3632]
	ldr x16, [x0, #3640]
	ldr x17, [x0, #3648]
	movz x6, #56389, lsl #0
	movk x6, #59535, lsl #16
	movk x6, #24713, lsl #32
	movk x6, #28372, lsl #48
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	ldr x1, [x0, #3512]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x0, #3656]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #3664]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3664]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x15, x15, x7
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #3656]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	adcs x15, x15, x7
	mul x1, x8, x6
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	adcs x15, x15, x7
	ldr x1, [x0, #3520]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #3656]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3664]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3664]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x8, x8, x7
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #3656]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x15, x15, x7
	adcs x8, x8, x7
	mul x1, x9, x6
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x8, x8, x7
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x15, x15, x7
	adcs x8, x8, x7
	ldr x1, [x0, #3528]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #3656]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3664]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3664]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #3656]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	mul x1, x10, x6
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #3536]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #3656]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3664]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #3664]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #3656]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	mul x1, x11, x6
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x1, [x0, #3544]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #3656]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #3664]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #3664]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #3656]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	mul x1, x12, x6
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x1, [x0, #3552]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #3656]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #3664]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #3664]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	ldr x3, [x0, #3656]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	mul x1, x13, x6
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #128]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adds x14, x14, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #128]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	ldr x2, [x0, #112]
	subs x1, x14, x2
	ldr x2, [x0, #120]
	sbcs x3, x15, x2
	ldr x2, [x0, #128]
	sbcs x4, x8, x2
	ldr x2, [x0, #136]
	sbcs x5, x9, x2
	ldr x2, [x0, #144]
	sbcs x6, x10, x2
	ldr x2, [x0, #152]
	sbcs x16, x11, x2
	sbcs x2, x12, x7
	csel x14, x1, x14, hs
	csel x15, x3, x15, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	csel x11, x16, x11, hs
	str x14, [x0, #1456]
	str x15, [x0, #1464]
	str x8, [x0, #1472]
	str x9, [x0, #1480]
	str x10, [x0, #1488]
	str x11, [x0, #1496]
	ldr x19, [x0, #3832]
	ret
	.p2align 6
