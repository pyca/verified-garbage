// The functions of `src/internal/vg_brainpoolp256r1_inv_mod_p.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp256r1_inv_mod_p:
	str x19, [x0, #2584]
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #10, lsl #0
	ldr x2, [x0, #64]
	str x2, [x0, #2296]
	ldr x2, [x0, #72]
	str x2, [x0, #2304]
	ldr x2, [x0, #80]
	str x2, [x0, #2312]
	ldr x2, [x0, #88]
	str x2, [x0, #2320]
	str x12, [x0, #2328]
	ldr x2, [x0, #576]
	str x2, [x0, #2336]
	ldr x2, [x0, #584]
	str x2, [x0, #2344]
	ldr x2, [x0, #592]
	str x2, [x0, #2352]
	ldr x2, [x0, #600]
	str x2, [x0, #2360]
	str x12, [x0, #2368]
	str x12, [x0, #2376]
	str x12, [x0, #2384]
	str x12, [x0, #2392]
	str x12, [x0, #2400]
	str x12, [x0, #2408]
	str x12, [x0, #2416]
	str x12, [x0, #2424]
	str x12, [x0, #2432]
	str x12, [x0, #2440]
	str x12, [x0, #2448]
	str x11, [x0, #2416]
20:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #2296]
	ldr x3, [x0, #2336]
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
	ldr x2, [x0, #2296]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #2536]
	ldr x2, [x0, #2304]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	ldr x2, [x0, #2312]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2552]
	ldr x2, [x0, #2320]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2560]
	ldr x2, [x0, #2328]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2568]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2336]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2344]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x2, [x0, #2352]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #2360]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2560]
	ldr x2, [x0, #2368]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2568]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2296]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	ldr x2, [x0, #2304]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2552]
	ldr x3, [x0, #2560]
	ldr x2, [x0, #2312]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	ldr x2, [x0, #2320]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2568]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2336]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	ldr x2, [x0, #2344]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2552]
	ldr x3, [x0, #2560]
	ldr x2, [x0, #2352]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	ldr x2, [x0, #2360]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2568]
	ldr x2, [x0, #2536]
	ldr x3, [x0, #2544]
	extr x8, x3, x2, #59
	str x8, [x0, #2456]
	ldr x2, [x0, #2544]
	ldr x3, [x0, #2552]
	extr x8, x3, x2, #59
	str x8, [x0, #2464]
	ldr x2, [x0, #2552]
	ldr x3, [x0, #2560]
	extr x8, x3, x2, #59
	str x8, [x0, #2472]
	ldr x2, [x0, #2560]
	ldr x3, [x0, #2568]
	extr x8, x3, x2, #59
	str x8, [x0, #2480]
	ldr x3, [x0, #2568]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #2488]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #2296]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #2536]
	ldr x2, [x0, #2304]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	ldr x2, [x0, #2312]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2552]
	ldr x2, [x0, #2320]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2560]
	ldr x2, [x0, #2328]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2568]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2336]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2344]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x2, [x0, #2352]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #2360]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2560]
	ldr x2, [x0, #2368]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2568]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2296]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	ldr x2, [x0, #2304]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2552]
	ldr x3, [x0, #2560]
	ldr x2, [x0, #2312]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	ldr x2, [x0, #2320]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2568]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2336]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	ldr x2, [x0, #2344]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2552]
	ldr x3, [x0, #2560]
	ldr x2, [x0, #2352]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	ldr x2, [x0, #2360]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2568]
	ldr x2, [x0, #2536]
	ldr x3, [x0, #2544]
	extr x8, x3, x2, #59
	str x8, [x0, #2496]
	ldr x2, [x0, #2544]
	ldr x3, [x0, #2552]
	extr x8, x3, x2, #59
	str x8, [x0, #2504]
	ldr x2, [x0, #2552]
	ldr x3, [x0, #2560]
	extr x8, x3, x2, #59
	str x8, [x0, #2512]
	ldr x2, [x0, #2560]
	ldr x3, [x0, #2568]
	extr x8, x3, x2, #59
	str x8, [x0, #2520]
	ldr x3, [x0, #2568]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #2528]
	ldr x2, [x0, #2456]
	str x2, [x0, #2296]
	ldr x2, [x0, #2464]
	str x2, [x0, #2304]
	ldr x2, [x0, #2472]
	str x2, [x0, #2312]
	ldr x2, [x0, #2480]
	str x2, [x0, #2320]
	ldr x2, [x0, #2488]
	str x2, [x0, #2328]
	ldr x2, [x0, #2496]
	str x2, [x0, #2336]
	ldr x2, [x0, #2504]
	str x2, [x0, #2344]
	ldr x2, [x0, #2512]
	str x2, [x0, #2352]
	ldr x2, [x0, #2520]
	str x2, [x0, #2360]
	ldr x2, [x0, #2528]
	str x2, [x0, #2368]
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #2376]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #2536]
	ldr x2, [x0, #2384]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	ldr x2, [x0, #2392]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2552]
	ldr x2, [x0, #2400]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2560]
	ldr x2, [x0, #2408]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2568]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2416]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2424]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x2, [x0, #2432]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #2440]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2560]
	ldr x2, [x0, #2448]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2568]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2376]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	ldr x2, [x0, #2384]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2552]
	ldr x3, [x0, #2560]
	ldr x2, [x0, #2392]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	ldr x2, [x0, #2400]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2568]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2416]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	ldr x2, [x0, #2424]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2552]
	ldr x3, [x0, #2560]
	ldr x2, [x0, #2432]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	ldr x2, [x0, #2440]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2568]
	ldr x2, [x0, #2536]
	movz x17, #35257, lsl #0
	movk x17, #52989, lsl #16
	movk x17, #21904, lsl #32
	movk x17, #50855, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #2568]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #2576]
	movz x10, #0, lsl #0
	ldr x2, [x0, #64]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #72]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x2, [x0, #80]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #88]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	adds x3, x3, x10
	str x3, [x0, #2568]
	ldr x3, [x0, #2576]
	adcs x3, x3, x12
	str x3, [x0, #2576]
	ldr x2, [x0, #2544]
	str x2, [x0, #2456]
	ldr x2, [x0, #2552]
	str x2, [x0, #2464]
	ldr x2, [x0, #2560]
	str x2, [x0, #2472]
	ldr x2, [x0, #2568]
	str x2, [x0, #2480]
	ldr x2, [x0, #2576]
	str x2, [x0, #2488]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #2376]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #2536]
	ldr x2, [x0, #2384]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	ldr x2, [x0, #2392]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2552]
	ldr x2, [x0, #2400]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2560]
	ldr x2, [x0, #2408]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2568]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2416]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2424]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x2, [x0, #2432]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #2440]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2560]
	ldr x2, [x0, #2448]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2568]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2376]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	ldr x2, [x0, #2384]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2552]
	ldr x3, [x0, #2560]
	ldr x2, [x0, #2392]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	ldr x2, [x0, #2400]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2568]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2416]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	ldr x2, [x0, #2424]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2552]
	ldr x3, [x0, #2560]
	ldr x2, [x0, #2432]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	ldr x2, [x0, #2440]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2568]
	ldr x2, [x0, #2536]
	movz x17, #35257, lsl #0
	movk x17, #52989, lsl #16
	movk x17, #21904, lsl #32
	movk x17, #50855, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #2568]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #2576]
	movz x10, #0, lsl #0
	ldr x2, [x0, #64]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #72]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x2, [x0, #80]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #88]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2560]
	ldr x3, [x0, #2568]
	adds x3, x3, x10
	str x3, [x0, #2568]
	ldr x3, [x0, #2576]
	adcs x3, x3, x12
	str x3, [x0, #2576]
	ldr x2, [x0, #2544]
	str x2, [x0, #2416]
	ldr x2, [x0, #2552]
	str x2, [x0, #2424]
	ldr x2, [x0, #2560]
	str x2, [x0, #2432]
	ldr x2, [x0, #2568]
	str x2, [x0, #2440]
	ldr x2, [x0, #2576]
	str x2, [x0, #2448]
	ldr x2, [x0, #2456]
	str x2, [x0, #2376]
	ldr x2, [x0, #2464]
	str x2, [x0, #2384]
	ldr x2, [x0, #2472]
	str x2, [x0, #2392]
	ldr x2, [x0, #2480]
	str x2, [x0, #2400]
	ldr x2, [x0, #2488]
	str x2, [x0, #2408]
	cbnz x19, 20b
	movz x12, #0, lsl #0
	ldr x3, [x0, #2408]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #2376]
	ldr x2, [x0, #64]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #2376]
	ldr x3, [x0, #2384]
	ldr x2, [x0, #72]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2384]
	ldr x3, [x0, #2392]
	ldr x2, [x0, #80]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2392]
	ldr x3, [x0, #2400]
	ldr x2, [x0, #88]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2400]
	ldr x3, [x0, #2408]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #2408]
	ldr x3, [x0, #2376]
	ldr x2, [x0, #64]
	subs x3, x3, x2
	str x3, [x0, #2376]
	ldr x3, [x0, #2384]
	ldr x2, [x0, #72]
	sbcs x3, x3, x2
	str x3, [x0, #2384]
	ldr x3, [x0, #2392]
	ldr x2, [x0, #80]
	sbcs x3, x3, x2
	str x3, [x0, #2392]
	ldr x3, [x0, #2400]
	ldr x2, [x0, #88]
	sbcs x3, x3, x2
	str x3, [x0, #2400]
	ldr x3, [x0, #2408]
	add x2, x12, x12
	sbcs x3, x3, x2
	str x3, [x0, #2408]
	ldr x3, [x0, #2408]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #2376]
	ldr x2, [x0, #64]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #2376]
	ldr x3, [x0, #2384]
	ldr x2, [x0, #72]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2384]
	ldr x3, [x0, #2392]
	ldr x2, [x0, #80]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2392]
	ldr x3, [x0, #2400]
	ldr x2, [x0, #88]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2400]
	ldr x3, [x0, #2408]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #2408]
	movz x12, #0, lsl #0
	ldr x3, [x0, #2296]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #61119, lsl #0
	movk x2, #35469, lsl #16
	movk x2, #10163, lsl #32
	movk x2, #58034, lsl #48
	movz x3, #25784, lsl #0
	movk x3, #38112, lsl #16
	movk x3, #8297, lsl #32
	movk x3, #15713, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2456]
	movz x2, #51418, lsl #0
	movk x2, #37322, lsl #16
	movk x2, #31338, lsl #32
	movk x2, #10193, lsl #48
	movz x3, #22349, lsl #0
	movk x3, #17243, lsl #16
	movk x3, #31673, lsl #32
	movk x3, #18026, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2464]
	movz x2, #47375, lsl #0
	movk x2, #15036, lsl #16
	movk x2, #5513, lsl #32
	movk x2, #16894, lsl #48
	movz x3, #54371, lsl #0
	movk x3, #25286, lsl #16
	movk x3, #62727, lsl #32
	movk x3, #64615, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2472]
	movz x2, #9715, lsl #0
	movk x2, #33871, lsl #16
	movk x2, #15466, lsl #32
	movk x2, #27202, lsl #48
	movz x3, #33736, lsl #0
	movk x3, #7583, lsl #16
	movk x3, #7025, lsl #32
	movk x3, #16313, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2480]
	movz x7, #0, lsl #0
	ldr x4, [x0, #2456]
	ldr x5, [x0, #2464]
	ldr x16, [x0, #2472]
	ldr x17, [x0, #2480]
	movz x6, #35257, lsl #0
	movk x6, #52989, lsl #16
	movk x6, #21904, lsl #32
	movk x6, #50855, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #2376]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #2384]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x13, x13, x2
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
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #2392]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
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
	ldr x3, [x0, #88]
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
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #2400]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
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
	adcs x8, x8, x2
	ldr x3, [x0, #88]
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
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #64]
	subs x1, x12, x2
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #992]
	str x13, [x0, #1000]
	str x8, [x0, #1008]
	str x9, [x0, #1016]
	ldr x19, [x0, #2584]
	ret
	.p2align 6
