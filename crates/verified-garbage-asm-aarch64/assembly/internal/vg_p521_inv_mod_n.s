// The functions of `src/internal/vg_p521_inv_mod_n.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_inv_mod_n:
	str x19, [x0, #5704]
	str x21, [x0, #5712]
	str x22, [x0, #5720]
	str x23, [x0, #5728]
	str x24, [x0, #5736]
	str x25, [x0, #5744]
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #23, lsl #0
	ldr x2, [x0, #136]
	str x2, [x0, #5056]
	ldr x2, [x0, #144]
	str x2, [x0, #5064]
	ldr x2, [x0, #152]
	str x2, [x0, #5072]
	ldr x2, [x0, #160]
	str x2, [x0, #5080]
	ldr x2, [x0, #168]
	str x2, [x0, #5088]
	ldr x2, [x0, #176]
	str x2, [x0, #5096]
	ldr x2, [x0, #184]
	str x2, [x0, #5104]
	ldr x2, [x0, #192]
	str x2, [x0, #5112]
	ldr x2, [x0, #200]
	str x2, [x0, #5120]
	str x12, [x0, #5128]
	ldr x2, [x0, #2728]
	str x2, [x0, #5136]
	ldr x2, [x0, #2736]
	str x2, [x0, #5144]
	ldr x2, [x0, #2744]
	str x2, [x0, #5152]
	ldr x2, [x0, #2752]
	str x2, [x0, #5160]
	ldr x2, [x0, #2760]
	str x2, [x0, #5168]
	ldr x2, [x0, #2768]
	str x2, [x0, #5176]
	ldr x2, [x0, #2776]
	str x2, [x0, #5184]
	ldr x2, [x0, #2784]
	str x2, [x0, #5192]
	ldr x2, [x0, #2792]
	str x2, [x0, #5200]
	str x12, [x0, #5208]
	str x12, [x0, #5216]
	str x12, [x0, #5224]
	str x12, [x0, #5232]
	str x12, [x0, #5240]
	str x12, [x0, #5248]
	str x12, [x0, #5256]
	str x12, [x0, #5264]
	str x12, [x0, #5272]
	str x12, [x0, #5280]
	str x12, [x0, #5288]
	str x12, [x0, #5296]
	str x12, [x0, #5304]
	str x12, [x0, #5312]
	str x12, [x0, #5320]
	str x12, [x0, #5328]
	str x12, [x0, #5336]
	str x12, [x0, #5344]
	str x12, [x0, #5352]
	str x12, [x0, #5360]
	str x12, [x0, #5368]
	str x11, [x0, #5296]
20:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #5056]
	ldr x3, [x0, #5136]
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
	ldr x2, [x0, #5056]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #5536]
	ldr x2, [x0, #5064]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5544]
	ldr x2, [x0, #5072]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5552]
	ldr x2, [x0, #5080]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5560]
	ldr x2, [x0, #5088]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5568]
	ldr x2, [x0, #5096]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5576]
	ldr x2, [x0, #5104]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5584]
	ldr x2, [x0, #5112]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5592]
	ldr x2, [x0, #5120]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5600]
	ldr x2, [x0, #5128]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5608]
	movz x10, #0, lsl #0
	ldr x2, [x0, #5136]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5536]
	ldr x2, [x0, #5144]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5544]
	ldr x2, [x0, #5152]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5552]
	ldr x2, [x0, #5160]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5560]
	ldr x2, [x0, #5168]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5568]
	ldr x2, [x0, #5176]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5576]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5576]
	ldr x2, [x0, #5184]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5584]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5584]
	ldr x2, [x0, #5192]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5592]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5592]
	ldr x2, [x0, #5200]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5600]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5600]
	ldr x2, [x0, #5208]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5608]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5608]
	ldr x3, [x0, #5544]
	ldr x2, [x0, #5056]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #5544]
	ldr x3, [x0, #5552]
	ldr x2, [x0, #5064]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5552]
	ldr x3, [x0, #5560]
	ldr x2, [x0, #5072]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5560]
	ldr x3, [x0, #5568]
	ldr x2, [x0, #5080]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5568]
	ldr x3, [x0, #5576]
	ldr x2, [x0, #5088]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5576]
	ldr x3, [x0, #5584]
	ldr x2, [x0, #5096]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5584]
	ldr x3, [x0, #5592]
	ldr x2, [x0, #5104]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5592]
	ldr x3, [x0, #5600]
	ldr x2, [x0, #5112]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	ldr x2, [x0, #5120]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5608]
	ldr x3, [x0, #5544]
	ldr x2, [x0, #5136]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #5544]
	ldr x3, [x0, #5552]
	ldr x2, [x0, #5144]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5552]
	ldr x3, [x0, #5560]
	ldr x2, [x0, #5152]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5560]
	ldr x3, [x0, #5568]
	ldr x2, [x0, #5160]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5568]
	ldr x3, [x0, #5576]
	ldr x2, [x0, #5168]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5576]
	ldr x3, [x0, #5584]
	ldr x2, [x0, #5176]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5584]
	ldr x3, [x0, #5592]
	ldr x2, [x0, #5184]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5592]
	ldr x3, [x0, #5600]
	ldr x2, [x0, #5192]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	ldr x2, [x0, #5200]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5608]
	ldr x2, [x0, #5536]
	ldr x3, [x0, #5544]
	extr x8, x3, x2, #59
	str x8, [x0, #5376]
	ldr x2, [x0, #5544]
	ldr x3, [x0, #5552]
	extr x8, x3, x2, #59
	str x8, [x0, #5384]
	ldr x2, [x0, #5552]
	ldr x3, [x0, #5560]
	extr x8, x3, x2, #59
	str x8, [x0, #5392]
	ldr x2, [x0, #5560]
	ldr x3, [x0, #5568]
	extr x8, x3, x2, #59
	str x8, [x0, #5400]
	ldr x2, [x0, #5568]
	ldr x3, [x0, #5576]
	extr x8, x3, x2, #59
	str x8, [x0, #5408]
	ldr x2, [x0, #5576]
	ldr x3, [x0, #5584]
	extr x8, x3, x2, #59
	str x8, [x0, #5416]
	ldr x2, [x0, #5584]
	ldr x3, [x0, #5592]
	extr x8, x3, x2, #59
	str x8, [x0, #5424]
	ldr x2, [x0, #5592]
	ldr x3, [x0, #5600]
	extr x8, x3, x2, #59
	str x8, [x0, #5432]
	ldr x2, [x0, #5600]
	ldr x3, [x0, #5608]
	extr x8, x3, x2, #59
	str x8, [x0, #5440]
	ldr x3, [x0, #5608]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #5448]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #5056]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #5536]
	ldr x2, [x0, #5064]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5544]
	ldr x2, [x0, #5072]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5552]
	ldr x2, [x0, #5080]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5560]
	ldr x2, [x0, #5088]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5568]
	ldr x2, [x0, #5096]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5576]
	ldr x2, [x0, #5104]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5584]
	ldr x2, [x0, #5112]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5592]
	ldr x2, [x0, #5120]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5600]
	ldr x2, [x0, #5128]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5608]
	movz x10, #0, lsl #0
	ldr x2, [x0, #5136]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5536]
	ldr x2, [x0, #5144]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5544]
	ldr x2, [x0, #5152]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5552]
	ldr x2, [x0, #5160]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5560]
	ldr x2, [x0, #5168]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5568]
	ldr x2, [x0, #5176]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5576]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5576]
	ldr x2, [x0, #5184]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5584]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5584]
	ldr x2, [x0, #5192]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5592]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5592]
	ldr x2, [x0, #5200]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5600]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5600]
	ldr x2, [x0, #5208]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5608]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5608]
	ldr x3, [x0, #5544]
	ldr x2, [x0, #5056]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #5544]
	ldr x3, [x0, #5552]
	ldr x2, [x0, #5064]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5552]
	ldr x3, [x0, #5560]
	ldr x2, [x0, #5072]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5560]
	ldr x3, [x0, #5568]
	ldr x2, [x0, #5080]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5568]
	ldr x3, [x0, #5576]
	ldr x2, [x0, #5088]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5576]
	ldr x3, [x0, #5584]
	ldr x2, [x0, #5096]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5584]
	ldr x3, [x0, #5592]
	ldr x2, [x0, #5104]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5592]
	ldr x3, [x0, #5600]
	ldr x2, [x0, #5112]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	ldr x2, [x0, #5120]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5608]
	ldr x3, [x0, #5544]
	ldr x2, [x0, #5136]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #5544]
	ldr x3, [x0, #5552]
	ldr x2, [x0, #5144]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5552]
	ldr x3, [x0, #5560]
	ldr x2, [x0, #5152]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5560]
	ldr x3, [x0, #5568]
	ldr x2, [x0, #5160]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5568]
	ldr x3, [x0, #5576]
	ldr x2, [x0, #5168]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5576]
	ldr x3, [x0, #5584]
	ldr x2, [x0, #5176]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5584]
	ldr x3, [x0, #5592]
	ldr x2, [x0, #5184]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5592]
	ldr x3, [x0, #5600]
	ldr x2, [x0, #5192]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	ldr x2, [x0, #5200]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5608]
	ldr x2, [x0, #5536]
	ldr x3, [x0, #5544]
	extr x8, x3, x2, #59
	str x8, [x0, #5456]
	ldr x2, [x0, #5544]
	ldr x3, [x0, #5552]
	extr x8, x3, x2, #59
	str x8, [x0, #5464]
	ldr x2, [x0, #5552]
	ldr x3, [x0, #5560]
	extr x8, x3, x2, #59
	str x8, [x0, #5472]
	ldr x2, [x0, #5560]
	ldr x3, [x0, #5568]
	extr x8, x3, x2, #59
	str x8, [x0, #5480]
	ldr x2, [x0, #5568]
	ldr x3, [x0, #5576]
	extr x8, x3, x2, #59
	str x8, [x0, #5488]
	ldr x2, [x0, #5576]
	ldr x3, [x0, #5584]
	extr x8, x3, x2, #59
	str x8, [x0, #5496]
	ldr x2, [x0, #5584]
	ldr x3, [x0, #5592]
	extr x8, x3, x2, #59
	str x8, [x0, #5504]
	ldr x2, [x0, #5592]
	ldr x3, [x0, #5600]
	extr x8, x3, x2, #59
	str x8, [x0, #5512]
	ldr x2, [x0, #5600]
	ldr x3, [x0, #5608]
	extr x8, x3, x2, #59
	str x8, [x0, #5520]
	ldr x3, [x0, #5608]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #5528]
	ldr x2, [x0, #5376]
	str x2, [x0, #5056]
	ldr x2, [x0, #5384]
	str x2, [x0, #5064]
	ldr x2, [x0, #5392]
	str x2, [x0, #5072]
	ldr x2, [x0, #5400]
	str x2, [x0, #5080]
	ldr x2, [x0, #5408]
	str x2, [x0, #5088]
	ldr x2, [x0, #5416]
	str x2, [x0, #5096]
	ldr x2, [x0, #5424]
	str x2, [x0, #5104]
	ldr x2, [x0, #5432]
	str x2, [x0, #5112]
	ldr x2, [x0, #5440]
	str x2, [x0, #5120]
	ldr x2, [x0, #5448]
	str x2, [x0, #5128]
	ldr x2, [x0, #5456]
	str x2, [x0, #5136]
	ldr x2, [x0, #5464]
	str x2, [x0, #5144]
	ldr x2, [x0, #5472]
	str x2, [x0, #5152]
	ldr x2, [x0, #5480]
	str x2, [x0, #5160]
	ldr x2, [x0, #5488]
	str x2, [x0, #5168]
	ldr x2, [x0, #5496]
	str x2, [x0, #5176]
	ldr x2, [x0, #5504]
	str x2, [x0, #5184]
	ldr x2, [x0, #5512]
	str x2, [x0, #5192]
	ldr x2, [x0, #5520]
	str x2, [x0, #5200]
	ldr x2, [x0, #5528]
	str x2, [x0, #5208]
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #5216]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #5536]
	ldr x2, [x0, #5224]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5544]
	ldr x2, [x0, #5232]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5552]
	ldr x2, [x0, #5240]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5560]
	ldr x2, [x0, #5248]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5568]
	ldr x2, [x0, #5256]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5576]
	ldr x2, [x0, #5264]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5584]
	ldr x2, [x0, #5272]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5592]
	ldr x2, [x0, #5280]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5600]
	ldr x2, [x0, #5288]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5608]
	movz x10, #0, lsl #0
	ldr x2, [x0, #5296]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5536]
	ldr x2, [x0, #5304]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5544]
	ldr x2, [x0, #5312]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5552]
	ldr x2, [x0, #5320]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5560]
	ldr x2, [x0, #5328]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5568]
	ldr x2, [x0, #5336]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5576]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5576]
	ldr x2, [x0, #5344]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5584]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5584]
	ldr x2, [x0, #5352]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5592]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5592]
	ldr x2, [x0, #5360]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5600]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5600]
	ldr x2, [x0, #5368]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5608]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5608]
	ldr x3, [x0, #5544]
	ldr x2, [x0, #5216]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #5544]
	ldr x3, [x0, #5552]
	ldr x2, [x0, #5224]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5552]
	ldr x3, [x0, #5560]
	ldr x2, [x0, #5232]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5560]
	ldr x3, [x0, #5568]
	ldr x2, [x0, #5240]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5568]
	ldr x3, [x0, #5576]
	ldr x2, [x0, #5248]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5576]
	ldr x3, [x0, #5584]
	ldr x2, [x0, #5256]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5584]
	ldr x3, [x0, #5592]
	ldr x2, [x0, #5264]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5592]
	ldr x3, [x0, #5600]
	ldr x2, [x0, #5272]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	ldr x2, [x0, #5280]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5608]
	ldr x3, [x0, #5544]
	ldr x2, [x0, #5296]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #5544]
	ldr x3, [x0, #5552]
	ldr x2, [x0, #5304]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5552]
	ldr x3, [x0, #5560]
	ldr x2, [x0, #5312]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5560]
	ldr x3, [x0, #5568]
	ldr x2, [x0, #5320]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5568]
	ldr x3, [x0, #5576]
	ldr x2, [x0, #5328]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5576]
	ldr x3, [x0, #5584]
	ldr x2, [x0, #5336]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5584]
	ldr x3, [x0, #5592]
	ldr x2, [x0, #5344]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5592]
	ldr x3, [x0, #5600]
	ldr x2, [x0, #5352]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	ldr x2, [x0, #5360]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5608]
	ldr x2, [x0, #5536]
	movz x17, #38343, lsl #0
	movk x17, #31145, lsl #16
	movk x17, #23757, lsl #32
	movk x17, #7471, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #5608]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #5616]
	movz x10, #0, lsl #0
	ldr x2, [x0, #136]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5536]
	ldr x2, [x0, #144]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5544]
	ldr x2, [x0, #152]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5552]
	ldr x2, [x0, #160]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5560]
	ldr x2, [x0, #168]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5568]
	ldr x2, [x0, #176]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5576]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5576]
	ldr x2, [x0, #184]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5584]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5584]
	ldr x2, [x0, #192]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5592]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5592]
	ldr x2, [x0, #200]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5600]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	adds x3, x3, x10
	str x3, [x0, #5608]
	ldr x3, [x0, #5616]
	adcs x3, x3, x12
	str x3, [x0, #5616]
	ldr x2, [x0, #5544]
	str x2, [x0, #5376]
	ldr x2, [x0, #5552]
	str x2, [x0, #5384]
	ldr x2, [x0, #5560]
	str x2, [x0, #5392]
	ldr x2, [x0, #5568]
	str x2, [x0, #5400]
	ldr x2, [x0, #5576]
	str x2, [x0, #5408]
	ldr x2, [x0, #5584]
	str x2, [x0, #5416]
	ldr x2, [x0, #5592]
	str x2, [x0, #5424]
	ldr x2, [x0, #5600]
	str x2, [x0, #5432]
	ldr x2, [x0, #5608]
	str x2, [x0, #5440]
	ldr x2, [x0, #5616]
	str x2, [x0, #5448]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #5216]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #5536]
	ldr x2, [x0, #5224]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5544]
	ldr x2, [x0, #5232]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5552]
	ldr x2, [x0, #5240]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5560]
	ldr x2, [x0, #5248]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5568]
	ldr x2, [x0, #5256]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5576]
	ldr x2, [x0, #5264]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5584]
	ldr x2, [x0, #5272]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5592]
	ldr x2, [x0, #5280]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5600]
	ldr x2, [x0, #5288]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #5608]
	movz x10, #0, lsl #0
	ldr x2, [x0, #5296]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5536]
	ldr x2, [x0, #5304]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5544]
	ldr x2, [x0, #5312]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5552]
	ldr x2, [x0, #5320]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5560]
	ldr x2, [x0, #5328]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5568]
	ldr x2, [x0, #5336]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5576]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5576]
	ldr x2, [x0, #5344]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5584]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5584]
	ldr x2, [x0, #5352]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5592]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5592]
	ldr x2, [x0, #5360]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5600]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5600]
	ldr x2, [x0, #5368]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5608]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5608]
	ldr x3, [x0, #5544]
	ldr x2, [x0, #5216]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #5544]
	ldr x3, [x0, #5552]
	ldr x2, [x0, #5224]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5552]
	ldr x3, [x0, #5560]
	ldr x2, [x0, #5232]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5560]
	ldr x3, [x0, #5568]
	ldr x2, [x0, #5240]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5568]
	ldr x3, [x0, #5576]
	ldr x2, [x0, #5248]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5576]
	ldr x3, [x0, #5584]
	ldr x2, [x0, #5256]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5584]
	ldr x3, [x0, #5592]
	ldr x2, [x0, #5264]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5592]
	ldr x3, [x0, #5600]
	ldr x2, [x0, #5272]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	ldr x2, [x0, #5280]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #5608]
	ldr x3, [x0, #5544]
	ldr x2, [x0, #5296]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #5544]
	ldr x3, [x0, #5552]
	ldr x2, [x0, #5304]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5552]
	ldr x3, [x0, #5560]
	ldr x2, [x0, #5312]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5560]
	ldr x3, [x0, #5568]
	ldr x2, [x0, #5320]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5568]
	ldr x3, [x0, #5576]
	ldr x2, [x0, #5328]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5576]
	ldr x3, [x0, #5584]
	ldr x2, [x0, #5336]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5584]
	ldr x3, [x0, #5592]
	ldr x2, [x0, #5344]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5592]
	ldr x3, [x0, #5600]
	ldr x2, [x0, #5352]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	ldr x2, [x0, #5360]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #5608]
	ldr x2, [x0, #5536]
	movz x17, #38343, lsl #0
	movk x17, #31145, lsl #16
	movk x17, #23757, lsl #32
	movk x17, #7471, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #5608]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #5616]
	movz x10, #0, lsl #0
	ldr x2, [x0, #136]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5536]
	ldr x2, [x0, #144]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5544]
	ldr x2, [x0, #152]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5552]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5552]
	ldr x2, [x0, #160]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5560]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5560]
	ldr x2, [x0, #168]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5568]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5568]
	ldr x2, [x0, #176]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5576]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5576]
	ldr x2, [x0, #184]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5584]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5584]
	ldr x2, [x0, #192]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5592]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5592]
	ldr x2, [x0, #200]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #5600]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #5600]
	ldr x3, [x0, #5608]
	adds x3, x3, x10
	str x3, [x0, #5608]
	ldr x3, [x0, #5616]
	adcs x3, x3, x12
	str x3, [x0, #5616]
	ldr x2, [x0, #5544]
	str x2, [x0, #5296]
	ldr x2, [x0, #5552]
	str x2, [x0, #5304]
	ldr x2, [x0, #5560]
	str x2, [x0, #5312]
	ldr x2, [x0, #5568]
	str x2, [x0, #5320]
	ldr x2, [x0, #5576]
	str x2, [x0, #5328]
	ldr x2, [x0, #5584]
	str x2, [x0, #5336]
	ldr x2, [x0, #5592]
	str x2, [x0, #5344]
	ldr x2, [x0, #5600]
	str x2, [x0, #5352]
	ldr x2, [x0, #5608]
	str x2, [x0, #5360]
	ldr x2, [x0, #5616]
	str x2, [x0, #5368]
	ldr x2, [x0, #5376]
	str x2, [x0, #5216]
	ldr x2, [x0, #5384]
	str x2, [x0, #5224]
	ldr x2, [x0, #5392]
	str x2, [x0, #5232]
	ldr x2, [x0, #5400]
	str x2, [x0, #5240]
	ldr x2, [x0, #5408]
	str x2, [x0, #5248]
	ldr x2, [x0, #5416]
	str x2, [x0, #5256]
	ldr x2, [x0, #5424]
	str x2, [x0, #5264]
	ldr x2, [x0, #5432]
	str x2, [x0, #5272]
	ldr x2, [x0, #5440]
	str x2, [x0, #5280]
	ldr x2, [x0, #5448]
	str x2, [x0, #5288]
	cbnz x19, 20b
	movz x12, #0, lsl #0
	ldr x3, [x0, #5288]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #5216]
	ldr x2, [x0, #136]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #5216]
	ldr x3, [x0, #5224]
	ldr x2, [x0, #144]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5224]
	ldr x3, [x0, #5232]
	ldr x2, [x0, #152]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5232]
	ldr x3, [x0, #5240]
	ldr x2, [x0, #160]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5240]
	ldr x3, [x0, #5248]
	ldr x2, [x0, #168]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5248]
	ldr x3, [x0, #5256]
	ldr x2, [x0, #176]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5256]
	ldr x3, [x0, #5264]
	ldr x2, [x0, #184]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5264]
	ldr x3, [x0, #5272]
	ldr x2, [x0, #192]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5272]
	ldr x3, [x0, #5280]
	ldr x2, [x0, #200]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5280]
	ldr x3, [x0, #5288]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #5288]
	ldr x3, [x0, #5216]
	ldr x2, [x0, #136]
	subs x3, x3, x2
	str x3, [x0, #5216]
	ldr x3, [x0, #5224]
	ldr x2, [x0, #144]
	sbcs x3, x3, x2
	str x3, [x0, #5224]
	ldr x3, [x0, #5232]
	ldr x2, [x0, #152]
	sbcs x3, x3, x2
	str x3, [x0, #5232]
	ldr x3, [x0, #5240]
	ldr x2, [x0, #160]
	sbcs x3, x3, x2
	str x3, [x0, #5240]
	ldr x3, [x0, #5248]
	ldr x2, [x0, #168]
	sbcs x3, x3, x2
	str x3, [x0, #5248]
	ldr x3, [x0, #5256]
	ldr x2, [x0, #176]
	sbcs x3, x3, x2
	str x3, [x0, #5256]
	ldr x3, [x0, #5264]
	ldr x2, [x0, #184]
	sbcs x3, x3, x2
	str x3, [x0, #5264]
	ldr x3, [x0, #5272]
	ldr x2, [x0, #192]
	sbcs x3, x3, x2
	str x3, [x0, #5272]
	ldr x3, [x0, #5280]
	ldr x2, [x0, #200]
	sbcs x3, x3, x2
	str x3, [x0, #5280]
	ldr x3, [x0, #5288]
	add x2, x12, x12
	sbcs x3, x3, x2
	str x3, [x0, #5288]
	ldr x3, [x0, #5288]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #5216]
	ldr x2, [x0, #136]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #5216]
	ldr x3, [x0, #5224]
	ldr x2, [x0, #144]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5224]
	ldr x3, [x0, #5232]
	ldr x2, [x0, #152]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5232]
	ldr x3, [x0, #5240]
	ldr x2, [x0, #160]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5240]
	ldr x3, [x0, #5248]
	ldr x2, [x0, #168]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5248]
	ldr x3, [x0, #5256]
	ldr x2, [x0, #176]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5256]
	ldr x3, [x0, #5264]
	ldr x2, [x0, #184]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5264]
	ldr x3, [x0, #5272]
	ldr x2, [x0, #192]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5272]
	ldr x3, [x0, #5280]
	ldr x2, [x0, #200]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #5280]
	ldr x3, [x0, #5288]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #5288]
	movz x12, #0, lsl #0
	ldr x3, [x0, #5056]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #44699, lsl #0
	movk x2, #11203, lsl #16
	movk x2, #57489, lsl #32
	movk x2, #20572, lsl #48
	movz x3, #46446, lsl #0
	movk x3, #25972, lsl #16
	movk x3, #54925, lsl #32
	movk x3, #27410, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #5376]
	movz x2, #14655, lsl #0
	movk x2, #16037, lsl #16
	movk x2, #57714, lsl #32
	movk x2, #33911, lsl #48
	movz x3, #3695, lsl #0
	movk x3, #19191, lsl #16
	movk x3, #59462, lsl #32
	movk x3, #46909, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #5384]
	movz x2, #64576, lsl #0
	movk x2, #65128, lsl #16
	movk x2, #31179, lsl #32
	movk x2, #19626, lsl #48
	movz x3, #43407, lsl #0
	movk x3, #63648, lsl #16
	movk x3, #34684, lsl #32
	movk x3, #13089, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #5392]
	movz x2, #40042, lsl #0
	movk x2, #63406, lsl #16
	movk x2, #34600, lsl #32
	movk x2, #15167, lsl #48
	movz x3, #64001, lsl #0
	movk x3, #51072, lsl #16
	movk x3, #90, lsl #32
	movk x3, #5703, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #5400]
	movz x2, #19943, lsl #0
	movk x2, #53283, lsl #16
	movk x2, #16425, lsl #32
	movk x2, #51558, lsl #48
	movz x3, #45587, lsl #0
	movk x3, #12252, lsl #16
	movk x3, #49110, lsl #32
	movk x3, #13977, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #5408]
	movz x2, #3449, lsl #0
	movk x2, #21812, lsl #16
	movk x2, #29962, lsl #32
	movk x2, #38751, lsl #48
	movz x3, #62086, lsl #0
	movk x3, #43723, lsl #16
	movk x3, #35573, lsl #32
	movk x3, #26784, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #5416]
	movz x2, #29532, lsl #0
	movk x2, #46684, lsl #16
	movk x2, #27223, lsl #32
	movk x2, #48387, lsl #48
	movz x3, #36003, lsl #0
	movk x3, #18851, lsl #16
	movk x3, #38312, lsl #32
	movk x3, #17148, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #5424]
	movz x2, #14152, lsl #0
	movk x2, #14283, lsl #16
	movk x2, #63611, lsl #32
	movk x2, #3702, lsl #48
	movz x3, #51383, lsl #0
	movk x3, #51252, lsl #16
	movk x3, #1924, lsl #32
	movk x3, #61833, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #5432]
	movz x2, #409, lsl #0
	movk x2, #0, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #102, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #5440]
	movz x7, #0, lsl #0
	ldr x4, [x0, #5376]
	ldr x5, [x0, #5384]
	ldr x16, [x0, #5392]
	ldr x17, [x0, #5400]
	movz x6, #38343, lsl #0
	movk x6, #31145, lsl #16
	movk x6, #23757, lsl #32
	movk x6, #7471, lsl #48
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
	movz x23, #0, lsl #0
	ldr x1, [x0, #5216]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x0, #5408]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #5416]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #5424]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #5432]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #5440]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #5440]
	umulh x2, x1, x3
	adcs x22, x22, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #5408]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #5416]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #5424]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #5432]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	mul x1, x8, x6
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #192]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #200]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #200]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x23, x23, x7
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #192]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	adcs x23, x23, x7
	ldr x1, [x0, #5224]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #5408]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #5416]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #5424]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #5432]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #5440]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #5440]
	umulh x2, x1, x3
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #5408]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #5416]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #5424]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #5432]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x23, x23, x7
	mul x1, x9, x6
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adds x9, x9, x2
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
	ldr x3, [x0, #192]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #200]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #200]
	umulh x2, x1, x3
	adcs x23, x23, x2
	adcs x8, x8, x7
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adds x10, x10, x2
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
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #192]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x23, x23, x7
	adcs x8, x8, x7
	ldr x1, [x0, #5232]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #5408]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #5416]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #5424]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #5432]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #5440]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #5440]
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
	ldr x3, [x0, #5408]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #5416]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #5424]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #5432]
	umulh x2, x1, x3
	adcs x23, x23, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adds x10, x10, x2
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
	ldr x3, [x0, #192]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #200]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #200]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adds x11, x11, x2
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
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #192]
	umulh x2, x1, x3
	adcs x23, x23, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #5240]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #5408]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #5416]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #5424]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #5432]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #5440]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #5440]
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
	ldr x3, [x0, #5408]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #5416]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #5424]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #5432]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adds x11, x11, x2
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
	ldr x3, [x0, #192]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #200]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #200]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adds x12, x12, x2
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
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #192]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x1, [x0, #5248]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #5408]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #5416]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #5424]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #5432]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #5440]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #5440]
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
	ldr x3, [x0, #5408]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #5416]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #5424]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #5432]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	mul x1, x12, x6
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adds x12, x12, x2
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
	adcs x23, x23, x2
	ldr x3, [x0, #192]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #200]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #200]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adds x13, x13, x2
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
	adcs x23, x23, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #192]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x1, [x0, #5256]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x21, x21, x2
	ldr x3, [x0, #5408]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #5416]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #5424]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #5432]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #5440]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #5440]
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
	ldr x3, [x0, #5408]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #5416]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #5424]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #5432]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	mul x1, x13, x6
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adds x13, x13, x2
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
	adcs x23, x23, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #192]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #200]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #200]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adds x14, x14, x2
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
	adcs x23, x23, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #192]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	ldr x1, [x0, #5264]
	mul x2, x1, x4
	adds x14, x14, x2
	mul x2, x1, x5
	adcs x15, x15, x2
	mul x2, x1, x16
	adcs x21, x21, x2
	mul x2, x1, x17
	adcs x22, x22, x2
	ldr x3, [x0, #5408]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #5416]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #5424]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #5432]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #5440]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #5440]
	umulh x2, x1, x3
	adcs x12, x12, x2
	umulh x2, x1, x4
	adds x15, x15, x2
	umulh x2, x1, x5
	adcs x21, x21, x2
	umulh x2, x1, x16
	adcs x22, x22, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	ldr x3, [x0, #5408]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #5416]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #5424]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #5432]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	mul x1, x14, x6
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adds x14, x14, x2
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
	adcs x23, x23, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #192]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #200]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #200]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adds x15, x15, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #192]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #5272]
	mul x2, x1, x4
	adds x15, x15, x2
	mul x2, x1, x5
	adcs x21, x21, x2
	mul x2, x1, x16
	adcs x22, x22, x2
	mul x2, x1, x17
	adcs x23, x23, x2
	ldr x3, [x0, #5408]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #5416]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #5424]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #5432]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #5440]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #5440]
	umulh x2, x1, x3
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x21, x21, x2
	umulh x2, x1, x5
	adcs x22, x22, x2
	umulh x2, x1, x16
	adcs x23, x23, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #5408]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #5416]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #5424]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #5432]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x15, x6
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adds x15, x15, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #160]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #168]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #176]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #184]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #192]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #200]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #200]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adds x21, x21, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #152]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #160]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #168]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #176]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #192]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x14, x14, x7
	ldr x1, [x0, #5280]
	mul x2, x1, x4
	adds x21, x21, x2
	mul x2, x1, x5
	adcs x22, x22, x2
	mul x2, x1, x16
	adcs x23, x23, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #5408]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #5416]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #5424]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #5432]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #5440]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #5440]
	umulh x2, x1, x3
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x22, x22, x2
	umulh x2, x1, x5
	adcs x23, x23, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	ldr x3, [x0, #5408]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #5416]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #5424]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #5432]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x1, x21, x6
	ldr x3, [x0, #136]
	mul x2, x1, x3
	adds x21, x21, x2
	ldr x3, [x0, #144]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #152]
	mul x2, x1, x3
	adcs x23, x23, x2
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
	ldr x3, [x0, #192]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #200]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #200]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x3, [x0, #136]
	umulh x2, x1, x3
	adds x22, x22, x2
	ldr x3, [x0, #144]
	umulh x2, x1, x3
	adcs x23, x23, x2
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
	ldr x3, [x0, #184]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #192]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	adcs x15, x15, x7
	ldr x2, [x0, #136]
	subs x1, x22, x2
	ldr x2, [x0, #144]
	sbcs x3, x23, x2
	ldr x2, [x0, #152]
	sbcs x4, x8, x2
	ldr x2, [x0, #160]
	sbcs x5, x9, x2
	ldr x2, [x0, #168]
	sbcs x6, x10, x2
	ldr x2, [x0, #176]
	sbcs x16, x11, x2
	ldr x2, [x0, #184]
	sbcs x17, x12, x2
	ldr x2, [x0, #192]
	sbcs x24, x13, x2
	ldr x2, [x0, #200]
	sbcs x25, x14, x2
	sbcs x2, x15, x7
	csel x22, x1, x22, hs
	csel x23, x3, x23, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	csel x11, x16, x11, hs
	csel x12, x17, x12, hs
	csel x13, x24, x13, hs
	csel x14, x25, x14, hs
	str x22, [x0, #2152]
	str x23, [x0, #2160]
	str x8, [x0, #2168]
	str x9, [x0, #2176]
	str x10, [x0, #2184]
	str x11, [x0, #2192]
	str x12, [x0, #2200]
	str x13, [x0, #2208]
	str x14, [x0, #2216]
	ldr x19, [x0, #5704]
	ldr x21, [x0, #5712]
	ldr x22, [x0, #5720]
	ldr x23, [x0, #5728]
	ldr x24, [x0, #5736]
	ldr x25, [x0, #5744]
	ret
	.p2align 6
