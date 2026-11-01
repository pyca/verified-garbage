// The functions of `src/idea.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_idea_expand_key:
	ldr x9, [x0, #0]
	ror x9, x9, #8
	movz x10, #255, lsl #0
	movk x10, #255, lsl #16
	movk x10, #255, lsl #32
	movk x10, #255, lsl #48
	and x11, x9, x10
	ldr x9, [x0, #0]
	ror x9, x9, #56
	movz x10, #65280, lsl #0
	movk x10, #65280, lsl #16
	movk x10, #65280, lsl #32
	movk x10, #65280, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #0]
	ldr x9, [x0, #8]
	ror x9, x9, #8
	movz x10, #255, lsl #0
	movk x10, #255, lsl #16
	movk x10, #255, lsl #32
	movk x10, #255, lsl #48
	and x11, x9, x10
	ldr x9, [x0, #8]
	ror x9, x9, #56
	movz x10, #65280, lsl #0
	movk x10, #65280, lsl #16
	movk x10, #65280, lsl #32
	movk x10, #65280, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #8]
	ldr x9, [x0, #0]
	ror x9, x9, #47
	movz x10, #1, lsl #0
	movk x10, #1, lsl #16
	and x11, x9, x10
	ldr x9, [x0, #0]
	ror x9, x9, #31
	movz x10, #510, lsl #0
	movk x10, #510, lsl #16
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #15
	movz x10, #65024, lsl #0
	movk x10, #65024, lsl #16
	movk x10, #65024, lsl #32
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #47
	movz x10, #0, lsl #0
	movk x10, #1, lsl #32
	movk x10, #1, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #31
	movz x10, #0, lsl #0
	movk x10, #510, lsl #32
	movk x10, #510, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #15
	movz x10, #0, lsl #0
	movk x10, #65024, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #16]
	ldr x9, [x0, #8]
	ror x9, x9, #47
	movz x10, #1, lsl #0
	movk x10, #1, lsl #16
	and x11, x9, x10
	ldr x9, [x0, #8]
	ror x9, x9, #31
	movz x10, #510, lsl #0
	movk x10, #510, lsl #16
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #15
	movz x10, #65024, lsl #0
	movk x10, #65024, lsl #16
	movk x10, #65024, lsl #32
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #47
	movz x10, #0, lsl #0
	movk x10, #1, lsl #32
	movk x10, #1, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #31
	movz x10, #0, lsl #0
	movk x10, #510, lsl #32
	movk x10, #510, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #15
	movz x10, #0, lsl #0
	movk x10, #65024, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #24]
	ldr x9, [x0, #8]
	ror x9, x9, #6
	movz x10, #3, lsl #0
	movk x10, #3, lsl #16
	movk x10, #3, lsl #32
	movk x10, #3, lsl #48
	and x11, x9, x10
	ldr x9, [x0, #0]
	ror x9, x9, #54
	movz x10, #1020, lsl #0
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #38
	movz x10, #64512, lsl #0
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #54
	movz x10, #0, lsl #0
	movk x10, #1020, lsl #16
	movk x10, #1020, lsl #32
	movk x10, #1020, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #38
	movz x10, #0, lsl #0
	movk x10, #64512, lsl #16
	movk x10, #64512, lsl #32
	movk x10, #64512, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #32]
	ldr x9, [x0, #0]
	ror x9, x9, #6
	movz x10, #3, lsl #0
	movk x10, #3, lsl #16
	movk x10, #3, lsl #32
	movk x10, #3, lsl #48
	and x11, x9, x10
	ldr x9, [x0, #8]
	ror x9, x9, #54
	movz x10, #1020, lsl #0
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #38
	movz x10, #64512, lsl #0
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #54
	movz x10, #0, lsl #0
	movk x10, #1020, lsl #16
	movk x10, #1020, lsl #32
	movk x10, #1020, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #38
	movz x10, #0, lsl #0
	movk x10, #64512, lsl #16
	movk x10, #64512, lsl #32
	movk x10, #64512, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #40]
	ldr x9, [x0, #8]
	ror x9, x9, #29
	movz x10, #7, lsl #0
	movk x10, #7, lsl #16
	movk x10, #7, lsl #32
	and x11, x9, x10
	ldr x9, [x0, #8]
	ror x9, x9, #13
	movz x10, #2040, lsl #0
	movk x10, #2040, lsl #16
	movk x10, #2040, lsl #32
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #61
	movz x10, #63488, lsl #0
	movk x10, #63488, lsl #16
	movk x10, #63488, lsl #32
	movk x10, #63488, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #29
	movz x10, #0, lsl #0
	movk x10, #7, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #13
	movz x10, #0, lsl #0
	movk x10, #2040, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #48]
	ldr x9, [x0, #0]
	ror x9, x9, #29
	movz x10, #7, lsl #0
	movk x10, #7, lsl #16
	movk x10, #7, lsl #32
	and x11, x9, x10
	ldr x9, [x0, #0]
	ror x9, x9, #13
	movz x10, #2040, lsl #0
	movk x10, #2040, lsl #16
	movk x10, #2040, lsl #32
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #61
	movz x10, #63488, lsl #0
	movk x10, #63488, lsl #16
	movk x10, #63488, lsl #32
	movk x10, #63488, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #29
	movz x10, #0, lsl #0
	movk x10, #7, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #13
	movz x10, #0, lsl #0
	movk x10, #2040, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #56]
	ldr x9, [x0, #8]
	ror x9, x9, #52
	movz x10, #15, lsl #0
	and x11, x9, x10
	ldr x9, [x0, #8]
	ror x9, x9, #36
	movz x10, #4080, lsl #0
	movk x10, #4080, lsl #16
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #20
	movz x10, #61440, lsl #0
	movk x10, #61440, lsl #16
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #52
	movz x10, #0, lsl #0
	movk x10, #15, lsl #16
	movk x10, #15, lsl #32
	movk x10, #15, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #36
	movz x10, #0, lsl #0
	movk x10, #4080, lsl #32
	movk x10, #4080, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #20
	movz x10, #0, lsl #0
	movk x10, #61440, lsl #32
	movk x10, #61440, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #64]
	ldr x9, [x0, #0]
	ror x9, x9, #52
	movz x10, #15, lsl #0
	and x11, x9, x10
	ldr x9, [x0, #0]
	ror x9, x9, #36
	movz x10, #4080, lsl #0
	movk x10, #4080, lsl #16
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #20
	movz x10, #61440, lsl #0
	movk x10, #61440, lsl #16
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #52
	movz x10, #0, lsl #0
	movk x10, #15, lsl #16
	movk x10, #15, lsl #32
	movk x10, #15, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #36
	movz x10, #0, lsl #0
	movk x10, #4080, lsl #32
	movk x10, #4080, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #20
	movz x10, #0, lsl #0
	movk x10, #61440, lsl #32
	movk x10, #61440, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #72]
	ldr x9, [x0, #0]
	ror x9, x9, #11
	movz x10, #31, lsl #0
	movk x10, #31, lsl #16
	movk x10, #31, lsl #32
	movk x10, #31, lsl #48
	and x11, x9, x10
	ldr x9, [x0, #0]
	ror x9, x9, #59
	movz x10, #8160, lsl #0
	movk x10, #8160, lsl #16
	movk x10, #8160, lsl #32
	movk x10, #8160, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #43
	movz x10, #57344, lsl #0
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #43
	movz x10, #0, lsl #0
	movk x10, #57344, lsl #16
	movk x10, #57344, lsl #32
	movk x10, #57344, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #80]
	ldr x9, [x0, #8]
	ror x9, x9, #11
	movz x10, #31, lsl #0
	movk x10, #31, lsl #16
	movk x10, #31, lsl #32
	movk x10, #31, lsl #48
	and x11, x9, x10
	ldr x9, [x0, #8]
	ror x9, x9, #59
	movz x10, #8160, lsl #0
	movk x10, #8160, lsl #16
	movk x10, #8160, lsl #32
	movk x10, #8160, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #43
	movz x10, #57344, lsl #0
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #43
	movz x10, #0, lsl #0
	movk x10, #57344, lsl #16
	movk x10, #57344, lsl #32
	movk x10, #57344, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #88]
	ldr x9, [x0, #0]
	ror x9, x9, #34
	movz x10, #63, lsl #0
	movk x10, #63, lsl #16
	and x11, x9, x10
	ldr x9, [x0, #0]
	ror x9, x9, #18
	movz x10, #16320, lsl #0
	movk x10, #16320, lsl #16
	movk x10, #16320, lsl #32
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #0]
	ror x9, x9, #2
	movz x10, #49152, lsl #0
	movk x10, #49152, lsl #16
	movk x10, #49152, lsl #32
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #34
	movz x10, #0, lsl #0
	movk x10, #63, lsl #32
	movk x10, #63, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #18
	movz x10, #0, lsl #0
	movk x10, #16320, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	ldr x9, [x0, #8]
	ror x9, x9, #2
	movz x10, #0, lsl #0
	movk x10, #49152, lsl #48
	and x9, x9, x10
	eor x11, x11, x9
	str x11, [x1, #96]
	ret
	.p2align 6

vg_idea_invert_key:
	movz x15, #65535, lsl #0
	ldr w5, [x0, #96]
	add x6, x5, #0
	movz x7, #15, lsl #0
20:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 20b
	add x3, x6, #0
	add x9, x3, #0
	ldr w4, [x0, #96]
	lsr x4, x4, #16
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w4, [x0, #100]
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w5, [x0, #100]
	lsr x5, x5, #16
	add x6, x5, #0
	movz x7, #15, lsl #0
21:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 21b
	add x3, x6, #0
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #0]
	ldr w3, [x0, #92]
	and x3, x3, x15
	add x9, x3, #0
	ldr w3, [x0, #92]
	lsr x3, x3, #16
	and x3, x3, x15
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w5, [x0, #84]
	add x6, x5, #0
	movz x7, #15, lsl #0
22:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 22b
	add x3, x6, #0
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w4, [x0, #88]
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #8]
	ldr w4, [x0, #84]
	lsr x4, x4, #16
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	add x9, x3, #0
	ldr w5, [x0, #88]
	lsr x5, x5, #16
	add x6, x5, #0
	movz x7, #15, lsl #0
23:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 23b
	add x3, x6, #0
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w3, [x0, #80]
	and x3, x3, x15
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w3, [x0, #80]
	lsr x3, x3, #16
	and x3, x3, x15
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #16]
	ldr w5, [x0, #72]
	add x6, x5, #0
	movz x7, #15, lsl #0
24:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 24b
	add x3, x6, #0
	add x9, x3, #0
	ldr w4, [x0, #76]
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w4, [x0, #72]
	lsr x4, x4, #16
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w5, [x0, #76]
	lsr x5, x5, #16
	add x6, x5, #0
	movz x7, #15, lsl #0
25:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 25b
	add x3, x6, #0
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #24]
	ldr w3, [x0, #68]
	and x3, x3, x15
	add x9, x3, #0
	ldr w3, [x0, #68]
	lsr x3, x3, #16
	and x3, x3, x15
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w5, [x0, #60]
	add x6, x5, #0
	movz x7, #15, lsl #0
26:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 26b
	add x3, x6, #0
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w4, [x0, #64]
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #32]
	ldr w4, [x0, #60]
	lsr x4, x4, #16
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	add x9, x3, #0
	ldr w5, [x0, #64]
	lsr x5, x5, #16
	add x6, x5, #0
	movz x7, #15, lsl #0
27:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 27b
	add x3, x6, #0
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w3, [x0, #56]
	and x3, x3, x15
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w3, [x0, #56]
	lsr x3, x3, #16
	and x3, x3, x15
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #40]
	ldr w5, [x0, #48]
	add x6, x5, #0
	movz x7, #15, lsl #0
28:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 28b
	add x3, x6, #0
	add x9, x3, #0
	ldr w4, [x0, #52]
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w4, [x0, #48]
	lsr x4, x4, #16
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w5, [x0, #52]
	lsr x5, x5, #16
	add x6, x5, #0
	movz x7, #15, lsl #0
29:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 29b
	add x3, x6, #0
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #48]
	ldr w3, [x0, #44]
	and x3, x3, x15
	add x9, x3, #0
	ldr w3, [x0, #44]
	lsr x3, x3, #16
	and x3, x3, x15
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w5, [x0, #36]
	add x6, x5, #0
	movz x7, #15, lsl #0
210:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 210b
	add x3, x6, #0
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w4, [x0, #40]
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #56]
	ldr w4, [x0, #36]
	lsr x4, x4, #16
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	add x9, x3, #0
	ldr w5, [x0, #40]
	lsr x5, x5, #16
	add x6, x5, #0
	movz x7, #15, lsl #0
211:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 211b
	add x3, x6, #0
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w3, [x0, #32]
	and x3, x3, x15
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w3, [x0, #32]
	lsr x3, x3, #16
	and x3, x3, x15
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #64]
	ldr w5, [x0, #24]
	add x6, x5, #0
	movz x7, #15, lsl #0
212:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 212b
	add x3, x6, #0
	add x9, x3, #0
	ldr w4, [x0, #28]
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w4, [x0, #24]
	lsr x4, x4, #16
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w5, [x0, #28]
	lsr x5, x5, #16
	add x6, x5, #0
	movz x7, #15, lsl #0
213:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 213b
	add x3, x6, #0
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #72]
	ldr w3, [x0, #20]
	and x3, x3, x15
	add x9, x3, #0
	ldr w3, [x0, #20]
	lsr x3, x3, #16
	and x3, x3, x15
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w5, [x0, #12]
	add x6, x5, #0
	movz x7, #15, lsl #0
214:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 214b
	add x3, x6, #0
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w4, [x0, #16]
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #80]
	ldr w4, [x0, #12]
	lsr x4, x4, #16
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	add x9, x3, #0
	ldr w5, [x0, #16]
	lsr x5, x5, #16
	add x6, x5, #0
	movz x7, #15, lsl #0
215:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 215b
	add x3, x6, #0
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w3, [x0, #8]
	and x3, x3, x15
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w3, [x0, #8]
	lsr x3, x3, #16
	and x3, x3, x15
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #88]
	ldr w5, [x0, #0]
	add x6, x5, #0
	movz x7, #15, lsl #0
216:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 216b
	add x3, x6, #0
	add x9, x3, #0
	ldr w4, [x0, #0]
	lsr x4, x4, #16
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #16
	orr x9, x9, x3
	ldr w4, [x0, #4]
	movz x3, #0, lsl #0
	sub x3, x3, x4
	and x3, x3, x15
	lsl x3, x3, #32
	orr x9, x9, x3
	ldr w5, [x0, #4]
	lsr x5, x5, #16
	add x6, x5, #0
	movz x7, #15, lsl #0
217:
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x6, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x5, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	sub x7, x7, #1
	cbnz x7, 217b
	add x3, x6, #0
	lsl x3, x3, #48
	orr x9, x9, x3
	str x9, [x1, #96]
	ret
	.p2align 6

vg_idea_ecb:
	cbz x2, 20f
	movz x15, #65535, lsl #0
22:
	ldrb w3, [x1, #0]
	lsl x3, x3, #8
	ldrb w7, [x1, #1]
	orr x3, x3, x7
	ldrb w4, [x1, #2]
	lsl x4, x4, #8
	ldrb w7, [x1, #3]
	orr x4, x4, x7
	ldrb w5, [x1, #4]
	lsl x5, x5, #8
	ldrb w7, [x1, #5]
	orr x5, x5, x7
	ldrb w6, [x1, #6]
	lsl x6, x6, #8
	ldrb w7, [x1, #7]
	orr x6, x6, x7
	ldr w8, [x0, #0]
	ldr w9, [x0, #4]
	ldr w13, [x0, #8]
	sub x11, x3, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x8, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x3, x12, x15
	lsr x14, x9, #16
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x14, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	lsr x14, x8, #16
	add x4, x4, x14
	and x4, x4, x15
	add x5, x5, x9
	and x5, x5, x15
	eor x7, x3, x5
	sub x11, x7, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x13, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x7, x12, x15
	eor x14, x4, x6
	add x14, x14, x7
	lsr x10, x13, #16
	sub x11, x14, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x10, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x14, x12, x15
	add x7, x7, x14
	and x7, x7, x15
	eor x3, x3, x14
	eor x5, x5, x14
	eor x4, x4, x7
	eor x6, x6, x7
	add x14, x4, #0
	add x4, x5, #0
	add x5, x14, #0
	ldr w8, [x0, #12]
	ldr w9, [x0, #16]
	ldr w13, [x0, #20]
	sub x11, x3, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x8, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x3, x12, x15
	lsr x14, x9, #16
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x14, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	lsr x14, x8, #16
	add x4, x4, x14
	and x4, x4, x15
	add x5, x5, x9
	and x5, x5, x15
	eor x7, x3, x5
	sub x11, x7, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x13, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x7, x12, x15
	eor x14, x4, x6
	add x14, x14, x7
	lsr x10, x13, #16
	sub x11, x14, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x10, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x14, x12, x15
	add x7, x7, x14
	and x7, x7, x15
	eor x3, x3, x14
	eor x5, x5, x14
	eor x4, x4, x7
	eor x6, x6, x7
	add x14, x4, #0
	add x4, x5, #0
	add x5, x14, #0
	ldr w8, [x0, #24]
	ldr w9, [x0, #28]
	ldr w13, [x0, #32]
	sub x11, x3, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x8, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x3, x12, x15
	lsr x14, x9, #16
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x14, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	lsr x14, x8, #16
	add x4, x4, x14
	and x4, x4, x15
	add x5, x5, x9
	and x5, x5, x15
	eor x7, x3, x5
	sub x11, x7, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x13, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x7, x12, x15
	eor x14, x4, x6
	add x14, x14, x7
	lsr x10, x13, #16
	sub x11, x14, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x10, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x14, x12, x15
	add x7, x7, x14
	and x7, x7, x15
	eor x3, x3, x14
	eor x5, x5, x14
	eor x4, x4, x7
	eor x6, x6, x7
	add x14, x4, #0
	add x4, x5, #0
	add x5, x14, #0
	ldr w8, [x0, #36]
	ldr w9, [x0, #40]
	ldr w13, [x0, #44]
	sub x11, x3, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x8, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x3, x12, x15
	lsr x14, x9, #16
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x14, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	lsr x14, x8, #16
	add x4, x4, x14
	and x4, x4, x15
	add x5, x5, x9
	and x5, x5, x15
	eor x7, x3, x5
	sub x11, x7, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x13, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x7, x12, x15
	eor x14, x4, x6
	add x14, x14, x7
	lsr x10, x13, #16
	sub x11, x14, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x10, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x14, x12, x15
	add x7, x7, x14
	and x7, x7, x15
	eor x3, x3, x14
	eor x5, x5, x14
	eor x4, x4, x7
	eor x6, x6, x7
	add x14, x4, #0
	add x4, x5, #0
	add x5, x14, #0
	ldr w8, [x0, #48]
	ldr w9, [x0, #52]
	ldr w13, [x0, #56]
	sub x11, x3, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x8, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x3, x12, x15
	lsr x14, x9, #16
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x14, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	lsr x14, x8, #16
	add x4, x4, x14
	and x4, x4, x15
	add x5, x5, x9
	and x5, x5, x15
	eor x7, x3, x5
	sub x11, x7, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x13, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x7, x12, x15
	eor x14, x4, x6
	add x14, x14, x7
	lsr x10, x13, #16
	sub x11, x14, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x10, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x14, x12, x15
	add x7, x7, x14
	and x7, x7, x15
	eor x3, x3, x14
	eor x5, x5, x14
	eor x4, x4, x7
	eor x6, x6, x7
	add x14, x4, #0
	add x4, x5, #0
	add x5, x14, #0
	ldr w8, [x0, #60]
	ldr w9, [x0, #64]
	ldr w13, [x0, #68]
	sub x11, x3, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x8, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x3, x12, x15
	lsr x14, x9, #16
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x14, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	lsr x14, x8, #16
	add x4, x4, x14
	and x4, x4, x15
	add x5, x5, x9
	and x5, x5, x15
	eor x7, x3, x5
	sub x11, x7, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x13, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x7, x12, x15
	eor x14, x4, x6
	add x14, x14, x7
	lsr x10, x13, #16
	sub x11, x14, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x10, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x14, x12, x15
	add x7, x7, x14
	and x7, x7, x15
	eor x3, x3, x14
	eor x5, x5, x14
	eor x4, x4, x7
	eor x6, x6, x7
	add x14, x4, #0
	add x4, x5, #0
	add x5, x14, #0
	ldr w8, [x0, #72]
	ldr w9, [x0, #76]
	ldr w13, [x0, #80]
	sub x11, x3, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x8, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x3, x12, x15
	lsr x14, x9, #16
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x14, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	lsr x14, x8, #16
	add x4, x4, x14
	and x4, x4, x15
	add x5, x5, x9
	and x5, x5, x15
	eor x7, x3, x5
	sub x11, x7, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x13, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x7, x12, x15
	eor x14, x4, x6
	add x14, x14, x7
	lsr x10, x13, #16
	sub x11, x14, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x10, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x14, x12, x15
	add x7, x7, x14
	and x7, x7, x15
	eor x3, x3, x14
	eor x5, x5, x14
	eor x4, x4, x7
	eor x6, x6, x7
	add x14, x4, #0
	add x4, x5, #0
	add x5, x14, #0
	ldr w8, [x0, #84]
	ldr w9, [x0, #88]
	ldr w13, [x0, #92]
	sub x11, x3, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x8, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x3, x12, x15
	lsr x14, x9, #16
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x14, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	lsr x14, x8, #16
	add x4, x4, x14
	and x4, x4, x15
	add x5, x5, x9
	and x5, x5, x15
	eor x7, x3, x5
	sub x11, x7, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x13, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x7, x12, x15
	eor x14, x4, x6
	add x14, x14, x7
	lsr x10, x13, #16
	sub x11, x14, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x10, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x14, x12, x15
	add x7, x7, x14
	and x7, x7, x15
	eor x3, x3, x14
	eor x5, x5, x14
	eor x4, x4, x7
	eor x6, x6, x7
	add x14, x4, #0
	add x4, x5, #0
	add x5, x14, #0
	ldr x8, [x0, #96]
	sub x11, x3, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x8, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x3, x12, x15
	lsr x14, x8, #48
	sub x11, x6, #1
	and x11, x11, x15
	add x11, x11, #1
	sub x12, x14, #1
	and x12, x12, x15
	add x12, x12, #1
	mul x11, x11, x12
	and x12, x11, x15
	lsr x11, x11, #16
	sub x12, x12, x11
	lsr x11, x12, #63
	add x12, x12, x11
	lsl x11, x11, #16
	add x12, x12, x11
	and x6, x12, x15
	lsr x14, x8, #16
	add x5, x5, x14
	and x5, x5, x15
	lsr x14, x8, #32
	add x4, x4, x14
	and x4, x4, x15
	strb w3, [x1, #1]
	lsr x14, x3, #8
	strb w14, [x1, #0]
	strb w5, [x1, #3]
	lsr x14, x5, #8
	strb w14, [x1, #2]
	strb w4, [x1, #5]
	lsr x14, x4, #8
	strb w14, [x1, #4]
	strb w6, [x1, #7]
	lsr x14, x6, #8
	strb w14, [x1, #6]
	add x1, x1, #8
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	ret
	.p2align 6
