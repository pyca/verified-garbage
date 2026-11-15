// The functions of `src/internal/vg_aes_expand_key_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch:
	movz x6, #31843, lsl #0
	movk x6, #31607, lsl #16
	movk x6, #27634, lsl #32
	movk x6, #50543, lsl #48
	movz x7, #304, lsl #0
	movk x7, #11111, lsl #16
	movk x7, #55294, lsl #32
	movk x7, #30379, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #33482, lsl #0
	movk x6, #32201, lsl #16
	movk x6, #23034, lsl #32
	movk x6, #61511, lsl #48
	movz x7, #54445, lsl #0
	movk x7, #44962, lsl #16
	movk x7, #42140, lsl #32
	movk x7, #49266, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #64951, lsl #0
	movk x6, #9875, lsl #16
	movk x6, #16182, lsl #32
	movk x6, #52471, lsl #48
	movz x7, #42292, lsl #0
	movk x7, #61925, lsl #16
	movk x7, #55409, lsl #32
	movk x7, #5425, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #50948, lsl #0
	movk x6, #49955, lsl #16
	movk x6, #38424, lsl #32
	movk x6, #39429, lsl #48
	movz x7, #4615, lsl #0
	movk x7, #57984, lsl #16
	movk x7, #10219, lsl #32
	movk x7, #30130, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #33545, lsl #0
	movk x6, #6700, lsl #16
	movk x6, #28187, lsl #32
	movk x6, #41050, lsl #48
	movz x7, #15186, lsl #0
	movk x7, #46038, lsl #16
	movk x7, #58153, lsl #32
	movk x7, #33839, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #53587, lsl #0
	movk x6, #60672, lsl #16
	movk x6, #64544, lsl #32
	movk x6, #23473, lsl #48
	movz x7, #52074, lsl #0
	movk x7, #14782, lsl #16
	movk x7, #19530, lsl #32
	movk x7, #53080, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #61392, lsl #0
	movk x6, #64426, lsl #16
	movk x6, #19779, lsl #32
	movk x6, #34099, lsl #48
	movz x7, #63813, lsl #0
	movk x7, #32514, lsl #16
	movk x7, #15440, lsl #32
	movk x7, #43167, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #41809, lsl #0
	movk x6, #36672, lsl #16
	movk x6, #40338, lsl #32
	movk x6, #62776, lsl #48
	movz x7, #46780, lsl #0
	movk x7, #8666, lsl #16
	movk x7, #65296, lsl #32
	movk x7, #54003, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #3277, lsl #0
	movk x6, #60435, lsl #16
	movk x6, #38751, lsl #32
	movk x6, #5956, lsl #48
	movz x7, #42948, lsl #0
	movk x7, #15742, lsl #16
	movk x7, #23908, lsl #32
	movk x7, #29465, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #33120, lsl #0
	movk x6, #56399, lsl #16
	movk x6, #10786, lsl #32
	movk x6, #34960, lsl #48
	movz x7, #60998, lsl #0
	movk x7, #5304, lsl #16
	movk x7, #24286, lsl #32
	movk x7, #56075, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #13024, lsl #0
	movk x6, #2618, lsl #16
	movk x6, #1609, lsl #32
	movk x6, #23588, lsl #48
	movz x7, #54210, lsl #0
	movk x7, #25260, lsl #16
	movk x7, #38289, lsl #32
	movk x7, #31204, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #51431, lsl #0
	movk x6, #27959, lsl #16
	movk x6, #54669, lsl #32
	movk x6, #43342, lsl #48
	movz x7, #22124, lsl #0
	movk x7, #60148, lsl #16
	movk x7, #31333, lsl #32
	movk x7, #2222, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #30906, lsl #0
	movk x6, #11813, lsl #16
	movk x6, #42524, lsl #32
	movk x6, #50868, lsl #48
	movz x7, #56808, lsl #0
	movk x7, #8052, lsl #16
	movk x7, #48459, lsl #32
	movk x7, #35467, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #15984, lsl #0
	movk x6, #26293, lsl #16
	movk x6, #840, lsl #32
	movk x6, #3830, lsl #48
	movz x7, #13665, lsl #0
	movk x7, #47447, lsl #16
	movk x7, #49542, lsl #32
	movk x7, #40477, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #63713, lsl #0
	movk x6, #4504, lsl #16
	movk x6, #55657, lsl #32
	movk x6, #38030, lsl #48
	movz x7, #7835, lsl #0
	movk x7, #59783, lsl #16
	movk x7, #21966, lsl #32
	movk x7, #57128, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #41356, lsl #0
	movk x6, #3465, lsl #16
	movk x6, #59071, lsl #32
	movk x6, #26690, lsl #48
	movz x7, #39233, lsl #0
	movk x7, #3885, lsl #16
	movk x7, #21680, lsl #32
	movk x7, #5819, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #1280, lsl #0
	movk x6, #3850, lsl #16
	movk x6, #2308, lsl #32
	movk x6, #782, lsl #48
	movz x7, #3336, lsl #0
	movk x7, #1794, lsl #16
	movk x7, #268, lsl #32
	movk x7, #2822, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	movz w6, #128, lsl #0
	dup v5.16b, w6
	movz w6, #64, lsl #0
	dup v6.16b, w6
	movz w6, #27, lsl #0
	dup v7.16b, w6
	add x5, x3, #0
	str x19, [x5, #384]
	str x20, [x5, #392]
	str x21, [x5, #400]
	str x22, [x5, #408]
	str x23, [x5, #416]
	str x24, [x5, #424]
	str x25, [x5, #432]
	str x26, [x5, #440]
	str x27, [x5, #448]
	str x28, [x5, #456]
	add x4, x1, #0
20:
	ldr x6, [x0, #0]
	str x6, [x2, #0]
	add x0, x0, #8
	add x2, x2, #8
	sub x4, x4, #8
	cbnz x4, 20b
	lsr x6, x6, #32
	sub x0, x2, x1
	lsr x3, x1, #2
	movz x1, #0, lsl #0
	add x4, x3, x3
	add x4, x4, x3
	add x4, x4, #28
	movz x7, #1, lsl #0
	str x7, [x5, #472]
21:
	cbz x1, 22f
	sub x7, x1, #4
	sub x8, x3, #8
	orr x7, x7, x8
	cbz x7, 24f
	b 25f
24:
	mov v0.d[0], x6
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x6, v0.d[0]
25:
	b 23f
22:
	mov v0.d[0], x6
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x6, v0.d[0]
	ror w6, w6, #8
	ldr x7, [x5, #472]
	eor w6, w6, w7
	lsr x8, x7, #7
	movz x9, #27, lsl #0
	mul x8, x8, x9
	lsl x7, x7, #1
	eor x7, x7, x8
	movz x9, #255, lsl #0
	and x7, x7, x9
	str x7, [x5, #472]
23:
	ldr w7, [x0, #0]
	eor w6, w6, w7
	str w6, [x2, #0]
	add x0, x0, #4
	add x2, x2, #4
	add x1, x1, #1
	sub x7, x1, x3
	cbz x7, 26f
	b 27f
26:
	movz x1, #0, lsl #0
27:
	sub x4, x4, #1
	cbnz x4, 21b
	ldr x19, [x5, #384]
	ldr x20, [x5, #392]
	ldr x21, [x5, #400]
	ldr x22, [x5, #408]
	ldr x23, [x5, #416]
	ldr x24, [x5, #424]
	ldr x25, [x5, #432]
	ldr x26, [x5, #440]
	ldr x27, [x5, #448]
	ldr x28, [x5, #456]
	ret
	.p2align 6
