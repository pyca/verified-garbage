// The functions of `src/internal/vg_camellia_prepare_keys.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_prepare_keys:
	add x5, x3, #0
	str x19, [x5, #2944]
	str x20, [x5, #2952]
	str x21, [x5, #2960]
	str x22, [x5, #2968]
	str x23, [x5, #2976]
	str x24, [x5, #2984]
	str x25, [x5, #2992]
	str x26, [x5, #3000]
	str x27, [x5, #3008]
	str x28, [x5, #3016]
	movz x21, #255, lsl #0
	movk x21, #255, lsl #16
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x5, #384]
	movz x21, #65280, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x5, #392]
	movz x21, #0, lsl #0
	movk x21, #65280, lsl #32
	movk x21, #255, lsl #48
	str x21, [x5, #400]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	str x21, [x5, #408]
	movz x21, #0, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #255, lsl #32
	str x21, [x5, #416]
	sub x21, x1, #18
	cbz x2, 20f
	cbz x21, 22f
	add x4, x5, #0
	add x4, x4, #2816
	add x0, x0, #256
	movz x22, #30, lsl #0
	b 23f
22:
	add x4, x5, #0
	add x4, x4, #2304
	add x0, x0, #192
	movz x22, #22, lsl #0
23:
	add x1, x5, #0
	add x1, x1, #768
	ldr x6, [x0, #0]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	ldr x6, [x0, #8]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	sub x0, x0, #8
24:
	ldr x6, [x0, #0]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	sub x0, x0, #8
	sub x22, x22, #1
	cbnz x22, 24b
	sub x0, x0, #8
	ldr x6, [x0, #0]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	ldr x6, [x0, #8]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	b 21f
20:
	cbz x21, 25f
	add x4, x5, #0
	add x4, x4, #2816
	movz x22, #34, lsl #0
	b 26f
25:
	add x4, x5, #0
	add x4, x4, #2304
	movz x22, #26, lsl #0
26:
	add x1, x5, #0
	add x1, x1, #768
27:
	ldr x6, [x0, #0]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	add x0, x0, #8
	sub x22, x22, #1
	cbnz x22, 27b
21:
	ldr x19, [x5, #2944]
	ldr x20, [x5, #2952]
	ldr x21, [x5, #2960]
	ldr x22, [x5, #2968]
	ldr x23, [x5, #2976]
	ldr x24, [x5, #2984]
	ldr x25, [x5, #2992]
	ldr x26, [x5, #3000]
	ldr x27, [x5, #3008]
	ldr x28, [x5, #3016]
	ret
	.p2align 6
