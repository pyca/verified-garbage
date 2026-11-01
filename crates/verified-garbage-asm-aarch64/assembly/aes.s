// The functions of `src/aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key:
	sub sp, sp, #512
	add x3, sp, #0
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
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x13, x7
	eor x16, x13, x10
	eor x17, x13, x8
	eor x11, x12, x11
	eor x19, x11, x6
	eor x10, x19, x10
	eor x20, x15, x14
	eor x21, x19, x13
	eor x7, x19, x7
	eor x22, x7, x17
	eor x9, x9, x20
	eor x8, x9, x8
	eor x9, x9, x12
	eor x12, x8, x6
	eor x23, x8, x11
	eor x24, x9, x16
	eor x25, x6, x24
	eor x26, x23, x24
	eor x27, x23, x17
	eor x11, x11, x24
	str x27, [x5, #0]
	eor x27, x15, x11
	eor x13, x13, x11
	str x13, [x5, #8]
	and x13, x20, x8
	str x20, [x5, #16]
	and x20, x22, x12
	eor x20, x20, x13
	str x22, [x5, #24]
	and x22, x10, x6
	eor x22, x22, x13
	and x13, x15, x11
	str x15, [x5, #32]
	and x15, x7, x19
	eor x15, x15, x13
	str x7, [x5, #40]
	and x7, x21, x25
	eor x7, x7, x13
	and x13, x16, x24
	str x16, [x5, #48]
	and x16, x14, x26
	eor x16, x16, x13
	str x14, [x5, #56]
	and x14, x17, x23
	eor x14, x14, x13
	eor x20, x20, x16
	eor x22, x22, x14
	eor x15, x15, x16
	eor x7, x7, x14
	eor x20, x20, x9
	ldr x9, [x5, #0]
	eor x22, x22, x9
	eor x15, x15, x27
	ldr x27, [x5, #8]
	eor x7, x7, x27
	eor x27, x20, x22
	and x20, x20, x15
	eor x9, x7, x20
	and x14, x27, x9
	eor x14, x14, x22
	eor x16, x15, x7
	eor x22, x22, x20
	and x22, x22, x16
	eor x22, x22, x7
	eor x15, x15, x22
	eor x16, x9, x22
	and x7, x7, x16
	eor x15, x7, x15
	eor x9, x9, x7
	and x9, x14, x9
	eor x27, x27, x9
	eor x9, x27, x15
	eor x7, x14, x22
	eor x16, x14, x27
	eor x20, x22, x15
	eor x13, x7, x9
	and x8, x20, x8
	and x12, x15, x12
	and x6, x22, x6
	and x11, x16, x11
	and x19, x27, x19
	and x25, x14, x25
	and x24, x7, x24
	and x26, x13, x26
	and x23, x9, x23
	str x12, [x5, #8]
	ldr x12, [x5, #16]
	and x20, x20, x12
	ldr x12, [x5, #24]
	and x15, x15, x12
	and x22, x22, x10
	ldr x10, [x5, #32]
	and x16, x16, x10
	ldr x10, [x5, #40]
	and x27, x27, x10
	and x14, x14, x21
	ldr x21, [x5, #48]
	and x7, x7, x21
	ldr x21, [x5, #56]
	and x13, x13, x21
	and x9, x9, x17
	eor x7, x7, x13
	eor x22, x15, x22
	eor x27, x25, x27
	eor x20, x20, x15
	eor x15, x6, x16
	eor x6, x6, x25
	eor x23, x26, x23
	eor x8, x8, x11
	eor x24, x24, x26
	eor x13, x13, x9
	eor x16, x16, x27
	eor x15, x15, x8
	eor x9, x19, x7
	eor x11, x11, x24
	eor x7, x7, x15
	eor x14, x14, x15
	eor x23, x23, x9
	eor x20, x20, x9
	eor x19, x19, x11
	eor x14, x14, x23
	ldr x9, [x5, #8]
	eor x9, x9, x20
	eor x11, x11, x20
	eor x16, x16, x23
	eor x16, x16, x28
	eor x27, x27, x7
	eor x27, x27, x28
	eor x7, x19, x14
	eor x10, x8, x9
	eor x9, x6, x9
	eor x8, x22, x14
	eor x12, x19, x10
	eor x12, x12, x28
	eor x13, x13, x7
	eor x13, x13, x28
	str x13, [x5, #8]
	add x13, x11, #0
	ldr x11, [x5, #8]
	add x7, x16, #0
	add x6, x27, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
25:
	b 23f
22:
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x13, x7
	eor x16, x13, x10
	eor x17, x13, x8
	eor x11, x12, x11
	eor x19, x11, x6
	eor x10, x19, x10
	eor x20, x15, x14
	eor x21, x19, x13
	eor x7, x19, x7
	eor x22, x7, x17
	eor x9, x9, x20
	eor x8, x9, x8
	eor x9, x9, x12
	eor x12, x8, x6
	eor x23, x8, x11
	eor x24, x9, x16
	eor x25, x6, x24
	eor x26, x23, x24
	eor x27, x23, x17
	eor x11, x11, x24
	str x27, [x5, #0]
	eor x27, x15, x11
	eor x13, x13, x11
	str x13, [x5, #8]
	and x13, x20, x8
	str x20, [x5, #16]
	and x20, x22, x12
	eor x20, x20, x13
	str x22, [x5, #24]
	and x22, x10, x6
	eor x22, x22, x13
	and x13, x15, x11
	str x15, [x5, #32]
	and x15, x7, x19
	eor x15, x15, x13
	str x7, [x5, #40]
	and x7, x21, x25
	eor x7, x7, x13
	and x13, x16, x24
	str x16, [x5, #48]
	and x16, x14, x26
	eor x16, x16, x13
	str x14, [x5, #56]
	and x14, x17, x23
	eor x14, x14, x13
	eor x20, x20, x16
	eor x22, x22, x14
	eor x15, x15, x16
	eor x7, x7, x14
	eor x20, x20, x9
	ldr x9, [x5, #0]
	eor x22, x22, x9
	eor x15, x15, x27
	ldr x27, [x5, #8]
	eor x7, x7, x27
	eor x27, x20, x22
	and x20, x20, x15
	eor x9, x7, x20
	and x14, x27, x9
	eor x14, x14, x22
	eor x16, x15, x7
	eor x22, x22, x20
	and x22, x22, x16
	eor x22, x22, x7
	eor x15, x15, x22
	eor x16, x9, x22
	and x7, x7, x16
	eor x15, x7, x15
	eor x9, x9, x7
	and x9, x14, x9
	eor x27, x27, x9
	eor x9, x27, x15
	eor x7, x14, x22
	eor x16, x14, x27
	eor x20, x22, x15
	eor x13, x7, x9
	and x8, x20, x8
	and x12, x15, x12
	and x6, x22, x6
	and x11, x16, x11
	and x19, x27, x19
	and x25, x14, x25
	and x24, x7, x24
	and x26, x13, x26
	and x23, x9, x23
	str x12, [x5, #8]
	ldr x12, [x5, #16]
	and x20, x20, x12
	ldr x12, [x5, #24]
	and x15, x15, x12
	and x22, x22, x10
	ldr x10, [x5, #32]
	and x16, x16, x10
	ldr x10, [x5, #40]
	and x27, x27, x10
	and x14, x14, x21
	ldr x21, [x5, #48]
	and x7, x7, x21
	ldr x21, [x5, #56]
	and x13, x13, x21
	and x9, x9, x17
	eor x7, x7, x13
	eor x22, x15, x22
	eor x27, x25, x27
	eor x20, x20, x15
	eor x15, x6, x16
	eor x6, x6, x25
	eor x23, x26, x23
	eor x8, x8, x11
	eor x24, x24, x26
	eor x13, x13, x9
	eor x16, x16, x27
	eor x15, x15, x8
	eor x9, x19, x7
	eor x11, x11, x24
	eor x7, x7, x15
	eor x14, x14, x15
	eor x23, x23, x9
	eor x20, x20, x9
	eor x19, x19, x11
	eor x14, x14, x23
	ldr x9, [x5, #8]
	eor x9, x9, x20
	eor x11, x11, x20
	eor x16, x16, x23
	eor x16, x16, x28
	eor x27, x27, x7
	eor x27, x27, x28
	eor x7, x19, x14
	eor x10, x8, x9
	eor x9, x6, x9
	eor x8, x22, x14
	eor x12, x19, x10
	eor x12, x12, x28
	eor x13, x13, x7
	eor x13, x13, x28
	str x13, [x5, #8]
	add x13, x11, #0
	ldr x11, [x5, #8]
	add x7, x16, #0
	add x6, x27, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add sp, sp, #512
	ret
	.p2align 6

vg_aes_expand_key_aes:
	.arch_extension aes
	sub sp, sp, #512
	add x3, sp, #0
	movi v0.2d, #0
	sub x9, x1, #24
	sub x10, x1, #32
	cbz x9, 20f
	cbz x10, 22f
	ldr w4, [x0, #0]
	str w4, [x2, #0]
	ldr w5, [x0, #4]
	str w5, [x2, #4]
	ldr w6, [x0, #8]
	str w6, [x2, #8]
	ldr w7, [x0, #12]
	str w7, [x2, #12]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #1, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #16]
	eor w5, w5, w4
	str w5, [x2, #20]
	eor w6, w6, w5
	str w6, [x2, #24]
	eor w7, w7, w6
	str w7, [x2, #28]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #2, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #32]
	eor w5, w5, w4
	str w5, [x2, #36]
	eor w6, w6, w5
	str w6, [x2, #40]
	eor w7, w7, w6
	str w7, [x2, #44]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #4, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #48]
	eor w5, w5, w4
	str w5, [x2, #52]
	eor w6, w6, w5
	str w6, [x2, #56]
	eor w7, w7, w6
	str w7, [x2, #60]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #8, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #64]
	eor w5, w5, w4
	str w5, [x2, #68]
	eor w6, w6, w5
	str w6, [x2, #72]
	eor w7, w7, w6
	str w7, [x2, #76]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #16, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #80]
	eor w5, w5, w4
	str w5, [x2, #84]
	eor w6, w6, w5
	str w6, [x2, #88]
	eor w7, w7, w6
	str w7, [x2, #92]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #32, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #96]
	eor w5, w5, w4
	str w5, [x2, #100]
	eor w6, w6, w5
	str w6, [x2, #104]
	eor w7, w7, w6
	str w7, [x2, #108]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #64, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #112]
	eor w5, w5, w4
	str w5, [x2, #116]
	eor w6, w6, w5
	str w6, [x2, #120]
	eor w7, w7, w6
	str w7, [x2, #124]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #128, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #128]
	eor w5, w5, w4
	str w5, [x2, #132]
	eor w6, w6, w5
	str w6, [x2, #136]
	eor w7, w7, w6
	str w7, [x2, #140]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #27, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #144]
	eor w5, w5, w4
	str w5, [x2, #148]
	eor w6, w6, w5
	str w6, [x2, #152]
	eor w7, w7, w6
	str w7, [x2, #156]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #54, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #160]
	eor w5, w5, w4
	str w5, [x2, #164]
	eor w6, w6, w5
	str w6, [x2, #168]
	eor w7, w7, w6
	str w7, [x2, #172]
	b 23f
22:
	ldr w4, [x0, #0]
	str w4, [x2, #0]
	ldr w5, [x0, #4]
	str w5, [x2, #4]
	ldr w6, [x0, #8]
	str w6, [x2, #8]
	ldr w7, [x0, #12]
	str w7, [x2, #12]
	ldr w8, [x0, #16]
	str w8, [x2, #16]
	ldr w11, [x0, #20]
	str w11, [x2, #20]
	ldr w12, [x0, #24]
	str w12, [x2, #24]
	ldr w13, [x0, #28]
	str w13, [x2, #28]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #1, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #32]
	eor w5, w5, w4
	str w5, [x2, #36]
	eor w6, w6, w5
	str w6, [x2, #40]
	eor w7, w7, w6
	str w7, [x2, #44]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #48]
	eor w11, w11, w8
	str w11, [x2, #52]
	eor w12, w12, w11
	str w12, [x2, #56]
	eor w13, w13, w12
	str w13, [x2, #60]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #2, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #64]
	eor w5, w5, w4
	str w5, [x2, #68]
	eor w6, w6, w5
	str w6, [x2, #72]
	eor w7, w7, w6
	str w7, [x2, #76]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #80]
	eor w11, w11, w8
	str w11, [x2, #84]
	eor w12, w12, w11
	str w12, [x2, #88]
	eor w13, w13, w12
	str w13, [x2, #92]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #4, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #96]
	eor w5, w5, w4
	str w5, [x2, #100]
	eor w6, w6, w5
	str w6, [x2, #104]
	eor w7, w7, w6
	str w7, [x2, #108]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #112]
	eor w11, w11, w8
	str w11, [x2, #116]
	eor w12, w12, w11
	str w12, [x2, #120]
	eor w13, w13, w12
	str w13, [x2, #124]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #8, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #128]
	eor w5, w5, w4
	str w5, [x2, #132]
	eor w6, w6, w5
	str w6, [x2, #136]
	eor w7, w7, w6
	str w7, [x2, #140]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #144]
	eor w11, w11, w8
	str w11, [x2, #148]
	eor w12, w12, w11
	str w12, [x2, #152]
	eor w13, w13, w12
	str w13, [x2, #156]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #16, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #160]
	eor w5, w5, w4
	str w5, [x2, #164]
	eor w6, w6, w5
	str w6, [x2, #168]
	eor w7, w7, w6
	str w7, [x2, #172]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #176]
	eor w11, w11, w8
	str w11, [x2, #180]
	eor w12, w12, w11
	str w12, [x2, #184]
	eor w13, w13, w12
	str w13, [x2, #188]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #32, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #192]
	eor w5, w5, w4
	str w5, [x2, #196]
	eor w6, w6, w5
	str w6, [x2, #200]
	eor w7, w7, w6
	str w7, [x2, #204]
	dup v1.4s, w7
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	eor w8, w8, w9
	str w8, [x2, #208]
	eor w11, w11, w8
	str w11, [x2, #212]
	eor w12, w12, w11
	str w12, [x2, #216]
	eor w13, w13, w12
	str w13, [x2, #220]
	dup v1.4s, w13
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #64, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #224]
	eor w5, w5, w4
	str w5, [x2, #228]
	eor w6, w6, w5
	str w6, [x2, #232]
	eor w7, w7, w6
	str w7, [x2, #236]
23:
	b 21f
20:
	ldr w4, [x0, #0]
	str w4, [x2, #0]
	ldr w5, [x0, #4]
	str w5, [x2, #4]
	ldr w6, [x0, #8]
	str w6, [x2, #8]
	ldr w7, [x0, #12]
	str w7, [x2, #12]
	ldr w8, [x0, #16]
	str w8, [x2, #16]
	ldr w11, [x0, #20]
	str w11, [x2, #20]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #1, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #24]
	eor w5, w5, w4
	str w5, [x2, #28]
	eor w6, w6, w5
	str w6, [x2, #32]
	eor w7, w7, w6
	str w7, [x2, #36]
	eor w8, w8, w7
	str w8, [x2, #40]
	eor w11, w11, w8
	str w11, [x2, #44]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #2, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #48]
	eor w5, w5, w4
	str w5, [x2, #52]
	eor w6, w6, w5
	str w6, [x2, #56]
	eor w7, w7, w6
	str w7, [x2, #60]
	eor w8, w8, w7
	str w8, [x2, #64]
	eor w11, w11, w8
	str w11, [x2, #68]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #4, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #72]
	eor w5, w5, w4
	str w5, [x2, #76]
	eor w6, w6, w5
	str w6, [x2, #80]
	eor w7, w7, w6
	str w7, [x2, #84]
	eor w8, w8, w7
	str w8, [x2, #88]
	eor w11, w11, w8
	str w11, [x2, #92]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #8, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #96]
	eor w5, w5, w4
	str w5, [x2, #100]
	eor w6, w6, w5
	str w6, [x2, #104]
	eor w7, w7, w6
	str w7, [x2, #108]
	eor w8, w8, w7
	str w8, [x2, #112]
	eor w11, w11, w8
	str w11, [x2, #116]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #16, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #120]
	eor w5, w5, w4
	str w5, [x2, #124]
	eor w6, w6, w5
	str w6, [x2, #128]
	eor w7, w7, w6
	str w7, [x2, #132]
	eor w8, w8, w7
	str w8, [x2, #136]
	eor w11, w11, w8
	str w11, [x2, #140]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #32, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #144]
	eor w5, w5, w4
	str w5, [x2, #148]
	eor w6, w6, w5
	str w6, [x2, #152]
	eor w7, w7, w6
	str w7, [x2, #156]
	eor w8, w8, w7
	str w8, [x2, #160]
	eor w11, w11, w8
	str w11, [x2, #164]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #64, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #168]
	eor w5, w5, w4
	str w5, [x2, #172]
	eor w6, w6, w5
	str w6, [x2, #176]
	eor w7, w7, w6
	str w7, [x2, #180]
	eor w8, w8, w7
	str w8, [x2, #184]
	eor w11, w11, w8
	str w11, [x2, #188]
	dup v1.4s, w11
	aese v1.16b, v0.16b
	umov w9, v1.s[0]
	movz w10, #128, lsl #0
	eor w9, w10, w9, ror #8
	eor w4, w4, w9
	str w4, [x2, #192]
	eor w5, w5, w4
	str w5, [x2, #196]
	eor w6, w6, w5
	str w6, [x2, #200]
	eor w7, w7, w6
	str w7, [x2, #204]
21:
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add sp, sp, #512
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_encrypt_blocks:
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
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
	add x2, x1, #1
	lsl x6, x1, #4
	add x0, x0, x6
	add x1, x5, #1920
20:
	ldr x6, [x0, #0]
	ldr x10, [x0, #8]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x11, x10, #0
	add x12, x10, #0
	add x13, x10, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
	sub x0, x0, #16
	sub x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 20b
	add x0, x1, #64
	cbz x4, 21f
23:
	lsr x21, x4, #2
	cbnz x21, 24f
	ldr x6, [x3, #0]
	ldr x10, [x3, #8]
	sub x21, x4, #1
	cbnz x21, 26f
	b 27f
26:
	ldr x7, [x3, #16]
	ldr x11, [x3, #24]
	sub x21, x4, #2
	cbnz x21, 28f
	b 29f
28:
	ldr x8, [x3, #32]
	ldr x12, [x3, #40]
29:
27:
	b 25f
24:
	ldr x6, [x3, #0]
	ldr x10, [x3, #8]
	ldr x7, [x3, #16]
	ldr x11, [x3, #24]
	ldr x8, [x3, #32]
	ldr x12, [x3, #40]
	ldr x9, [x3, #48]
	ldr x13, [x3, #56]
25:
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
	add x1, x0, #0
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
210:
	add x1, x1, #64
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x13, x7
	eor x16, x13, x10
	eor x17, x13, x8
	eor x11, x12, x11
	eor x19, x11, x6
	eor x10, x19, x10
	eor x20, x15, x14
	eor x21, x19, x13
	eor x7, x19, x7
	eor x22, x7, x17
	eor x9, x9, x20
	eor x8, x9, x8
	eor x9, x9, x12
	eor x12, x8, x6
	eor x23, x8, x11
	eor x24, x9, x16
	eor x25, x6, x24
	eor x26, x23, x24
	eor x27, x23, x17
	eor x11, x11, x24
	str x27, [x5, #0]
	eor x27, x15, x11
	eor x13, x13, x11
	str x13, [x5, #8]
	and x13, x20, x8
	str x20, [x5, #16]
	and x20, x22, x12
	eor x20, x20, x13
	str x22, [x5, #24]
	and x22, x10, x6
	eor x22, x22, x13
	and x13, x15, x11
	str x15, [x5, #32]
	and x15, x7, x19
	eor x15, x15, x13
	str x7, [x5, #40]
	and x7, x21, x25
	eor x7, x7, x13
	and x13, x16, x24
	str x16, [x5, #48]
	and x16, x14, x26
	eor x16, x16, x13
	str x14, [x5, #56]
	and x14, x17, x23
	eor x14, x14, x13
	eor x20, x20, x16
	eor x22, x22, x14
	eor x15, x15, x16
	eor x7, x7, x14
	eor x20, x20, x9
	ldr x9, [x5, #0]
	eor x22, x22, x9
	eor x15, x15, x27
	ldr x27, [x5, #8]
	eor x7, x7, x27
	eor x27, x20, x22
	and x20, x20, x15
	eor x9, x7, x20
	and x14, x27, x9
	eor x14, x14, x22
	eor x16, x15, x7
	eor x22, x22, x20
	and x22, x22, x16
	eor x22, x22, x7
	eor x15, x15, x22
	eor x16, x9, x22
	and x7, x7, x16
	eor x15, x7, x15
	eor x9, x9, x7
	and x9, x14, x9
	eor x27, x27, x9
	eor x9, x27, x15
	eor x7, x14, x22
	eor x16, x14, x27
	eor x20, x22, x15
	eor x13, x7, x9
	and x8, x20, x8
	and x12, x15, x12
	and x6, x22, x6
	and x11, x16, x11
	and x19, x27, x19
	and x25, x14, x25
	and x24, x7, x24
	and x26, x13, x26
	and x23, x9, x23
	str x12, [x5, #8]
	ldr x12, [x5, #16]
	and x20, x20, x12
	ldr x12, [x5, #24]
	and x15, x15, x12
	and x22, x22, x10
	ldr x10, [x5, #32]
	and x16, x16, x10
	ldr x10, [x5, #40]
	and x27, x27, x10
	and x14, x14, x21
	ldr x21, [x5, #48]
	and x7, x7, x21
	ldr x21, [x5, #56]
	and x13, x13, x21
	and x9, x9, x17
	eor x7, x7, x13
	eor x22, x15, x22
	eor x27, x25, x27
	eor x20, x20, x15
	eor x15, x6, x16
	eor x6, x6, x25
	eor x23, x26, x23
	eor x8, x8, x11
	eor x24, x24, x26
	eor x13, x13, x9
	eor x16, x16, x27
	eor x15, x15, x8
	eor x9, x19, x7
	eor x11, x11, x24
	eor x7, x7, x15
	eor x14, x14, x15
	eor x23, x23, x9
	eor x20, x20, x9
	eor x19, x19, x11
	eor x14, x14, x23
	ldr x9, [x5, #8]
	eor x9, x9, x20
	eor x11, x11, x20
	eor x16, x16, x23
	eor x16, x16, x28
	eor x27, x27, x7
	eor x27, x27, x28
	eor x7, x19, x14
	eor x10, x8, x9
	eor x9, x6, x9
	eor x8, x22, x14
	eor x12, x19, x10
	eor x12, x12, x28
	eor x13, x13, x7
	eor x13, x13, x28
	str x13, [x5, #8]
	add x13, x11, #0
	ldr x11, [x5, #8]
	add x7, x16, #0
	add x6, x27, #0
	movz x14, #65535, lsl #0
	movk x14, #65535, lsl #32
	movz x15, #0, lsl #0
	movk x15, #4095, lsl #16
	movk x15, #4095, lsl #48
	movz x16, #0, lsl #0
	movk x16, #61440, lsl #16
	movk x16, #61440, lsl #48
	movz x17, #65535, lsl #0
	movk x17, #65535, lsl #16
	movz x19, #0, lsl #0
	movk x19, #255, lsl #32
	movk x19, #255, lsl #48
	movz x20, #0, lsl #0
	movk x20, #65280, lsl #32
	movk x20, #65280, lsl #48
	ror x21, x6, #4
	and x21, x21, x15
	ror x22, x6, #52
	and x22, x22, x16
	and x6, x6, x14
	eor x6, x6, x21
	eor x6, x6, x22
	ror x21, x6, #8
	and x21, x21, x19
	ror x22, x6, #56
	and x22, x22, x20
	and x6, x6, x17
	eor x6, x6, x21
	eor x6, x6, x22
	ror x21, x7, #4
	and x21, x21, x15
	ror x22, x7, #52
	and x22, x22, x16
	and x7, x7, x14
	eor x7, x7, x21
	eor x7, x7, x22
	ror x21, x7, #8
	and x21, x21, x19
	ror x22, x7, #56
	and x22, x22, x20
	and x7, x7, x17
	eor x7, x7, x21
	eor x7, x7, x22
	ror x21, x8, #4
	and x21, x21, x15
	ror x22, x8, #52
	and x22, x22, x16
	and x8, x8, x14
	eor x8, x8, x21
	eor x8, x8, x22
	ror x21, x8, #8
	and x21, x21, x19
	ror x22, x8, #56
	and x22, x22, x20
	and x8, x8, x17
	eor x8, x8, x21
	eor x8, x8, x22
	ror x21, x9, #4
	and x21, x21, x15
	ror x22, x9, #52
	and x22, x22, x16
	and x9, x9, x14
	eor x9, x9, x21
	eor x9, x9, x22
	ror x21, x9, #8
	and x21, x21, x19
	ror x22, x9, #56
	and x22, x22, x20
	and x9, x9, x17
	eor x9, x9, x21
	eor x9, x9, x22
	ror x21, x10, #4
	and x21, x21, x15
	ror x22, x10, #52
	and x22, x22, x16
	and x10, x10, x14
	eor x10, x10, x21
	eor x10, x10, x22
	ror x21, x10, #8
	and x21, x21, x19
	ror x22, x10, #56
	and x22, x22, x20
	and x10, x10, x17
	eor x10, x10, x21
	eor x10, x10, x22
	ror x21, x11, #4
	and x21, x21, x15
	ror x22, x11, #52
	and x22, x22, x16
	and x11, x11, x14
	eor x11, x11, x21
	eor x11, x11, x22
	ror x21, x11, #8
	and x21, x21, x19
	ror x22, x11, #56
	and x22, x22, x20
	and x11, x11, x17
	eor x11, x11, x21
	eor x11, x11, x22
	ror x21, x12, #4
	and x21, x21, x15
	ror x22, x12, #52
	and x22, x22, x16
	and x12, x12, x14
	eor x12, x12, x21
	eor x12, x12, x22
	ror x21, x12, #8
	and x21, x21, x19
	ror x22, x12, #56
	and x22, x22, x20
	and x12, x12, x17
	eor x12, x12, x21
	eor x12, x12, x22
	ror x21, x13, #4
	and x21, x21, x15
	ror x22, x13, #52
	and x22, x22, x16
	and x13, x13, x14
	eor x13, x13, x21
	eor x13, x13, x22
	ror x21, x13, #8
	and x21, x21, x19
	ror x22, x13, #56
	and x22, x22, x20
	and x13, x13, x17
	eor x13, x13, x21
	eor x13, x13, x22
	ror x23, x13, #16
	eor x23, x23, x13
	ror x21, x6, #16
	eor x6, x6, x21
	eor x21, x21, x23
	ror x24, x6, #32
	eor x21, x21, x24
	ror x22, x7, #16
	eor x7, x7, x22
	eor x22, x22, x6
	eor x22, x22, x23
	ror x24, x7, #32
	eor x22, x22, x24
	ror x6, x8, #16
	eor x8, x8, x6
	eor x6, x6, x7
	ror x24, x8, #32
	eor x6, x6, x24
	ror x7, x9, #16
	eor x9, x9, x7
	eor x7, x7, x8
	eor x7, x7, x23
	ror x24, x9, #32
	eor x7, x7, x24
	ror x8, x10, #16
	eor x10, x10, x8
	eor x8, x8, x9
	eor x8, x8, x23
	ror x24, x10, #32
	eor x8, x8, x24
	ror x9, x11, #16
	eor x11, x11, x9
	eor x9, x9, x10
	ror x24, x11, #32
	eor x9, x9, x24
	ror x10, x12, #16
	eor x12, x12, x10
	eor x10, x10, x11
	ror x24, x12, #32
	eor x10, x10, x24
	ror x11, x13, #16
	eor x13, x13, x11
	eor x11, x11, x12
	ror x24, x13, #32
	eor x11, x11, x24
	add x13, x11, #0
	add x12, x10, #0
	add x11, x9, #0
	add x10, x8, #0
	add x9, x7, #0
	add x8, x6, #0
	add x7, x22, #0
	add x6, x21, #0
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	sub x21, x1, x5
	sub x21, x21, #1856
	cbnz x21, 210b
	add x1, x1, #64
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x13, x7
	eor x16, x13, x10
	eor x17, x13, x8
	eor x11, x12, x11
	eor x19, x11, x6
	eor x10, x19, x10
	eor x20, x15, x14
	eor x21, x19, x13
	eor x7, x19, x7
	eor x22, x7, x17
	eor x9, x9, x20
	eor x8, x9, x8
	eor x9, x9, x12
	eor x12, x8, x6
	eor x23, x8, x11
	eor x24, x9, x16
	eor x25, x6, x24
	eor x26, x23, x24
	eor x27, x23, x17
	eor x11, x11, x24
	str x27, [x5, #0]
	eor x27, x15, x11
	eor x13, x13, x11
	str x13, [x5, #8]
	and x13, x20, x8
	str x20, [x5, #16]
	and x20, x22, x12
	eor x20, x20, x13
	str x22, [x5, #24]
	and x22, x10, x6
	eor x22, x22, x13
	and x13, x15, x11
	str x15, [x5, #32]
	and x15, x7, x19
	eor x15, x15, x13
	str x7, [x5, #40]
	and x7, x21, x25
	eor x7, x7, x13
	and x13, x16, x24
	str x16, [x5, #48]
	and x16, x14, x26
	eor x16, x16, x13
	str x14, [x5, #56]
	and x14, x17, x23
	eor x14, x14, x13
	eor x20, x20, x16
	eor x22, x22, x14
	eor x15, x15, x16
	eor x7, x7, x14
	eor x20, x20, x9
	ldr x9, [x5, #0]
	eor x22, x22, x9
	eor x15, x15, x27
	ldr x27, [x5, #8]
	eor x7, x7, x27
	eor x27, x20, x22
	and x20, x20, x15
	eor x9, x7, x20
	and x14, x27, x9
	eor x14, x14, x22
	eor x16, x15, x7
	eor x22, x22, x20
	and x22, x22, x16
	eor x22, x22, x7
	eor x15, x15, x22
	eor x16, x9, x22
	and x7, x7, x16
	eor x15, x7, x15
	eor x9, x9, x7
	and x9, x14, x9
	eor x27, x27, x9
	eor x9, x27, x15
	eor x7, x14, x22
	eor x16, x14, x27
	eor x20, x22, x15
	eor x13, x7, x9
	and x8, x20, x8
	and x12, x15, x12
	and x6, x22, x6
	and x11, x16, x11
	and x19, x27, x19
	and x25, x14, x25
	and x24, x7, x24
	and x26, x13, x26
	and x23, x9, x23
	str x12, [x5, #8]
	ldr x12, [x5, #16]
	and x20, x20, x12
	ldr x12, [x5, #24]
	and x15, x15, x12
	and x22, x22, x10
	ldr x10, [x5, #32]
	and x16, x16, x10
	ldr x10, [x5, #40]
	and x27, x27, x10
	and x14, x14, x21
	ldr x21, [x5, #48]
	and x7, x7, x21
	ldr x21, [x5, #56]
	and x13, x13, x21
	and x9, x9, x17
	eor x7, x7, x13
	eor x22, x15, x22
	eor x27, x25, x27
	eor x20, x20, x15
	eor x15, x6, x16
	eor x6, x6, x25
	eor x23, x26, x23
	eor x8, x8, x11
	eor x24, x24, x26
	eor x13, x13, x9
	eor x16, x16, x27
	eor x15, x15, x8
	eor x9, x19, x7
	eor x11, x11, x24
	eor x7, x7, x15
	eor x14, x14, x15
	eor x23, x23, x9
	eor x20, x20, x9
	eor x19, x19, x11
	eor x14, x14, x23
	ldr x9, [x5, #8]
	eor x9, x9, x20
	eor x11, x11, x20
	eor x16, x16, x23
	eor x16, x16, x28
	eor x27, x27, x7
	eor x27, x27, x28
	eor x7, x19, x14
	eor x10, x8, x9
	eor x9, x6, x9
	eor x8, x22, x14
	eor x12, x19, x10
	eor x12, x12, x28
	eor x13, x13, x7
	eor x13, x13, x28
	str x13, [x5, #8]
	add x13, x11, #0
	ldr x11, [x5, #8]
	add x7, x16, #0
	add x6, x27, #0
	movz x14, #65535, lsl #0
	movk x14, #65535, lsl #32
	movz x15, #0, lsl #0
	movk x15, #4095, lsl #16
	movk x15, #4095, lsl #48
	movz x16, #0, lsl #0
	movk x16, #61440, lsl #16
	movk x16, #61440, lsl #48
	movz x17, #65535, lsl #0
	movk x17, #65535, lsl #16
	movz x19, #0, lsl #0
	movk x19, #255, lsl #32
	movk x19, #255, lsl #48
	movz x20, #0, lsl #0
	movk x20, #65280, lsl #32
	movk x20, #65280, lsl #48
	ror x21, x6, #4
	and x21, x21, x15
	ror x22, x6, #52
	and x22, x22, x16
	and x6, x6, x14
	eor x6, x6, x21
	eor x6, x6, x22
	ror x21, x6, #8
	and x21, x21, x19
	ror x22, x6, #56
	and x22, x22, x20
	and x6, x6, x17
	eor x6, x6, x21
	eor x6, x6, x22
	ror x21, x7, #4
	and x21, x21, x15
	ror x22, x7, #52
	and x22, x22, x16
	and x7, x7, x14
	eor x7, x7, x21
	eor x7, x7, x22
	ror x21, x7, #8
	and x21, x21, x19
	ror x22, x7, #56
	and x22, x22, x20
	and x7, x7, x17
	eor x7, x7, x21
	eor x7, x7, x22
	ror x21, x8, #4
	and x21, x21, x15
	ror x22, x8, #52
	and x22, x22, x16
	and x8, x8, x14
	eor x8, x8, x21
	eor x8, x8, x22
	ror x21, x8, #8
	and x21, x21, x19
	ror x22, x8, #56
	and x22, x22, x20
	and x8, x8, x17
	eor x8, x8, x21
	eor x8, x8, x22
	ror x21, x9, #4
	and x21, x21, x15
	ror x22, x9, #52
	and x22, x22, x16
	and x9, x9, x14
	eor x9, x9, x21
	eor x9, x9, x22
	ror x21, x9, #8
	and x21, x21, x19
	ror x22, x9, #56
	and x22, x22, x20
	and x9, x9, x17
	eor x9, x9, x21
	eor x9, x9, x22
	ror x21, x10, #4
	and x21, x21, x15
	ror x22, x10, #52
	and x22, x22, x16
	and x10, x10, x14
	eor x10, x10, x21
	eor x10, x10, x22
	ror x21, x10, #8
	and x21, x21, x19
	ror x22, x10, #56
	and x22, x22, x20
	and x10, x10, x17
	eor x10, x10, x21
	eor x10, x10, x22
	ror x21, x11, #4
	and x21, x21, x15
	ror x22, x11, #52
	and x22, x22, x16
	and x11, x11, x14
	eor x11, x11, x21
	eor x11, x11, x22
	ror x21, x11, #8
	and x21, x21, x19
	ror x22, x11, #56
	and x22, x22, x20
	and x11, x11, x17
	eor x11, x11, x21
	eor x11, x11, x22
	ror x21, x12, #4
	and x21, x21, x15
	ror x22, x12, #52
	and x22, x22, x16
	and x12, x12, x14
	eor x12, x12, x21
	eor x12, x12, x22
	ror x21, x12, #8
	and x21, x21, x19
	ror x22, x12, #56
	and x22, x22, x20
	and x12, x12, x17
	eor x12, x12, x21
	eor x12, x12, x22
	ror x21, x13, #4
	and x21, x21, x15
	ror x22, x13, #52
	and x22, x22, x16
	and x13, x13, x14
	eor x13, x13, x21
	eor x13, x13, x22
	ror x21, x13, #8
	and x21, x21, x19
	ror x22, x13, #56
	and x22, x22, x20
	and x13, x13, x17
	eor x13, x13, x21
	eor x13, x13, x22
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
	lsr x21, x4, #2
	cbnz x21, 211f
	str x6, [x3, #0]
	str x10, [x3, #8]
	sub x21, x4, #1
	cbnz x21, 213f
	b 214f
213:
	str x7, [x3, #16]
	str x11, [x3, #24]
	sub x21, x4, #2
	cbnz x21, 215f
	b 216f
215:
	str x8, [x3, #32]
	str x12, [x3, #40]
216:
214:
	movz x4, #0, lsl #0
	b 212f
211:
	str x6, [x3, #0]
	str x10, [x3, #8]
	str x7, [x3, #16]
	str x11, [x3, #24]
	str x8, [x3, #32]
	str x12, [x3, #40]
	str x9, [x3, #48]
	str x13, [x3, #56]
	add x3, x3, #64
	sub x4, x4, #4
212:
	cbnz x4, 23b
	b 22f
21:
22:
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

vg_aes_decrypt_blocks:
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
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
	add x2, x1, #1
	lsl x6, x1, #4
	add x0, x0, x6
	add x1, x5, #1920
20:
	ldr x6, [x0, #0]
	ldr x10, [x0, #8]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x11, x10, #0
	add x12, x10, #0
	add x13, x10, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
	sub x0, x0, #16
	sub x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 20b
	add x0, x1, #64
	cbz x4, 21f
23:
	lsr x21, x4, #2
	cbnz x21, 24f
	ldr x6, [x3, #0]
	ldr x10, [x3, #8]
	sub x21, x4, #1
	cbnz x21, 26f
	b 27f
26:
	ldr x7, [x3, #16]
	ldr x11, [x3, #24]
	sub x21, x4, #2
	cbnz x21, 28f
	b 29f
28:
	ldr x8, [x3, #32]
	ldr x12, [x3, #40]
29:
27:
	b 25f
24:
	ldr x6, [x3, #0]
	ldr x10, [x3, #8]
	ldr x7, [x3, #16]
	ldr x11, [x3, #24]
	ldr x8, [x3, #32]
	ldr x12, [x3, #40]
	ldr x9, [x3, #48]
	ldr x13, [x3, #56]
25:
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
	add x1, x5, #1920
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
210:
	sub x1, x1, #64
	movz x14, #65535, lsl #0
	movk x14, #65535, lsl #32
	movz x15, #0, lsl #0
	movk x15, #65520, lsl #16
	movk x15, #65520, lsl #48
	movz x16, #0, lsl #0
	movk x16, #15, lsl #16
	movk x16, #15, lsl #48
	movz x17, #65535, lsl #0
	movk x17, #65535, lsl #16
	movz x19, #0, lsl #0
	movk x19, #255, lsl #32
	movk x19, #255, lsl #48
	movz x20, #0, lsl #0
	movk x20, #65280, lsl #32
	movk x20, #65280, lsl #48
	ror x21, x6, #60
	and x21, x21, x15
	ror x22, x6, #12
	and x22, x22, x16
	and x6, x6, x14
	eor x6, x6, x21
	eor x6, x6, x22
	ror x21, x6, #8
	and x21, x21, x19
	ror x22, x6, #56
	and x22, x22, x20
	and x6, x6, x17
	eor x6, x6, x21
	eor x6, x6, x22
	ror x21, x7, #60
	and x21, x21, x15
	ror x22, x7, #12
	and x22, x22, x16
	and x7, x7, x14
	eor x7, x7, x21
	eor x7, x7, x22
	ror x21, x7, #8
	and x21, x21, x19
	ror x22, x7, #56
	and x22, x22, x20
	and x7, x7, x17
	eor x7, x7, x21
	eor x7, x7, x22
	ror x21, x8, #60
	and x21, x21, x15
	ror x22, x8, #12
	and x22, x22, x16
	and x8, x8, x14
	eor x8, x8, x21
	eor x8, x8, x22
	ror x21, x8, #8
	and x21, x21, x19
	ror x22, x8, #56
	and x22, x22, x20
	and x8, x8, x17
	eor x8, x8, x21
	eor x8, x8, x22
	ror x21, x9, #60
	and x21, x21, x15
	ror x22, x9, #12
	and x22, x22, x16
	and x9, x9, x14
	eor x9, x9, x21
	eor x9, x9, x22
	ror x21, x9, #8
	and x21, x21, x19
	ror x22, x9, #56
	and x22, x22, x20
	and x9, x9, x17
	eor x9, x9, x21
	eor x9, x9, x22
	ror x21, x10, #60
	and x21, x21, x15
	ror x22, x10, #12
	and x22, x22, x16
	and x10, x10, x14
	eor x10, x10, x21
	eor x10, x10, x22
	ror x21, x10, #8
	and x21, x21, x19
	ror x22, x10, #56
	and x22, x22, x20
	and x10, x10, x17
	eor x10, x10, x21
	eor x10, x10, x22
	ror x21, x11, #60
	and x21, x21, x15
	ror x22, x11, #12
	and x22, x22, x16
	and x11, x11, x14
	eor x11, x11, x21
	eor x11, x11, x22
	ror x21, x11, #8
	and x21, x21, x19
	ror x22, x11, #56
	and x22, x22, x20
	and x11, x11, x17
	eor x11, x11, x21
	eor x11, x11, x22
	ror x21, x12, #60
	and x21, x21, x15
	ror x22, x12, #12
	and x22, x22, x16
	and x12, x12, x14
	eor x12, x12, x21
	eor x12, x12, x22
	ror x21, x12, #8
	and x21, x21, x19
	ror x22, x12, #56
	and x22, x22, x20
	and x12, x12, x17
	eor x12, x12, x21
	eor x12, x12, x22
	ror x21, x13, #60
	and x21, x21, x15
	ror x22, x13, #12
	and x22, x22, x16
	and x13, x13, x14
	eor x13, x13, x21
	eor x13, x13, x22
	ror x21, x13, #8
	and x21, x21, x19
	ror x22, x13, #56
	and x22, x22, x20
	and x13, x13, x17
	eor x13, x13, x21
	eor x13, x13, x22
	movz x28, #0, lsl #0
	sub x28, x28, #1
	add x14, x6, #0
	add x15, x7, #0
	add x16, x8, #0
	add x17, x9, #0
	add x19, x10, #0
	add x20, x11, #0
	add x25, x12, #0
	add x26, x13, #0
	eor x6, x16, x20
	eor x6, x6, x26
	eor x6, x6, x28
	eor x7, x17, x25
	eor x7, x7, x14
	eor x8, x19, x26
	eor x8, x8, x15
	eor x8, x8, x28
	eor x9, x20, x14
	eor x9, x9, x16
	eor x10, x25, x15
	eor x10, x10, x17
	eor x11, x26, x16
	eor x11, x11, x19
	eor x12, x14, x17
	eor x12, x12, x20
	eor x13, x15, x19
	eor x13, x13, x25
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x13, x7
	eor x16, x13, x10
	eor x17, x13, x8
	eor x11, x12, x11
	eor x19, x11, x6
	eor x10, x19, x10
	eor x20, x15, x14
	eor x21, x19, x13
	eor x7, x19, x7
	eor x22, x7, x17
	eor x9, x9, x20
	eor x8, x9, x8
	eor x9, x9, x12
	eor x12, x8, x6
	eor x23, x8, x11
	eor x24, x9, x16
	eor x25, x6, x24
	eor x26, x23, x24
	eor x27, x23, x17
	eor x11, x11, x24
	str x27, [x5, #0]
	eor x27, x15, x11
	eor x13, x13, x11
	str x13, [x5, #8]
	and x13, x20, x8
	str x20, [x5, #16]
	and x20, x22, x12
	eor x20, x20, x13
	str x22, [x5, #24]
	and x22, x10, x6
	eor x22, x22, x13
	and x13, x15, x11
	str x15, [x5, #32]
	and x15, x7, x19
	eor x15, x15, x13
	str x7, [x5, #40]
	and x7, x21, x25
	eor x7, x7, x13
	and x13, x16, x24
	str x16, [x5, #48]
	and x16, x14, x26
	eor x16, x16, x13
	str x14, [x5, #56]
	and x14, x17, x23
	eor x14, x14, x13
	eor x20, x20, x16
	eor x22, x22, x14
	eor x15, x15, x16
	eor x7, x7, x14
	eor x20, x20, x9
	ldr x9, [x5, #0]
	eor x22, x22, x9
	eor x15, x15, x27
	ldr x27, [x5, #8]
	eor x7, x7, x27
	eor x27, x20, x22
	and x20, x20, x15
	eor x9, x7, x20
	and x14, x27, x9
	eor x14, x14, x22
	eor x16, x15, x7
	eor x22, x22, x20
	and x22, x22, x16
	eor x22, x22, x7
	eor x15, x15, x22
	eor x16, x9, x22
	and x7, x7, x16
	eor x15, x7, x15
	eor x9, x9, x7
	and x9, x14, x9
	eor x27, x27, x9
	eor x9, x27, x15
	eor x7, x14, x22
	eor x16, x14, x27
	eor x20, x22, x15
	eor x13, x7, x9
	and x8, x20, x8
	and x12, x15, x12
	and x6, x22, x6
	and x11, x16, x11
	and x19, x27, x19
	and x25, x14, x25
	and x24, x7, x24
	and x26, x13, x26
	and x23, x9, x23
	str x12, [x5, #8]
	ldr x12, [x5, #16]
	and x20, x20, x12
	ldr x12, [x5, #24]
	and x15, x15, x12
	and x22, x22, x10
	ldr x10, [x5, #32]
	and x16, x16, x10
	ldr x10, [x5, #40]
	and x27, x27, x10
	and x14, x14, x21
	ldr x21, [x5, #48]
	and x7, x7, x21
	ldr x21, [x5, #56]
	and x13, x13, x21
	and x9, x9, x17
	eor x7, x7, x13
	eor x22, x15, x22
	eor x27, x25, x27
	eor x20, x20, x15
	eor x15, x6, x16
	eor x6, x6, x25
	eor x23, x26, x23
	eor x8, x8, x11
	eor x24, x24, x26
	eor x13, x13, x9
	eor x16, x16, x27
	eor x15, x15, x8
	eor x9, x19, x7
	eor x11, x11, x24
	eor x7, x7, x15
	eor x14, x14, x15
	eor x23, x23, x9
	eor x20, x20, x9
	eor x19, x19, x11
	eor x14, x14, x23
	ldr x9, [x5, #8]
	eor x9, x9, x20
	eor x11, x11, x20
	eor x16, x16, x23
	eor x16, x16, x28
	eor x27, x27, x7
	eor x27, x27, x28
	eor x7, x19, x14
	eor x10, x8, x9
	eor x9, x6, x9
	eor x8, x22, x14
	eor x12, x19, x10
	eor x12, x12, x28
	eor x13, x13, x7
	eor x13, x13, x28
	str x13, [x5, #8]
	add x13, x11, #0
	ldr x11, [x5, #8]
	add x7, x16, #0
	add x6, x27, #0
	movz x28, #0, lsl #0
	sub x28, x28, #1
	add x14, x6, #0
	add x15, x7, #0
	add x16, x8, #0
	add x17, x9, #0
	add x19, x10, #0
	add x20, x11, #0
	add x25, x12, #0
	add x26, x13, #0
	eor x6, x16, x20
	eor x6, x6, x26
	eor x6, x6, x28
	eor x7, x17, x25
	eor x7, x7, x14
	eor x8, x19, x26
	eor x8, x8, x15
	eor x8, x8, x28
	eor x9, x20, x14
	eor x9, x9, x16
	eor x10, x25, x15
	eor x10, x10, x17
	eor x11, x26, x16
	eor x11, x11, x19
	eor x12, x14, x17
	eor x12, x12, x20
	eor x13, x15, x19
	eor x13, x13, x25
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	ror x14, x6, #32
	eor x14, x14, x6
	ror x15, x7, #32
	eor x15, x15, x7
	ror x16, x8, #32
	eor x16, x16, x8
	ror x17, x9, #32
	eor x17, x17, x9
	ror x19, x10, #32
	eor x19, x19, x10
	ror x20, x11, #32
	eor x20, x20, x11
	ror x25, x12, #32
	eor x25, x25, x12
	ror x26, x13, #32
	eor x26, x26, x13
	eor x6, x6, x25
	eor x7, x7, x25
	eor x7, x7, x26
	eor x8, x8, x14
	eor x8, x8, x26
	eor x9, x9, x15
	eor x9, x9, x25
	eor x10, x10, x16
	eor x10, x10, x25
	eor x10, x10, x26
	eor x11, x11, x17
	eor x11, x11, x26
	eor x12, x12, x19
	eor x13, x13, x20
	ror x23, x13, #16
	eor x23, x23, x13
	ror x21, x6, #16
	eor x6, x6, x21
	eor x21, x21, x23
	ror x24, x6, #32
	eor x21, x21, x24
	ror x22, x7, #16
	eor x7, x7, x22
	eor x22, x22, x6
	eor x22, x22, x23
	ror x24, x7, #32
	eor x22, x22, x24
	ror x6, x8, #16
	eor x8, x8, x6
	eor x6, x6, x7
	ror x24, x8, #32
	eor x6, x6, x24
	ror x7, x9, #16
	eor x9, x9, x7
	eor x7, x7, x8
	eor x7, x7, x23
	ror x24, x9, #32
	eor x7, x7, x24
	ror x8, x10, #16
	eor x10, x10, x8
	eor x8, x8, x9
	eor x8, x8, x23
	ror x24, x10, #32
	eor x8, x8, x24
	ror x9, x11, #16
	eor x11, x11, x9
	eor x9, x9, x10
	ror x24, x11, #32
	eor x9, x9, x24
	ror x10, x12, #16
	eor x12, x12, x10
	eor x10, x10, x11
	ror x24, x12, #32
	eor x10, x10, x24
	ror x11, x13, #16
	eor x13, x13, x11
	eor x11, x11, x12
	ror x24, x13, #32
	eor x11, x11, x24
	add x13, x11, #0
	add x12, x10, #0
	add x11, x9, #0
	add x10, x8, #0
	add x9, x7, #0
	add x8, x6, #0
	add x7, x22, #0
	add x6, x21, #0
	sub x21, x1, x0
	sub x21, x21, #64
	cbnz x21, 210b
	sub x1, x1, #64
	movz x14, #65535, lsl #0
	movk x14, #65535, lsl #32
	movz x15, #0, lsl #0
	movk x15, #65520, lsl #16
	movk x15, #65520, lsl #48
	movz x16, #0, lsl #0
	movk x16, #15, lsl #16
	movk x16, #15, lsl #48
	movz x17, #65535, lsl #0
	movk x17, #65535, lsl #16
	movz x19, #0, lsl #0
	movk x19, #255, lsl #32
	movk x19, #255, lsl #48
	movz x20, #0, lsl #0
	movk x20, #65280, lsl #32
	movk x20, #65280, lsl #48
	ror x21, x6, #60
	and x21, x21, x15
	ror x22, x6, #12
	and x22, x22, x16
	and x6, x6, x14
	eor x6, x6, x21
	eor x6, x6, x22
	ror x21, x6, #8
	and x21, x21, x19
	ror x22, x6, #56
	and x22, x22, x20
	and x6, x6, x17
	eor x6, x6, x21
	eor x6, x6, x22
	ror x21, x7, #60
	and x21, x21, x15
	ror x22, x7, #12
	and x22, x22, x16
	and x7, x7, x14
	eor x7, x7, x21
	eor x7, x7, x22
	ror x21, x7, #8
	and x21, x21, x19
	ror x22, x7, #56
	and x22, x22, x20
	and x7, x7, x17
	eor x7, x7, x21
	eor x7, x7, x22
	ror x21, x8, #60
	and x21, x21, x15
	ror x22, x8, #12
	and x22, x22, x16
	and x8, x8, x14
	eor x8, x8, x21
	eor x8, x8, x22
	ror x21, x8, #8
	and x21, x21, x19
	ror x22, x8, #56
	and x22, x22, x20
	and x8, x8, x17
	eor x8, x8, x21
	eor x8, x8, x22
	ror x21, x9, #60
	and x21, x21, x15
	ror x22, x9, #12
	and x22, x22, x16
	and x9, x9, x14
	eor x9, x9, x21
	eor x9, x9, x22
	ror x21, x9, #8
	and x21, x21, x19
	ror x22, x9, #56
	and x22, x22, x20
	and x9, x9, x17
	eor x9, x9, x21
	eor x9, x9, x22
	ror x21, x10, #60
	and x21, x21, x15
	ror x22, x10, #12
	and x22, x22, x16
	and x10, x10, x14
	eor x10, x10, x21
	eor x10, x10, x22
	ror x21, x10, #8
	and x21, x21, x19
	ror x22, x10, #56
	and x22, x22, x20
	and x10, x10, x17
	eor x10, x10, x21
	eor x10, x10, x22
	ror x21, x11, #60
	and x21, x21, x15
	ror x22, x11, #12
	and x22, x22, x16
	and x11, x11, x14
	eor x11, x11, x21
	eor x11, x11, x22
	ror x21, x11, #8
	and x21, x21, x19
	ror x22, x11, #56
	and x22, x22, x20
	and x11, x11, x17
	eor x11, x11, x21
	eor x11, x11, x22
	ror x21, x12, #60
	and x21, x21, x15
	ror x22, x12, #12
	and x22, x22, x16
	and x12, x12, x14
	eor x12, x12, x21
	eor x12, x12, x22
	ror x21, x12, #8
	and x21, x21, x19
	ror x22, x12, #56
	and x22, x22, x20
	and x12, x12, x17
	eor x12, x12, x21
	eor x12, x12, x22
	ror x21, x13, #60
	and x21, x21, x15
	ror x22, x13, #12
	and x22, x22, x16
	and x13, x13, x14
	eor x13, x13, x21
	eor x13, x13, x22
	ror x21, x13, #8
	and x21, x21, x19
	ror x22, x13, #56
	and x22, x22, x20
	and x13, x13, x17
	eor x13, x13, x21
	eor x13, x13, x22
	movz x28, #0, lsl #0
	sub x28, x28, #1
	add x14, x6, #0
	add x15, x7, #0
	add x16, x8, #0
	add x17, x9, #0
	add x19, x10, #0
	add x20, x11, #0
	add x25, x12, #0
	add x26, x13, #0
	eor x6, x16, x20
	eor x6, x6, x26
	eor x6, x6, x28
	eor x7, x17, x25
	eor x7, x7, x14
	eor x8, x19, x26
	eor x8, x8, x15
	eor x8, x8, x28
	eor x9, x20, x14
	eor x9, x9, x16
	eor x10, x25, x15
	eor x10, x10, x17
	eor x11, x26, x16
	eor x11, x11, x19
	eor x12, x14, x17
	eor x12, x12, x20
	eor x13, x15, x19
	eor x13, x13, x25
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x13, x7
	eor x16, x13, x10
	eor x17, x13, x8
	eor x11, x12, x11
	eor x19, x11, x6
	eor x10, x19, x10
	eor x20, x15, x14
	eor x21, x19, x13
	eor x7, x19, x7
	eor x22, x7, x17
	eor x9, x9, x20
	eor x8, x9, x8
	eor x9, x9, x12
	eor x12, x8, x6
	eor x23, x8, x11
	eor x24, x9, x16
	eor x25, x6, x24
	eor x26, x23, x24
	eor x27, x23, x17
	eor x11, x11, x24
	str x27, [x5, #0]
	eor x27, x15, x11
	eor x13, x13, x11
	str x13, [x5, #8]
	and x13, x20, x8
	str x20, [x5, #16]
	and x20, x22, x12
	eor x20, x20, x13
	str x22, [x5, #24]
	and x22, x10, x6
	eor x22, x22, x13
	and x13, x15, x11
	str x15, [x5, #32]
	and x15, x7, x19
	eor x15, x15, x13
	str x7, [x5, #40]
	and x7, x21, x25
	eor x7, x7, x13
	and x13, x16, x24
	str x16, [x5, #48]
	and x16, x14, x26
	eor x16, x16, x13
	str x14, [x5, #56]
	and x14, x17, x23
	eor x14, x14, x13
	eor x20, x20, x16
	eor x22, x22, x14
	eor x15, x15, x16
	eor x7, x7, x14
	eor x20, x20, x9
	ldr x9, [x5, #0]
	eor x22, x22, x9
	eor x15, x15, x27
	ldr x27, [x5, #8]
	eor x7, x7, x27
	eor x27, x20, x22
	and x20, x20, x15
	eor x9, x7, x20
	and x14, x27, x9
	eor x14, x14, x22
	eor x16, x15, x7
	eor x22, x22, x20
	and x22, x22, x16
	eor x22, x22, x7
	eor x15, x15, x22
	eor x16, x9, x22
	and x7, x7, x16
	eor x15, x7, x15
	eor x9, x9, x7
	and x9, x14, x9
	eor x27, x27, x9
	eor x9, x27, x15
	eor x7, x14, x22
	eor x16, x14, x27
	eor x20, x22, x15
	eor x13, x7, x9
	and x8, x20, x8
	and x12, x15, x12
	and x6, x22, x6
	and x11, x16, x11
	and x19, x27, x19
	and x25, x14, x25
	and x24, x7, x24
	and x26, x13, x26
	and x23, x9, x23
	str x12, [x5, #8]
	ldr x12, [x5, #16]
	and x20, x20, x12
	ldr x12, [x5, #24]
	and x15, x15, x12
	and x22, x22, x10
	ldr x10, [x5, #32]
	and x16, x16, x10
	ldr x10, [x5, #40]
	and x27, x27, x10
	and x14, x14, x21
	ldr x21, [x5, #48]
	and x7, x7, x21
	ldr x21, [x5, #56]
	and x13, x13, x21
	and x9, x9, x17
	eor x7, x7, x13
	eor x22, x15, x22
	eor x27, x25, x27
	eor x20, x20, x15
	eor x15, x6, x16
	eor x6, x6, x25
	eor x23, x26, x23
	eor x8, x8, x11
	eor x24, x24, x26
	eor x13, x13, x9
	eor x16, x16, x27
	eor x15, x15, x8
	eor x9, x19, x7
	eor x11, x11, x24
	eor x7, x7, x15
	eor x14, x14, x15
	eor x23, x23, x9
	eor x20, x20, x9
	eor x19, x19, x11
	eor x14, x14, x23
	ldr x9, [x5, #8]
	eor x9, x9, x20
	eor x11, x11, x20
	eor x16, x16, x23
	eor x16, x16, x28
	eor x27, x27, x7
	eor x27, x27, x28
	eor x7, x19, x14
	eor x10, x8, x9
	eor x9, x6, x9
	eor x8, x22, x14
	eor x12, x19, x10
	eor x12, x12, x28
	eor x13, x13, x7
	eor x13, x13, x28
	str x13, [x5, #8]
	add x13, x11, #0
	ldr x11, [x5, #8]
	add x7, x16, #0
	add x6, x27, #0
	movz x28, #0, lsl #0
	sub x28, x28, #1
	add x14, x6, #0
	add x15, x7, #0
	add x16, x8, #0
	add x17, x9, #0
	add x19, x10, #0
	add x20, x11, #0
	add x25, x12, #0
	add x26, x13, #0
	eor x6, x16, x20
	eor x6, x6, x26
	eor x6, x6, x28
	eor x7, x17, x25
	eor x7, x7, x14
	eor x8, x19, x26
	eor x8, x8, x15
	eor x8, x8, x28
	eor x9, x20, x14
	eor x9, x9, x16
	eor x10, x25, x15
	eor x10, x10, x17
	eor x11, x26, x16
	eor x11, x11, x19
	eor x12, x14, x17
	eor x12, x12, x20
	eor x13, x15, x19
	eor x13, x13, x25
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
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
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
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
	lsr x21, x4, #2
	cbnz x21, 211f
	str x6, [x3, #0]
	str x10, [x3, #8]
	sub x21, x4, #1
	cbnz x21, 213f
	b 214f
213:
	str x7, [x3, #16]
	str x11, [x3, #24]
	sub x21, x4, #2
	cbnz x21, 215f
	b 216f
215:
	str x8, [x3, #32]
	str x12, [x3, #40]
216:
214:
	movz x4, #0, lsl #0
	b 212f
211:
	str x6, [x3, #0]
	str x10, [x3, #8]
	str x7, [x3, #16]
	str x11, [x3, #24]
	str x8, [x3, #32]
	str x12, [x3, #40]
	str x9, [x3, #48]
	str x13, [x3, #56]
	add x3, x3, #64
	sub x4, x4, #4
212:
	cbnz x4, 23b
	b 22f
21:
22:
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

vg_aes_encrypt_blocks_aes:
	.arch_extension aes
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	ldr q24, [x0, #128]
	ldr q25, [x0, #144]
	ldr q26, [x0, #160]
	ldr q27, [x0, #176]
	ldr q28, [x0, #192]
	lsl x9, x1, #4
	add x9, x0, x9
	ldr q30, [x9, #0]
	sub x6, x1, #10
	sub x7, x1, #12
	lsr x13, x3, #3
	sub x9, x9, #16
	ldr q29, [x9, #0]
	cbz x13, 20f
22:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	ldr q2, [x2, #32]
	ldr q3, [x2, #48]
	ldr q4, [x2, #64]
	ldr q5, [x2, #80]
	ldr q6, [x2, #96]
	ldr q7, [x2, #112]
	aese v0.16b, v16.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v16.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v16.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v16.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v16.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v16.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v16.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v16.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v17.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v17.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v17.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v17.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v17.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v17.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v17.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v18.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v18.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v18.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v18.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v18.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v18.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v18.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v19.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v19.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v19.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v19.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v19.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v19.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v19.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v20.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v20.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v20.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v20.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v20.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v20.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v20.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v21.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v21.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v21.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v21.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v21.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v21.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v21.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v22.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v22.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v22.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v22.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v22.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v22.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v22.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v23.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v23.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v23.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v23.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v23.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v23.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v23.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v24.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v24.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v24.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v24.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v24.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v24.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v24.16b
	aesmc v7.16b, v7.16b
	cbz x6, 23f
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v25.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v25.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v25.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v25.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v25.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v25.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v25.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v26.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v26.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v26.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v26.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v26.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v26.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v26.16b
	aesmc v7.16b, v7.16b
	cbz x7, 25f
	aese v0.16b, v27.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v27.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v27.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v27.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v27.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v27.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v27.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v27.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v28.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v28.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v28.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v28.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v28.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v28.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v28.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v28.16b
	aesmc v7.16b, v7.16b
	b 26f
25:
26:
	b 24f
23:
24:
	aese v0.16b, v29.16b
	eor v0.16b, v0.16b, v30.16b
	aese v1.16b, v29.16b
	eor v1.16b, v1.16b, v30.16b
	aese v2.16b, v29.16b
	eor v2.16b, v2.16b, v30.16b
	aese v3.16b, v29.16b
	eor v3.16b, v3.16b, v30.16b
	aese v4.16b, v29.16b
	eor v4.16b, v4.16b, v30.16b
	aese v5.16b, v29.16b
	eor v5.16b, v5.16b, v30.16b
	aese v6.16b, v29.16b
	eor v6.16b, v6.16b, v30.16b
	aese v7.16b, v29.16b
	eor v7.16b, v7.16b, v30.16b
	str q0, [x2, #0]
	str q1, [x2, #16]
	str q2, [x2, #32]
	str q3, [x2, #48]
	str q4, [x2, #64]
	str q5, [x2, #80]
	str q6, [x2, #96]
	str q7, [x2, #112]
	add x2, x2, #128
	sub x3, x3, #8
	lsr x13, x3, #3
	cbnz x13, 22b
	b 21f
20:
21:
	cbz x3, 27f
29:
	ldr q0, [x2, #0]
	aese v0.16b, v16.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	cbz x6, 210f
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	cbz x7, 212f
	aese v0.16b, v27.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v28.16b
	aesmc v0.16b, v0.16b
	b 213f
212:
213:
	b 211f
210:
211:
	aese v0.16b, v29.16b
	eor v0.16b, v0.16b, v30.16b
	str q0, [x2, #0]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 29b
	b 28f
27:
28:
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_decrypt_blocks_aes:
	.arch_extension aes
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	ldr q24, [x0, #128]
	ldr q25, [x0, #144]
	ldr q26, [x0, #160]
	ldr q27, [x0, #176]
	ldr q28, [x0, #192]
	lsl x9, x1, #4
	add x9, x0, x9
	ldr q30, [x9, #0]
	sub x6, x1, #10
	sub x7, x1, #12
	lsr x13, x3, #3
	ldr q29, [x0, #208]
	aesimc v17.16b, v17.16b
	aesimc v18.16b, v18.16b
	aesimc v19.16b, v19.16b
	aesimc v20.16b, v20.16b
	aesimc v21.16b, v21.16b
	aesimc v22.16b, v22.16b
	aesimc v23.16b, v23.16b
	aesimc v24.16b, v24.16b
	aesimc v25.16b, v25.16b
	aesimc v26.16b, v26.16b
	aesimc v27.16b, v27.16b
	aesimc v28.16b, v28.16b
	aesimc v29.16b, v29.16b
	cbz x13, 20f
22:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	ldr q2, [x2, #32]
	ldr q3, [x2, #48]
	ldr q4, [x2, #64]
	ldr q5, [x2, #80]
	ldr q6, [x2, #96]
	ldr q7, [x2, #112]
	aesd v0.16b, v30.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v30.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v30.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v30.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v30.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v30.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v30.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v30.16b
	aesimc v7.16b, v7.16b
	cbz x6, 23f
	cbz x7, 25f
	aesd v0.16b, v29.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v29.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v29.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v29.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v29.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v29.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v29.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v29.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v28.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v28.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v28.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v28.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v28.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v28.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v28.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v28.16b
	aesimc v7.16b, v7.16b
	b 26f
25:
26:
	aesd v0.16b, v27.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v27.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v27.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v27.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v27.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v27.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v27.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v27.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v26.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v26.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v26.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v26.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v26.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v26.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v26.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v26.16b
	aesimc v7.16b, v7.16b
	b 24f
23:
24:
	aesd v0.16b, v25.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v25.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v25.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v25.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v25.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v25.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v25.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v25.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v24.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v24.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v24.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v24.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v24.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v24.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v24.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v24.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v23.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v23.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v23.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v23.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v23.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v23.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v23.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v23.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v22.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v22.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v22.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v22.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v22.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v22.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v22.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v22.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v21.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v21.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v21.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v21.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v21.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v21.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v21.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v21.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v20.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v20.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v20.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v20.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v20.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v20.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v20.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v20.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v19.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v19.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v19.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v19.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v19.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v19.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v19.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v19.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v18.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v18.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v18.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v18.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v18.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v18.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v18.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v18.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v17.16b
	eor v0.16b, v0.16b, v16.16b
	aesd v1.16b, v17.16b
	eor v1.16b, v1.16b, v16.16b
	aesd v2.16b, v17.16b
	eor v2.16b, v2.16b, v16.16b
	aesd v3.16b, v17.16b
	eor v3.16b, v3.16b, v16.16b
	aesd v4.16b, v17.16b
	eor v4.16b, v4.16b, v16.16b
	aesd v5.16b, v17.16b
	eor v5.16b, v5.16b, v16.16b
	aesd v6.16b, v17.16b
	eor v6.16b, v6.16b, v16.16b
	aesd v7.16b, v17.16b
	eor v7.16b, v7.16b, v16.16b
	str q0, [x2, #0]
	str q1, [x2, #16]
	str q2, [x2, #32]
	str q3, [x2, #48]
	str q4, [x2, #64]
	str q5, [x2, #80]
	str q6, [x2, #96]
	str q7, [x2, #112]
	add x2, x2, #128
	sub x3, x3, #8
	lsr x13, x3, #3
	cbnz x13, 22b
	b 21f
20:
21:
	cbz x3, 27f
29:
	ldr q0, [x2, #0]
	aesd v0.16b, v30.16b
	aesimc v0.16b, v0.16b
	cbz x6, 210f
	cbz x7, 212f
	aesd v0.16b, v29.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v28.16b
	aesimc v0.16b, v0.16b
	b 213f
212:
213:
	aesd v0.16b, v27.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v26.16b
	aesimc v0.16b, v0.16b
	b 211f
210:
211:
	aesd v0.16b, v25.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v24.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v23.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v22.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v21.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v20.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v19.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v18.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v17.16b
	eor v0.16b, v0.16b, v16.16b
	str q0, [x2, #0]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 29b
	b 28f
27:
28:
	ret
	.arch_extension noaes
	.p2align 6
