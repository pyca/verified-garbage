// The functions of `src/internal/vg_aes_ctr32_to.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_to:
	cbz x4, 20f
	sub x7, x4, #1
	cbz x7, 22f
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
	str x30, [x5, #464]
	add x30, x6, #0
	ldr x6, [x2, #0]
	str x6, [x5, #472]
	ldr w6, [x2, #8]
	str x6, [x5, #480]
	ldr w6, [x2, #12]
	rev w6, w6
	str w6, [x5, #488]
	add w6, w6, w4
	rev w6, w6
	str w6, [x2, #12]
	add x2, x1, #1
	lsl x6, x1, #4
	add x0, x0, x6
	add x1, x5, #1920
24:
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
	cbnz x2, 24b
	add x0, x1, #64
	cbz x4, 25f
27:
	ldr x6, [x5, #472]
	ldr w21, [x5, #488]
	add w21, w21, #0
	rev w21, w21
	lsl x21, x21, #32
	ldr x10, [x5, #480]
	eor x10, x10, x21
	ldr x7, [x5, #472]
	ldr w21, [x5, #488]
	add w21, w21, #1
	rev w21, w21
	lsl x21, x21, #32
	ldr x11, [x5, #480]
	eor x11, x11, x21
	ldr x8, [x5, #472]
	ldr w21, [x5, #488]
	add w21, w21, #2
	rev w21, w21
	lsl x21, x21, #32
	ldr x12, [x5, #480]
	eor x12, x12, x21
	ldr x9, [x5, #472]
	ldr w21, [x5, #488]
	add w21, w21, #3
	rev w21, w21
	lsl x21, x21, #32
	ldr x13, [x5, #480]
	eor x13, x13, x21
	ldr w21, [x5, #488]
	add w21, w21, #4
	str w21, [x5, #488]
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
28:
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
	cbnz x21, 28b
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
	cbnz x21, 29f
	ldr x21, [x3, #0]
	ldr x24, [x3, #8]
	eor x21, x21, x6
	eor x24, x24, x10
	str x21, [x30, #0]
	str x24, [x30, #8]
	sub x21, x4, #1
	cbnz x21, 211f
	b 212f
211:
	ldr x21, [x3, #16]
	ldr x24, [x3, #24]
	eor x21, x21, x7
	eor x24, x24, x11
	str x21, [x30, #16]
	str x24, [x30, #24]
	sub x21, x4, #2
	cbnz x21, 213f
	b 214f
213:
	ldr x21, [x3, #32]
	ldr x24, [x3, #40]
	eor x21, x21, x8
	eor x24, x24, x12
	str x21, [x30, #32]
	str x24, [x30, #40]
214:
212:
	movz x4, #0, lsl #0
	b 210f
29:
	ldr x21, [x3, #0]
	ldr x24, [x3, #8]
	eor x21, x21, x6
	eor x24, x24, x10
	str x21, [x30, #0]
	str x24, [x30, #8]
	ldr x21, [x3, #16]
	ldr x24, [x3, #24]
	eor x21, x21, x7
	eor x24, x24, x11
	str x21, [x30, #16]
	str x24, [x30, #24]
	ldr x21, [x3, #32]
	ldr x24, [x3, #40]
	eor x21, x21, x8
	eor x24, x24, x12
	str x21, [x30, #32]
	str x24, [x30, #40]
	ldr x21, [x3, #48]
	ldr x24, [x3, #56]
	eor x21, x21, x9
	eor x24, x24, x13
	str x21, [x30, #48]
	str x24, [x30, #56]
	add x3, x3, #64
	sub x4, x4, #4
	add x30, x30, #64
210:
	cbnz x4, 27b
	b 26f
25:
26:
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
	ldr x30, [x5, #464]
	b 23f
22:
	add x8, x6, #0
	ldr q0, [x2, #0]
	ldr w6, [x2, #12]
	rev w6, w6
	add w6, w6, #1
	rev w6, w6
	str w6, [x2, #12]
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
	ldr q1, [x0, #0]
	eor v0.16b, v0.16b, v1.16b
	sub x1, x1, #1
215:
	tbl v0.16b, {v0.16b}, v4.16b
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
	sshr v1.16b, v0.16b, #7
	shl v2.16b, v0.16b, #1
	and v1.16b, v1.16b, v7.16b
	eor v2.16b, v2.16b, v1.16b
	rev32 v1.8h, v0.8h
	eor v2.16b, v2.16b, v1.16b
	eor v0.16b, v0.16b, v2.16b
	ushr v1.4s, v0.4s, #8
	sli v1.4s, v0.4s, #24
	eor v0.16b, v1.16b, v2.16b
	add x0, x0, #16
	ldr q1, [x0, #0]
	eor v0.16b, v0.16b, v1.16b
	sub x1, x1, #1
	cbnz x1, 215b
	tbl v0.16b, {v0.16b}, v4.16b
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
	ldr q1, [x0, #16]
	eor v0.16b, v0.16b, v1.16b
	ldr q1, [x3, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x8, #0]
23:
	b 21f
20:
21:
	ret
	.p2align 6
