// The functions of `src/camellia.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_expand_key:
	sub sp, sp, #3248
	add x3, sp, #0
	add x5, x3, #0
	add x3, x1, #0
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
	add x1, x5, #0
	add x1, x1, #768
	movz x21, #65280, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x1, #0]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	movk x21, #255, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x1, #8]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #16]
	movz x21, #65280, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x1, #24]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #32]
	movz x21, #65535, lsl #0
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #40]
	movz x21, #0, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #48]
	movz x21, #255, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #56]
	add x1, x1, #64
	movz x21, #0, lsl #0
	movk x21, #65280, lsl #32
	str x21, [x1, #0]
	movz x21, #255, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #8]
	movz x21, #65535, lsl #0
	str x21, [x1, #16]
	movz x21, #65280, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #24]
	movz x21, #255, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x1, #32]
	movz x21, #255, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #40]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #48]
	movz x21, #255, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #255, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #56]
	add x1, x1, #64
	movz x21, #65280, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #0]
	movz x21, #255, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x1, #8]
	movz x21, #255, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #255, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x1, #16]
	movz x21, #65280, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x1, #24]
	movz x21, #0, lsl #0
	movk x21, #255, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #32]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	movk x21, #255, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x1, #40]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x1, #48]
	movz x21, #65535, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #56]
	add x1, x1, #64
	movz x21, #65280, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #0]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x1, #8]
	movz x21, #255, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x1, #16]
	movz x21, #0, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #24]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #255, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #32]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #40]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x1, #48]
	movz x21, #65280, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #255, lsl #48
	str x21, [x1, #56]
	add x1, x1, #64
	movz x21, #0, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #0]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #8]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #16]
	movz x21, #65280, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x1, #24]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x1, #32]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #255, lsl #48
	str x21, [x1, #40]
	movz x21, #65280, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #255, lsl #48
	str x21, [x1, #48]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	movk x21, #255, lsl #48
	str x21, [x1, #56]
	add x1, x1, #64
	movz x21, #65280, lsl #0
	movk x21, #65280, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #0]
	movz x21, #65280, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #255, lsl #48
	str x21, [x1, #8]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65280, lsl #48
	str x21, [x1, #16]
	movz x21, #0, lsl #0
	movk x21, #255, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x1, #24]
	movz x21, #65535, lsl #0
	movk x21, #255, lsl #16
	movk x21, #65280, lsl #48
	str x21, [x1, #32]
	movz x21, #65535, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #65280, lsl #48
	str x21, [x1, #40]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x1, #48]
	movz x21, #65535, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x1, #56]
	add x1, x1, #64
	ldr x21, [x0, #0]
	str x21, [x5, #3024]
	ldr x21, [x0, #8]
	str x21, [x5, #3032]
	sub x22, x3, #16
	cbz x22, 20f
	ldr x21, [x0, #16]
	str x21, [x5, #3040]
	sub x22, x3, #24
	cbz x22, 22f
	ldr x21, [x0, #24]
	str x21, [x5, #3048]
	b 23f
22:
	movz x23, #0, lsl #0
	sub x23, x23, #1
	eor x21, x21, x23
	str x21, [x5, #3048]
23:
	b 21f
20:
	movz x21, #0, lsl #0
	str x21, [x5, #3040]
	str x21, [x5, #3048]
21:
	add x1, x5, #0
	add x1, x1, #768
	ldr x21, [x5, #3024]
	str x21, [x5, #3056]
	ldr x21, [x5, #3032]
	str x21, [x5, #3064]
	ldr x21, [x5, #3040]
	ldr x22, [x5, #3056]
	eor x21, x21, x22
	str x21, [x5, #3056]
	ldr x21, [x5, #3048]
	ldr x22, [x5, #3064]
	eor x21, x21, x22
	str x21, [x5, #3064]
	movz x4, #3, lsl #0
	add x0, x5, #0
	add x0, x0, #3056
24:
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
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
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
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
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
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #576]
	eor x6, x6, x21
	str x6, [x5, #576]
	ldr x21, [x5, #584]
	eor x7, x7, x21
	str x7, [x5, #584]
	ldr x21, [x5, #592]
	eor x8, x8, x21
	str x8, [x5, #592]
	ldr x21, [x5, #600]
	eor x9, x9, x21
	str x9, [x5, #600]
	ldr x21, [x5, #608]
	eor x10, x10, x21
	str x10, [x5, #608]
	ldr x21, [x5, #616]
	eor x11, x11, x21
	str x11, [x5, #616]
	ldr x21, [x5, #624]
	eor x12, x12, x21
	str x12, [x5, #624]
	ldr x21, [x5, #632]
	eor x13, x13, x21
	str x13, [x5, #632]
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #512]
	eor x6, x6, x21
	str x6, [x5, #512]
	ldr x21, [x5, #520]
	eor x7, x7, x21
	str x7, [x5, #520]
	ldr x21, [x5, #528]
	eor x8, x8, x21
	str x8, [x5, #528]
	ldr x21, [x5, #536]
	eor x9, x9, x21
	str x9, [x5, #536]
	ldr x21, [x5, #544]
	eor x10, x10, x21
	str x10, [x5, #544]
	ldr x21, [x5, #552]
	eor x11, x11, x21
	str x11, [x5, #552]
	ldr x21, [x5, #560]
	eor x12, x12, x21
	str x12, [x5, #560]
	ldr x21, [x5, #568]
	eor x13, x13, x21
	str x13, [x5, #568]
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
	str x6, [x5, #3056]
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
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
	str x6, [x5, #3064]
	add x1, x1, #128
	lsr x22, x4, #1
	cbnz x22, 25f
	ldr x21, [x5, #3056]
	str x21, [x5, #3088]
	ldr x21, [x5, #3064]
	str x21, [x5, #3096]
	b 26f
25:
	sub x22, x4, #3
	cbz x22, 27f
	ldr x21, [x5, #3056]
	str x21, [x5, #3072]
	ldr x21, [x5, #3064]
	str x21, [x5, #3080]
	ldr x21, [x5, #3040]
	ldr x22, [x5, #3056]
	eor x21, x21, x22
	str x21, [x5, #3056]
	ldr x21, [x5, #3048]
	ldr x22, [x5, #3064]
	eor x21, x21, x22
	str x21, [x5, #3064]
	b 28f
27:
	ldr x21, [x5, #3024]
	ldr x22, [x5, #3056]
	eor x21, x21, x22
	str x21, [x5, #3056]
	ldr x21, [x5, #3032]
	ldr x22, [x5, #3064]
	eor x21, x21, x22
	str x21, [x5, #3064]
28:
26:
	sub x4, x4, #1
	cbnz x4, 24b
	ldr x6, [x5, #3024]
	rev x6, x6
	ldr x7, [x5, #3032]
	rev x7, x7
	ldr x8, [x5, #3040]
	rev x8, x8
	ldr x9, [x5, #3048]
	rev x9, x9
	ldr x10, [x5, #3072]
	rev x10, x10
	ldr x11, [x5, #3080]
	rev x11, x11
	ldr x12, [x5, #3088]
	rev x12, x12
	ldr x13, [x5, #3096]
	rev x13, x13
	sub x21, x3, #16
	cbz x21, 29f
	add x21, x6, #0
	rev x21, x21
	str x21, [x2, #0]
	add x21, x7, #0
	rev x21, x21
	str x21, [x2, #8]
	add x21, x12, #0
	rev x21, x21
	str x21, [x2, #16]
	add x21, x13, #0
	rev x21, x21
	str x21, [x2, #24]
	lsl x21, x8, #15
	lsr x22, x9, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #32]
	lsl x21, x9, #15
	lsr x22, x8, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #40]
	lsl x21, x10, #15
	lsr x22, x11, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #48]
	lsl x21, x11, #15
	lsr x22, x10, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #56]
	lsl x21, x8, #30
	lsr x22, x9, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #64]
	lsl x21, x9, #30
	lsr x22, x8, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #72]
	lsl x21, x12, #30
	lsr x22, x13, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #80]
	lsl x21, x13, #30
	lsr x22, x12, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #88]
	lsl x21, x6, #45
	lsr x22, x7, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #96]
	lsl x21, x7, #45
	lsr x22, x6, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #104]
	lsl x21, x10, #45
	lsr x22, x11, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #112]
	lsl x21, x11, #45
	lsr x22, x10, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #120]
	lsl x21, x6, #60
	lsr x22, x7, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #128]
	lsl x21, x7, #60
	lsr x22, x6, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #136]
	lsl x21, x8, #60
	lsr x22, x9, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #144]
	lsl x21, x9, #60
	lsr x22, x8, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #152]
	lsl x21, x12, #60
	lsr x22, x13, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #160]
	lsl x21, x13, #60
	lsr x22, x12, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #168]
	lsl x21, x7, #13
	lsr x22, x6, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #176]
	lsl x21, x6, #13
	lsr x22, x7, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #184]
	lsl x21, x11, #13
	lsr x22, x10, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #192]
	lsl x21, x10, #13
	lsr x22, x11, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #200]
	lsl x21, x9, #30
	lsr x22, x8, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #208]
	lsl x21, x8, #30
	lsr x22, x9, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #216]
	lsl x21, x11, #30
	lsr x22, x10, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #224]
	lsl x21, x10, #30
	lsr x22, x11, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #232]
	lsl x21, x7, #47
	lsr x22, x6, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #240]
	lsl x21, x6, #47
	lsr x22, x7, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #248]
	lsl x21, x13, #47
	lsr x22, x12, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #256]
	lsl x21, x12, #47
	lsr x22, x13, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #264]
	b 210f
29:
	add x21, x6, #0
	rev x21, x21
	str x21, [x2, #0]
	add x21, x7, #0
	rev x21, x21
	str x21, [x2, #8]
	add x21, x10, #0
	rev x21, x21
	str x21, [x2, #16]
	add x21, x11, #0
	rev x21, x21
	str x21, [x2, #24]
	lsl x21, x6, #15
	lsr x22, x7, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #32]
	lsl x21, x7, #15
	lsr x22, x6, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #40]
	lsl x21, x10, #15
	lsr x22, x11, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #48]
	lsl x21, x11, #15
	lsr x22, x10, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #56]
	lsl x21, x10, #30
	lsr x22, x11, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #64]
	lsl x21, x11, #30
	lsr x22, x10, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #72]
	lsl x21, x6, #45
	lsr x22, x7, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #80]
	lsl x21, x7, #45
	lsr x22, x6, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #88]
	lsl x21, x10, #45
	lsr x22, x11, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #96]
	lsl x21, x7, #60
	lsr x22, x6, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #104]
	lsl x21, x10, #60
	lsr x22, x11, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #112]
	lsl x21, x11, #60
	lsr x22, x10, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #120]
	lsl x21, x7, #13
	lsr x22, x6, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #128]
	lsl x21, x6, #13
	lsr x22, x7, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #136]
	lsl x21, x7, #30
	lsr x22, x6, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #144]
	lsl x21, x6, #30
	lsr x22, x7, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #152]
	lsl x21, x11, #30
	lsr x22, x10, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #160]
	lsl x21, x10, #30
	lsr x22, x11, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #168]
	lsl x21, x7, #47
	lsr x22, x6, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #176]
	lsl x21, x6, #47
	lsr x22, x7, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #184]
	lsl x21, x11, #47
	lsr x22, x10, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #192]
	lsl x21, x10, #47
	lsr x22, x11, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #200]
210:
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
	add x16, sp, #512
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
	add x16, sp, #1024
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
	add x16, sp, #1536
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
	add x16, sp, #2048
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
	add x16, sp, #2560
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
	add x16, sp, #3072
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
	add sp, sp, #3248
	ret
	.p2align 6

vg_camellia_ecb_encrypt:
	sub sp, sp, #3248
	add x4, sp, #0
	add x5, x4, #0
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
	cbz x21, 20f
	add x4, x5, #0
	add x4, x4, #2816
	movz x22, #34, lsl #0
	b 21f
20:
	add x4, x5, #0
	add x4, x4, #2304
	movz x22, #26, lsl #0
21:
	add x1, x5, #0
	add x1, x1, #768
22:
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
	cbnz x22, 22b
	cbz x3, 23f
25:
	lsr x21, x3, #3
	cbnz x21, 26f
	add x16, x3, #0
	b 27f
26:
	movz x16, #8, lsl #0
27:
	add x14, x2, #0
	add x15, x5, #0
	add x15, x15, #3024
	add x17, x16, #0
28:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 28b
	add x1, x5, #0
	add x1, x1, #768
	ldr x6, [x5, #3032]
	ldr x7, [x5, #3048]
	ldr x8, [x5, #3064]
	ldr x9, [x5, #3080]
	ldr x10, [x5, #3096]
	ldr x11, [x5, #3112]
	ldr x12, [x5, #3128]
	ldr x13, [x5, #3144]
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
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #3024]
	ldr x7, [x5, #3040]
	ldr x8, [x5, #3056]
	ldr x9, [x5, #3072]
	ldr x10, [x5, #3088]
	ldr x11, [x5, #3104]
	ldr x12, [x5, #3120]
	ldr x13, [x5, #3136]
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
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	ldr x21, [x5, #576]
	ldr x23, [x1, #64]
	eor x21, x21, x23
	str x21, [x5, #576]
	ldr x21, [x5, #584]
	ldr x23, [x1, #72]
	eor x21, x21, x23
	str x21, [x5, #584]
	ldr x21, [x5, #592]
	ldr x23, [x1, #80]
	eor x21, x21, x23
	str x21, [x5, #592]
	ldr x21, [x5, #600]
	ldr x23, [x1, #88]
	eor x21, x21, x23
	str x21, [x5, #600]
	ldr x21, [x5, #608]
	ldr x23, [x1, #96]
	eor x21, x21, x23
	str x21, [x5, #608]
	ldr x21, [x5, #616]
	ldr x23, [x1, #104]
	eor x21, x21, x23
	str x21, [x5, #616]
	ldr x21, [x5, #624]
	ldr x23, [x1, #112]
	eor x21, x21, x23
	str x21, [x5, #624]
	ldr x21, [x5, #632]
	ldr x23, [x1, #120]
	eor x21, x21, x23
	str x21, [x5, #632]
	add x1, x1, #128
29:
	add x0, x1, #384
210:
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
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #576]
	eor x6, x6, x21
	str x6, [x5, #576]
	ldr x21, [x5, #584]
	eor x7, x7, x21
	str x7, [x5, #584]
	ldr x21, [x5, #592]
	eor x8, x8, x21
	str x8, [x5, #592]
	ldr x21, [x5, #600]
	eor x9, x9, x21
	str x9, [x5, #600]
	ldr x21, [x5, #608]
	eor x10, x10, x21
	str x10, [x5, #608]
	ldr x21, [x5, #616]
	eor x11, x11, x21
	str x11, [x5, #616]
	ldr x21, [x5, #624]
	eor x12, x12, x21
	str x12, [x5, #624]
	ldr x21, [x5, #632]
	eor x13, x13, x21
	str x13, [x5, #632]
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #512]
	eor x6, x6, x21
	str x6, [x5, #512]
	ldr x21, [x5, #520]
	eor x7, x7, x21
	str x7, [x5, #520]
	ldr x21, [x5, #528]
	eor x8, x8, x21
	str x8, [x5, #528]
	ldr x21, [x5, #536]
	eor x9, x9, x21
	str x9, [x5, #536]
	ldr x21, [x5, #544]
	eor x10, x10, x21
	str x10, [x5, #544]
	ldr x21, [x5, #552]
	eor x11, x11, x21
	str x11, [x5, #552]
	ldr x21, [x5, #560]
	eor x12, x12, x21
	str x12, [x5, #560]
	ldr x21, [x5, #568]
	eor x13, x13, x21
	str x13, [x5, #568]
	add x1, x1, #128
	sub x21, x1, x0
	cbnz x21, 210b
	sub x21, x1, x4
	cbnz x21, 211f
	b 212f
211:
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
	ldr x24, [x5, #384]
	ldr x23, [x1, #120]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #112]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #104]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #96]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #88]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #80]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #72]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #64]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #112]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #104]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #96]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #88]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #80]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #72]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #64]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #120]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #512]
	ldr x7, [x5, #520]
	ldr x8, [x5, #528]
	ldr x9, [x5, #536]
	ldr x10, [x5, #544]
	ldr x11, [x5, #552]
	ldr x12, [x5, #560]
	ldr x13, [x5, #568]
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #48]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #40]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #32]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #24]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #16]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #8]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #0]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #56]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #384]
	ldr x23, [x1, #56]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #48]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #40]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #32]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #24]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #16]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #8]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #0]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	add x1, x1, #128
212:
	sub x21, x1, x4
	cbnz x21, 29b
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
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
	str x6, [x5, #3032]
	str x7, [x5, #3048]
	str x8, [x5, #3064]
	str x9, [x5, #3080]
	str x10, [x5, #3096]
	str x11, [x5, #3112]
	str x12, [x5, #3128]
	str x13, [x5, #3144]
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
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
	str x6, [x5, #3024]
	str x7, [x5, #3040]
	str x8, [x5, #3056]
	str x9, [x5, #3072]
	str x10, [x5, #3088]
	str x11, [x5, #3104]
	str x12, [x5, #3120]
	str x13, [x5, #3136]
	lsr x21, x3, #3
	cbnz x21, 213f
	add x16, x3, #0
	b 214f
213:
	movz x16, #8, lsl #0
214:
	add x14, x5, #0
	add x14, x14, #3024
	add x15, x2, #0
	add x17, x16, #0
215:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 215b
	sub x3, x3, x16
	add x2, x2, #128
	cbnz x3, 25b
	b 24f
23:
24:
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
	add x16, sp, #512
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
	add x16, sp, #1024
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
	add x16, sp, #1536
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
	add x16, sp, #2048
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
	add x16, sp, #2560
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
	add x16, sp, #3072
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
	add sp, sp, #3248
	ret
	.p2align 6

vg_camellia_ecb_decrypt:
	sub sp, sp, #3248
	add x4, sp, #0
	add x5, x4, #0
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
	cbz x21, 20f
	add x4, x5, #0
	add x4, x4, #2816
	add x0, x0, #256
	movz x22, #30, lsl #0
	b 21f
20:
	add x4, x5, #0
	add x4, x4, #2304
	add x0, x0, #192
	movz x22, #22, lsl #0
21:
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
22:
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
	cbnz x22, 22b
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
	cbz x3, 23f
25:
	lsr x21, x3, #3
	cbnz x21, 26f
	add x16, x3, #0
	b 27f
26:
	movz x16, #8, lsl #0
27:
	add x14, x2, #0
	add x15, x5, #0
	add x15, x15, #3024
	add x17, x16, #0
28:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 28b
	add x1, x5, #0
	add x1, x1, #768
	ldr x6, [x5, #3032]
	ldr x7, [x5, #3048]
	ldr x8, [x5, #3064]
	ldr x9, [x5, #3080]
	ldr x10, [x5, #3096]
	ldr x11, [x5, #3112]
	ldr x12, [x5, #3128]
	ldr x13, [x5, #3144]
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
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #3024]
	ldr x7, [x5, #3040]
	ldr x8, [x5, #3056]
	ldr x9, [x5, #3072]
	ldr x10, [x5, #3088]
	ldr x11, [x5, #3104]
	ldr x12, [x5, #3120]
	ldr x13, [x5, #3136]
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
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	ldr x21, [x5, #576]
	ldr x23, [x1, #64]
	eor x21, x21, x23
	str x21, [x5, #576]
	ldr x21, [x5, #584]
	ldr x23, [x1, #72]
	eor x21, x21, x23
	str x21, [x5, #584]
	ldr x21, [x5, #592]
	ldr x23, [x1, #80]
	eor x21, x21, x23
	str x21, [x5, #592]
	ldr x21, [x5, #600]
	ldr x23, [x1, #88]
	eor x21, x21, x23
	str x21, [x5, #600]
	ldr x21, [x5, #608]
	ldr x23, [x1, #96]
	eor x21, x21, x23
	str x21, [x5, #608]
	ldr x21, [x5, #616]
	ldr x23, [x1, #104]
	eor x21, x21, x23
	str x21, [x5, #616]
	ldr x21, [x5, #624]
	ldr x23, [x1, #112]
	eor x21, x21, x23
	str x21, [x5, #624]
	ldr x21, [x5, #632]
	ldr x23, [x1, #120]
	eor x21, x21, x23
	str x21, [x5, #632]
	add x1, x1, #128
29:
	add x0, x1, #384
210:
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
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #576]
	eor x6, x6, x21
	str x6, [x5, #576]
	ldr x21, [x5, #584]
	eor x7, x7, x21
	str x7, [x5, #584]
	ldr x21, [x5, #592]
	eor x8, x8, x21
	str x8, [x5, #592]
	ldr x21, [x5, #600]
	eor x9, x9, x21
	str x9, [x5, #600]
	ldr x21, [x5, #608]
	eor x10, x10, x21
	str x10, [x5, #608]
	ldr x21, [x5, #616]
	eor x11, x11, x21
	str x11, [x5, #616]
	ldr x21, [x5, #624]
	eor x12, x12, x21
	str x12, [x5, #624]
	ldr x21, [x5, #632]
	eor x13, x13, x21
	str x13, [x5, #632]
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #512]
	eor x6, x6, x21
	str x6, [x5, #512]
	ldr x21, [x5, #520]
	eor x7, x7, x21
	str x7, [x5, #520]
	ldr x21, [x5, #528]
	eor x8, x8, x21
	str x8, [x5, #528]
	ldr x21, [x5, #536]
	eor x9, x9, x21
	str x9, [x5, #536]
	ldr x21, [x5, #544]
	eor x10, x10, x21
	str x10, [x5, #544]
	ldr x21, [x5, #552]
	eor x11, x11, x21
	str x11, [x5, #552]
	ldr x21, [x5, #560]
	eor x12, x12, x21
	str x12, [x5, #560]
	ldr x21, [x5, #568]
	eor x13, x13, x21
	str x13, [x5, #568]
	add x1, x1, #128
	sub x21, x1, x0
	cbnz x21, 210b
	sub x21, x1, x4
	cbnz x21, 211f
	b 212f
211:
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
	ldr x24, [x5, #384]
	ldr x23, [x1, #120]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #112]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #104]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #96]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #88]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #80]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #72]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #64]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #112]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #104]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #96]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #88]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #80]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #72]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #64]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #120]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #512]
	ldr x7, [x5, #520]
	ldr x8, [x5, #528]
	ldr x9, [x5, #536]
	ldr x10, [x5, #544]
	ldr x11, [x5, #552]
	ldr x12, [x5, #560]
	ldr x13, [x5, #568]
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #48]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #40]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #32]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #24]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #16]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #8]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #0]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #56]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #384]
	ldr x23, [x1, #56]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #48]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #40]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #32]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #24]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #16]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #8]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #0]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	add x1, x1, #128
212:
	sub x21, x1, x4
	cbnz x21, 29b
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
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
	str x6, [x5, #3032]
	str x7, [x5, #3048]
	str x8, [x5, #3064]
	str x9, [x5, #3080]
	str x10, [x5, #3096]
	str x11, [x5, #3112]
	str x12, [x5, #3128]
	str x13, [x5, #3144]
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
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
	str x6, [x5, #3024]
	str x7, [x5, #3040]
	str x8, [x5, #3056]
	str x9, [x5, #3072]
	str x10, [x5, #3088]
	str x11, [x5, #3104]
	str x12, [x5, #3120]
	str x13, [x5, #3136]
	lsr x21, x3, #3
	cbnz x21, 213f
	add x16, x3, #0
	b 214f
213:
	movz x16, #8, lsl #0
214:
	add x14, x5, #0
	add x14, x14, #3024
	add x15, x2, #0
	add x17, x16, #0
215:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 215b
	sub x3, x3, x16
	add x2, x2, #128
	cbnz x3, 25b
	b 24f
23:
24:
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
	add x16, sp, #512
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
	add x16, sp, #1024
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
	add x16, sp, #1536
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
	add x16, sp, #2048
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
	add x16, sp, #2560
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
	add x16, sp, #3072
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
	add sp, sp, #3248
	ret
	.p2align 6

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

vg_camellia_crypt_prepared:
	add x5, x1, #0
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
	sub x21, x0, #18
	cbz x21, 20f
	add x4, x5, #0
	add x4, x4, #2816
	b 21f
20:
	add x4, x5, #0
	add x4, x4, #2304
21:
	add x1, x5, #0
	add x1, x1, #768
	ldr x6, [x5, #3032]
	ldr x7, [x5, #3048]
	ldr x8, [x5, #3064]
	ldr x9, [x5, #3080]
	ldr x10, [x5, #3096]
	ldr x11, [x5, #3112]
	ldr x12, [x5, #3128]
	ldr x13, [x5, #3144]
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
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #3024]
	ldr x7, [x5, #3040]
	ldr x8, [x5, #3056]
	ldr x9, [x5, #3072]
	ldr x10, [x5, #3088]
	ldr x11, [x5, #3104]
	ldr x12, [x5, #3120]
	ldr x13, [x5, #3136]
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
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	ldr x21, [x5, #576]
	ldr x23, [x1, #64]
	eor x21, x21, x23
	str x21, [x5, #576]
	ldr x21, [x5, #584]
	ldr x23, [x1, #72]
	eor x21, x21, x23
	str x21, [x5, #584]
	ldr x21, [x5, #592]
	ldr x23, [x1, #80]
	eor x21, x21, x23
	str x21, [x5, #592]
	ldr x21, [x5, #600]
	ldr x23, [x1, #88]
	eor x21, x21, x23
	str x21, [x5, #600]
	ldr x21, [x5, #608]
	ldr x23, [x1, #96]
	eor x21, x21, x23
	str x21, [x5, #608]
	ldr x21, [x5, #616]
	ldr x23, [x1, #104]
	eor x21, x21, x23
	str x21, [x5, #616]
	ldr x21, [x5, #624]
	ldr x23, [x1, #112]
	eor x21, x21, x23
	str x21, [x5, #624]
	ldr x21, [x5, #632]
	ldr x23, [x1, #120]
	eor x21, x21, x23
	str x21, [x5, #632]
	add x1, x1, #128
22:
	add x0, x1, #384
23:
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
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #576]
	eor x6, x6, x21
	str x6, [x5, #576]
	ldr x21, [x5, #584]
	eor x7, x7, x21
	str x7, [x5, #584]
	ldr x21, [x5, #592]
	eor x8, x8, x21
	str x8, [x5, #592]
	ldr x21, [x5, #600]
	eor x9, x9, x21
	str x9, [x5, #600]
	ldr x21, [x5, #608]
	eor x10, x10, x21
	str x10, [x5, #608]
	ldr x21, [x5, #616]
	eor x11, x11, x21
	str x11, [x5, #616]
	ldr x21, [x5, #624]
	eor x12, x12, x21
	str x12, [x5, #624]
	ldr x21, [x5, #632]
	eor x13, x13, x21
	str x13, [x5, #632]
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #512]
	eor x6, x6, x21
	str x6, [x5, #512]
	ldr x21, [x5, #520]
	eor x7, x7, x21
	str x7, [x5, #520]
	ldr x21, [x5, #528]
	eor x8, x8, x21
	str x8, [x5, #528]
	ldr x21, [x5, #536]
	eor x9, x9, x21
	str x9, [x5, #536]
	ldr x21, [x5, #544]
	eor x10, x10, x21
	str x10, [x5, #544]
	ldr x21, [x5, #552]
	eor x11, x11, x21
	str x11, [x5, #552]
	ldr x21, [x5, #560]
	eor x12, x12, x21
	str x12, [x5, #560]
	ldr x21, [x5, #568]
	eor x13, x13, x21
	str x13, [x5, #568]
	add x1, x1, #128
	sub x21, x1, x0
	cbnz x21, 23b
	sub x21, x1, x4
	cbnz x21, 24f
	b 25f
24:
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
	ldr x24, [x5, #384]
	ldr x23, [x1, #120]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #112]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #104]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #96]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #88]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #80]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #72]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #64]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #112]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #104]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #96]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #88]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #80]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #72]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #64]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #120]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #512]
	ldr x7, [x5, #520]
	ldr x8, [x5, #528]
	ldr x9, [x5, #536]
	ldr x10, [x5, #544]
	ldr x11, [x5, #552]
	ldr x12, [x5, #560]
	ldr x13, [x5, #568]
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #48]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #40]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #32]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #24]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #16]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #8]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #0]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #56]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #384]
	ldr x23, [x1, #56]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #48]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #40]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #32]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #24]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #16]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #8]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #0]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	add x1, x1, #128
25:
	sub x21, x1, x4
	cbnz x21, 22b
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
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
	str x6, [x5, #3032]
	str x7, [x5, #3048]
	str x8, [x5, #3064]
	str x9, [x5, #3080]
	str x10, [x5, #3096]
	str x11, [x5, #3112]
	str x12, [x5, #3128]
	str x13, [x5, #3144]
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
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
	str x6, [x5, #3024]
	str x7, [x5, #3040]
	str x8, [x5, #3056]
	str x9, [x5, #3072]
	str x10, [x5, #3088]
	str x11, [x5, #3104]
	str x12, [x5, #3120]
	str x13, [x5, #3136]
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

vg_camellia_prepare_encrypt_keys:
	add x5, x2, #0
	add x9, x21, #0
	movz x21, #33392, lsl #0
	movk x21, #60460, lsl #16
	movk x21, #10163, lsl #32
	movk x21, #58816, lsl #48
	str x21, [x5, #0]
	movz x21, #34276, lsl #0
	movk x21, #13655, lsl #16
	movk x21, #3306, lsl #32
	movk x21, #16814, lsl #48
	str x21, [x5, #8]
	movz x21, #61219, lsl #0
	movk x21, #37739, lsl #16
	movk x21, #6469, lsl #32
	movk x21, #8613, lsl #48
	str x21, [x5, #16]
	movz x21, #3821, lsl #0
	movk x21, #20047, lsl #16
	movk x21, #25885, lsl #32
	movk x21, #48530, lsl #48
	str x21, [x5, #24]
	movz x21, #47238, lsl #0
	movk x21, #36783, lsl #16
	movk x21, #60284, lsl #32
	movk x21, #52767, lsl #48
	str x21, [x5, #32]
	movz x21, #12350, lsl #0
	movk x21, #24540, lsl #16
	movk x21, #50526, lsl #32
	movk x21, #6667, lsl #48
	str x21, [x5, #40]
	movz x21, #57766, lsl #0
	movk x21, #51769, lsl #16
	movk x21, #18389, lsl #32
	movk x21, #15709, lsl #48
	str x21, [x5, #48]
	movz x21, #473, lsl #0
	movk x21, #54874, lsl #16
	movk x21, #22097, lsl #32
	movk x21, #19820, lsl #48
	str x21, [x5, #56]
	movz x21, #3467, lsl #0
	movk x21, #26266, lsl #16
	movk x21, #52475, lsl #32
	movk x21, #11696, lsl #48
	str x21, [x5, #64]
	movz x21, #4724, lsl #0
	movk x21, #8235, lsl #16
	movk x21, #45552, lsl #32
	movk x21, #39300, lsl #48
	str x21, [x5, #72]
	movz x21, #19679, lsl #0
	movk x21, #49867, lsl #16
	movk x21, #32308, lsl #32
	movk x21, #1398, lsl #48
	str x21, [x5, #80]
	movz x21, #46957, lsl #0
	movk x21, #12713, lsl #16
	movk x21, #6097, lsl #32
	movk x21, #55044, lsl #48
	str x21, [x5, #88]
	movz x21, #22548, lsl #0
	movk x21, #24890, lsl #16
	movk x21, #7134, lsl #32
	movk x21, #7185, lsl #48
	str x21, [x5, #96]
	movz x21, #3890, lsl #0
	movk x21, #5788, lsl #16
	movk x21, #6227, lsl #32
	movk x21, #8946, lsl #48
	str x21, [x5, #104]
	movz x21, #17662, lsl #0
	movk x21, #45775, lsl #16
	movk x21, #46531, lsl #32
	movk x21, #37242, lsl #48
	str x21, [x5, #112]
	movz x21, #2084, lsl #0
	movk x21, #43240, lsl #16
	movk x21, #64608, lsl #32
	movk x21, #20585, lsl #48
	str x21, [x5, #120]
	movz x21, #53418, lsl #0
	movk x21, #32160, lsl #16
	movk x21, #35233, lsl #32
	movk x21, #38754, lsl #48
	str x21, [x5, #128]
	movz x21, #23380, lsl #0
	movk x21, #38174, lsl #16
	movk x21, #65504, lsl #32
	movk x21, #53860, lsl #48
	str x21, [x5, #136]
	movz x21, #50192, lsl #0
	movk x21, #18432, lsl #16
	movk x21, #63395, lsl #32
	movk x21, #56181, lsl #48
	str x21, [x5, #144]
	movz x21, #906, lsl #0
	movk x21, #56038, lsl #16
	movk x21, #16137, lsl #32
	movk x21, #38109, lsl #48
	str x21, [x5, #152]
	movz x21, #23687, lsl #0
	movk x21, #643, lsl #16
	movk x21, #19149, lsl #32
	movk x21, #13200, lsl #48
	str x21, [x5, #160]
	movz x21, #26483, lsl #0
	movk x21, #62454, lsl #16
	movk x21, #32669, lsl #32
	movk x21, #58047, lsl #48
	str x21, [x5, #168]
	movz x21, #39762, lsl #0
	movk x21, #9944, lsl #16
	movk x21, #14280, lsl #32
	movk x21, #15302, lsl #48
	str x21, [x5, #176]
	movz x21, #38529, lsl #0
	movk x21, #19311, lsl #16
	movk x21, #48659, lsl #32
	movk x21, #11875, lsl #48
	str x21, [x5, #184]
	movz x21, #31209, lsl #0
	movk x21, #36007, lsl #16
	movk x21, #28319, lsl #32
	movk x21, #36540, lsl #48
	str x21, [x5, #192]
	movz x21, #62761, lsl #0
	movk x21, #46841, lsl #16
	movk x21, #64815, lsl #32
	movk x21, #22964, lsl #48
	str x21, [x5, #200]
	movz x21, #39032, lsl #0
	movk x21, #27142, lsl #16
	movk x21, #18151, lsl #32
	movk x21, #47729, lsl #48
	str x21, [x5, #208]
	movz x21, #9684, lsl #0
	movk x21, #17067, lsl #16
	movk x21, #41608, lsl #32
	movk x21, #64141, lsl #48
	str x21, [x5, #216]
	movz x21, #1906, lsl #0
	movk x21, #21945, lsl #16
	movk x21, #61176, lsl #32
	movk x21, #2732, lsl #48
	str x21, [x5, #224]
	movz x21, #18742, lsl #0
	movk x21, #26666, lsl #16
	movk x21, #14396, lsl #32
	movk x21, #42225, lsl #48
	str x21, [x5, #232]
	movz x21, #10304, lsl #0
	movk x21, #31699, lsl #16
	movk x21, #51643, lsl #32
	movk x21, #49475, lsl #48
	str x21, [x5, #240]
	movz x21, #58133, lsl #0
	movk x21, #62637, lsl #16
	movk x21, #51063, lsl #32
	movk x21, #40576, lsl #48
	str x21, [x5, #248]
	add x14, x0, #0
	add x15, x5, #256
	movz x17, #17, lsl #0
20:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 20b
	add x21, x9, #0
	ret
	.p2align 6

vg_camellia_encrypt_prepared:
	add x5, x1, #0
	add x1, x0, #0
	ldr q16, [x5, #0]
	ldr q17, [x5, #16]
	ldr q18, [x5, #32]
	ldr q19, [x5, #48]
	ldr q20, [x5, #64]
	ldr q21, [x5, #80]
	ldr q22, [x5, #96]
	ldr q23, [x5, #112]
	ldr q24, [x5, #128]
	ldr q25, [x5, #144]
	ldr q26, [x5, #160]
	ldr q27, [x5, #176]
	ldr q28, [x5, #192]
	ldr q29, [x5, #208]
	ldr q30, [x5, #224]
	ldr q31, [x5, #240]
	movz w15, #64, lsl #0
	dup v4.16b, w15
	movz w15, #128, lsl #0
	dup v5.16b, w15
	movz w15, #192, lsl #0
	dup v6.16b, w15
	movz x15, #65280, lsl #0
	movk x15, #255, lsl #32
	dup v7.2d, x15
	movz x13, #0, lsl #0
	movk x13, #65280, lsl #16
	movk x13, #255, lsl #48
	movz x14, #0, lsl #0
	movk x14, #255, lsl #16
	movk x14, #65280, lsl #32
	ldr x6, [x5, #768]
	rev x6, x6
	ldr x7, [x5, #776]
	rev x7, x7
	ldr x10, [x5, #256]
	rev x10, x10
	eor x6, x6, x10
	ldr x10, [x5, #264]
	rev x10, x10
	eor x7, x7, x10
	ldr x8, [x5, #272]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #280]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #288]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #296]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #304]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #312]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #320]
	rev x8, x8
	lsr x10, x6, #32
	add w12, w6, #0
	lsr x16, x8, #32
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	orr w11, w12, w8
	eor w10, w10, w11
	lsl x6, x10, #32
	orr x6, x6, x12
	ldr x8, [x5, #328]
	rev x8, x8
	lsr x10, x7, #32
	add w12, w7, #0
	lsr x16, x8, #32
	orr w11, w12, w8
	eor w10, w10, w11
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	lsl x7, x10, #32
	orr x7, x7, x12
	ldr x8, [x5, #336]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #344]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #352]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #360]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #368]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #376]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #384]
	rev x8, x8
	lsr x10, x6, #32
	add w12, w6, #0
	lsr x16, x8, #32
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	orr w11, w12, w8
	eor w10, w10, w11
	lsl x6, x10, #32
	orr x6, x6, x12
	ldr x8, [x5, #392]
	rev x8, x8
	lsr x10, x7, #32
	add w12, w7, #0
	lsr x16, x8, #32
	orr w11, w12, w8
	eor w10, w10, w11
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	lsl x7, x10, #32
	orr x7, x7, x12
	ldr x8, [x5, #400]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #408]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #416]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #424]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #432]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #440]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	sub x8, x1, #18
	cbz x8, 20f
	ldr x8, [x5, #448]
	rev x8, x8
	lsr x10, x6, #32
	add w12, w6, #0
	lsr x16, x8, #32
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	orr w11, w12, w8
	eor w10, w10, w11
	lsl x6, x10, #32
	orr x6, x6, x12
	ldr x8, [x5, #456]
	rev x8, x8
	lsr x10, x7, #32
	add w12, w7, #0
	lsr x16, x8, #32
	orr w11, w12, w8
	eor w10, w10, w11
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	lsl x7, x10, #32
	orr x7, x7, x12
	ldr x8, [x5, #464]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #472]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #480]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #488]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #496]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	ldr x8, [x5, #504]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x10, [x5, #512]
	rev x10, x10
	eor x7, x7, x10
	ldr x10, [x5, #520]
	rev x10, x10
	eor x6, x6, x10
	rev x7, x7
	rev x6, x6
	str x7, [x5, #768]
	str x6, [x5, #776]
	b 21f
20:
	ldr x10, [x5, #448]
	rev x10, x10
	eor x7, x7, x10
	ldr x10, [x5, #456]
	rev x10, x10
	eor x6, x6, x10
	rev x7, x7
	rev x6, x6
	str x7, [x5, #768]
	str x6, [x5, #776]
21:
	ret
	.p2align 6
