// The functions of `src/blake2b.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_compress:
	str x25, [x5, #0]
	str x26, [x5, #8]
	str x27, [x5, #16]
	str x3, [x5, #32]
	movz x27, #0, lsl #0
	str x27, [x5, #40]
	orr w4, w4, w4
	sub x3, x27, x4
	orr x4, x4, x3
	lsr x4, x4, #63
	sub x4, x27, x4
	str x4, [x5, #48]
	cbz x2, 20f
22:
	ldr x3, [x0, #0]
	ldr x4, [x0, #8]
	ldr x6, [x0, #16]
	ldr x7, [x0, #24]
	ldr x8, [x0, #32]
	ldr x9, [x0, #40]
	ldr x10, [x0, #48]
	ldr x11, [x0, #56]
	movz x12, #51464, lsl #0
	movk x12, #62396, lsl #16
	movk x12, #58983, lsl #32
	movk x12, #27145, lsl #48
	movz x13, #42811, lsl #0
	movk x13, #33994, lsl #16
	movk x13, #44677, lsl #32
	movk x13, #47975, lsl #48
	movz x14, #63531, lsl #0
	movk x14, #65172, lsl #16
	movk x14, #62322, lsl #32
	movk x14, #15470, lsl #48
	movz x15, #14065, lsl #0
	movk x15, #24349, lsl #16
	movk x15, #62778, lsl #32
	movk x15, #42319, lsl #48
	movz x16, #33489, lsl #0
	movk x16, #44518, lsl #16
	movk x16, #21119, lsl #32
	movk x16, #20750, lsl #48
	movz x17, #27679, lsl #0
	movk x17, #11070, lsl #16
	movk x17, #26764, lsl #32
	movk x17, #39685, lsl #48
	movz x25, #48491, lsl #0
	movk x25, #64321, lsl #16
	movk x25, #55723, lsl #32
	movk x25, #8067, lsl #48
	movz x26, #8569, lsl #0
	movk x26, #4990, lsl #16
	movk x26, #52505, lsl #32
	movk x26, #23520, lsl #48
	ldr x27, [x5, #32]
	eor x16, x16, x27
	ldr x27, [x5, #40]
	eor x17, x17, x27
	ldr x27, [x5, #48]
	eor x25, x25, x27
	ldr x27, [x1, #0]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #16]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #32]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #48]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #8]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #24]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #40]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #56]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #64]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #80]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #96]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #112]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #72]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #88]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #104]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #120]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #112]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #32]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #72]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #104]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #80]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #64]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #120]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #48]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #8]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #0]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #88]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #40]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #96]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #16]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #56]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #24]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #88]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #96]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #40]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #120]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #64]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #0]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #16]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #104]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #80]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #24]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #56]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #72]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #112]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #48]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #8]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #32]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #56]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #24]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #104]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #88]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #72]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #8]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #96]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #112]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #16]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #40]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #32]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #120]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #48]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #80]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #0]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #64]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #72]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #40]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #16]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #80]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #0]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #56]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #32]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #120]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #112]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #88]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #48]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #24]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #8]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #96]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #64]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #104]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #16]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #48]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #0]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #64]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #96]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #80]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #88]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #24]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #32]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #56]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #120]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #8]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #104]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #40]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #112]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #72]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #96]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #8]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #112]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #32]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #40]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #120]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #104]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #80]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #0]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #48]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #72]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #64]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #56]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #24]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #16]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #88]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #104]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #56]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #96]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #24]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #88]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #112]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #8]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #72]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #40]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #120]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #64]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #16]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #0]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #32]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #48]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #80]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #48]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #112]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #88]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #0]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #120]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #72]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #24]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #64]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #96]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #104]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #8]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #80]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #16]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #56]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #32]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #40]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #80]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #64]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #56]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #8]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #16]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #32]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #48]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #40]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #120]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #72]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #24]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #104]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #88]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #112]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #96]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #0]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #0]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #16]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #32]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #48]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #8]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #24]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #40]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #56]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #64]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #80]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #96]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #112]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #72]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #88]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #104]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #120]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x1, #112]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #32]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #72]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #104]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	ror x26, x26, #32
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #24
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ldr x27, [x1, #80]
	add x3, x3, x27
	add x3, x3, x8
	ldr x27, [x1, #64]
	add x4, x4, x27
	add x4, x4, x9
	ldr x27, [x1, #120]
	add x6, x6, x27
	add x6, x6, x10
	ldr x27, [x1, #48]
	add x7, x7, x27
	add x7, x7, x11
	eor x16, x16, x3
	eor x17, x17, x4
	eor x25, x25, x6
	eor x26, x26, x7
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	ror x26, x26, #16
	add x12, x12, x16
	add x13, x13, x17
	add x14, x14, x25
	add x15, x15, x26
	eor x8, x8, x12
	eor x9, x9, x13
	eor x10, x10, x14
	eor x11, x11, x15
	ror x8, x8, #63
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ldr x27, [x1, #8]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #0]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #88]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #40]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #32
	ror x16, x16, #32
	ror x17, x17, #32
	ror x25, x25, #32
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #24
	ror x10, x10, #24
	ror x11, x11, #24
	ror x8, x8, #24
	ldr x27, [x1, #96]
	add x3, x3, x27
	add x3, x3, x9
	ldr x27, [x1, #16]
	add x4, x4, x27
	add x4, x4, x10
	ldr x27, [x1, #56]
	add x6, x6, x27
	add x6, x6, x11
	ldr x27, [x1, #24]
	add x7, x7, x27
	add x7, x7, x8
	eor x26, x26, x3
	eor x16, x16, x4
	eor x17, x17, x6
	eor x25, x25, x7
	ror x26, x26, #16
	ror x16, x16, #16
	ror x17, x17, #16
	ror x25, x25, #16
	add x14, x14, x26
	add x15, x15, x16
	add x12, x12, x17
	add x13, x13, x25
	eor x9, x9, x14
	eor x10, x10, x15
	eor x11, x11, x12
	eor x8, x8, x13
	ror x9, x9, #63
	ror x10, x10, #63
	ror x11, x11, #63
	ror x8, x8, #63
	ldr x27, [x0, #0]
	eor x27, x27, x3
	eor x27, x27, x12
	str x27, [x0, #0]
	ldr x27, [x0, #8]
	eor x27, x27, x4
	eor x27, x27, x13
	str x27, [x0, #8]
	ldr x27, [x0, #16]
	eor x27, x27, x6
	eor x27, x27, x14
	str x27, [x0, #16]
	ldr x27, [x0, #24]
	eor x27, x27, x7
	eor x27, x27, x15
	str x27, [x0, #24]
	ldr x27, [x0, #32]
	eor x27, x27, x8
	eor x27, x27, x16
	str x27, [x0, #32]
	ldr x27, [x0, #40]
	eor x27, x27, x9
	eor x27, x27, x17
	str x27, [x0, #40]
	ldr x27, [x0, #48]
	eor x27, x27, x10
	eor x27, x27, x25
	str x27, [x0, #48]
	ldr x27, [x0, #56]
	eor x27, x27, x11
	eor x27, x27, x26
	str x27, [x0, #56]
	add x1, x1, #128
	ldr x3, [x5, #32]
	add x3, x3, #128
	str x3, [x5, #32]
	lsr x4, x3, #7
	sub x4, x4, #1
	lsr x4, x4, #63
	ldr x6, [x5, #40]
	add x6, x6, x4
	str x6, [x5, #40]
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	ldr x25, [x5, #0]
	ldr x26, [x5, #8]
	ldr x27, [x5, #16]
	ret
	.p2align 6

vg_blake2b_init:
	movz x9, #42811, lsl #0
	movk x9, #33994, lsl #16
	movk x9, #44677, lsl #32
	movk x9, #47975, lsl #48
	str x9, [x0, #8]
	movz x9, #63531, lsl #0
	movk x9, #65172, lsl #16
	movk x9, #62322, lsl #32
	movk x9, #15470, lsl #48
	str x9, [x0, #16]
	movz x9, #14065, lsl #0
	movk x9, #24349, lsl #16
	movk x9, #62778, lsl #32
	movk x9, #42319, lsl #48
	str x9, [x0, #24]
	movz x9, #33489, lsl #0
	movk x9, #44518, lsl #16
	movk x9, #21119, lsl #32
	movk x9, #20750, lsl #48
	str x9, [x0, #32]
	movz x9, #27679, lsl #0
	movk x9, #11070, lsl #16
	movk x9, #26764, lsl #32
	movk x9, #39685, lsl #48
	str x9, [x0, #40]
	movz x9, #48491, lsl #0
	movk x9, #64321, lsl #16
	movk x9, #55723, lsl #32
	movk x9, #8067, lsl #48
	str x9, [x0, #48]
	movz x9, #8569, lsl #0
	movk x9, #4990, lsl #16
	movk x9, #52505, lsl #32
	movk x9, #23520, lsl #48
	str x9, [x0, #56]
	movz x9, #51464, lsl #0
	movk x9, #62141, lsl #16
	movk x9, #58983, lsl #32
	movk x9, #27145, lsl #48
	lsl x10, x3, #8
	eor x9, x9, x10
	eor x9, x9, x1
	str x9, [x0, #0]
	cbz x3, 20f
	movz x9, #0, lsl #0
	str x9, [x0, #64]
	str x9, [x0, #72]
	str x9, [x0, #80]
	str x9, [x0, #88]
	str x9, [x0, #96]
	str x9, [x0, #104]
	str x9, [x0, #112]
	str x9, [x0, #120]
	str x9, [x0, #128]
	str x9, [x0, #136]
	str x9, [x0, #144]
	str x9, [x0, #152]
	str x9, [x0, #160]
	str x9, [x0, #168]
	str x9, [x0, #176]
	str x9, [x0, #184]
	add x12, x0, #64
22:
	ldrb w9, [x2, #0]
	strb w9, [x12, #0]
	add x2, x2, #1
	add x12, x12, #1
	sub x3, x3, #1
	cbnz x3, 22b
	b 21f
20:
21:
	ret
	.p2align 6

vg_blake2b_update:
	sub sp, sp, #576
	add x4, sp, #0
	str x30, [sp, #-16]!
	str x19, [x4, #512]
	str x20, [x4, #520]
	str x21, [x4, #528]
	str x22, [x4, #536]
	str x23, [x4, #544]
	str x24, [x4, #552]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x2, #0
	add x22, x3, #0
	add x24, x1, #0
	sub x23, x24, #1
	movz x9, #127, lsl #0
	and x23, x23, x9
	add x23, x23, #1
	cbz x24, 20f
	b 21f
20:
	movz x23, #0, lsl #0
21:
	cbz x22, 22f
	cbz x23, 24f
	movz x11, #128, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #7
	cbz x9, 26f
	b 27f
26:
	add x9, x22, x23
	lsr x9, x9, #7
	cbz x9, 28f
	b 29f
28:
	add x11, x22, #0
29:
27:
	sub x22, x22, x11
	add x24, x24, x11
	cbz x11, 210f
212:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #64]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 212b
	b 211f
210:
211:
	cbz x22, 213f
	add x0, x19, #0
	add x1, x19, #64
	movz x2, #1, lsl #0
	add x3, x24, #0
	movz x4, #0, lsl #0
	add x5, x20, #0
	bl {vg_blake2b_compress}
	movz x23, #0, lsl #0
	b 214f
213:
214:
	b 25f
24:
25:
	cbz x22, 215f
	sub x9, x22, #1
	lsr x10, x9, #7
	cbz x10, 217f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x10, #0
	add x3, x24, #128
	movz x4, #0, lsl #0
	add x5, x20, #0
	bl {vg_blake2b_compress}
	sub x9, x22, #1
	movz x10, #127, lsl #0
	and x9, x9, x10
	add x9, x9, #1
	sub x10, x22, x9
	add x21, x21, x10
	add x24, x24, x10
	add x22, x9, #0
	b 218f
217:
218:
	add x11, x22, #0
	add x24, x24, x22
	movz x22, #0, lsl #0
219:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #64]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 219b
	b 216f
215:
216:
	b 23f
22:
23:
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #576
	ret
	.p2align 6

vg_blake2b_finalize:
	sub sp, sp, #576
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #512]
	str x20, [x3, #520]
	str x21, [x3, #528]
	str x22, [x3, #536]
	str x23, [x3, #544]
	str x24, [x3, #552]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x24, x1, #0
	sub x23, x24, #1
	movz x9, #127, lsl #0
	and x23, x23, x9
	add x23, x23, #1
	cbz x24, 20f
	b 21f
20:
	movz x23, #0, lsl #0
21:
	movz x9, #0, lsl #0
	movz x11, #128, lsl #0
	sub x11, x11, x23
	cbz x11, 22f
24:
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 24b
	b 23f
22:
23:
	add x0, x19, #0
	add x1, x19, #64
	movz x2, #1, lsl #0
	add x3, x24, #0
	movz x4, #1, lsl #0
	add x5, x20, #0
	bl {vg_blake2b_compress}
	ldr x9, [x19, #0]
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	str x9, [x21, #56]
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #576
	ret
	.p2align 6

vg_blake2b_update_scratch:
	str x30, [sp, #-16]!
	str x19, [x4, #512]
	str x20, [x4, #520]
	str x21, [x4, #528]
	str x22, [x4, #536]
	str x23, [x4, #544]
	str x24, [x4, #552]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x2, #0
	add x22, x3, #0
	add x24, x1, #0
	sub x23, x24, #1
	movz x9, #127, lsl #0
	and x23, x23, x9
	add x23, x23, #1
	cbz x24, 20f
	b 21f
20:
	movz x23, #0, lsl #0
21:
	cbz x22, 22f
	cbz x23, 24f
	movz x11, #128, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #7
	cbz x9, 26f
	b 27f
26:
	add x9, x22, x23
	lsr x9, x9, #7
	cbz x9, 28f
	b 29f
28:
	add x11, x22, #0
29:
27:
	sub x22, x22, x11
	add x24, x24, x11
	cbz x11, 210f
212:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #64]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 212b
	b 211f
210:
211:
	cbz x22, 213f
	add x0, x19, #0
	add x1, x19, #64
	movz x2, #1, lsl #0
	add x3, x24, #0
	movz x4, #0, lsl #0
	add x5, x20, #0
	bl {vg_blake2b_compress}
	movz x23, #0, lsl #0
	b 214f
213:
214:
	b 25f
24:
25:
	cbz x22, 215f
	sub x9, x22, #1
	lsr x10, x9, #7
	cbz x10, 217f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x10, #0
	add x3, x24, #128
	movz x4, #0, lsl #0
	add x5, x20, #0
	bl {vg_blake2b_compress}
	sub x9, x22, #1
	movz x10, #127, lsl #0
	and x9, x9, x10
	add x9, x9, #1
	sub x10, x22, x9
	add x21, x21, x10
	add x24, x24, x10
	add x22, x9, #0
	b 218f
217:
218:
	add x11, x22, #0
	add x24, x24, x22
	movz x22, #0, lsl #0
219:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #64]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 219b
	b 216f
215:
216:
	b 23f
22:
23:
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_blake2b_finalize_scratch:
	str x30, [sp, #-16]!
	str x19, [x3, #512]
	str x20, [x3, #520]
	str x21, [x3, #528]
	str x22, [x3, #536]
	str x23, [x3, #544]
	str x24, [x3, #552]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x24, x1, #0
	sub x23, x24, #1
	movz x9, #127, lsl #0
	and x23, x23, x9
	add x23, x23, #1
	cbz x24, 20f
	b 21f
20:
	movz x23, #0, lsl #0
21:
	movz x9, #0, lsl #0
	movz x11, #128, lsl #0
	sub x11, x11, x23
	cbz x11, 22f
24:
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 24b
	b 23f
22:
23:
	add x0, x19, #0
	add x1, x19, #64
	movz x2, #1, lsl #0
	add x3, x24, #0
	movz x4, #1, lsl #0
	add x5, x20, #0
	bl {vg_blake2b_compress}
	ldr x9, [x19, #0]
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	str x9, [x21, #56]
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	ret
	.p2align 6
