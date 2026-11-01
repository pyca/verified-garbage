// The functions of `src/internal/vg_sha512_compress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress:
	cbz x2, 20f
22:
	ldr x4, [x0, #0]
	ldr x5, [x0, #8]
	ldr x6, [x0, #16]
	ldr x7, [x0, #24]
	ldr x8, [x0, #32]
	ldr x9, [x0, #40]
	ldr x10, [x0, #48]
	ldr x11, [x0, #56]
	ldr x12, [x1, #0]
	rev x12, x12
	str x12, [x3, #0]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #44578, lsl #0
	movk x13, #55080, lsl #16
	movk x13, #12184, lsl #32
	movk x13, #17034, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x12, [x1, #8]
	rev x12, x12
	str x12, [x3, #8]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #26061, lsl #0
	movk x13, #9199, lsl #16
	movk x13, #17553, lsl #32
	movk x13, #28983, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x12, [x1, #16]
	rev x12, x12
	str x12, [x3, #16]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #15151, lsl #0
	movk x13, #60493, lsl #16
	movk x13, #64463, lsl #32
	movk x13, #46528, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x12, [x1, #24]
	rev x12, x12
	str x12, [x3, #24]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #56252, lsl #0
	movk x13, #33161, lsl #16
	movk x13, #56229, lsl #32
	movk x13, #59829, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x12, [x1, #32]
	rev x12, x12
	str x12, [x3, #32]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #46392, lsl #0
	movk x13, #62280, lsl #16
	movk x13, #49755, lsl #32
	movk x13, #14678, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x12, [x1, #40]
	rev x12, x12
	str x12, [x3, #40]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #53273, lsl #0
	movk x13, #46597, lsl #16
	movk x13, #4593, lsl #32
	movk x13, #23025, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x12, [x1, #48]
	rev x12, x12
	str x12, [x3, #48]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #20379, lsl #0
	movk x13, #44825, lsl #16
	movk x13, #33444, lsl #32
	movk x13, #37439, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x12, [x1, #56]
	rev x12, x12
	str x12, [x3, #56]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #33048, lsl #0
	movk x13, #55917, lsl #16
	movk x13, #24277, lsl #32
	movk x13, #43804, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x12, [x1, #64]
	rev x12, x12
	str x12, [x3, #64]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #578, lsl #0
	movk x13, #41731, lsl #16
	movk x13, #43672, lsl #32
	movk x13, #55303, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x12, [x1, #72]
	rev x12, x12
	str x12, [x3, #72]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #28606, lsl #0
	movk x13, #17776, lsl #16
	movk x13, #23297, lsl #32
	movk x13, #4739, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x12, [x1, #80]
	rev x12, x12
	str x12, [x3, #80]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #45708, lsl #0
	movk x13, #20196, lsl #16
	movk x13, #34238, lsl #32
	movk x13, #9265, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x12, [x1, #88]
	rev x12, x12
	str x12, [x3, #88]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #46306, lsl #0
	movk x13, #54783, lsl #16
	movk x13, #32195, lsl #32
	movk x13, #21772, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x12, [x1, #96]
	rev x12, x12
	str x12, [x3, #96]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #35183, lsl #0
	movk x13, #62075, lsl #16
	movk x13, #23924, lsl #32
	movk x13, #29374, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x12, [x1, #104]
	rev x12, x12
	str x12, [x3, #104]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #38577, lsl #0
	movk x13, #15126, lsl #16
	movk x13, #45566, lsl #32
	movk x13, #32990, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x12, [x1, #112]
	rev x12, x12
	str x12, [x3, #112]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #4661, lsl #0
	movk x13, #9671, lsl #16
	movk x13, #1703, lsl #32
	movk x13, #39900, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x12, [x1, #120]
	rev x12, x12
	str x12, [x3, #120]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #9876, lsl #0
	movk x13, #53097, lsl #16
	movk x13, #61812, lsl #32
	movk x13, #49563, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x13, [x3, #112]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #72]
	add x12, x12, x14
	ldr x13, [x3, #8]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #0]
	add x12, x12, x14
	str x12, [x3, #0]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #19154, lsl #0
	movk x13, #40689, lsl #16
	movk x13, #27073, lsl #32
	movk x13, #58523, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x13, [x3, #120]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #80]
	add x12, x12, x14
	ldr x13, [x3, #16]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #8]
	add x12, x12, x14
	str x12, [x3, #8]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #9699, lsl #0
	movk x13, #14415, lsl #16
	movk x13, #18310, lsl #32
	movk x13, #61374, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x13, [x3, #0]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #88]
	add x12, x12, x14
	ldr x13, [x3, #24]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #16]
	add x12, x12, x14
	str x12, [x3, #16]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #54709, lsl #0
	movk x13, #35724, lsl #16
	movk x13, #40390, lsl #32
	movk x13, #4033, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x13, [x3, #8]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #96]
	add x12, x12, x14
	ldr x13, [x3, #32]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #24]
	add x12, x12, x14
	str x12, [x3, #24]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #40037, lsl #0
	movk x13, #30636, lsl #16
	movk x13, #41420, lsl #32
	movk x13, #9228, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x13, [x3, #16]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #104]
	add x12, x12, x14
	ldr x13, [x3, #40]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #32]
	add x12, x12, x14
	str x12, [x3, #32]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #629, lsl #0
	movk x13, #22827, lsl #16
	movk x13, #11375, lsl #32
	movk x13, #11753, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x13, [x3, #24]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #112]
	add x12, x12, x14
	ldr x13, [x3, #48]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #40]
	add x12, x12, x14
	str x12, [x3, #40]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #58499, lsl #0
	movk x13, #28326, lsl #16
	movk x13, #33962, lsl #32
	movk x13, #19060, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x13, [x3, #32]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #120]
	add x12, x12, x14
	ldr x13, [x3, #56]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #48]
	add x12, x12, x14
	str x12, [x3, #48]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #64468, lsl #0
	movk x13, #48449, lsl #16
	movk x13, #43484, lsl #32
	movk x13, #23728, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x13, [x3, #40]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #0]
	add x12, x12, x14
	ldr x13, [x3, #64]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #56]
	add x12, x12, x14
	str x12, [x3, #56]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #21429, lsl #0
	movk x13, #33553, lsl #16
	movk x13, #35034, lsl #32
	movk x13, #30457, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x13, [x3, #48]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #8]
	add x12, x12, x14
	ldr x13, [x3, #72]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #64]
	add x12, x12, x14
	str x12, [x3, #64]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #57259, lsl #0
	movk x13, #61030, lsl #16
	movk x13, #20818, lsl #32
	movk x13, #38974, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x13, [x3, #56]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #16]
	add x12, x12, x14
	ldr x13, [x3, #80]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #72]
	add x12, x12, x14
	str x12, [x3, #72]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #12816, lsl #0
	movk x13, #11700, lsl #16
	movk x13, #50797, lsl #32
	movk x13, #43057, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x13, [x3, #64]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #24]
	add x12, x12, x14
	ldr x13, [x3, #88]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #80]
	add x12, x12, x14
	str x12, [x3, #80]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #8511, lsl #0
	movk x13, #39163, lsl #16
	movk x13, #10184, lsl #32
	movk x13, #45059, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x13, [x3, #72]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #32]
	add x12, x12, x14
	ldr x13, [x3, #96]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #88]
	add x12, x12, x14
	str x12, [x3, #88]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #3812, lsl #0
	movk x13, #48879, lsl #16
	movk x13, #32711, lsl #32
	movk x13, #48985, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x13, [x3, #80]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #40]
	add x12, x12, x14
	ldr x13, [x3, #104]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #96]
	add x12, x12, x14
	str x12, [x3, #96]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #36802, lsl #0
	movk x13, #15784, lsl #16
	movk x13, #3059, lsl #32
	movk x13, #50912, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x13, [x3, #88]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #48]
	add x12, x12, x14
	ldr x13, [x3, #112]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #104]
	add x12, x12, x14
	str x12, [x3, #104]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #42789, lsl #0
	movk x13, #37642, lsl #16
	movk x13, #37191, lsl #32
	movk x13, #54695, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x13, [x3, #96]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #56]
	add x12, x12, x14
	ldr x13, [x3, #120]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #112]
	add x12, x12, x14
	str x12, [x3, #112]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #33391, lsl #0
	movk x13, #57347, lsl #16
	movk x13, #25425, lsl #32
	movk x13, #1738, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x13, [x3, #104]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #64]
	add x12, x12, x14
	ldr x13, [x3, #0]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #120]
	add x12, x12, x14
	str x12, [x3, #120]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #28272, lsl #0
	movk x13, #2574, lsl #16
	movk x13, #10599, lsl #32
	movk x13, #5161, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x13, [x3, #112]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #72]
	add x12, x12, x14
	ldr x13, [x3, #8]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #0]
	add x12, x12, x14
	str x12, [x3, #0]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #12284, lsl #0
	movk x13, #18130, lsl #16
	movk x13, #2693, lsl #32
	movk x13, #10167, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x13, [x3, #120]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #80]
	add x12, x12, x14
	ldr x13, [x3, #16]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #8]
	add x12, x12, x14
	str x12, [x3, #8]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #51494, lsl #0
	movk x13, #23590, lsl #16
	movk x13, #8504, lsl #32
	movk x13, #11803, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x13, [x3, #0]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #88]
	add x12, x12, x14
	ldr x13, [x3, #24]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #16]
	add x12, x12, x14
	str x12, [x3, #16]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #10989, lsl #0
	movk x13, #23236, lsl #16
	movk x13, #28156, lsl #32
	movk x13, #19756, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x13, [x3, #8]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #96]
	add x12, x12, x14
	ldr x13, [x3, #32]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #24]
	add x12, x12, x14
	str x12, [x3, #24]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #46047, lsl #0
	movk x13, #40341, lsl #16
	movk x13, #3347, lsl #32
	movk x13, #21304, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x13, [x3, #16]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #104]
	add x12, x12, x14
	ldr x13, [x3, #40]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #32]
	add x12, x12, x14
	str x12, [x3, #32]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #25566, lsl #0
	movk x13, #35759, lsl #16
	movk x13, #29524, lsl #32
	movk x13, #25866, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x13, [x3, #24]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #112]
	add x12, x12, x14
	ldr x13, [x3, #48]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #40]
	add x12, x12, x14
	str x12, [x3, #40]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #45736, lsl #0
	movk x13, #15479, lsl #16
	movk x13, #2747, lsl #32
	movk x13, #30314, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x13, [x3, #32]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #120]
	add x12, x12, x14
	ldr x13, [x3, #56]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #48]
	add x12, x12, x14
	str x12, [x3, #48]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #44774, lsl #0
	movk x13, #18413, lsl #16
	movk x13, #51502, lsl #32
	movk x13, #33218, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x13, [x3, #40]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #0]
	add x12, x12, x14
	ldr x13, [x3, #64]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #56]
	add x12, x12, x14
	str x12, [x3, #56]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #13627, lsl #0
	movk x13, #5250, lsl #16
	movk x13, #11397, lsl #32
	movk x13, #37490, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x13, [x3, #48]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #8]
	add x12, x12, x14
	ldr x13, [x3, #72]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #64]
	add x12, x12, x14
	str x12, [x3, #64]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #868, lsl #0
	movk x13, #19697, lsl #16
	movk x13, #59553, lsl #32
	movk x13, #41663, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x13, [x3, #56]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #16]
	add x12, x12, x14
	ldr x13, [x3, #80]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #72]
	add x12, x12, x14
	str x12, [x3, #72]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #12289, lsl #0
	movk x13, #48194, lsl #16
	movk x13, #26187, lsl #32
	movk x13, #43034, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x13, [x3, #64]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #24]
	add x12, x12, x14
	ldr x13, [x3, #88]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #80]
	add x12, x12, x14
	str x12, [x3, #80]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #38801, lsl #0
	movk x13, #53496, lsl #16
	movk x13, #35696, lsl #32
	movk x13, #49739, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x13, [x3, #72]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #32]
	add x12, x12, x14
	ldr x13, [x3, #96]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #88]
	add x12, x12, x14
	str x12, [x3, #88]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #48688, lsl #0
	movk x13, #1620, lsl #16
	movk x13, #20899, lsl #32
	movk x13, #51052, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x13, [x3, #80]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #40]
	add x12, x12, x14
	ldr x13, [x3, #104]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #96]
	add x12, x12, x14
	str x12, [x3, #96]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #21016, lsl #0
	movk x13, #55023, lsl #16
	movk x13, #59417, lsl #32
	movk x13, #53650, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x13, [x3, #88]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #48]
	add x12, x12, x14
	ldr x13, [x3, #112]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #104]
	add x12, x12, x14
	str x12, [x3, #104]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #43280, lsl #0
	movk x13, #21861, lsl #16
	movk x13, #1572, lsl #32
	movk x13, #54937, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x13, [x3, #96]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #56]
	add x12, x12, x14
	ldr x13, [x3, #120]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #112]
	add x12, x12, x14
	str x12, [x3, #112]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #8234, lsl #0
	movk x13, #22385, lsl #16
	movk x13, #13701, lsl #32
	movk x13, #62478, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x13, [x3, #104]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #64]
	add x12, x12, x14
	ldr x13, [x3, #0]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #120]
	add x12, x12, x14
	str x12, [x3, #120]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #53688, lsl #0
	movk x13, #12987, lsl #16
	movk x13, #41072, lsl #32
	movk x13, #4202, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x13, [x3, #112]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #72]
	add x12, x12, x14
	ldr x13, [x3, #8]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #0]
	add x12, x12, x14
	str x12, [x3, #0]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #53448, lsl #0
	movk x13, #47314, lsl #16
	movk x13, #49430, lsl #32
	movk x13, #6564, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x13, [x3, #120]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #80]
	add x12, x12, x14
	ldr x13, [x3, #16]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #8]
	add x12, x12, x14
	str x12, [x3, #8]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #43859, lsl #0
	movk x13, #20801, lsl #16
	movk x13, #27656, lsl #32
	movk x13, #7735, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x13, [x3, #0]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #88]
	add x12, x12, x14
	ldr x13, [x3, #24]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #16]
	add x12, x12, x14
	str x12, [x3, #16]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #60313, lsl #0
	movk x13, #57230, lsl #16
	movk x13, #30540, lsl #32
	movk x13, #10056, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x13, [x3, #8]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #96]
	add x12, x12, x14
	ldr x13, [x3, #32]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #24]
	add x12, x12, x14
	str x12, [x3, #24]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #18600, lsl #0
	movk x13, #57755, lsl #16
	movk x13, #48309, lsl #32
	movk x13, #13488, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x13, [x3, #16]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #104]
	add x12, x12, x14
	ldr x13, [x3, #40]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #32]
	add x12, x12, x14
	str x12, [x3, #32]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #23139, lsl #0
	movk x13, #50633, lsl #16
	movk x13, #3251, lsl #32
	movk x13, #14620, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x13, [x3, #24]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #112]
	add x12, x12, x14
	ldr x13, [x3, #48]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #40]
	add x12, x12, x14
	str x12, [x3, #40]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #35531, lsl #0
	movk x13, #58177, lsl #16
	movk x13, #43594, lsl #32
	movk x13, #20184, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x13, [x3, #32]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #120]
	add x12, x12, x14
	ldr x13, [x3, #56]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #48]
	add x12, x12, x14
	str x12, [x3, #48]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #58227, lsl #0
	movk x13, #30563, lsl #16
	movk x13, #51791, lsl #32
	movk x13, #23452, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x13, [x3, #40]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #0]
	add x12, x12, x14
	ldr x13, [x3, #64]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #56]
	add x12, x12, x14
	str x12, [x3, #56]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #47267, lsl #0
	movk x13, #54962, lsl #16
	movk x13, #28659, lsl #32
	movk x13, #26670, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x13, [x3, #48]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #8]
	add x12, x12, x14
	ldr x13, [x3, #72]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #64]
	add x12, x12, x14
	str x12, [x3, #64]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #45820, lsl #0
	movk x13, #24047, lsl #16
	movk x13, #33518, lsl #32
	movk x13, #29839, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x13, [x3, #56]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #16]
	add x12, x12, x14
	ldr x13, [x3, #80]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #72]
	add x12, x12, x14
	str x12, [x3, #72]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #12128, lsl #0
	movk x13, #17175, lsl #16
	movk x13, #25455, lsl #32
	movk x13, #30885, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x13, [x3, #64]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #24]
	add x12, x12, x14
	ldr x13, [x3, #88]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #80]
	add x12, x12, x14
	str x12, [x3, #80]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #43890, lsl #0
	movk x13, #41456, lsl #16
	movk x13, #30740, lsl #32
	movk x13, #33992, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x13, [x3, #72]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #32]
	add x12, x12, x14
	ldr x13, [x3, #96]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #88]
	add x12, x12, x14
	str x12, [x3, #88]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #14828, lsl #0
	movk x13, #6756, lsl #16
	movk x13, #520, lsl #32
	movk x13, #36039, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x13, [x3, #80]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #40]
	add x12, x12, x14
	ldr x13, [x3, #104]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #96]
	add x12, x12, x14
	str x12, [x3, #96]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #7720, lsl #0
	movk x13, #9059, lsl #16
	movk x13, #65530, lsl #32
	movk x13, #37054, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x13, [x3, #88]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #48]
	add x12, x12, x14
	ldr x13, [x3, #112]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #104]
	add x12, x12, x14
	str x12, [x3, #104]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #48617, lsl #0
	movk x13, #56962, lsl #16
	movk x13, #27883, lsl #32
	movk x13, #42064, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x13, [x3, #96]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #56]
	add x12, x12, x14
	ldr x13, [x3, #120]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #112]
	add x12, x12, x14
	str x12, [x3, #112]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #30997, lsl #0
	movk x13, #45766, lsl #16
	movk x13, #41975, lsl #32
	movk x13, #48889, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x13, [x3, #104]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #64]
	add x12, x12, x14
	ldr x13, [x3, #0]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #120]
	add x12, x12, x14
	str x12, [x3, #120]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #21291, lsl #0
	movk x13, #58226, lsl #16
	movk x13, #30962, lsl #32
	movk x13, #50801, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x13, [x3, #112]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #72]
	add x12, x12, x14
	ldr x13, [x3, #8]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #0]
	add x12, x12, x14
	str x12, [x3, #0]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #24988, lsl #0
	movk x13, #59942, lsl #16
	movk x13, #16078, lsl #32
	movk x13, #51751, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x13, [x3, #120]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #80]
	add x12, x12, x14
	ldr x13, [x3, #16]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #8]
	add x12, x12, x14
	str x12, [x3, #8]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #49671, lsl #0
	movk x13, #8640, lsl #16
	movk x13, #47303, lsl #32
	movk x13, #53638, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x13, [x3, #0]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #88]
	add x12, x12, x14
	ldr x13, [x3, #24]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #16]
	add x12, x12, x14
	str x12, [x3, #16]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #60190, lsl #0
	movk x13, #52704, lsl #16
	movk x13, #32214, lsl #32
	movk x13, #60122, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x13, [x3, #8]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #96]
	add x12, x12, x14
	ldr x13, [x3, #32]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #24]
	add x12, x12, x14
	str x12, [x3, #24]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #53624, lsl #0
	movk x13, #61038, lsl #16
	movk x13, #20351, lsl #32
	movk x13, #62845, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x13, [x3, #16]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #104]
	add x12, x12, x14
	ldr x13, [x3, #40]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #32]
	add x12, x12, x14
	str x12, [x3, #32]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #28602, lsl #0
	movk x13, #29207, lsl #16
	movk x13, #26538, lsl #32
	movk x13, #1776, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x13, [x3, #24]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #112]
	add x12, x12, x14
	ldr x13, [x3, #48]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #40]
	add x12, x12, x14
	str x12, [x3, #40]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #39078, lsl #0
	movk x13, #41672, lsl #16
	movk x13, #32197, lsl #32
	movk x13, #2659, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x13, [x3, #32]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #120]
	add x12, x12, x14
	ldr x13, [x3, #56]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #48]
	add x12, x12, x14
	str x12, [x3, #48]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #3502, lsl #0
	movk x13, #48889, lsl #16
	movk x13, #38916, lsl #32
	movk x13, #4415, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x13, [x3, #40]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #0]
	add x12, x12, x14
	ldr x13, [x3, #64]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #56]
	add x12, x12, x14
	str x12, [x3, #56]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #18203, lsl #0
	movk x13, #4892, lsl #16
	movk x13, #2869, lsl #32
	movk x13, #7025, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x13, [x3, #48]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #8]
	add x12, x12, x14
	ldr x13, [x3, #72]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #64]
	add x12, x12, x14
	str x12, [x3, #64]
	ror x13, x8, #14
	ror x14, x8, #18
	eor x13, x13, x14
	ror x14, x8, #41
	eor x13, x13, x14
	add x11, x11, x13
	eor x13, x9, x10
	and x13, x13, x8
	eor x13, x13, x10
	add x11, x11, x13
	movz x13, #32132, lsl #0
	movk x13, #8964, lsl #16
	movk x13, #30709, lsl #32
	movk x13, #10459, lsl #48
	add x11, x11, x13
	add x11, x11, x12
	add x7, x7, x11
	ror x13, x4, #28
	ror x14, x4, #34
	eor x13, x13, x14
	ror x14, x4, #39
	eor x13, x13, x14
	add x11, x11, x13
	orr x13, x4, x5
	and x13, x13, x6
	and x14, x4, x5
	orr x13, x13, x14
	add x11, x11, x13
	ldr x13, [x3, #56]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #16]
	add x12, x12, x14
	ldr x13, [x3, #80]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #72]
	add x12, x12, x14
	str x12, [x3, #72]
	ror x13, x7, #14
	ror x14, x7, #18
	eor x13, x13, x14
	ror x14, x7, #41
	eor x13, x13, x14
	add x10, x10, x13
	eor x13, x8, x9
	and x13, x13, x7
	eor x13, x13, x9
	add x10, x10, x13
	movz x13, #9363, lsl #0
	movk x13, #16583, lsl #16
	movk x13, #43899, lsl #32
	movk x13, #13002, lsl #48
	add x10, x10, x13
	add x10, x10, x12
	add x6, x6, x10
	ror x13, x11, #28
	ror x14, x11, #34
	eor x13, x13, x14
	ror x14, x11, #39
	eor x13, x13, x14
	add x10, x10, x13
	orr x13, x11, x4
	and x13, x13, x5
	and x14, x11, x4
	orr x13, x13, x14
	add x10, x10, x13
	ldr x13, [x3, #64]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #24]
	add x12, x12, x14
	ldr x13, [x3, #88]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #80]
	add x12, x12, x14
	str x12, [x3, #80]
	ror x13, x6, #14
	ror x14, x6, #18
	eor x13, x13, x14
	ror x14, x6, #41
	eor x13, x13, x14
	add x9, x9, x13
	eor x13, x7, x8
	and x13, x13, x6
	eor x13, x13, x8
	add x9, x9, x13
	movz x13, #48828, lsl #0
	movk x13, #5577, lsl #16
	movk x13, #48650, lsl #32
	movk x13, #15518, lsl #48
	add x9, x9, x13
	add x9, x9, x12
	add x5, x5, x9
	ror x13, x10, #28
	ror x14, x10, #34
	eor x13, x13, x14
	ror x14, x10, #39
	eor x13, x13, x14
	add x9, x9, x13
	orr x13, x10, x11
	and x13, x13, x4
	and x14, x10, x11
	orr x13, x13, x14
	add x9, x9, x13
	ldr x13, [x3, #72]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #32]
	add x12, x12, x14
	ldr x13, [x3, #96]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #88]
	add x12, x12, x14
	str x12, [x3, #88]
	ror x13, x5, #14
	ror x14, x5, #18
	eor x13, x13, x14
	ror x14, x5, #41
	eor x13, x13, x14
	add x8, x8, x13
	eor x13, x6, x7
	and x13, x13, x5
	eor x13, x13, x7
	add x8, x8, x13
	movz x13, #3404, lsl #0
	movk x13, #39952, lsl #16
	movk x13, #26564, lsl #32
	movk x13, #17181, lsl #48
	add x8, x8, x13
	add x8, x8, x12
	add x4, x4, x8
	ror x13, x9, #28
	ror x14, x9, #34
	eor x13, x13, x14
	ror x14, x9, #39
	eor x13, x13, x14
	add x8, x8, x13
	orr x13, x9, x10
	and x13, x13, x11
	and x14, x9, x10
	orr x13, x13, x14
	add x8, x8, x13
	ldr x13, [x3, #80]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #40]
	add x12, x12, x14
	ldr x13, [x3, #104]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #96]
	add x12, x12, x14
	str x12, [x3, #96]
	ror x13, x4, #14
	ror x14, x4, #18
	eor x13, x13, x14
	ror x14, x4, #41
	eor x13, x13, x14
	add x7, x7, x13
	eor x13, x5, x6
	and x13, x13, x4
	eor x13, x13, x6
	add x7, x7, x13
	movz x13, #17078, lsl #0
	movk x13, #52030, lsl #16
	movk x13, #54462, lsl #32
	movk x13, #19653, lsl #48
	add x7, x7, x13
	add x7, x7, x12
	add x11, x11, x7
	ror x13, x8, #28
	ror x14, x8, #34
	eor x13, x13, x14
	ror x14, x8, #39
	eor x13, x13, x14
	add x7, x7, x13
	orr x13, x8, x9
	and x13, x13, x10
	and x14, x8, x9
	orr x13, x13, x14
	add x7, x7, x13
	ldr x13, [x3, #88]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #48]
	add x12, x12, x14
	ldr x13, [x3, #112]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #104]
	add x12, x12, x14
	str x12, [x3, #104]
	ror x13, x11, #14
	ror x14, x11, #18
	eor x13, x13, x14
	ror x14, x11, #41
	eor x13, x13, x14
	add x6, x6, x13
	eor x13, x4, x5
	and x13, x13, x11
	eor x13, x13, x5
	add x6, x6, x13
	movz x13, #32298, lsl #0
	movk x13, #64613, lsl #16
	movk x13, #10652, lsl #32
	movk x13, #22911, lsl #48
	add x6, x6, x13
	add x6, x6, x12
	add x10, x10, x6
	ror x13, x7, #28
	ror x14, x7, #34
	eor x13, x13, x14
	ror x14, x7, #39
	eor x13, x13, x14
	add x6, x6, x13
	orr x13, x7, x8
	and x13, x13, x9
	and x14, x7, x8
	orr x13, x13, x14
	add x6, x6, x13
	ldr x13, [x3, #96]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #56]
	add x12, x12, x14
	ldr x13, [x3, #120]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #112]
	add x12, x12, x14
	str x12, [x3, #112]
	ror x13, x10, #14
	ror x14, x10, #18
	eor x13, x13, x14
	ror x14, x10, #41
	eor x13, x13, x14
	add x5, x5, x13
	eor x13, x11, x4
	and x13, x13, x10
	eor x13, x13, x4
	add x5, x5, x13
	movz x13, #64236, lsl #0
	movk x13, #15062, lsl #16
	movk x13, #28587, lsl #32
	movk x13, #24523, lsl #48
	add x5, x5, x13
	add x5, x5, x12
	add x9, x9, x5
	ror x13, x6, #28
	ror x14, x6, #34
	eor x13, x13, x14
	ror x14, x6, #39
	eor x13, x13, x14
	add x5, x5, x13
	orr x13, x6, x7
	and x13, x13, x8
	and x14, x6, x7
	orr x13, x13, x14
	add x5, x5, x13
	ldr x13, [x3, #104]
	ror x12, x13, #19
	ror x14, x13, #61
	eor x12, x12, x14
	lsr x14, x13, #6
	eor x12, x12, x14
	ldr x14, [x3, #64]
	add x12, x12, x14
	ldr x13, [x3, #0]
	ror x14, x13, #1
	ror x15, x13, #8
	eor x14, x14, x15
	lsr x15, x13, #7
	eor x14, x14, x15
	add x12, x12, x14
	ldr x14, [x3, #120]
	add x12, x12, x14
	str x12, [x3, #120]
	ror x13, x9, #14
	ror x14, x9, #18
	eor x13, x13, x14
	ror x14, x9, #41
	eor x13, x13, x14
	add x4, x4, x13
	eor x13, x10, x11
	and x13, x13, x9
	eor x13, x13, x11
	add x4, x4, x13
	movz x13, #22551, lsl #0
	movk x13, #19015, lsl #16
	movk x13, #6540, lsl #32
	movk x13, #27716, lsl #48
	add x4, x4, x13
	add x4, x4, x12
	add x8, x8, x4
	ror x13, x5, #28
	ror x14, x5, #34
	eor x13, x13, x14
	ror x14, x5, #39
	eor x13, x13, x14
	add x4, x4, x13
	orr x13, x5, x6
	and x13, x13, x7
	and x14, x5, x6
	orr x13, x13, x14
	add x4, x4, x13
	ldr x12, [x0, #0]
	ldr x13, [x0, #8]
	ldr x14, [x0, #16]
	ldr x15, [x0, #24]
	add x4, x4, x12
	add x5, x5, x13
	add x6, x6, x14
	add x7, x7, x15
	ldr x12, [x0, #32]
	ldr x13, [x0, #40]
	ldr x14, [x0, #48]
	ldr x15, [x0, #56]
	add x8, x8, x12
	add x9, x9, x13
	add x10, x10, x14
	add x11, x11, x15
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	str x7, [x0, #24]
	str x8, [x0, #32]
	str x9, [x0, #40]
	str x10, [x0, #48]
	str x11, [x0, #56]
	add x1, x1, #128
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	ret
	.p2align 6
