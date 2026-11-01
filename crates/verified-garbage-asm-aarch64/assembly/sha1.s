// The functions of `src/sha1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_compress:
	cbz x2, 20f
22:
	ldr w4, [x0, #0]
	ldr w5, [x0, #4]
	ldr w6, [x0, #8]
	ldr w7, [x0, #12]
	ldr w8, [x0, #16]
	ldr w12, [x1, #0]
	rev w12, w12
	str w12, [x3, #0]
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x1, #4]
	rev w12, w12
	str w12, [x3, #4]
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x1, #8]
	rev w12, w12
	str w12, [x3, #8]
	eor w13, w4, w5
	and w13, w13, w8
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x1, #12]
	rev w12, w12
	str w12, [x3, #12]
	eor w13, w8, w4
	and w13, w13, w7
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x1, #16]
	rev w12, w12
	str w12, [x3, #16]
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x1, #20]
	rev w12, w12
	str w12, [x3, #20]
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x1, #24]
	rev w12, w12
	str w12, [x3, #24]
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x1, #28]
	rev w12, w12
	str w12, [x3, #28]
	eor w13, w4, w5
	and w13, w13, w8
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x1, #32]
	rev w12, w12
	str w12, [x3, #32]
	eor w13, w8, w4
	and w13, w13, w7
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x1, #36]
	rev w12, w12
	str w12, [x3, #36]
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x1, #40]
	rev w12, w12
	str w12, [x3, #40]
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x1, #44]
	rev w12, w12
	str w12, [x3, #44]
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x1, #48]
	rev w12, w12
	str w12, [x3, #48]
	eor w13, w4, w5
	and w13, w13, w8
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x1, #52]
	rev w12, w12
	str w12, [x3, #52]
	eor w13, w8, w4
	and w13, w13, w7
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x1, #56]
	rev w12, w12
	str w12, [x3, #56]
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x1, #60]
	rev w12, w12
	str w12, [x3, #60]
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #52]
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #0]
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #56]
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #4]
	eor w13, w4, w5
	and w13, w13, w8
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #60]
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #8]
	eor w13, w8, w4
	and w13, w13, w7
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #0]
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #12]
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #31129, lsl #0
	movk w13, #23170, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #4]
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #16]
	eor w13, w5, w6
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #8]
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #20]
	eor w13, w4, w5
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #12]
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #24]
	eor w13, w8, w4
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #16]
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #28]
	eor w13, w7, w8
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #20]
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #32]
	eor w13, w6, w7
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #24]
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #36]
	eor w13, w5, w6
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #28]
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #40]
	eor w13, w4, w5
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #32]
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #44]
	eor w13, w8, w4
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #36]
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #48]
	eor w13, w7, w8
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #40]
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #52]
	eor w13, w6, w7
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #44]
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #56]
	eor w13, w5, w6
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #48]
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #60]
	eor w13, w4, w5
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #52]
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #0]
	eor w13, w8, w4
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #56]
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #4]
	eor w13, w7, w8
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #60]
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #8]
	eor w13, w6, w7
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #0]
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #12]
	eor w13, w5, w6
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #4]
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #16]
	eor w13, w4, w5
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #8]
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #20]
	eor w13, w8, w4
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #12]
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #24]
	eor w13, w7, w8
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #16]
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #28]
	eor w13, w6, w7
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #60321, lsl #0
	movk w13, #28377, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #20]
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #32]
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #24]
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #36]
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #28]
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #40]
	orr w13, w8, w4
	and w13, w13, w5
	and w14, w8, w4
	orr w13, w13, w14
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #32]
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #44]
	orr w13, w7, w8
	and w13, w13, w4
	and w14, w7, w8
	orr w13, w13, w14
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #36]
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #48]
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #40]
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #52]
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #44]
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #56]
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #48]
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #60]
	orr w13, w8, w4
	and w13, w13, w5
	and w14, w8, w4
	orr w13, w13, w14
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #52]
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #0]
	orr w13, w7, w8
	and w13, w13, w4
	and w14, w7, w8
	orr w13, w13, w14
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #56]
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #4]
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #60]
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #8]
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #0]
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #12]
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #4]
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #16]
	orr w13, w8, w4
	and w13, w13, w5
	and w14, w8, w4
	orr w13, w13, w14
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #8]
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #20]
	orr w13, w7, w8
	and w13, w13, w4
	and w14, w7, w8
	orr w13, w13, w14
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #12]
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #24]
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #16]
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #28]
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #20]
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #32]
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #24]
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #36]
	orr w13, w8, w4
	and w13, w13, w5
	and w14, w8, w4
	orr w13, w13, w14
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #28]
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #40]
	orr w13, w7, w8
	and w13, w13, w4
	and w14, w7, w8
	orr w13, w13, w14
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #32]
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #44]
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #48348, lsl #0
	movk w13, #36635, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #36]
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #48]
	eor w13, w5, w6
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #40]
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #52]
	eor w13, w4, w5
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #44]
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #56]
	eor w13, w8, w4
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #48]
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #60]
	eor w13, w7, w8
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #52]
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #0]
	eor w13, w6, w7
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #56]
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #4]
	eor w13, w5, w6
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #60]
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #8]
	eor w13, w4, w5
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #0]
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #12]
	eor w13, w8, w4
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #4]
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #16]
	eor w13, w7, w8
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #8]
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #20]
	eor w13, w6, w7
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #12]
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #24]
	eor w13, w5, w6
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #16]
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #28]
	eor w13, w4, w5
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #20]
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ldr w13, [x3, #32]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #32]
	eor w13, w8, w4
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #24]
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ldr w13, [x3, #36]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #36]
	eor w13, w7, w8
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #28]
	ldr w13, [x3, #8]
	eor w12, w12, w13
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ldr w13, [x3, #40]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #40]
	eor w13, w6, w7
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w12, [x3, #32]
	ldr w13, [x3, #12]
	eor w12, w12, w13
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ldr w13, [x3, #44]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #44]
	eor w13, w5, w6
	eor w13, w13, w7
	ror w14, w4, #27
	add w14, w14, w13
	add w14, w14, w8
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w8, w14, w12
	ror w5, w5, #2
	ldr w12, [x3, #36]
	ldr w13, [x3, #16]
	eor w12, w12, w13
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ldr w13, [x3, #48]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #48]
	eor w13, w4, w5
	eor w13, w13, w6
	ror w14, w8, #27
	add w14, w14, w13
	add w14, w14, w7
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w7, w14, w12
	ror w4, w4, #2
	ldr w12, [x3, #40]
	ldr w13, [x3, #20]
	eor w12, w12, w13
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ldr w13, [x3, #52]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #52]
	eor w13, w8, w4
	eor w13, w13, w5
	ror w14, w7, #27
	add w14, w14, w13
	add w14, w14, w6
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w6, w14, w12
	ror w8, w8, #2
	ldr w12, [x3, #44]
	ldr w13, [x3, #24]
	eor w12, w12, w13
	ldr w13, [x3, #0]
	eor w12, w12, w13
	ldr w13, [x3, #56]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #56]
	eor w13, w7, w8
	eor w13, w13, w4
	ror w14, w6, #27
	add w14, w14, w13
	add w14, w14, w5
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w5, w14, w12
	ror w7, w7, #2
	ldr w12, [x3, #48]
	ldr w13, [x3, #28]
	eor w12, w12, w13
	ldr w13, [x3, #4]
	eor w12, w12, w13
	ldr w13, [x3, #60]
	eor w12, w12, w13
	ror w12, w12, #31
	str w12, [x3, #60]
	eor w13, w6, w7
	eor w13, w13, w8
	ror w14, w5, #27
	add w14, w14, w13
	add w14, w14, w4
	movz w13, #49622, lsl #0
	movk w13, #51810, lsl #16
	add w14, w14, w13
	add w4, w14, w12
	ror w6, w6, #2
	ldr w9, [x0, #0]
	ldr w10, [x0, #4]
	ldr w11, [x0, #8]
	ldr w12, [x0, #12]
	ldr w13, [x0, #16]
	add w4, w4, w9
	add w5, w5, w10
	add w6, w6, w11
	add w7, w7, w12
	add w8, w8, w13
	str w4, [x0, #0]
	str w5, [x0, #4]
	str w6, [x0, #8]
	str w7, [x0, #12]
	str w8, [x0, #16]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	ret
	.p2align 6

vg_sha1_init:
	movz w9, #8961, lsl #0
	movk w9, #26437, lsl #16
	str w9, [x0, #0]
	movz w9, #43913, lsl #0
	movk w9, #61389, lsl #16
	str w9, [x0, #4]
	movz w9, #56574, lsl #0
	movk w9, #39098, lsl #16
	str w9, [x0, #8]
	movz w9, #21622, lsl #0
	movk w9, #4146, lsl #16
	str w9, [x0, #12]
	movz w9, #57840, lsl #0
	movk w9, #50130, lsl #16
	str w9, [x0, #16]
	ret
	.p2align 6

vg_sha1_compress_sha2:
	.arch_extension sha2
	cbz x2, 20f
	movz w4, #31129, lsl #0
	movk w4, #23170, lsl #16
	dup v18.4s, w4
	movz w4, #60321, lsl #0
	movk w4, #28377, lsl #16
	dup v19.4s, w4
	movz w4, #48348, lsl #0
	movk w4, #36635, lsl #16
	dup v20.4s, w4
	movz w4, #49622, lsl #0
	movk w4, #51810, lsl #16
	dup v21.4s, w4
	ldr q0, [x0, #0]
	ldr w4, [x0, #16]
	dup v1.4s, w4
	dup s1, v1.s[0]
22:
	mov v16.16b, v0.16b
	mov v17.16b, v1.16b
	ldr q4, [x1, #0]
	rev32 v4.16b, v4.16b
	add v3.4s, v18.4s, v4.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	ldr q5, [x1, #16]
	rev32 v5.16b, v5.16b
	add v3.4s, v18.4s, v5.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	ldr q6, [x1, #32]
	rev32 v6.16b, v6.16b
	add v3.4s, v18.4s, v6.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	ldr q7, [x1, #48]
	rev32 v7.16b, v7.16b
	add v3.4s, v18.4s, v7.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v4.4s, v5.4s, v6.4s
	sha1su1 v4.4s, v7.4s
	add v3.4s, v18.4s, v4.4s
	sha1h s2, s0
	sha1c q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v5.4s, v6.4s, v7.4s
	sha1su1 v5.4s, v4.4s
	add v3.4s, v19.4s, v5.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v6.4s, v7.4s, v4.4s
	sha1su1 v6.4s, v5.4s
	add v3.4s, v19.4s, v6.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v7.4s, v4.4s, v5.4s
	sha1su1 v7.4s, v6.4s
	add v3.4s, v19.4s, v7.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v4.4s, v5.4s, v6.4s
	sha1su1 v4.4s, v7.4s
	add v3.4s, v19.4s, v4.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v5.4s, v6.4s, v7.4s
	sha1su1 v5.4s, v4.4s
	add v3.4s, v19.4s, v5.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v6.4s, v7.4s, v4.4s
	sha1su1 v6.4s, v5.4s
	add v3.4s, v20.4s, v6.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v7.4s, v4.4s, v5.4s
	sha1su1 v7.4s, v6.4s
	add v3.4s, v20.4s, v7.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v4.4s, v5.4s, v6.4s
	sha1su1 v4.4s, v7.4s
	add v3.4s, v20.4s, v4.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v5.4s, v6.4s, v7.4s
	sha1su1 v5.4s, v4.4s
	add v3.4s, v20.4s, v5.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v6.4s, v7.4s, v4.4s
	sha1su1 v6.4s, v5.4s
	add v3.4s, v20.4s, v6.4s
	sha1h s2, s0
	sha1m q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v7.4s, v4.4s, v5.4s
	sha1su1 v7.4s, v6.4s
	add v3.4s, v21.4s, v7.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v4.4s, v5.4s, v6.4s
	sha1su1 v4.4s, v7.4s
	add v3.4s, v21.4s, v4.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v5.4s, v6.4s, v7.4s
	sha1su1 v5.4s, v4.4s
	add v3.4s, v21.4s, v5.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v6.4s, v7.4s, v4.4s
	sha1su1 v6.4s, v5.4s
	add v3.4s, v21.4s, v6.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	sha1su0 v7.4s, v4.4s, v5.4s
	sha1su1 v7.4s, v6.4s
	add v3.4s, v21.4s, v7.4s
	sha1h s2, s0
	sha1p q0, s1, v3.4s
	mov v1.16b, v2.16b
	add v0.4s, v0.4s, v16.4s
	add v1.4s, v1.4s, v17.4s
	str q0, [x0, #0]
	umov w4, v1.s[0]
	str w4, [x0, #16]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha1_update:
	sub sp, sp, #160
	add x4, sp, #0
	str x30, [sp, #-16]!
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x23, [x4, #144]
	str x24, [x4, #152]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x2, #0
	add x22, x3, #0
	movz x9, #63, lsl #0
	and x23, x1, x9
	cbz x22, 20f
22:
	movz x10, #0, lsl #0
	cbz x23, 23f
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 25f
	b 26f
25:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 27f
	b 28f
27:
	add x11, x22, #0
28:
26:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 29f
211:
	ldr x9, [x21, #0]
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 211b
	b 210f
29:
210:
	cbz x11, 212f
214:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #20]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 214b
	b 213f
212:
213:
	sub x9, x23, #64
	cbz x9, 215f
	b 216f
215:
	add x1, x19, #20
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
216:
	b 24f
23:
	lsr x9, x22, #6
	cbz x9, 217f
	add x1, x21, #0
	lsr x10, x22, #6
	lsl x9, x10, #6
	add x21, x21, x9
	sub x22, x22, x9
	b 218f
217:
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 219f
	b 220f
219:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 221f
	b 222f
221:
	add x11, x22, #0
222:
220:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 223f
225:
	ldr x9, [x21, #0]
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 225b
	b 224f
223:
224:
	cbz x11, 226f
228:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #20]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 228b
	b 227f
226:
227:
	sub x9, x23, #64
	cbz x9, 229f
	b 230f
229:
	add x1, x19, #20
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	b 232f
231:
232:
	cbnz x22, 22b
	b 21f
20:
21:
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #160
	ret
	.p2align 6

vg_sha1_finalize:
	sub sp, sp, #160
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #112]
	str x20, [x3, #120]
	str x21, [x3, #128]
	str x22, [x3, #136]
	str x23, [x3, #144]
	str x24, [x3, #152]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #63, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #20]
	add x23, x23, #1
	add x24, x23, #7
	lsr x24, x24, #6
20:
	movz x11, #64, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #56, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 25b
	b 24f
23:
24:
	cbz x11, 26f
28:
	add x12, x19, x23
	strb w9, [x12, #20]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
210:
	add x1, x19, #20
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #160
	ret
	.p2align 6

vg_sha1_update_scratch:
	str x30, [sp, #-16]!
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x23, [x4, #144]
	str x24, [x4, #152]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x2, #0
	add x22, x3, #0
	movz x9, #63, lsl #0
	and x23, x1, x9
	cbz x22, 20f
22:
	movz x10, #0, lsl #0
	cbz x23, 23f
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 25f
	b 26f
25:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 27f
	b 28f
27:
	add x11, x22, #0
28:
26:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 29f
211:
	ldr x9, [x21, #0]
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 211b
	b 210f
29:
210:
	cbz x11, 212f
214:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #20]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 214b
	b 213f
212:
213:
	sub x9, x23, #64
	cbz x9, 215f
	b 216f
215:
	add x1, x19, #20
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
216:
	b 24f
23:
	lsr x9, x22, #6
	cbz x9, 217f
	add x1, x21, #0
	lsr x10, x22, #6
	lsl x9, x10, #6
	add x21, x21, x9
	sub x22, x22, x9
	b 218f
217:
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 219f
	b 220f
219:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 221f
	b 222f
221:
	add x11, x22, #0
222:
220:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 223f
225:
	ldr x9, [x21, #0]
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 225b
	b 224f
223:
224:
	cbz x11, 226f
228:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #20]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 228b
	b 227f
226:
227:
	sub x9, x23, #64
	cbz x9, 229f
	b 230f
229:
	add x1, x19, #20
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	b 232f
231:
232:
	cbnz x22, 22b
	b 21f
20:
21:
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_sha1_finalize_scratch:
	str x30, [sp, #-16]!
	str x19, [x3, #112]
	str x20, [x3, #120]
	str x21, [x3, #128]
	str x22, [x3, #136]
	str x23, [x3, #144]
	str x24, [x3, #152]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #63, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #20]
	add x23, x23, #1
	add x24, x23, #7
	lsr x24, x24, #6
20:
	movz x11, #64, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #56, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 25b
	b 24f
23:
24:
	cbz x11, 26f
28:
	add x12, x19, x23
	strb w9, [x12, #20]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
210:
	add x1, x19, #20
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_sha1_digest:
	sub sp, sp, #272
	add x10, sp, #208
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz w9, #8961, lsl #0
	movk w9, #26437, lsl #16
	str w9, [x0, #0]
	movz w9, #43913, lsl #0
	movk w9, #61389, lsl #16
	str w9, [x0, #4]
	movz w9, #56574, lsl #0
	movk w9, #39098, lsl #16
	str w9, [x0, #8]
	movz w9, #21622, lsl #0
	movk w9, #4146, lsl #16
	str w9, [x0, #12]
	movz w9, #57840, lsl #0
	movk w9, #50130, lsl #16
	str w9, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha1_compress}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #20
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	movz x9, #63, lsl #0
	and x28, x25, x9
	lsr x13, x28, #4
	cbz x13, 22f
24:
	ldp x9, x10, [x27, #0]
	stp x9, x10, [x12, #0]
	add x27, x27, #16
	add x12, x12, #16
	sub x13, x13, #1
	cbnz x13, 24b
	b 23f
22:
23:
	movz x9, #15, lsl #0
	and x11, x28, x9
	cbz x11, 25f
	lsr x9, x25, #4
	cbz x9, 27f
	add x13, x27, x11
	sub x13, x13, #16
	movz x9, #128, lsl #0
	ldr q0, [x13, #0]
	movi v1.2d, #0
	mov v1.d[0], x9
	movz x6, #4368, lsl #0
	movk x6, #4882, lsl #16
	movk x6, #5396, lsl #32
	movk x6, #5910, lsl #48
	movz x7, #6424, lsl #0
	movk x7, #6938, lsl #16
	movk x7, #7452, lsl #32
	movk x7, #7966, lsl #48
	mov v2.d[0], x6
	mov v2.d[1], x7
	dup v3.16b, w11
	sub v2.16b, v2.16b, v3.16b
	tbl v4.16b, {v0.16b, v1.16b}, v2.16b
	str q4, [x12, #0]
	b 28f
27:
29:
	ldrb w9, [x27, #0]
	strb w9, [x12, #0]
	add x27, x27, #1
	add x12, x12, #1
	sub x11, x11, #1
	cbnz x11, 29b
	movz x9, #128, lsl #0
	strb w9, [x12, #0]
28:
	b 26f
25:
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x12, #0]
26:
	add x9, x28, #8
	lsr x9, x9, #6
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #20
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha1_compress}
	movz x9, #0, lsl #0
	add x12, sp, #20
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x12, sp, #68
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #20
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha1_compress}
	add x19, sp, #0
	add x21, x26, #0
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	add x16, sp, #208
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #272
	ret
	.p2align 6

vg_sha1_update_sha2:
	.arch_extension sha2
	sub sp, sp, #160
	add x4, sp, #0
	str x30, [sp, #-16]!
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x23, [x4, #144]
	str x24, [x4, #152]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x2, #0
	add x22, x3, #0
	movz x9, #63, lsl #0
	and x23, x1, x9
	cbz x22, 20f
22:
	movz x10, #0, lsl #0
	cbz x23, 23f
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 25f
	b 26f
25:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 27f
	b 28f
27:
	add x11, x22, #0
28:
26:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 29f
211:
	ldr x9, [x21, #0]
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 211b
	b 210f
29:
210:
	cbz x11, 212f
214:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #20]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 214b
	b 213f
212:
213:
	sub x9, x23, #64
	cbz x9, 215f
	b 216f
215:
	add x1, x19, #20
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
216:
	b 24f
23:
	lsr x9, x22, #6
	cbz x9, 217f
	add x1, x21, #0
	lsr x10, x22, #6
	lsl x9, x10, #6
	add x21, x21, x9
	sub x22, x22, x9
	b 218f
217:
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 219f
	b 220f
219:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 221f
	b 222f
221:
	add x11, x22, #0
222:
220:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 223f
225:
	ldr x9, [x21, #0]
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 225b
	b 224f
223:
224:
	cbz x11, 226f
228:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #20]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 228b
	b 227f
226:
227:
	sub x9, x23, #64
	cbz x9, 229f
	b 230f
229:
	add x1, x19, #20
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	b 232f
231:
232:
	cbnz x22, 22b
	b 21f
20:
21:
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #160
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha1_finalize_sha2:
	.arch_extension sha2
	sub sp, sp, #160
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #112]
	str x20, [x3, #120]
	str x21, [x3, #128]
	str x22, [x3, #136]
	str x23, [x3, #144]
	str x24, [x3, #152]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #63, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #20]
	add x23, x23, #1
	add x24, x23, #7
	lsr x24, x24, #6
20:
	movz x11, #64, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #56, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 25b
	b 24f
23:
24:
	cbz x11, 26f
28:
	add x12, x19, x23
	strb w9, [x12, #20]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
210:
	add x1, x19, #20
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #160
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha1_update_scratch_sha2:
	.arch_extension sha2
	str x30, [sp, #-16]!
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x23, [x4, #144]
	str x24, [x4, #152]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x2, #0
	add x22, x3, #0
	movz x9, #63, lsl #0
	and x23, x1, x9
	cbz x22, 20f
22:
	movz x10, #0, lsl #0
	cbz x23, 23f
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 25f
	b 26f
25:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 27f
	b 28f
27:
	add x11, x22, #0
28:
26:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 29f
211:
	ldr x9, [x21, #0]
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 211b
	b 210f
29:
210:
	cbz x11, 212f
214:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #20]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 214b
	b 213f
212:
213:
	sub x9, x23, #64
	cbz x9, 215f
	b 216f
215:
	add x1, x19, #20
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
216:
	b 24f
23:
	lsr x9, x22, #6
	cbz x9, 217f
	add x1, x21, #0
	lsr x10, x22, #6
	lsl x9, x10, #6
	add x21, x21, x9
	sub x22, x22, x9
	b 218f
217:
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 219f
	b 220f
219:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 221f
	b 222f
221:
	add x11, x22, #0
222:
220:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 223f
225:
	ldr x9, [x21, #0]
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 225b
	b 224f
223:
224:
	cbz x11, 226f
228:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #20]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 228b
	b 227f
226:
227:
	sub x9, x23, #64
	cbz x9, 229f
	b 230f
229:
	add x1, x19, #20
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	b 232f
231:
232:
	cbnz x22, 22b
	b 21f
20:
21:
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha1_finalize_scratch_sha2:
	.arch_extension sha2
	str x30, [sp, #-16]!
	str x19, [x3, #112]
	str x20, [x3, #120]
	str x21, [x3, #128]
	str x22, [x3, #136]
	str x23, [x3, #144]
	str x24, [x3, #152]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #63, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #20]
	add x23, x23, #1
	add x24, x23, #7
	lsr x24, x24, #6
20:
	movz x11, #64, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #56, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	add x12, x12, #20
	str x9, [x12, #0]
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 25b
	b 24f
23:
24:
	cbz x11, 26f
28:
	add x12, x19, x23
	strb w9, [x12, #20]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
210:
	add x1, x19, #20
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha1_digest_sha2:
	.arch_extension sha2
	sub sp, sp, #272
	add x10, sp, #208
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz w9, #8961, lsl #0
	movk w9, #26437, lsl #16
	str w9, [x0, #0]
	movz w9, #43913, lsl #0
	movk w9, #61389, lsl #16
	str w9, [x0, #4]
	movz w9, #56574, lsl #0
	movk w9, #39098, lsl #16
	str w9, [x0, #8]
	movz w9, #21622, lsl #0
	movk w9, #4146, lsl #16
	str w9, [x0, #12]
	movz w9, #57840, lsl #0
	movk w9, #50130, lsl #16
	str w9, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha1_compress_sha2}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #20
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	movz x9, #63, lsl #0
	and x28, x25, x9
	lsr x13, x28, #4
	cbz x13, 22f
24:
	ldp x9, x10, [x27, #0]
	stp x9, x10, [x12, #0]
	add x27, x27, #16
	add x12, x12, #16
	sub x13, x13, #1
	cbnz x13, 24b
	b 23f
22:
23:
	movz x9, #15, lsl #0
	and x11, x28, x9
	cbz x11, 25f
	lsr x9, x25, #4
	cbz x9, 27f
	add x13, x27, x11
	sub x13, x13, #16
	movz x9, #128, lsl #0
	ldr q0, [x13, #0]
	movi v1.2d, #0
	mov v1.d[0], x9
	movz x6, #4368, lsl #0
	movk x6, #4882, lsl #16
	movk x6, #5396, lsl #32
	movk x6, #5910, lsl #48
	movz x7, #6424, lsl #0
	movk x7, #6938, lsl #16
	movk x7, #7452, lsl #32
	movk x7, #7966, lsl #48
	mov v2.d[0], x6
	mov v2.d[1], x7
	dup v3.16b, w11
	sub v2.16b, v2.16b, v3.16b
	tbl v4.16b, {v0.16b, v1.16b}, v2.16b
	str q4, [x12, #0]
	b 28f
27:
29:
	ldrb w9, [x27, #0]
	strb w9, [x12, #0]
	add x27, x27, #1
	add x12, x12, #1
	sub x11, x11, #1
	cbnz x11, 29b
	movz x9, #128, lsl #0
	strb w9, [x12, #0]
28:
	b 26f
25:
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x12, #0]
26:
	add x9, x28, #8
	lsr x9, x9, #6
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #20
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha1_compress_sha2}
	movz x9, #0, lsl #0
	add x12, sp, #20
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x12, sp, #68
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #20
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha1_compress_sha2}
	add x19, sp, #0
	add x21, x26, #0
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	add x16, sp, #208
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #272
	ret
	.arch_extension nosha2
	.p2align 6
