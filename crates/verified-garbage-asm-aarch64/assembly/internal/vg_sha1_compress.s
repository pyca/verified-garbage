// The functions of `src/internal/vg_sha1_compress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
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
