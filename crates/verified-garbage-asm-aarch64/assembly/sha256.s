// The functions of `src/sha256.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha224_init:
	adrp x9, {VG_SHA224_H0}
	add x9, x9, {VG_SHA224_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	ret
	.p2align 6

vg_sha256_compress:
	cbz x2, 20f
22:
	ldr w4, [x0, #0]
	ldr w5, [x0, #4]
	ldr w6, [x0, #8]
	ldr w7, [x0, #12]
	ldr w8, [x0, #16]
	ldr w9, [x0, #20]
	ldr w10, [x0, #24]
	ldr w11, [x0, #28]
	ldr w12, [x1, #0]
	rev w12, w12
	str w12, [x3, #0]
	ror w13, w8, #6
	ror w14, w8, #11
	eor w13, w13, w14
	ror w14, w8, #25
	eor w13, w13, w14
	add w11, w11, w13
	eor w13, w9, w10
	and w13, w13, w8
	eor w13, w13, w10
	add w11, w11, w13
	movz w13, #12184, lsl #0
	movk w13, #17034, lsl #16
	add w11, w11, w13
	add w11, w11, w12
	add w7, w7, w11
	ror w13, w4, #2
	ror w14, w4, #13
	eor w13, w13, w14
	ror w14, w4, #22
	eor w13, w13, w14
	add w11, w11, w13
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	add w11, w11, w13
	ldr w12, [x1, #4]
	rev w12, w12
	str w12, [x3, #4]
	ror w13, w7, #6
	ror w14, w7, #11
	eor w13, w13, w14
	ror w14, w7, #25
	eor w13, w13, w14
	add w10, w10, w13
	eor w13, w8, w9
	and w13, w13, w7
	eor w13, w13, w9
	add w10, w10, w13
	movz w13, #17553, lsl #0
	movk w13, #28983, lsl #16
	add w10, w10, w13
	add w10, w10, w12
	add w6, w6, w10
	ror w13, w11, #2
	ror w14, w11, #13
	eor w13, w13, w14
	ror w14, w11, #22
	eor w13, w13, w14
	add w10, w10, w13
	orr w13, w11, w4
	and w13, w13, w5
	and w14, w11, w4
	orr w13, w13, w14
	add w10, w10, w13
	ldr w12, [x1, #8]
	rev w12, w12
	str w12, [x3, #8]
	ror w13, w6, #6
	ror w14, w6, #11
	eor w13, w13, w14
	ror w14, w6, #25
	eor w13, w13, w14
	add w9, w9, w13
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	add w9, w9, w13
	movz w13, #64463, lsl #0
	movk w13, #46528, lsl #16
	add w9, w9, w13
	add w9, w9, w12
	add w5, w5, w9
	ror w13, w10, #2
	ror w14, w10, #13
	eor w13, w13, w14
	ror w14, w10, #22
	eor w13, w13, w14
	add w9, w9, w13
	orr w13, w10, w11
	and w13, w13, w4
	and w14, w10, w11
	orr w13, w13, w14
	add w9, w9, w13
	ldr w12, [x1, #12]
	rev w12, w12
	str w12, [x3, #12]
	ror w13, w5, #6
	ror w14, w5, #11
	eor w13, w13, w14
	ror w14, w5, #25
	eor w13, w13, w14
	add w8, w8, w13
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	add w8, w8, w13
	movz w13, #56229, lsl #0
	movk w13, #59829, lsl #16
	add w8, w8, w13
	add w8, w8, w12
	add w4, w4, w8
	ror w13, w9, #2
	ror w14, w9, #13
	eor w13, w13, w14
	ror w14, w9, #22
	eor w13, w13, w14
	add w8, w8, w13
	orr w13, w9, w10
	and w13, w13, w11
	and w14, w9, w10
	orr w13, w13, w14
	add w8, w8, w13
	ldr w12, [x1, #16]
	rev w12, w12
	str w12, [x3, #16]
	ror w13, w4, #6
	ror w14, w4, #11
	eor w13, w13, w14
	ror w14, w4, #25
	eor w13, w13, w14
	add w7, w7, w13
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	add w7, w7, w13
	movz w13, #49755, lsl #0
	movk w13, #14678, lsl #16
	add w7, w7, w13
	add w7, w7, w12
	add w11, w11, w7
	ror w13, w8, #2
	ror w14, w8, #13
	eor w13, w13, w14
	ror w14, w8, #22
	eor w13, w13, w14
	add w7, w7, w13
	orr w13, w8, w9
	and w13, w13, w10
	and w14, w8, w9
	orr w13, w13, w14
	add w7, w7, w13
	ldr w12, [x1, #20]
	rev w12, w12
	str w12, [x3, #20]
	ror w13, w11, #6
	ror w14, w11, #11
	eor w13, w13, w14
	ror w14, w11, #25
	eor w13, w13, w14
	add w6, w6, w13
	eor w13, w4, w5
	and w13, w13, w11
	eor w13, w13, w5
	add w6, w6, w13
	movz w13, #4593, lsl #0
	movk w13, #23025, lsl #16
	add w6, w6, w13
	add w6, w6, w12
	add w10, w10, w6
	ror w13, w7, #2
	ror w14, w7, #13
	eor w13, w13, w14
	ror w14, w7, #22
	eor w13, w13, w14
	add w6, w6, w13
	orr w13, w7, w8
	and w13, w13, w9
	and w14, w7, w8
	orr w13, w13, w14
	add w6, w6, w13
	ldr w12, [x1, #24]
	rev w12, w12
	str w12, [x3, #24]
	ror w13, w10, #6
	ror w14, w10, #11
	eor w13, w13, w14
	ror w14, w10, #25
	eor w13, w13, w14
	add w5, w5, w13
	eor w13, w11, w4
	and w13, w13, w10
	eor w13, w13, w4
	add w5, w5, w13
	movz w13, #33444, lsl #0
	movk w13, #37439, lsl #16
	add w5, w5, w13
	add w5, w5, w12
	add w9, w9, w5
	ror w13, w6, #2
	ror w14, w6, #13
	eor w13, w13, w14
	ror w14, w6, #22
	eor w13, w13, w14
	add w5, w5, w13
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	add w5, w5, w13
	ldr w12, [x1, #28]
	rev w12, w12
	str w12, [x3, #28]
	ror w13, w9, #6
	ror w14, w9, #11
	eor w13, w13, w14
	ror w14, w9, #25
	eor w13, w13, w14
	add w4, w4, w13
	eor w13, w10, w11
	and w13, w13, w9
	eor w13, w13, w11
	add w4, w4, w13
	movz w13, #24277, lsl #0
	movk w13, #43804, lsl #16
	add w4, w4, w13
	add w4, w4, w12
	add w8, w8, w4
	ror w13, w5, #2
	ror w14, w5, #13
	eor w13, w13, w14
	ror w14, w5, #22
	eor w13, w13, w14
	add w4, w4, w13
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	add w4, w4, w13
	ldr w12, [x1, #32]
	rev w12, w12
	str w12, [x3, #32]
	ror w13, w8, #6
	ror w14, w8, #11
	eor w13, w13, w14
	ror w14, w8, #25
	eor w13, w13, w14
	add w11, w11, w13
	eor w13, w9, w10
	and w13, w13, w8
	eor w13, w13, w10
	add w11, w11, w13
	movz w13, #43672, lsl #0
	movk w13, #55303, lsl #16
	add w11, w11, w13
	add w11, w11, w12
	add w7, w7, w11
	ror w13, w4, #2
	ror w14, w4, #13
	eor w13, w13, w14
	ror w14, w4, #22
	eor w13, w13, w14
	add w11, w11, w13
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	add w11, w11, w13
	ldr w12, [x1, #36]
	rev w12, w12
	str w12, [x3, #36]
	ror w13, w7, #6
	ror w14, w7, #11
	eor w13, w13, w14
	ror w14, w7, #25
	eor w13, w13, w14
	add w10, w10, w13
	eor w13, w8, w9
	and w13, w13, w7
	eor w13, w13, w9
	add w10, w10, w13
	movz w13, #23297, lsl #0
	movk w13, #4739, lsl #16
	add w10, w10, w13
	add w10, w10, w12
	add w6, w6, w10
	ror w13, w11, #2
	ror w14, w11, #13
	eor w13, w13, w14
	ror w14, w11, #22
	eor w13, w13, w14
	add w10, w10, w13
	orr w13, w11, w4
	and w13, w13, w5
	and w14, w11, w4
	orr w13, w13, w14
	add w10, w10, w13
	ldr w12, [x1, #40]
	rev w12, w12
	str w12, [x3, #40]
	ror w13, w6, #6
	ror w14, w6, #11
	eor w13, w13, w14
	ror w14, w6, #25
	eor w13, w13, w14
	add w9, w9, w13
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	add w9, w9, w13
	movz w13, #34238, lsl #0
	movk w13, #9265, lsl #16
	add w9, w9, w13
	add w9, w9, w12
	add w5, w5, w9
	ror w13, w10, #2
	ror w14, w10, #13
	eor w13, w13, w14
	ror w14, w10, #22
	eor w13, w13, w14
	add w9, w9, w13
	orr w13, w10, w11
	and w13, w13, w4
	and w14, w10, w11
	orr w13, w13, w14
	add w9, w9, w13
	ldr w12, [x1, #44]
	rev w12, w12
	str w12, [x3, #44]
	ror w13, w5, #6
	ror w14, w5, #11
	eor w13, w13, w14
	ror w14, w5, #25
	eor w13, w13, w14
	add w8, w8, w13
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	add w8, w8, w13
	movz w13, #32195, lsl #0
	movk w13, #21772, lsl #16
	add w8, w8, w13
	add w8, w8, w12
	add w4, w4, w8
	ror w13, w9, #2
	ror w14, w9, #13
	eor w13, w13, w14
	ror w14, w9, #22
	eor w13, w13, w14
	add w8, w8, w13
	orr w13, w9, w10
	and w13, w13, w11
	and w14, w9, w10
	orr w13, w13, w14
	add w8, w8, w13
	ldr w12, [x1, #48]
	rev w12, w12
	str w12, [x3, #48]
	ror w13, w4, #6
	ror w14, w4, #11
	eor w13, w13, w14
	ror w14, w4, #25
	eor w13, w13, w14
	add w7, w7, w13
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	add w7, w7, w13
	movz w13, #23924, lsl #0
	movk w13, #29374, lsl #16
	add w7, w7, w13
	add w7, w7, w12
	add w11, w11, w7
	ror w13, w8, #2
	ror w14, w8, #13
	eor w13, w13, w14
	ror w14, w8, #22
	eor w13, w13, w14
	add w7, w7, w13
	orr w13, w8, w9
	and w13, w13, w10
	and w14, w8, w9
	orr w13, w13, w14
	add w7, w7, w13
	ldr w12, [x1, #52]
	rev w12, w12
	str w12, [x3, #52]
	ror w13, w11, #6
	ror w14, w11, #11
	eor w13, w13, w14
	ror w14, w11, #25
	eor w13, w13, w14
	add w6, w6, w13
	eor w13, w4, w5
	and w13, w13, w11
	eor w13, w13, w5
	add w6, w6, w13
	movz w13, #45566, lsl #0
	movk w13, #32990, lsl #16
	add w6, w6, w13
	add w6, w6, w12
	add w10, w10, w6
	ror w13, w7, #2
	ror w14, w7, #13
	eor w13, w13, w14
	ror w14, w7, #22
	eor w13, w13, w14
	add w6, w6, w13
	orr w13, w7, w8
	and w13, w13, w9
	and w14, w7, w8
	orr w13, w13, w14
	add w6, w6, w13
	ldr w12, [x1, #56]
	rev w12, w12
	str w12, [x3, #56]
	ror w13, w10, #6
	ror w14, w10, #11
	eor w13, w13, w14
	ror w14, w10, #25
	eor w13, w13, w14
	add w5, w5, w13
	eor w13, w11, w4
	and w13, w13, w10
	eor w13, w13, w4
	add w5, w5, w13
	movz w13, #1703, lsl #0
	movk w13, #39900, lsl #16
	add w5, w5, w13
	add w5, w5, w12
	add w9, w9, w5
	ror w13, w6, #2
	ror w14, w6, #13
	eor w13, w13, w14
	ror w14, w6, #22
	eor w13, w13, w14
	add w5, w5, w13
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	add w5, w5, w13
	ldr w12, [x1, #60]
	rev w12, w12
	str w12, [x3, #60]
	ror w13, w9, #6
	ror w14, w9, #11
	eor w13, w13, w14
	ror w14, w9, #25
	eor w13, w13, w14
	add w4, w4, w13
	eor w13, w10, w11
	and w13, w13, w9
	eor w13, w13, w11
	add w4, w4, w13
	movz w13, #61812, lsl #0
	movk w13, #49563, lsl #16
	add w4, w4, w13
	add w4, w4, w12
	add w8, w8, w4
	ror w13, w5, #2
	ror w14, w5, #13
	eor w13, w13, w14
	ror w14, w5, #22
	eor w13, w13, w14
	add w4, w4, w13
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	add w4, w4, w13
	ldr w13, [x3, #56]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #36]
	add w12, w12, w14
	ldr w13, [x3, #4]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #0]
	add w12, w12, w14
	str w12, [x3, #0]
	ror w13, w8, #6
	ror w14, w8, #11
	eor w13, w13, w14
	ror w14, w8, #25
	eor w13, w13, w14
	add w11, w11, w13
	eor w13, w9, w10
	and w13, w13, w8
	eor w13, w13, w10
	add w11, w11, w13
	movz w13, #27073, lsl #0
	movk w13, #58523, lsl #16
	add w11, w11, w13
	add w11, w11, w12
	add w7, w7, w11
	ror w13, w4, #2
	ror w14, w4, #13
	eor w13, w13, w14
	ror w14, w4, #22
	eor w13, w13, w14
	add w11, w11, w13
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	add w11, w11, w13
	ldr w13, [x3, #60]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #40]
	add w12, w12, w14
	ldr w13, [x3, #8]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #4]
	add w12, w12, w14
	str w12, [x3, #4]
	ror w13, w7, #6
	ror w14, w7, #11
	eor w13, w13, w14
	ror w14, w7, #25
	eor w13, w13, w14
	add w10, w10, w13
	eor w13, w8, w9
	and w13, w13, w7
	eor w13, w13, w9
	add w10, w10, w13
	movz w13, #18310, lsl #0
	movk w13, #61374, lsl #16
	add w10, w10, w13
	add w10, w10, w12
	add w6, w6, w10
	ror w13, w11, #2
	ror w14, w11, #13
	eor w13, w13, w14
	ror w14, w11, #22
	eor w13, w13, w14
	add w10, w10, w13
	orr w13, w11, w4
	and w13, w13, w5
	and w14, w11, w4
	orr w13, w13, w14
	add w10, w10, w13
	ldr w13, [x3, #0]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #44]
	add w12, w12, w14
	ldr w13, [x3, #12]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #8]
	add w12, w12, w14
	str w12, [x3, #8]
	ror w13, w6, #6
	ror w14, w6, #11
	eor w13, w13, w14
	ror w14, w6, #25
	eor w13, w13, w14
	add w9, w9, w13
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	add w9, w9, w13
	movz w13, #40390, lsl #0
	movk w13, #4033, lsl #16
	add w9, w9, w13
	add w9, w9, w12
	add w5, w5, w9
	ror w13, w10, #2
	ror w14, w10, #13
	eor w13, w13, w14
	ror w14, w10, #22
	eor w13, w13, w14
	add w9, w9, w13
	orr w13, w10, w11
	and w13, w13, w4
	and w14, w10, w11
	orr w13, w13, w14
	add w9, w9, w13
	ldr w13, [x3, #4]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #48]
	add w12, w12, w14
	ldr w13, [x3, #16]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #12]
	add w12, w12, w14
	str w12, [x3, #12]
	ror w13, w5, #6
	ror w14, w5, #11
	eor w13, w13, w14
	ror w14, w5, #25
	eor w13, w13, w14
	add w8, w8, w13
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	add w8, w8, w13
	movz w13, #41420, lsl #0
	movk w13, #9228, lsl #16
	add w8, w8, w13
	add w8, w8, w12
	add w4, w4, w8
	ror w13, w9, #2
	ror w14, w9, #13
	eor w13, w13, w14
	ror w14, w9, #22
	eor w13, w13, w14
	add w8, w8, w13
	orr w13, w9, w10
	and w13, w13, w11
	and w14, w9, w10
	orr w13, w13, w14
	add w8, w8, w13
	ldr w13, [x3, #8]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #52]
	add w12, w12, w14
	ldr w13, [x3, #20]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #16]
	add w12, w12, w14
	str w12, [x3, #16]
	ror w13, w4, #6
	ror w14, w4, #11
	eor w13, w13, w14
	ror w14, w4, #25
	eor w13, w13, w14
	add w7, w7, w13
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	add w7, w7, w13
	movz w13, #11375, lsl #0
	movk w13, #11753, lsl #16
	add w7, w7, w13
	add w7, w7, w12
	add w11, w11, w7
	ror w13, w8, #2
	ror w14, w8, #13
	eor w13, w13, w14
	ror w14, w8, #22
	eor w13, w13, w14
	add w7, w7, w13
	orr w13, w8, w9
	and w13, w13, w10
	and w14, w8, w9
	orr w13, w13, w14
	add w7, w7, w13
	ldr w13, [x3, #12]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #56]
	add w12, w12, w14
	ldr w13, [x3, #24]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #20]
	add w12, w12, w14
	str w12, [x3, #20]
	ror w13, w11, #6
	ror w14, w11, #11
	eor w13, w13, w14
	ror w14, w11, #25
	eor w13, w13, w14
	add w6, w6, w13
	eor w13, w4, w5
	and w13, w13, w11
	eor w13, w13, w5
	add w6, w6, w13
	movz w13, #33962, lsl #0
	movk w13, #19060, lsl #16
	add w6, w6, w13
	add w6, w6, w12
	add w10, w10, w6
	ror w13, w7, #2
	ror w14, w7, #13
	eor w13, w13, w14
	ror w14, w7, #22
	eor w13, w13, w14
	add w6, w6, w13
	orr w13, w7, w8
	and w13, w13, w9
	and w14, w7, w8
	orr w13, w13, w14
	add w6, w6, w13
	ldr w13, [x3, #16]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #60]
	add w12, w12, w14
	ldr w13, [x3, #28]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #24]
	add w12, w12, w14
	str w12, [x3, #24]
	ror w13, w10, #6
	ror w14, w10, #11
	eor w13, w13, w14
	ror w14, w10, #25
	eor w13, w13, w14
	add w5, w5, w13
	eor w13, w11, w4
	and w13, w13, w10
	eor w13, w13, w4
	add w5, w5, w13
	movz w13, #43484, lsl #0
	movk w13, #23728, lsl #16
	add w5, w5, w13
	add w5, w5, w12
	add w9, w9, w5
	ror w13, w6, #2
	ror w14, w6, #13
	eor w13, w13, w14
	ror w14, w6, #22
	eor w13, w13, w14
	add w5, w5, w13
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	add w5, w5, w13
	ldr w13, [x3, #20]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #0]
	add w12, w12, w14
	ldr w13, [x3, #32]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #28]
	add w12, w12, w14
	str w12, [x3, #28]
	ror w13, w9, #6
	ror w14, w9, #11
	eor w13, w13, w14
	ror w14, w9, #25
	eor w13, w13, w14
	add w4, w4, w13
	eor w13, w10, w11
	and w13, w13, w9
	eor w13, w13, w11
	add w4, w4, w13
	movz w13, #35034, lsl #0
	movk w13, #30457, lsl #16
	add w4, w4, w13
	add w4, w4, w12
	add w8, w8, w4
	ror w13, w5, #2
	ror w14, w5, #13
	eor w13, w13, w14
	ror w14, w5, #22
	eor w13, w13, w14
	add w4, w4, w13
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	add w4, w4, w13
	ldr w13, [x3, #24]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #4]
	add w12, w12, w14
	ldr w13, [x3, #36]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #32]
	add w12, w12, w14
	str w12, [x3, #32]
	ror w13, w8, #6
	ror w14, w8, #11
	eor w13, w13, w14
	ror w14, w8, #25
	eor w13, w13, w14
	add w11, w11, w13
	eor w13, w9, w10
	and w13, w13, w8
	eor w13, w13, w10
	add w11, w11, w13
	movz w13, #20818, lsl #0
	movk w13, #38974, lsl #16
	add w11, w11, w13
	add w11, w11, w12
	add w7, w7, w11
	ror w13, w4, #2
	ror w14, w4, #13
	eor w13, w13, w14
	ror w14, w4, #22
	eor w13, w13, w14
	add w11, w11, w13
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	add w11, w11, w13
	ldr w13, [x3, #28]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #8]
	add w12, w12, w14
	ldr w13, [x3, #40]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #36]
	add w12, w12, w14
	str w12, [x3, #36]
	ror w13, w7, #6
	ror w14, w7, #11
	eor w13, w13, w14
	ror w14, w7, #25
	eor w13, w13, w14
	add w10, w10, w13
	eor w13, w8, w9
	and w13, w13, w7
	eor w13, w13, w9
	add w10, w10, w13
	movz w13, #50797, lsl #0
	movk w13, #43057, lsl #16
	add w10, w10, w13
	add w10, w10, w12
	add w6, w6, w10
	ror w13, w11, #2
	ror w14, w11, #13
	eor w13, w13, w14
	ror w14, w11, #22
	eor w13, w13, w14
	add w10, w10, w13
	orr w13, w11, w4
	and w13, w13, w5
	and w14, w11, w4
	orr w13, w13, w14
	add w10, w10, w13
	ldr w13, [x3, #32]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #12]
	add w12, w12, w14
	ldr w13, [x3, #44]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #40]
	add w12, w12, w14
	str w12, [x3, #40]
	ror w13, w6, #6
	ror w14, w6, #11
	eor w13, w13, w14
	ror w14, w6, #25
	eor w13, w13, w14
	add w9, w9, w13
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	add w9, w9, w13
	movz w13, #10184, lsl #0
	movk w13, #45059, lsl #16
	add w9, w9, w13
	add w9, w9, w12
	add w5, w5, w9
	ror w13, w10, #2
	ror w14, w10, #13
	eor w13, w13, w14
	ror w14, w10, #22
	eor w13, w13, w14
	add w9, w9, w13
	orr w13, w10, w11
	and w13, w13, w4
	and w14, w10, w11
	orr w13, w13, w14
	add w9, w9, w13
	ldr w13, [x3, #36]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #16]
	add w12, w12, w14
	ldr w13, [x3, #48]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #44]
	add w12, w12, w14
	str w12, [x3, #44]
	ror w13, w5, #6
	ror w14, w5, #11
	eor w13, w13, w14
	ror w14, w5, #25
	eor w13, w13, w14
	add w8, w8, w13
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	add w8, w8, w13
	movz w13, #32711, lsl #0
	movk w13, #48985, lsl #16
	add w8, w8, w13
	add w8, w8, w12
	add w4, w4, w8
	ror w13, w9, #2
	ror w14, w9, #13
	eor w13, w13, w14
	ror w14, w9, #22
	eor w13, w13, w14
	add w8, w8, w13
	orr w13, w9, w10
	and w13, w13, w11
	and w14, w9, w10
	orr w13, w13, w14
	add w8, w8, w13
	ldr w13, [x3, #40]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #20]
	add w12, w12, w14
	ldr w13, [x3, #52]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #48]
	add w12, w12, w14
	str w12, [x3, #48]
	ror w13, w4, #6
	ror w14, w4, #11
	eor w13, w13, w14
	ror w14, w4, #25
	eor w13, w13, w14
	add w7, w7, w13
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	add w7, w7, w13
	movz w13, #3059, lsl #0
	movk w13, #50912, lsl #16
	add w7, w7, w13
	add w7, w7, w12
	add w11, w11, w7
	ror w13, w8, #2
	ror w14, w8, #13
	eor w13, w13, w14
	ror w14, w8, #22
	eor w13, w13, w14
	add w7, w7, w13
	orr w13, w8, w9
	and w13, w13, w10
	and w14, w8, w9
	orr w13, w13, w14
	add w7, w7, w13
	ldr w13, [x3, #44]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #24]
	add w12, w12, w14
	ldr w13, [x3, #56]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #52]
	add w12, w12, w14
	str w12, [x3, #52]
	ror w13, w11, #6
	ror w14, w11, #11
	eor w13, w13, w14
	ror w14, w11, #25
	eor w13, w13, w14
	add w6, w6, w13
	eor w13, w4, w5
	and w13, w13, w11
	eor w13, w13, w5
	add w6, w6, w13
	movz w13, #37191, lsl #0
	movk w13, #54695, lsl #16
	add w6, w6, w13
	add w6, w6, w12
	add w10, w10, w6
	ror w13, w7, #2
	ror w14, w7, #13
	eor w13, w13, w14
	ror w14, w7, #22
	eor w13, w13, w14
	add w6, w6, w13
	orr w13, w7, w8
	and w13, w13, w9
	and w14, w7, w8
	orr w13, w13, w14
	add w6, w6, w13
	ldr w13, [x3, #48]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #28]
	add w12, w12, w14
	ldr w13, [x3, #60]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #56]
	add w12, w12, w14
	str w12, [x3, #56]
	ror w13, w10, #6
	ror w14, w10, #11
	eor w13, w13, w14
	ror w14, w10, #25
	eor w13, w13, w14
	add w5, w5, w13
	eor w13, w11, w4
	and w13, w13, w10
	eor w13, w13, w4
	add w5, w5, w13
	movz w13, #25425, lsl #0
	movk w13, #1738, lsl #16
	add w5, w5, w13
	add w5, w5, w12
	add w9, w9, w5
	ror w13, w6, #2
	ror w14, w6, #13
	eor w13, w13, w14
	ror w14, w6, #22
	eor w13, w13, w14
	add w5, w5, w13
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	add w5, w5, w13
	ldr w13, [x3, #52]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #32]
	add w12, w12, w14
	ldr w13, [x3, #0]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #60]
	add w12, w12, w14
	str w12, [x3, #60]
	ror w13, w9, #6
	ror w14, w9, #11
	eor w13, w13, w14
	ror w14, w9, #25
	eor w13, w13, w14
	add w4, w4, w13
	eor w13, w10, w11
	and w13, w13, w9
	eor w13, w13, w11
	add w4, w4, w13
	movz w13, #10599, lsl #0
	movk w13, #5161, lsl #16
	add w4, w4, w13
	add w4, w4, w12
	add w8, w8, w4
	ror w13, w5, #2
	ror w14, w5, #13
	eor w13, w13, w14
	ror w14, w5, #22
	eor w13, w13, w14
	add w4, w4, w13
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	add w4, w4, w13
	ldr w13, [x3, #56]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #36]
	add w12, w12, w14
	ldr w13, [x3, #4]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #0]
	add w12, w12, w14
	str w12, [x3, #0]
	ror w13, w8, #6
	ror w14, w8, #11
	eor w13, w13, w14
	ror w14, w8, #25
	eor w13, w13, w14
	add w11, w11, w13
	eor w13, w9, w10
	and w13, w13, w8
	eor w13, w13, w10
	add w11, w11, w13
	movz w13, #2693, lsl #0
	movk w13, #10167, lsl #16
	add w11, w11, w13
	add w11, w11, w12
	add w7, w7, w11
	ror w13, w4, #2
	ror w14, w4, #13
	eor w13, w13, w14
	ror w14, w4, #22
	eor w13, w13, w14
	add w11, w11, w13
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	add w11, w11, w13
	ldr w13, [x3, #60]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #40]
	add w12, w12, w14
	ldr w13, [x3, #8]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #4]
	add w12, w12, w14
	str w12, [x3, #4]
	ror w13, w7, #6
	ror w14, w7, #11
	eor w13, w13, w14
	ror w14, w7, #25
	eor w13, w13, w14
	add w10, w10, w13
	eor w13, w8, w9
	and w13, w13, w7
	eor w13, w13, w9
	add w10, w10, w13
	movz w13, #8504, lsl #0
	movk w13, #11803, lsl #16
	add w10, w10, w13
	add w10, w10, w12
	add w6, w6, w10
	ror w13, w11, #2
	ror w14, w11, #13
	eor w13, w13, w14
	ror w14, w11, #22
	eor w13, w13, w14
	add w10, w10, w13
	orr w13, w11, w4
	and w13, w13, w5
	and w14, w11, w4
	orr w13, w13, w14
	add w10, w10, w13
	ldr w13, [x3, #0]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #44]
	add w12, w12, w14
	ldr w13, [x3, #12]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #8]
	add w12, w12, w14
	str w12, [x3, #8]
	ror w13, w6, #6
	ror w14, w6, #11
	eor w13, w13, w14
	ror w14, w6, #25
	eor w13, w13, w14
	add w9, w9, w13
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	add w9, w9, w13
	movz w13, #28156, lsl #0
	movk w13, #19756, lsl #16
	add w9, w9, w13
	add w9, w9, w12
	add w5, w5, w9
	ror w13, w10, #2
	ror w14, w10, #13
	eor w13, w13, w14
	ror w14, w10, #22
	eor w13, w13, w14
	add w9, w9, w13
	orr w13, w10, w11
	and w13, w13, w4
	and w14, w10, w11
	orr w13, w13, w14
	add w9, w9, w13
	ldr w13, [x3, #4]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #48]
	add w12, w12, w14
	ldr w13, [x3, #16]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #12]
	add w12, w12, w14
	str w12, [x3, #12]
	ror w13, w5, #6
	ror w14, w5, #11
	eor w13, w13, w14
	ror w14, w5, #25
	eor w13, w13, w14
	add w8, w8, w13
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	add w8, w8, w13
	movz w13, #3347, lsl #0
	movk w13, #21304, lsl #16
	add w8, w8, w13
	add w8, w8, w12
	add w4, w4, w8
	ror w13, w9, #2
	ror w14, w9, #13
	eor w13, w13, w14
	ror w14, w9, #22
	eor w13, w13, w14
	add w8, w8, w13
	orr w13, w9, w10
	and w13, w13, w11
	and w14, w9, w10
	orr w13, w13, w14
	add w8, w8, w13
	ldr w13, [x3, #8]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #52]
	add w12, w12, w14
	ldr w13, [x3, #20]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #16]
	add w12, w12, w14
	str w12, [x3, #16]
	ror w13, w4, #6
	ror w14, w4, #11
	eor w13, w13, w14
	ror w14, w4, #25
	eor w13, w13, w14
	add w7, w7, w13
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	add w7, w7, w13
	movz w13, #29524, lsl #0
	movk w13, #25866, lsl #16
	add w7, w7, w13
	add w7, w7, w12
	add w11, w11, w7
	ror w13, w8, #2
	ror w14, w8, #13
	eor w13, w13, w14
	ror w14, w8, #22
	eor w13, w13, w14
	add w7, w7, w13
	orr w13, w8, w9
	and w13, w13, w10
	and w14, w8, w9
	orr w13, w13, w14
	add w7, w7, w13
	ldr w13, [x3, #12]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #56]
	add w12, w12, w14
	ldr w13, [x3, #24]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #20]
	add w12, w12, w14
	str w12, [x3, #20]
	ror w13, w11, #6
	ror w14, w11, #11
	eor w13, w13, w14
	ror w14, w11, #25
	eor w13, w13, w14
	add w6, w6, w13
	eor w13, w4, w5
	and w13, w13, w11
	eor w13, w13, w5
	add w6, w6, w13
	movz w13, #2747, lsl #0
	movk w13, #30314, lsl #16
	add w6, w6, w13
	add w6, w6, w12
	add w10, w10, w6
	ror w13, w7, #2
	ror w14, w7, #13
	eor w13, w13, w14
	ror w14, w7, #22
	eor w13, w13, w14
	add w6, w6, w13
	orr w13, w7, w8
	and w13, w13, w9
	and w14, w7, w8
	orr w13, w13, w14
	add w6, w6, w13
	ldr w13, [x3, #16]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #60]
	add w12, w12, w14
	ldr w13, [x3, #28]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #24]
	add w12, w12, w14
	str w12, [x3, #24]
	ror w13, w10, #6
	ror w14, w10, #11
	eor w13, w13, w14
	ror w14, w10, #25
	eor w13, w13, w14
	add w5, w5, w13
	eor w13, w11, w4
	and w13, w13, w10
	eor w13, w13, w4
	add w5, w5, w13
	movz w13, #51502, lsl #0
	movk w13, #33218, lsl #16
	add w5, w5, w13
	add w5, w5, w12
	add w9, w9, w5
	ror w13, w6, #2
	ror w14, w6, #13
	eor w13, w13, w14
	ror w14, w6, #22
	eor w13, w13, w14
	add w5, w5, w13
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	add w5, w5, w13
	ldr w13, [x3, #20]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #0]
	add w12, w12, w14
	ldr w13, [x3, #32]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #28]
	add w12, w12, w14
	str w12, [x3, #28]
	ror w13, w9, #6
	ror w14, w9, #11
	eor w13, w13, w14
	ror w14, w9, #25
	eor w13, w13, w14
	add w4, w4, w13
	eor w13, w10, w11
	and w13, w13, w9
	eor w13, w13, w11
	add w4, w4, w13
	movz w13, #11397, lsl #0
	movk w13, #37490, lsl #16
	add w4, w4, w13
	add w4, w4, w12
	add w8, w8, w4
	ror w13, w5, #2
	ror w14, w5, #13
	eor w13, w13, w14
	ror w14, w5, #22
	eor w13, w13, w14
	add w4, w4, w13
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	add w4, w4, w13
	ldr w13, [x3, #24]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #4]
	add w12, w12, w14
	ldr w13, [x3, #36]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #32]
	add w12, w12, w14
	str w12, [x3, #32]
	ror w13, w8, #6
	ror w14, w8, #11
	eor w13, w13, w14
	ror w14, w8, #25
	eor w13, w13, w14
	add w11, w11, w13
	eor w13, w9, w10
	and w13, w13, w8
	eor w13, w13, w10
	add w11, w11, w13
	movz w13, #59553, lsl #0
	movk w13, #41663, lsl #16
	add w11, w11, w13
	add w11, w11, w12
	add w7, w7, w11
	ror w13, w4, #2
	ror w14, w4, #13
	eor w13, w13, w14
	ror w14, w4, #22
	eor w13, w13, w14
	add w11, w11, w13
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	add w11, w11, w13
	ldr w13, [x3, #28]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #8]
	add w12, w12, w14
	ldr w13, [x3, #40]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #36]
	add w12, w12, w14
	str w12, [x3, #36]
	ror w13, w7, #6
	ror w14, w7, #11
	eor w13, w13, w14
	ror w14, w7, #25
	eor w13, w13, w14
	add w10, w10, w13
	eor w13, w8, w9
	and w13, w13, w7
	eor w13, w13, w9
	add w10, w10, w13
	movz w13, #26187, lsl #0
	movk w13, #43034, lsl #16
	add w10, w10, w13
	add w10, w10, w12
	add w6, w6, w10
	ror w13, w11, #2
	ror w14, w11, #13
	eor w13, w13, w14
	ror w14, w11, #22
	eor w13, w13, w14
	add w10, w10, w13
	orr w13, w11, w4
	and w13, w13, w5
	and w14, w11, w4
	orr w13, w13, w14
	add w10, w10, w13
	ldr w13, [x3, #32]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #12]
	add w12, w12, w14
	ldr w13, [x3, #44]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #40]
	add w12, w12, w14
	str w12, [x3, #40]
	ror w13, w6, #6
	ror w14, w6, #11
	eor w13, w13, w14
	ror w14, w6, #25
	eor w13, w13, w14
	add w9, w9, w13
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	add w9, w9, w13
	movz w13, #35696, lsl #0
	movk w13, #49739, lsl #16
	add w9, w9, w13
	add w9, w9, w12
	add w5, w5, w9
	ror w13, w10, #2
	ror w14, w10, #13
	eor w13, w13, w14
	ror w14, w10, #22
	eor w13, w13, w14
	add w9, w9, w13
	orr w13, w10, w11
	and w13, w13, w4
	and w14, w10, w11
	orr w13, w13, w14
	add w9, w9, w13
	ldr w13, [x3, #36]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #16]
	add w12, w12, w14
	ldr w13, [x3, #48]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #44]
	add w12, w12, w14
	str w12, [x3, #44]
	ror w13, w5, #6
	ror w14, w5, #11
	eor w13, w13, w14
	ror w14, w5, #25
	eor w13, w13, w14
	add w8, w8, w13
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	add w8, w8, w13
	movz w13, #20899, lsl #0
	movk w13, #51052, lsl #16
	add w8, w8, w13
	add w8, w8, w12
	add w4, w4, w8
	ror w13, w9, #2
	ror w14, w9, #13
	eor w13, w13, w14
	ror w14, w9, #22
	eor w13, w13, w14
	add w8, w8, w13
	orr w13, w9, w10
	and w13, w13, w11
	and w14, w9, w10
	orr w13, w13, w14
	add w8, w8, w13
	ldr w13, [x3, #40]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #20]
	add w12, w12, w14
	ldr w13, [x3, #52]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #48]
	add w12, w12, w14
	str w12, [x3, #48]
	ror w13, w4, #6
	ror w14, w4, #11
	eor w13, w13, w14
	ror w14, w4, #25
	eor w13, w13, w14
	add w7, w7, w13
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	add w7, w7, w13
	movz w13, #59417, lsl #0
	movk w13, #53650, lsl #16
	add w7, w7, w13
	add w7, w7, w12
	add w11, w11, w7
	ror w13, w8, #2
	ror w14, w8, #13
	eor w13, w13, w14
	ror w14, w8, #22
	eor w13, w13, w14
	add w7, w7, w13
	orr w13, w8, w9
	and w13, w13, w10
	and w14, w8, w9
	orr w13, w13, w14
	add w7, w7, w13
	ldr w13, [x3, #44]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #24]
	add w12, w12, w14
	ldr w13, [x3, #56]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #52]
	add w12, w12, w14
	str w12, [x3, #52]
	ror w13, w11, #6
	ror w14, w11, #11
	eor w13, w13, w14
	ror w14, w11, #25
	eor w13, w13, w14
	add w6, w6, w13
	eor w13, w4, w5
	and w13, w13, w11
	eor w13, w13, w5
	add w6, w6, w13
	movz w13, #1572, lsl #0
	movk w13, #54937, lsl #16
	add w6, w6, w13
	add w6, w6, w12
	add w10, w10, w6
	ror w13, w7, #2
	ror w14, w7, #13
	eor w13, w13, w14
	ror w14, w7, #22
	eor w13, w13, w14
	add w6, w6, w13
	orr w13, w7, w8
	and w13, w13, w9
	and w14, w7, w8
	orr w13, w13, w14
	add w6, w6, w13
	ldr w13, [x3, #48]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #28]
	add w12, w12, w14
	ldr w13, [x3, #60]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #56]
	add w12, w12, w14
	str w12, [x3, #56]
	ror w13, w10, #6
	ror w14, w10, #11
	eor w13, w13, w14
	ror w14, w10, #25
	eor w13, w13, w14
	add w5, w5, w13
	eor w13, w11, w4
	and w13, w13, w10
	eor w13, w13, w4
	add w5, w5, w13
	movz w13, #13701, lsl #0
	movk w13, #62478, lsl #16
	add w5, w5, w13
	add w5, w5, w12
	add w9, w9, w5
	ror w13, w6, #2
	ror w14, w6, #13
	eor w13, w13, w14
	ror w14, w6, #22
	eor w13, w13, w14
	add w5, w5, w13
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	add w5, w5, w13
	ldr w13, [x3, #52]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #32]
	add w12, w12, w14
	ldr w13, [x3, #0]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #60]
	add w12, w12, w14
	str w12, [x3, #60]
	ror w13, w9, #6
	ror w14, w9, #11
	eor w13, w13, w14
	ror w14, w9, #25
	eor w13, w13, w14
	add w4, w4, w13
	eor w13, w10, w11
	and w13, w13, w9
	eor w13, w13, w11
	add w4, w4, w13
	movz w13, #41072, lsl #0
	movk w13, #4202, lsl #16
	add w4, w4, w13
	add w4, w4, w12
	add w8, w8, w4
	ror w13, w5, #2
	ror w14, w5, #13
	eor w13, w13, w14
	ror w14, w5, #22
	eor w13, w13, w14
	add w4, w4, w13
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	add w4, w4, w13
	ldr w13, [x3, #56]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #36]
	add w12, w12, w14
	ldr w13, [x3, #4]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #0]
	add w12, w12, w14
	str w12, [x3, #0]
	ror w13, w8, #6
	ror w14, w8, #11
	eor w13, w13, w14
	ror w14, w8, #25
	eor w13, w13, w14
	add w11, w11, w13
	eor w13, w9, w10
	and w13, w13, w8
	eor w13, w13, w10
	add w11, w11, w13
	movz w13, #49430, lsl #0
	movk w13, #6564, lsl #16
	add w11, w11, w13
	add w11, w11, w12
	add w7, w7, w11
	ror w13, w4, #2
	ror w14, w4, #13
	eor w13, w13, w14
	ror w14, w4, #22
	eor w13, w13, w14
	add w11, w11, w13
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	add w11, w11, w13
	ldr w13, [x3, #60]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #40]
	add w12, w12, w14
	ldr w13, [x3, #8]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #4]
	add w12, w12, w14
	str w12, [x3, #4]
	ror w13, w7, #6
	ror w14, w7, #11
	eor w13, w13, w14
	ror w14, w7, #25
	eor w13, w13, w14
	add w10, w10, w13
	eor w13, w8, w9
	and w13, w13, w7
	eor w13, w13, w9
	add w10, w10, w13
	movz w13, #27656, lsl #0
	movk w13, #7735, lsl #16
	add w10, w10, w13
	add w10, w10, w12
	add w6, w6, w10
	ror w13, w11, #2
	ror w14, w11, #13
	eor w13, w13, w14
	ror w14, w11, #22
	eor w13, w13, w14
	add w10, w10, w13
	orr w13, w11, w4
	and w13, w13, w5
	and w14, w11, w4
	orr w13, w13, w14
	add w10, w10, w13
	ldr w13, [x3, #0]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #44]
	add w12, w12, w14
	ldr w13, [x3, #12]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #8]
	add w12, w12, w14
	str w12, [x3, #8]
	ror w13, w6, #6
	ror w14, w6, #11
	eor w13, w13, w14
	ror w14, w6, #25
	eor w13, w13, w14
	add w9, w9, w13
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	add w9, w9, w13
	movz w13, #30540, lsl #0
	movk w13, #10056, lsl #16
	add w9, w9, w13
	add w9, w9, w12
	add w5, w5, w9
	ror w13, w10, #2
	ror w14, w10, #13
	eor w13, w13, w14
	ror w14, w10, #22
	eor w13, w13, w14
	add w9, w9, w13
	orr w13, w10, w11
	and w13, w13, w4
	and w14, w10, w11
	orr w13, w13, w14
	add w9, w9, w13
	ldr w13, [x3, #4]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #48]
	add w12, w12, w14
	ldr w13, [x3, #16]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #12]
	add w12, w12, w14
	str w12, [x3, #12]
	ror w13, w5, #6
	ror w14, w5, #11
	eor w13, w13, w14
	ror w14, w5, #25
	eor w13, w13, w14
	add w8, w8, w13
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	add w8, w8, w13
	movz w13, #48309, lsl #0
	movk w13, #13488, lsl #16
	add w8, w8, w13
	add w8, w8, w12
	add w4, w4, w8
	ror w13, w9, #2
	ror w14, w9, #13
	eor w13, w13, w14
	ror w14, w9, #22
	eor w13, w13, w14
	add w8, w8, w13
	orr w13, w9, w10
	and w13, w13, w11
	and w14, w9, w10
	orr w13, w13, w14
	add w8, w8, w13
	ldr w13, [x3, #8]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #52]
	add w12, w12, w14
	ldr w13, [x3, #20]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #16]
	add w12, w12, w14
	str w12, [x3, #16]
	ror w13, w4, #6
	ror w14, w4, #11
	eor w13, w13, w14
	ror w14, w4, #25
	eor w13, w13, w14
	add w7, w7, w13
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	add w7, w7, w13
	movz w13, #3251, lsl #0
	movk w13, #14620, lsl #16
	add w7, w7, w13
	add w7, w7, w12
	add w11, w11, w7
	ror w13, w8, #2
	ror w14, w8, #13
	eor w13, w13, w14
	ror w14, w8, #22
	eor w13, w13, w14
	add w7, w7, w13
	orr w13, w8, w9
	and w13, w13, w10
	and w14, w8, w9
	orr w13, w13, w14
	add w7, w7, w13
	ldr w13, [x3, #12]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #56]
	add w12, w12, w14
	ldr w13, [x3, #24]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #20]
	add w12, w12, w14
	str w12, [x3, #20]
	ror w13, w11, #6
	ror w14, w11, #11
	eor w13, w13, w14
	ror w14, w11, #25
	eor w13, w13, w14
	add w6, w6, w13
	eor w13, w4, w5
	and w13, w13, w11
	eor w13, w13, w5
	add w6, w6, w13
	movz w13, #43594, lsl #0
	movk w13, #20184, lsl #16
	add w6, w6, w13
	add w6, w6, w12
	add w10, w10, w6
	ror w13, w7, #2
	ror w14, w7, #13
	eor w13, w13, w14
	ror w14, w7, #22
	eor w13, w13, w14
	add w6, w6, w13
	orr w13, w7, w8
	and w13, w13, w9
	and w14, w7, w8
	orr w13, w13, w14
	add w6, w6, w13
	ldr w13, [x3, #16]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #60]
	add w12, w12, w14
	ldr w13, [x3, #28]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #24]
	add w12, w12, w14
	str w12, [x3, #24]
	ror w13, w10, #6
	ror w14, w10, #11
	eor w13, w13, w14
	ror w14, w10, #25
	eor w13, w13, w14
	add w5, w5, w13
	eor w13, w11, w4
	and w13, w13, w10
	eor w13, w13, w4
	add w5, w5, w13
	movz w13, #51791, lsl #0
	movk w13, #23452, lsl #16
	add w5, w5, w13
	add w5, w5, w12
	add w9, w9, w5
	ror w13, w6, #2
	ror w14, w6, #13
	eor w13, w13, w14
	ror w14, w6, #22
	eor w13, w13, w14
	add w5, w5, w13
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	add w5, w5, w13
	ldr w13, [x3, #20]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #0]
	add w12, w12, w14
	ldr w13, [x3, #32]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #28]
	add w12, w12, w14
	str w12, [x3, #28]
	ror w13, w9, #6
	ror w14, w9, #11
	eor w13, w13, w14
	ror w14, w9, #25
	eor w13, w13, w14
	add w4, w4, w13
	eor w13, w10, w11
	and w13, w13, w9
	eor w13, w13, w11
	add w4, w4, w13
	movz w13, #28659, lsl #0
	movk w13, #26670, lsl #16
	add w4, w4, w13
	add w4, w4, w12
	add w8, w8, w4
	ror w13, w5, #2
	ror w14, w5, #13
	eor w13, w13, w14
	ror w14, w5, #22
	eor w13, w13, w14
	add w4, w4, w13
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	add w4, w4, w13
	ldr w13, [x3, #24]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #4]
	add w12, w12, w14
	ldr w13, [x3, #36]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #32]
	add w12, w12, w14
	str w12, [x3, #32]
	ror w13, w8, #6
	ror w14, w8, #11
	eor w13, w13, w14
	ror w14, w8, #25
	eor w13, w13, w14
	add w11, w11, w13
	eor w13, w9, w10
	and w13, w13, w8
	eor w13, w13, w10
	add w11, w11, w13
	movz w13, #33518, lsl #0
	movk w13, #29839, lsl #16
	add w11, w11, w13
	add w11, w11, w12
	add w7, w7, w11
	ror w13, w4, #2
	ror w14, w4, #13
	eor w13, w13, w14
	ror w14, w4, #22
	eor w13, w13, w14
	add w11, w11, w13
	orr w13, w4, w5
	and w13, w13, w6
	and w14, w4, w5
	orr w13, w13, w14
	add w11, w11, w13
	ldr w13, [x3, #28]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #8]
	add w12, w12, w14
	ldr w13, [x3, #40]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #36]
	add w12, w12, w14
	str w12, [x3, #36]
	ror w13, w7, #6
	ror w14, w7, #11
	eor w13, w13, w14
	ror w14, w7, #25
	eor w13, w13, w14
	add w10, w10, w13
	eor w13, w8, w9
	and w13, w13, w7
	eor w13, w13, w9
	add w10, w10, w13
	movz w13, #25455, lsl #0
	movk w13, #30885, lsl #16
	add w10, w10, w13
	add w10, w10, w12
	add w6, w6, w10
	ror w13, w11, #2
	ror w14, w11, #13
	eor w13, w13, w14
	ror w14, w11, #22
	eor w13, w13, w14
	add w10, w10, w13
	orr w13, w11, w4
	and w13, w13, w5
	and w14, w11, w4
	orr w13, w13, w14
	add w10, w10, w13
	ldr w13, [x3, #32]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #12]
	add w12, w12, w14
	ldr w13, [x3, #44]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #40]
	add w12, w12, w14
	str w12, [x3, #40]
	ror w13, w6, #6
	ror w14, w6, #11
	eor w13, w13, w14
	ror w14, w6, #25
	eor w13, w13, w14
	add w9, w9, w13
	eor w13, w7, w8
	and w13, w13, w6
	eor w13, w13, w8
	add w9, w9, w13
	movz w13, #30740, lsl #0
	movk w13, #33992, lsl #16
	add w9, w9, w13
	add w9, w9, w12
	add w5, w5, w9
	ror w13, w10, #2
	ror w14, w10, #13
	eor w13, w13, w14
	ror w14, w10, #22
	eor w13, w13, w14
	add w9, w9, w13
	orr w13, w10, w11
	and w13, w13, w4
	and w14, w10, w11
	orr w13, w13, w14
	add w9, w9, w13
	ldr w13, [x3, #36]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #16]
	add w12, w12, w14
	ldr w13, [x3, #48]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #44]
	add w12, w12, w14
	str w12, [x3, #44]
	ror w13, w5, #6
	ror w14, w5, #11
	eor w13, w13, w14
	ror w14, w5, #25
	eor w13, w13, w14
	add w8, w8, w13
	eor w13, w6, w7
	and w13, w13, w5
	eor w13, w13, w7
	add w8, w8, w13
	movz w13, #520, lsl #0
	movk w13, #36039, lsl #16
	add w8, w8, w13
	add w8, w8, w12
	add w4, w4, w8
	ror w13, w9, #2
	ror w14, w9, #13
	eor w13, w13, w14
	ror w14, w9, #22
	eor w13, w13, w14
	add w8, w8, w13
	orr w13, w9, w10
	and w13, w13, w11
	and w14, w9, w10
	orr w13, w13, w14
	add w8, w8, w13
	ldr w13, [x3, #40]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #20]
	add w12, w12, w14
	ldr w13, [x3, #52]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #48]
	add w12, w12, w14
	str w12, [x3, #48]
	ror w13, w4, #6
	ror w14, w4, #11
	eor w13, w13, w14
	ror w14, w4, #25
	eor w13, w13, w14
	add w7, w7, w13
	eor w13, w5, w6
	and w13, w13, w4
	eor w13, w13, w6
	add w7, w7, w13
	movz w13, #65530, lsl #0
	movk w13, #37054, lsl #16
	add w7, w7, w13
	add w7, w7, w12
	add w11, w11, w7
	ror w13, w8, #2
	ror w14, w8, #13
	eor w13, w13, w14
	ror w14, w8, #22
	eor w13, w13, w14
	add w7, w7, w13
	orr w13, w8, w9
	and w13, w13, w10
	and w14, w8, w9
	orr w13, w13, w14
	add w7, w7, w13
	ldr w13, [x3, #44]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #24]
	add w12, w12, w14
	ldr w13, [x3, #56]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #52]
	add w12, w12, w14
	str w12, [x3, #52]
	ror w13, w11, #6
	ror w14, w11, #11
	eor w13, w13, w14
	ror w14, w11, #25
	eor w13, w13, w14
	add w6, w6, w13
	eor w13, w4, w5
	and w13, w13, w11
	eor w13, w13, w5
	add w6, w6, w13
	movz w13, #27883, lsl #0
	movk w13, #42064, lsl #16
	add w6, w6, w13
	add w6, w6, w12
	add w10, w10, w6
	ror w13, w7, #2
	ror w14, w7, #13
	eor w13, w13, w14
	ror w14, w7, #22
	eor w13, w13, w14
	add w6, w6, w13
	orr w13, w7, w8
	and w13, w13, w9
	and w14, w7, w8
	orr w13, w13, w14
	add w6, w6, w13
	ldr w13, [x3, #48]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #28]
	add w12, w12, w14
	ldr w13, [x3, #60]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #56]
	add w12, w12, w14
	str w12, [x3, #56]
	ror w13, w10, #6
	ror w14, w10, #11
	eor w13, w13, w14
	ror w14, w10, #25
	eor w13, w13, w14
	add w5, w5, w13
	eor w13, w11, w4
	and w13, w13, w10
	eor w13, w13, w4
	add w5, w5, w13
	movz w13, #41975, lsl #0
	movk w13, #48889, lsl #16
	add w5, w5, w13
	add w5, w5, w12
	add w9, w9, w5
	ror w13, w6, #2
	ror w14, w6, #13
	eor w13, w13, w14
	ror w14, w6, #22
	eor w13, w13, w14
	add w5, w5, w13
	orr w13, w6, w7
	and w13, w13, w8
	and w14, w6, w7
	orr w13, w13, w14
	add w5, w5, w13
	ldr w13, [x3, #52]
	ror w12, w13, #17
	ror w14, w13, #19
	eor w12, w12, w14
	lsr w14, w13, #10
	eor w12, w12, w14
	ldr w14, [x3, #32]
	add w12, w12, w14
	ldr w13, [x3, #0]
	ror w14, w13, #7
	ror w15, w13, #18
	eor w14, w14, w15
	lsr w15, w13, #3
	eor w14, w14, w15
	add w12, w12, w14
	ldr w14, [x3, #60]
	add w12, w12, w14
	str w12, [x3, #60]
	ror w13, w9, #6
	ror w14, w9, #11
	eor w13, w13, w14
	ror w14, w9, #25
	eor w13, w13, w14
	add w4, w4, w13
	eor w13, w10, w11
	and w13, w13, w9
	eor w13, w13, w11
	add w4, w4, w13
	movz w13, #30962, lsl #0
	movk w13, #50801, lsl #16
	add w4, w4, w13
	add w4, w4, w12
	add w8, w8, w4
	ror w13, w5, #2
	ror w14, w5, #13
	eor w13, w13, w14
	ror w14, w5, #22
	eor w13, w13, w14
	add w4, w4, w13
	orr w13, w5, w6
	and w13, w13, w7
	and w14, w5, w6
	orr w13, w13, w14
	add w4, w4, w13
	ldr w12, [x0, #0]
	ldr w13, [x0, #4]
	ldr w14, [x0, #8]
	ldr w15, [x0, #12]
	add w4, w4, w12
	add w5, w5, w13
	add w6, w6, w14
	add w7, w7, w15
	ldr w12, [x0, #16]
	ldr w13, [x0, #20]
	ldr w14, [x0, #24]
	ldr w15, [x0, #28]
	add w8, w8, w12
	add w9, w9, w13
	add w10, w10, w14
	add w11, w11, w15
	str w4, [x0, #0]
	str w5, [x0, #4]
	str w6, [x0, #8]
	str w7, [x0, #12]
	str w8, [x0, #16]
	str w9, [x0, #20]
	str w10, [x0, #24]
	str w11, [x0, #28]
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	ret
	.p2align 6

vg_sha256_init:
	adrp x9, {VG_SHA256_H0}
	add x9, x9, {VG_SHA256_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	ret
	.p2align 6

vg_sha256_compress_sha2:
	.arch_extension sha2
	cbz x2, 20f
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	mov v30.16b, v0.16b
	mov v31.16b, v1.16b
	adrp x4, {VG_SHA256_K}
	add x4, x4, {VG_SHA256_K}
	ldr q16, [x4, #0]
	ldr q17, [x4, #16]
	ldr q4, [x1, #0]
	rev32 v4.16b, v4.16b
	ldr q18, [x4, #32]
	add v3.4s, v16.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q5, [x1, #16]
	rev32 v5.16b, v5.16b
	ldr q19, [x4, #48]
	add v3.4s, v17.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q6, [x1, #32]
	rev32 v6.16b, v6.16b
	ldr q20, [x4, #64]
	add v3.4s, v18.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q7, [x1, #48]
	rev32 v7.16b, v7.16b
	ldr q21, [x4, #80]
	add v3.4s, v19.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	ldr q22, [x4, #96]
	add v3.4s, v20.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	ldr q23, [x4, #112]
	add v3.4s, v21.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	ldr q24, [x4, #128]
	add v3.4s, v22.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	ldr q25, [x4, #144]
	add v3.4s, v23.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	ldr q26, [x4, #160]
	add v3.4s, v24.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	ldr q27, [x4, #176]
	add v3.4s, v25.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	ldr q28, [x4, #192]
	add v3.4s, v26.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	ldr q29, [x4, #208]
	add v3.4s, v27.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	add v3.4s, v28.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	add v3.4s, v29.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	ldr q3, [x4, #224]
	add v3.4s, v3.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	ldr q3, [x4, #240]
	add v3.4s, v3.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	add v0.4s, v0.4s, v30.4s
	add v1.4s, v1.4s, v31.4s
	add x1, x1, #64
	sub x2, x2, #1
	cbz x2, 22f
	.p2align 6
24:
	mov v30.16b, v0.16b
	mov v31.16b, v1.16b
	ldr q4, [x1, #0]
	rev32 v4.16b, v4.16b
	add v3.4s, v16.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q5, [x1, #16]
	rev32 v5.16b, v5.16b
	add v3.4s, v17.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q6, [x1, #32]
	rev32 v6.16b, v6.16b
	add v3.4s, v18.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	ldr q7, [x1, #48]
	rev32 v7.16b, v7.16b
	add v3.4s, v19.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	add v3.4s, v20.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	add v3.4s, v21.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	add v3.4s, v22.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	add v3.4s, v23.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	add v3.4s, v24.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	add v3.4s, v25.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	add v3.4s, v26.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	add v3.4s, v27.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v4.4s, v5.4s
	sha256su1 v4.4s, v6.4s, v7.4s
	add v3.4s, v28.4s, v4.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v5.4s, v6.4s
	sha256su1 v5.4s, v7.4s, v4.4s
	add v3.4s, v29.4s, v5.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v6.4s, v7.4s
	sha256su1 v6.4s, v4.4s, v5.4s
	ldr q3, [x4, #224]
	add v3.4s, v3.4s, v6.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	sha256su0 v7.4s, v4.4s
	sha256su1 v7.4s, v5.4s, v6.4s
	ldr q3, [x4, #240]
	add v3.4s, v3.4s, v7.4s
	mov v2.16b, v0.16b
	sha256h q0, q1, v3.4s
	sha256h2 q1, q2, v3.4s
	add v0.4s, v0.4s, v30.4s
	add v1.4s, v1.4s, v31.4s
	add x1, x1, #64
	sub x2, x2, #1
	cbnz x2, 24b
	b 23f
22:
23:
	str q0, [x0, #0]
	str q1, [x0, #16]
	b 21f
20:
21:
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha224_finalize:
	sub sp, sp, #608
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
	strb w9, [x12, #32]
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	str x9, [x19, #88]
210:
	add x1, x19, #32
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha256_compress}
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
	ldr w9, [x19, #20]
	rev w9, w9
	str w9, [x21, #20]
	ldr w9, [x19, #24]
	rev w9, w9
	str w9, [x21, #24]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.p2align 6

vg_sha224_digest:
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
	adrp x9, {VG_SHA224_H0}
	add x9, x9, {VG_SHA224_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #32
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
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	movz x9, #0, lsl #0
	add x12, sp, #32
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
	str x9, [x19, #88]
	add x12, sp, #80
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress}
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
	ldr w9, [x19, #20]
	rev w9, w9
	str w9, [x21, #20]
	ldr w9, [x19, #24]
	rev w9, w9
	str w9, [x21, #24]
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

vg_sha224_finalize_sha2:
	.arch_extension sha2
	sub sp, sp, #608
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
	strb w9, [x12, #32]
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	str x9, [x19, #88]
210:
	add x1, x19, #32
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha256_compress_sha2}
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
	ldr w9, [x19, #20]
	rev w9, w9
	str w9, [x21, #20]
	ldr w9, [x19, #24]
	rev w9, w9
	str w9, [x21, #24]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha224_digest_sha2:
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
	adrp x9, {VG_SHA224_H0}
	add x9, x9, {VG_SHA224_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #32
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
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	movz x9, #0, lsl #0
	add x12, sp, #32
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
	str x9, [x19, #88]
	add x12, sp, #80
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
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
	ldr w9, [x19, #20]
	rev w9, w9
	str w9, [x21, #20]
	ldr w9, [x19, #24]
	rev w9, w9
	str w9, [x21, #24]
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

vg_sha256_update:
	sub sp, sp, #608
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	add x1, x19, #32
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	add x1, x19, #32
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sha256_compress}
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
	add sp, sp, #608
	ret
	.p2align 6

vg_sha256_finalize:
	sub sp, sp, #608
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
	strb w9, [x12, #32]
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	str x9, [x19, #88]
210:
	add x1, x19, #32
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha256_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.p2align 6

vg_sha256_update_scratch:
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	add x1, x19, #32
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	add x1, x19, #32
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sha256_compress}
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

vg_sha256_finalize_scratch:
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
	strb w9, [x12, #32]
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	str x9, [x19, #88]
210:
	add x1, x19, #32
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha256_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_sha256_digest:
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
	adrp x9, {VG_SHA256_H0}
	add x9, x9, {VG_SHA256_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #32
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
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	movz x9, #0, lsl #0
	add x12, sp, #32
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
	str x9, [x19, #88]
	add x12, sp, #80
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	add x19, sp, #0
	add x21, x26, #0
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
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

vg_sha256_update_sha2:
	.arch_extension sha2
	sub sp, sp, #608
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	add x1, x19, #32
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	add x1, x19, #32
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sha256_compress_sha2}
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
	add sp, sp, #608
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha256_finalize_sha2:
	.arch_extension sha2
	sub sp, sp, #608
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
	strb w9, [x12, #32]
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	str x9, [x19, #88]
210:
	add x1, x19, #32
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha256_compress_sha2}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha256_update_scratch_sha2:
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	add x1, x19, #32
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	add x1, x19, #32
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sha256_compress_sha2}
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

vg_sha256_finalize_scratch_sha2:
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
	strb w9, [x12, #32]
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
	str x9, [x12, #32]
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
	strb w9, [x12, #32]
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
	str x9, [x19, #88]
210:
	add x1, x19, #32
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha256_compress_sha2}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
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

vg_sha256_digest_sha2:
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
	adrp x9, {VG_SHA256_H0}
	add x9, x9, {VG_SHA256_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #32
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
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	movz x9, #0, lsl #0
	add x12, sp, #32
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
	str x9, [x19, #88]
	add x12, sp, #80
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	add x19, sp, #0
	add x21, x26, #0
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
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
