// The functions of `src/internal/vg_sha256_compress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_compress:
	cbz x2, 20f
	adrp x15, {VG_SHA256_K}
	add x15, x15, {VG_SHA256_K}
22:
	ldr w4, [x0, #0]
	ldr w5, [x0, #4]
	ldr w6, [x0, #8]
	ldr w7, [x0, #12]
	ldr w8, [x0, #16]
	ldr w9, [x0, #20]
	ldr w10, [x0, #24]
	ldr w11, [x0, #28]
	eor w14, w5, w6
	ldr w16, [x1, #0]
	rev w16, w16
	str w16, [x3, #0]
	ldr q16, [x15, #0]
	umov w12, v16.s[0]
	add w11, w11, w16
	add w11, w11, w12
	ror w12, w8, #6
	eor w12, w12, w8, ror #11
	eor w12, w12, w8, ror #25
	add w11, w11, w12
	eor w12, w9, w10
	and w12, w12, w8
	eor w12, w12, w10
	add w11, w11, w12
	add w7, w7, w11
	ror w12, w4, #2
	eor w12, w12, w4, ror #13
	eor w12, w12, w4, ror #22
	add w11, w11, w12
	eor w13, w4, w5
	and w14, w14, w13
	eor w14, w14, w5
	add w11, w11, w14
	ldr w17, [x1, #4]
	rev w17, w17
	str w17, [x3, #4]
	umov w12, v16.s[1]
	add w10, w10, w17
	add w10, w10, w12
	ror w12, w7, #6
	eor w12, w12, w7, ror #11
	eor w12, w12, w7, ror #25
	add w10, w10, w12
	eor w12, w8, w9
	and w12, w12, w7
	eor w12, w12, w9
	add w10, w10, w12
	add w6, w6, w10
	ror w12, w11, #2
	eor w12, w12, w11, ror #13
	eor w12, w12, w11, ror #22
	add w10, w10, w12
	eor w14, w11, w4
	and w13, w13, w14
	eor w13, w13, w4
	add w10, w10, w13
	ldr w16, [x1, #8]
	rev w16, w16
	str w16, [x3, #8]
	umov w12, v16.s[2]
	add w9, w9, w16
	add w9, w9, w12
	ror w12, w6, #6
	eor w12, w12, w6, ror #11
	eor w12, w12, w6, ror #25
	add w9, w9, w12
	eor w12, w7, w8
	and w12, w12, w6
	eor w12, w12, w8
	add w9, w9, w12
	add w5, w5, w9
	ror w12, w10, #2
	eor w12, w12, w10, ror #13
	eor w12, w12, w10, ror #22
	add w9, w9, w12
	eor w13, w10, w11
	and w14, w14, w13
	eor w14, w14, w11
	add w9, w9, w14
	ldr w17, [x1, #12]
	rev w17, w17
	str w17, [x3, #12]
	umov w12, v16.s[3]
	add w8, w8, w17
	add w8, w8, w12
	ror w12, w5, #6
	eor w12, w12, w5, ror #11
	eor w12, w12, w5, ror #25
	add w8, w8, w12
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w8, w8, w12
	add w4, w4, w8
	ror w12, w9, #2
	eor w12, w12, w9, ror #13
	eor w12, w12, w9, ror #22
	add w8, w8, w12
	eor w14, w9, w10
	and w13, w13, w14
	eor w13, w13, w10
	add w8, w8, w13
	ldr w16, [x1, #16]
	rev w16, w16
	str w16, [x3, #16]
	ldr q16, [x15, #16]
	umov w12, v16.s[0]
	add w7, w7, w16
	add w7, w7, w12
	ror w12, w4, #6
	eor w12, w12, w4, ror #11
	eor w12, w12, w4, ror #25
	add w7, w7, w12
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	add w11, w11, w7
	ror w12, w8, #2
	eor w12, w12, w8, ror #13
	eor w12, w12, w8, ror #22
	add w7, w7, w12
	eor w13, w8, w9
	and w14, w14, w13
	eor w14, w14, w9
	add w7, w7, w14
	ldr w17, [x1, #20]
	rev w17, w17
	str w17, [x3, #20]
	umov w12, v16.s[1]
	add w6, w6, w17
	add w6, w6, w12
	ror w12, w11, #6
	eor w12, w12, w11, ror #11
	eor w12, w12, w11, ror #25
	add w6, w6, w12
	eor w12, w4, w5
	and w12, w12, w11
	eor w12, w12, w5
	add w6, w6, w12
	add w10, w10, w6
	ror w12, w7, #2
	eor w12, w12, w7, ror #13
	eor w12, w12, w7, ror #22
	add w6, w6, w12
	eor w14, w7, w8
	and w13, w13, w14
	eor w13, w13, w8
	add w6, w6, w13
	ldr w16, [x1, #24]
	rev w16, w16
	str w16, [x3, #24]
	umov w12, v16.s[2]
	add w5, w5, w16
	add w5, w5, w12
	ror w12, w10, #6
	eor w12, w12, w10, ror #11
	eor w12, w12, w10, ror #25
	add w5, w5, w12
	eor w12, w11, w4
	and w12, w12, w10
	eor w12, w12, w4
	add w5, w5, w12
	add w9, w9, w5
	ror w12, w6, #2
	eor w12, w12, w6, ror #13
	eor w12, w12, w6, ror #22
	add w5, w5, w12
	eor w13, w6, w7
	and w14, w14, w13
	eor w14, w14, w7
	add w5, w5, w14
	ldr w17, [x1, #28]
	rev w17, w17
	str w17, [x3, #28]
	umov w12, v16.s[3]
	add w4, w4, w17
	add w4, w4, w12
	ror w12, w9, #6
	eor w12, w12, w9, ror #11
	eor w12, w12, w9, ror #25
	add w4, w4, w12
	eor w12, w10, w11
	and w12, w12, w9
	eor w12, w12, w11
	add w4, w4, w12
	add w8, w8, w4
	ror w12, w5, #2
	eor w12, w12, w5, ror #13
	eor w12, w12, w5, ror #22
	add w4, w4, w12
	eor w14, w5, w6
	and w13, w13, w14
	eor w13, w13, w6
	add w4, w4, w13
	ldr w16, [x1, #32]
	rev w16, w16
	str w16, [x3, #32]
	ldr q16, [x15, #32]
	umov w12, v16.s[0]
	add w11, w11, w16
	add w11, w11, w12
	ror w12, w8, #6
	eor w12, w12, w8, ror #11
	eor w12, w12, w8, ror #25
	add w11, w11, w12
	eor w12, w9, w10
	and w12, w12, w8
	eor w12, w12, w10
	add w11, w11, w12
	add w7, w7, w11
	ror w12, w4, #2
	eor w12, w12, w4, ror #13
	eor w12, w12, w4, ror #22
	add w11, w11, w12
	eor w13, w4, w5
	and w14, w14, w13
	eor w14, w14, w5
	add w11, w11, w14
	ldr w17, [x1, #36]
	rev w17, w17
	str w17, [x3, #36]
	umov w12, v16.s[1]
	add w10, w10, w17
	add w10, w10, w12
	ror w12, w7, #6
	eor w12, w12, w7, ror #11
	eor w12, w12, w7, ror #25
	add w10, w10, w12
	eor w12, w8, w9
	and w12, w12, w7
	eor w12, w12, w9
	add w10, w10, w12
	add w6, w6, w10
	ror w12, w11, #2
	eor w12, w12, w11, ror #13
	eor w12, w12, w11, ror #22
	add w10, w10, w12
	eor w14, w11, w4
	and w13, w13, w14
	eor w13, w13, w4
	add w10, w10, w13
	ldr w16, [x1, #40]
	rev w16, w16
	str w16, [x3, #40]
	umov w12, v16.s[2]
	add w9, w9, w16
	add w9, w9, w12
	ror w12, w6, #6
	eor w12, w12, w6, ror #11
	eor w12, w12, w6, ror #25
	add w9, w9, w12
	eor w12, w7, w8
	and w12, w12, w6
	eor w12, w12, w8
	add w9, w9, w12
	add w5, w5, w9
	ror w12, w10, #2
	eor w12, w12, w10, ror #13
	eor w12, w12, w10, ror #22
	add w9, w9, w12
	eor w13, w10, w11
	and w14, w14, w13
	eor w14, w14, w11
	add w9, w9, w14
	ldr w17, [x1, #44]
	rev w17, w17
	str w17, [x3, #44]
	umov w12, v16.s[3]
	add w8, w8, w17
	add w8, w8, w12
	ror w12, w5, #6
	eor w12, w12, w5, ror #11
	eor w12, w12, w5, ror #25
	add w8, w8, w12
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w8, w8, w12
	add w4, w4, w8
	ror w12, w9, #2
	eor w12, w12, w9, ror #13
	eor w12, w12, w9, ror #22
	add w8, w8, w12
	eor w14, w9, w10
	and w13, w13, w14
	eor w13, w13, w10
	add w8, w8, w13
	ldr w16, [x1, #48]
	rev w16, w16
	str w16, [x3, #48]
	ldr q16, [x15, #48]
	umov w12, v16.s[0]
	add w7, w7, w16
	add w7, w7, w12
	ror w12, w4, #6
	eor w12, w12, w4, ror #11
	eor w12, w12, w4, ror #25
	add w7, w7, w12
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	add w11, w11, w7
	ror w12, w8, #2
	eor w12, w12, w8, ror #13
	eor w12, w12, w8, ror #22
	add w7, w7, w12
	eor w13, w8, w9
	and w14, w14, w13
	eor w14, w14, w9
	add w7, w7, w14
	ldr w17, [x1, #52]
	rev w17, w17
	str w17, [x3, #52]
	umov w12, v16.s[1]
	add w6, w6, w17
	add w6, w6, w12
	ror w12, w11, #6
	eor w12, w12, w11, ror #11
	eor w12, w12, w11, ror #25
	add w6, w6, w12
	eor w12, w4, w5
	and w12, w12, w11
	eor w12, w12, w5
	add w6, w6, w12
	add w10, w10, w6
	ror w12, w7, #2
	eor w12, w12, w7, ror #13
	eor w12, w12, w7, ror #22
	add w6, w6, w12
	eor w14, w7, w8
	and w13, w13, w14
	eor w13, w13, w8
	add w6, w6, w13
	ldr w16, [x1, #56]
	rev w16, w16
	str w16, [x3, #56]
	umov w12, v16.s[2]
	add w5, w5, w16
	add w5, w5, w12
	ror w12, w10, #6
	eor w12, w12, w10, ror #11
	eor w12, w12, w10, ror #25
	add w5, w5, w12
	eor w12, w11, w4
	and w12, w12, w10
	eor w12, w12, w4
	add w5, w5, w12
	add w9, w9, w5
	ror w12, w6, #2
	eor w12, w12, w6, ror #13
	eor w12, w12, w6, ror #22
	add w5, w5, w12
	eor w13, w6, w7
	and w14, w14, w13
	eor w14, w14, w7
	add w5, w5, w14
	ldr w17, [x1, #60]
	rev w17, w17
	str w17, [x3, #60]
	umov w12, v16.s[3]
	add w4, w4, w17
	add w4, w4, w12
	ror w12, w9, #6
	eor w12, w12, w9, ror #11
	eor w12, w12, w9, ror #25
	add w4, w4, w12
	eor w12, w10, w11
	and w12, w12, w9
	eor w12, w12, w11
	add w4, w4, w12
	add w8, w8, w4
	ror w12, w5, #2
	eor w12, w12, w5, ror #13
	eor w12, w12, w5, ror #22
	add w4, w4, w12
	eor w14, w5, w6
	and w13, w13, w14
	eor w13, w13, w6
	add w4, w4, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #0]
	ldr w12, [x3, #4]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #36]
	add w16, w16, w12
	str w16, [x3, #0]
	ldr q16, [x15, #64]
	umov w12, v16.s[0]
	add w11, w11, w16
	add w11, w11, w12
	ror w12, w8, #6
	eor w12, w12, w8, ror #11
	eor w12, w12, w8, ror #25
	add w11, w11, w12
	eor w12, w9, w10
	and w12, w12, w8
	eor w12, w12, w10
	add w11, w11, w12
	add w7, w7, w11
	ror w12, w4, #2
	eor w12, w12, w4, ror #13
	eor w12, w12, w4, ror #22
	add w11, w11, w12
	eor w13, w4, w5
	and w14, w14, w13
	eor w14, w14, w5
	add w11, w11, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #4]
	ldr w12, [x3, #8]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #40]
	add w17, w17, w12
	str w17, [x3, #4]
	umov w12, v16.s[1]
	add w10, w10, w17
	add w10, w10, w12
	ror w12, w7, #6
	eor w12, w12, w7, ror #11
	eor w12, w12, w7, ror #25
	add w10, w10, w12
	eor w12, w8, w9
	and w12, w12, w7
	eor w12, w12, w9
	add w10, w10, w12
	add w6, w6, w10
	ror w12, w11, #2
	eor w12, w12, w11, ror #13
	eor w12, w12, w11, ror #22
	add w10, w10, w12
	eor w14, w11, w4
	and w13, w13, w14
	eor w13, w13, w4
	add w10, w10, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #8]
	ldr w12, [x3, #12]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #44]
	add w16, w16, w12
	str w16, [x3, #8]
	umov w12, v16.s[2]
	add w9, w9, w16
	add w9, w9, w12
	ror w12, w6, #6
	eor w12, w12, w6, ror #11
	eor w12, w12, w6, ror #25
	add w9, w9, w12
	eor w12, w7, w8
	and w12, w12, w6
	eor w12, w12, w8
	add w9, w9, w12
	add w5, w5, w9
	ror w12, w10, #2
	eor w12, w12, w10, ror #13
	eor w12, w12, w10, ror #22
	add w9, w9, w12
	eor w13, w10, w11
	and w14, w14, w13
	eor w14, w14, w11
	add w9, w9, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #12]
	ldr w12, [x3, #16]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #48]
	add w17, w17, w12
	str w17, [x3, #12]
	umov w12, v16.s[3]
	add w8, w8, w17
	add w8, w8, w12
	ror w12, w5, #6
	eor w12, w12, w5, ror #11
	eor w12, w12, w5, ror #25
	add w8, w8, w12
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w8, w8, w12
	add w4, w4, w8
	ror w12, w9, #2
	eor w12, w12, w9, ror #13
	eor w12, w12, w9, ror #22
	add w8, w8, w12
	eor w14, w9, w10
	and w13, w13, w14
	eor w13, w13, w10
	add w8, w8, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #16]
	ldr w12, [x3, #20]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #52]
	add w16, w16, w12
	str w16, [x3, #16]
	ldr q16, [x15, #80]
	umov w12, v16.s[0]
	add w7, w7, w16
	add w7, w7, w12
	ror w12, w4, #6
	eor w12, w12, w4, ror #11
	eor w12, w12, w4, ror #25
	add w7, w7, w12
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	add w11, w11, w7
	ror w12, w8, #2
	eor w12, w12, w8, ror #13
	eor w12, w12, w8, ror #22
	add w7, w7, w12
	eor w13, w8, w9
	and w14, w14, w13
	eor w14, w14, w9
	add w7, w7, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #20]
	ldr w12, [x3, #24]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #56]
	add w17, w17, w12
	str w17, [x3, #20]
	umov w12, v16.s[1]
	add w6, w6, w17
	add w6, w6, w12
	ror w12, w11, #6
	eor w12, w12, w11, ror #11
	eor w12, w12, w11, ror #25
	add w6, w6, w12
	eor w12, w4, w5
	and w12, w12, w11
	eor w12, w12, w5
	add w6, w6, w12
	add w10, w10, w6
	ror w12, w7, #2
	eor w12, w12, w7, ror #13
	eor w12, w12, w7, ror #22
	add w6, w6, w12
	eor w14, w7, w8
	and w13, w13, w14
	eor w13, w13, w8
	add w6, w6, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #24]
	ldr w12, [x3, #28]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #60]
	add w16, w16, w12
	str w16, [x3, #24]
	umov w12, v16.s[2]
	add w5, w5, w16
	add w5, w5, w12
	ror w12, w10, #6
	eor w12, w12, w10, ror #11
	eor w12, w12, w10, ror #25
	add w5, w5, w12
	eor w12, w11, w4
	and w12, w12, w10
	eor w12, w12, w4
	add w5, w5, w12
	add w9, w9, w5
	ror w12, w6, #2
	eor w12, w12, w6, ror #13
	eor w12, w12, w6, ror #22
	add w5, w5, w12
	eor w13, w6, w7
	and w14, w14, w13
	eor w14, w14, w7
	add w5, w5, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #28]
	ldr w12, [x3, #32]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #0]
	add w17, w17, w12
	str w17, [x3, #28]
	umov w12, v16.s[3]
	add w4, w4, w17
	add w4, w4, w12
	ror w12, w9, #6
	eor w12, w12, w9, ror #11
	eor w12, w12, w9, ror #25
	add w4, w4, w12
	eor w12, w10, w11
	and w12, w12, w9
	eor w12, w12, w11
	add w4, w4, w12
	add w8, w8, w4
	ror w12, w5, #2
	eor w12, w12, w5, ror #13
	eor w12, w12, w5, ror #22
	add w4, w4, w12
	eor w14, w5, w6
	and w13, w13, w14
	eor w13, w13, w6
	add w4, w4, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #32]
	ldr w12, [x3, #36]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #4]
	add w16, w16, w12
	str w16, [x3, #32]
	ldr q16, [x15, #96]
	umov w12, v16.s[0]
	add w11, w11, w16
	add w11, w11, w12
	ror w12, w8, #6
	eor w12, w12, w8, ror #11
	eor w12, w12, w8, ror #25
	add w11, w11, w12
	eor w12, w9, w10
	and w12, w12, w8
	eor w12, w12, w10
	add w11, w11, w12
	add w7, w7, w11
	ror w12, w4, #2
	eor w12, w12, w4, ror #13
	eor w12, w12, w4, ror #22
	add w11, w11, w12
	eor w13, w4, w5
	and w14, w14, w13
	eor w14, w14, w5
	add w11, w11, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #36]
	ldr w12, [x3, #40]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #8]
	add w17, w17, w12
	str w17, [x3, #36]
	umov w12, v16.s[1]
	add w10, w10, w17
	add w10, w10, w12
	ror w12, w7, #6
	eor w12, w12, w7, ror #11
	eor w12, w12, w7, ror #25
	add w10, w10, w12
	eor w12, w8, w9
	and w12, w12, w7
	eor w12, w12, w9
	add w10, w10, w12
	add w6, w6, w10
	ror w12, w11, #2
	eor w12, w12, w11, ror #13
	eor w12, w12, w11, ror #22
	add w10, w10, w12
	eor w14, w11, w4
	and w13, w13, w14
	eor w13, w13, w4
	add w10, w10, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #40]
	ldr w12, [x3, #44]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #12]
	add w16, w16, w12
	str w16, [x3, #40]
	umov w12, v16.s[2]
	add w9, w9, w16
	add w9, w9, w12
	ror w12, w6, #6
	eor w12, w12, w6, ror #11
	eor w12, w12, w6, ror #25
	add w9, w9, w12
	eor w12, w7, w8
	and w12, w12, w6
	eor w12, w12, w8
	add w9, w9, w12
	add w5, w5, w9
	ror w12, w10, #2
	eor w12, w12, w10, ror #13
	eor w12, w12, w10, ror #22
	add w9, w9, w12
	eor w13, w10, w11
	and w14, w14, w13
	eor w14, w14, w11
	add w9, w9, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #44]
	ldr w12, [x3, #48]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #16]
	add w17, w17, w12
	str w17, [x3, #44]
	umov w12, v16.s[3]
	add w8, w8, w17
	add w8, w8, w12
	ror w12, w5, #6
	eor w12, w12, w5, ror #11
	eor w12, w12, w5, ror #25
	add w8, w8, w12
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w8, w8, w12
	add w4, w4, w8
	ror w12, w9, #2
	eor w12, w12, w9, ror #13
	eor w12, w12, w9, ror #22
	add w8, w8, w12
	eor w14, w9, w10
	and w13, w13, w14
	eor w13, w13, w10
	add w8, w8, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #48]
	ldr w12, [x3, #52]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #20]
	add w16, w16, w12
	str w16, [x3, #48]
	ldr q16, [x15, #112]
	umov w12, v16.s[0]
	add w7, w7, w16
	add w7, w7, w12
	ror w12, w4, #6
	eor w12, w12, w4, ror #11
	eor w12, w12, w4, ror #25
	add w7, w7, w12
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	add w11, w11, w7
	ror w12, w8, #2
	eor w12, w12, w8, ror #13
	eor w12, w12, w8, ror #22
	add w7, w7, w12
	eor w13, w8, w9
	and w14, w14, w13
	eor w14, w14, w9
	add w7, w7, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #52]
	ldr w12, [x3, #56]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #24]
	add w17, w17, w12
	str w17, [x3, #52]
	umov w12, v16.s[1]
	add w6, w6, w17
	add w6, w6, w12
	ror w12, w11, #6
	eor w12, w12, w11, ror #11
	eor w12, w12, w11, ror #25
	add w6, w6, w12
	eor w12, w4, w5
	and w12, w12, w11
	eor w12, w12, w5
	add w6, w6, w12
	add w10, w10, w6
	ror w12, w7, #2
	eor w12, w12, w7, ror #13
	eor w12, w12, w7, ror #22
	add w6, w6, w12
	eor w14, w7, w8
	and w13, w13, w14
	eor w13, w13, w8
	add w6, w6, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #56]
	ldr w12, [x3, #60]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #28]
	add w16, w16, w12
	str w16, [x3, #56]
	umov w12, v16.s[2]
	add w5, w5, w16
	add w5, w5, w12
	ror w12, w10, #6
	eor w12, w12, w10, ror #11
	eor w12, w12, w10, ror #25
	add w5, w5, w12
	eor w12, w11, w4
	and w12, w12, w10
	eor w12, w12, w4
	add w5, w5, w12
	add w9, w9, w5
	ror w12, w6, #2
	eor w12, w12, w6, ror #13
	eor w12, w12, w6, ror #22
	add w5, w5, w12
	eor w13, w6, w7
	and w14, w14, w13
	eor w14, w14, w7
	add w5, w5, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #60]
	ldr w12, [x3, #0]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #32]
	add w17, w17, w12
	str w17, [x3, #60]
	umov w12, v16.s[3]
	add w4, w4, w17
	add w4, w4, w12
	ror w12, w9, #6
	eor w12, w12, w9, ror #11
	eor w12, w12, w9, ror #25
	add w4, w4, w12
	eor w12, w10, w11
	and w12, w12, w9
	eor w12, w12, w11
	add w4, w4, w12
	add w8, w8, w4
	ror w12, w5, #2
	eor w12, w12, w5, ror #13
	eor w12, w12, w5, ror #22
	add w4, w4, w12
	eor w14, w5, w6
	and w13, w13, w14
	eor w13, w13, w6
	add w4, w4, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #0]
	ldr w12, [x3, #4]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #36]
	add w16, w16, w12
	str w16, [x3, #0]
	ldr q16, [x15, #128]
	umov w12, v16.s[0]
	add w11, w11, w16
	add w11, w11, w12
	ror w12, w8, #6
	eor w12, w12, w8, ror #11
	eor w12, w12, w8, ror #25
	add w11, w11, w12
	eor w12, w9, w10
	and w12, w12, w8
	eor w12, w12, w10
	add w11, w11, w12
	add w7, w7, w11
	ror w12, w4, #2
	eor w12, w12, w4, ror #13
	eor w12, w12, w4, ror #22
	add w11, w11, w12
	eor w13, w4, w5
	and w14, w14, w13
	eor w14, w14, w5
	add w11, w11, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #4]
	ldr w12, [x3, #8]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #40]
	add w17, w17, w12
	str w17, [x3, #4]
	umov w12, v16.s[1]
	add w10, w10, w17
	add w10, w10, w12
	ror w12, w7, #6
	eor w12, w12, w7, ror #11
	eor w12, w12, w7, ror #25
	add w10, w10, w12
	eor w12, w8, w9
	and w12, w12, w7
	eor w12, w12, w9
	add w10, w10, w12
	add w6, w6, w10
	ror w12, w11, #2
	eor w12, w12, w11, ror #13
	eor w12, w12, w11, ror #22
	add w10, w10, w12
	eor w14, w11, w4
	and w13, w13, w14
	eor w13, w13, w4
	add w10, w10, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #8]
	ldr w12, [x3, #12]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #44]
	add w16, w16, w12
	str w16, [x3, #8]
	umov w12, v16.s[2]
	add w9, w9, w16
	add w9, w9, w12
	ror w12, w6, #6
	eor w12, w12, w6, ror #11
	eor w12, w12, w6, ror #25
	add w9, w9, w12
	eor w12, w7, w8
	and w12, w12, w6
	eor w12, w12, w8
	add w9, w9, w12
	add w5, w5, w9
	ror w12, w10, #2
	eor w12, w12, w10, ror #13
	eor w12, w12, w10, ror #22
	add w9, w9, w12
	eor w13, w10, w11
	and w14, w14, w13
	eor w14, w14, w11
	add w9, w9, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #12]
	ldr w12, [x3, #16]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #48]
	add w17, w17, w12
	str w17, [x3, #12]
	umov w12, v16.s[3]
	add w8, w8, w17
	add w8, w8, w12
	ror w12, w5, #6
	eor w12, w12, w5, ror #11
	eor w12, w12, w5, ror #25
	add w8, w8, w12
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w8, w8, w12
	add w4, w4, w8
	ror w12, w9, #2
	eor w12, w12, w9, ror #13
	eor w12, w12, w9, ror #22
	add w8, w8, w12
	eor w14, w9, w10
	and w13, w13, w14
	eor w13, w13, w10
	add w8, w8, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #16]
	ldr w12, [x3, #20]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #52]
	add w16, w16, w12
	str w16, [x3, #16]
	ldr q16, [x15, #144]
	umov w12, v16.s[0]
	add w7, w7, w16
	add w7, w7, w12
	ror w12, w4, #6
	eor w12, w12, w4, ror #11
	eor w12, w12, w4, ror #25
	add w7, w7, w12
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	add w11, w11, w7
	ror w12, w8, #2
	eor w12, w12, w8, ror #13
	eor w12, w12, w8, ror #22
	add w7, w7, w12
	eor w13, w8, w9
	and w14, w14, w13
	eor w14, w14, w9
	add w7, w7, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #20]
	ldr w12, [x3, #24]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #56]
	add w17, w17, w12
	str w17, [x3, #20]
	umov w12, v16.s[1]
	add w6, w6, w17
	add w6, w6, w12
	ror w12, w11, #6
	eor w12, w12, w11, ror #11
	eor w12, w12, w11, ror #25
	add w6, w6, w12
	eor w12, w4, w5
	and w12, w12, w11
	eor w12, w12, w5
	add w6, w6, w12
	add w10, w10, w6
	ror w12, w7, #2
	eor w12, w12, w7, ror #13
	eor w12, w12, w7, ror #22
	add w6, w6, w12
	eor w14, w7, w8
	and w13, w13, w14
	eor w13, w13, w8
	add w6, w6, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #24]
	ldr w12, [x3, #28]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #60]
	add w16, w16, w12
	str w16, [x3, #24]
	umov w12, v16.s[2]
	add w5, w5, w16
	add w5, w5, w12
	ror w12, w10, #6
	eor w12, w12, w10, ror #11
	eor w12, w12, w10, ror #25
	add w5, w5, w12
	eor w12, w11, w4
	and w12, w12, w10
	eor w12, w12, w4
	add w5, w5, w12
	add w9, w9, w5
	ror w12, w6, #2
	eor w12, w12, w6, ror #13
	eor w12, w12, w6, ror #22
	add w5, w5, w12
	eor w13, w6, w7
	and w14, w14, w13
	eor w14, w14, w7
	add w5, w5, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #28]
	ldr w12, [x3, #32]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #0]
	add w17, w17, w12
	str w17, [x3, #28]
	umov w12, v16.s[3]
	add w4, w4, w17
	add w4, w4, w12
	ror w12, w9, #6
	eor w12, w12, w9, ror #11
	eor w12, w12, w9, ror #25
	add w4, w4, w12
	eor w12, w10, w11
	and w12, w12, w9
	eor w12, w12, w11
	add w4, w4, w12
	add w8, w8, w4
	ror w12, w5, #2
	eor w12, w12, w5, ror #13
	eor w12, w12, w5, ror #22
	add w4, w4, w12
	eor w14, w5, w6
	and w13, w13, w14
	eor w13, w13, w6
	add w4, w4, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #32]
	ldr w12, [x3, #36]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #4]
	add w16, w16, w12
	str w16, [x3, #32]
	ldr q16, [x15, #160]
	umov w12, v16.s[0]
	add w11, w11, w16
	add w11, w11, w12
	ror w12, w8, #6
	eor w12, w12, w8, ror #11
	eor w12, w12, w8, ror #25
	add w11, w11, w12
	eor w12, w9, w10
	and w12, w12, w8
	eor w12, w12, w10
	add w11, w11, w12
	add w7, w7, w11
	ror w12, w4, #2
	eor w12, w12, w4, ror #13
	eor w12, w12, w4, ror #22
	add w11, w11, w12
	eor w13, w4, w5
	and w14, w14, w13
	eor w14, w14, w5
	add w11, w11, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #36]
	ldr w12, [x3, #40]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #8]
	add w17, w17, w12
	str w17, [x3, #36]
	umov w12, v16.s[1]
	add w10, w10, w17
	add w10, w10, w12
	ror w12, w7, #6
	eor w12, w12, w7, ror #11
	eor w12, w12, w7, ror #25
	add w10, w10, w12
	eor w12, w8, w9
	and w12, w12, w7
	eor w12, w12, w9
	add w10, w10, w12
	add w6, w6, w10
	ror w12, w11, #2
	eor w12, w12, w11, ror #13
	eor w12, w12, w11, ror #22
	add w10, w10, w12
	eor w14, w11, w4
	and w13, w13, w14
	eor w13, w13, w4
	add w10, w10, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #40]
	ldr w12, [x3, #44]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #12]
	add w16, w16, w12
	str w16, [x3, #40]
	umov w12, v16.s[2]
	add w9, w9, w16
	add w9, w9, w12
	ror w12, w6, #6
	eor w12, w12, w6, ror #11
	eor w12, w12, w6, ror #25
	add w9, w9, w12
	eor w12, w7, w8
	and w12, w12, w6
	eor w12, w12, w8
	add w9, w9, w12
	add w5, w5, w9
	ror w12, w10, #2
	eor w12, w12, w10, ror #13
	eor w12, w12, w10, ror #22
	add w9, w9, w12
	eor w13, w10, w11
	and w14, w14, w13
	eor w14, w14, w11
	add w9, w9, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #44]
	ldr w12, [x3, #48]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #16]
	add w17, w17, w12
	str w17, [x3, #44]
	umov w12, v16.s[3]
	add w8, w8, w17
	add w8, w8, w12
	ror w12, w5, #6
	eor w12, w12, w5, ror #11
	eor w12, w12, w5, ror #25
	add w8, w8, w12
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w8, w8, w12
	add w4, w4, w8
	ror w12, w9, #2
	eor w12, w12, w9, ror #13
	eor w12, w12, w9, ror #22
	add w8, w8, w12
	eor w14, w9, w10
	and w13, w13, w14
	eor w13, w13, w10
	add w8, w8, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #48]
	ldr w12, [x3, #52]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #20]
	add w16, w16, w12
	str w16, [x3, #48]
	ldr q16, [x15, #176]
	umov w12, v16.s[0]
	add w7, w7, w16
	add w7, w7, w12
	ror w12, w4, #6
	eor w12, w12, w4, ror #11
	eor w12, w12, w4, ror #25
	add w7, w7, w12
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	add w11, w11, w7
	ror w12, w8, #2
	eor w12, w12, w8, ror #13
	eor w12, w12, w8, ror #22
	add w7, w7, w12
	eor w13, w8, w9
	and w14, w14, w13
	eor w14, w14, w9
	add w7, w7, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #52]
	ldr w12, [x3, #56]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #24]
	add w17, w17, w12
	str w17, [x3, #52]
	umov w12, v16.s[1]
	add w6, w6, w17
	add w6, w6, w12
	ror w12, w11, #6
	eor w12, w12, w11, ror #11
	eor w12, w12, w11, ror #25
	add w6, w6, w12
	eor w12, w4, w5
	and w12, w12, w11
	eor w12, w12, w5
	add w6, w6, w12
	add w10, w10, w6
	ror w12, w7, #2
	eor w12, w12, w7, ror #13
	eor w12, w12, w7, ror #22
	add w6, w6, w12
	eor w14, w7, w8
	and w13, w13, w14
	eor w13, w13, w8
	add w6, w6, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #56]
	ldr w12, [x3, #60]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #28]
	add w16, w16, w12
	str w16, [x3, #56]
	umov w12, v16.s[2]
	add w5, w5, w16
	add w5, w5, w12
	ror w12, w10, #6
	eor w12, w12, w10, ror #11
	eor w12, w12, w10, ror #25
	add w5, w5, w12
	eor w12, w11, w4
	and w12, w12, w10
	eor w12, w12, w4
	add w5, w5, w12
	add w9, w9, w5
	ror w12, w6, #2
	eor w12, w12, w6, ror #13
	eor w12, w12, w6, ror #22
	add w5, w5, w12
	eor w13, w6, w7
	and w14, w14, w13
	eor w14, w14, w7
	add w5, w5, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #60]
	ldr w12, [x3, #0]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #32]
	add w17, w17, w12
	str w17, [x3, #60]
	umov w12, v16.s[3]
	add w4, w4, w17
	add w4, w4, w12
	ror w12, w9, #6
	eor w12, w12, w9, ror #11
	eor w12, w12, w9, ror #25
	add w4, w4, w12
	eor w12, w10, w11
	and w12, w12, w9
	eor w12, w12, w11
	add w4, w4, w12
	add w8, w8, w4
	ror w12, w5, #2
	eor w12, w12, w5, ror #13
	eor w12, w12, w5, ror #22
	add w4, w4, w12
	eor w14, w5, w6
	and w13, w13, w14
	eor w13, w13, w6
	add w4, w4, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #0]
	ldr w12, [x3, #4]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #36]
	add w16, w16, w12
	str w16, [x3, #0]
	ldr q16, [x15, #192]
	umov w12, v16.s[0]
	add w11, w11, w16
	add w11, w11, w12
	ror w12, w8, #6
	eor w12, w12, w8, ror #11
	eor w12, w12, w8, ror #25
	add w11, w11, w12
	eor w12, w9, w10
	and w12, w12, w8
	eor w12, w12, w10
	add w11, w11, w12
	add w7, w7, w11
	ror w12, w4, #2
	eor w12, w12, w4, ror #13
	eor w12, w12, w4, ror #22
	add w11, w11, w12
	eor w13, w4, w5
	and w14, w14, w13
	eor w14, w14, w5
	add w11, w11, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #4]
	ldr w12, [x3, #8]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #40]
	add w17, w17, w12
	str w17, [x3, #4]
	umov w12, v16.s[1]
	add w10, w10, w17
	add w10, w10, w12
	ror w12, w7, #6
	eor w12, w12, w7, ror #11
	eor w12, w12, w7, ror #25
	add w10, w10, w12
	eor w12, w8, w9
	and w12, w12, w7
	eor w12, w12, w9
	add w10, w10, w12
	add w6, w6, w10
	ror w12, w11, #2
	eor w12, w12, w11, ror #13
	eor w12, w12, w11, ror #22
	add w10, w10, w12
	eor w14, w11, w4
	and w13, w13, w14
	eor w13, w13, w4
	add w10, w10, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #8]
	ldr w12, [x3, #12]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #44]
	add w16, w16, w12
	str w16, [x3, #8]
	umov w12, v16.s[2]
	add w9, w9, w16
	add w9, w9, w12
	ror w12, w6, #6
	eor w12, w12, w6, ror #11
	eor w12, w12, w6, ror #25
	add w9, w9, w12
	eor w12, w7, w8
	and w12, w12, w6
	eor w12, w12, w8
	add w9, w9, w12
	add w5, w5, w9
	ror w12, w10, #2
	eor w12, w12, w10, ror #13
	eor w12, w12, w10, ror #22
	add w9, w9, w12
	eor w13, w10, w11
	and w14, w14, w13
	eor w14, w14, w11
	add w9, w9, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #12]
	ldr w12, [x3, #16]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #48]
	add w17, w17, w12
	str w17, [x3, #12]
	umov w12, v16.s[3]
	add w8, w8, w17
	add w8, w8, w12
	ror w12, w5, #6
	eor w12, w12, w5, ror #11
	eor w12, w12, w5, ror #25
	add w8, w8, w12
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w8, w8, w12
	add w4, w4, w8
	ror w12, w9, #2
	eor w12, w12, w9, ror #13
	eor w12, w12, w9, ror #22
	add w8, w8, w12
	eor w14, w9, w10
	and w13, w13, w14
	eor w13, w13, w10
	add w8, w8, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #16]
	ldr w12, [x3, #20]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #52]
	add w16, w16, w12
	str w16, [x3, #16]
	ldr q16, [x15, #208]
	umov w12, v16.s[0]
	add w7, w7, w16
	add w7, w7, w12
	ror w12, w4, #6
	eor w12, w12, w4, ror #11
	eor w12, w12, w4, ror #25
	add w7, w7, w12
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	add w11, w11, w7
	ror w12, w8, #2
	eor w12, w12, w8, ror #13
	eor w12, w12, w8, ror #22
	add w7, w7, w12
	eor w13, w8, w9
	and w14, w14, w13
	eor w14, w14, w9
	add w7, w7, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #20]
	ldr w12, [x3, #24]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #56]
	add w17, w17, w12
	str w17, [x3, #20]
	umov w12, v16.s[1]
	add w6, w6, w17
	add w6, w6, w12
	ror w12, w11, #6
	eor w12, w12, w11, ror #11
	eor w12, w12, w11, ror #25
	add w6, w6, w12
	eor w12, w4, w5
	and w12, w12, w11
	eor w12, w12, w5
	add w6, w6, w12
	add w10, w10, w6
	ror w12, w7, #2
	eor w12, w12, w7, ror #13
	eor w12, w12, w7, ror #22
	add w6, w6, w12
	eor w14, w7, w8
	and w13, w13, w14
	eor w13, w13, w8
	add w6, w6, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #24]
	ldr w12, [x3, #28]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #60]
	add w16, w16, w12
	str w16, [x3, #24]
	umov w12, v16.s[2]
	add w5, w5, w16
	add w5, w5, w12
	ror w12, w10, #6
	eor w12, w12, w10, ror #11
	eor w12, w12, w10, ror #25
	add w5, w5, w12
	eor w12, w11, w4
	and w12, w12, w10
	eor w12, w12, w4
	add w5, w5, w12
	add w9, w9, w5
	ror w12, w6, #2
	eor w12, w12, w6, ror #13
	eor w12, w12, w6, ror #22
	add w5, w5, w12
	eor w13, w6, w7
	and w14, w14, w13
	eor w14, w14, w7
	add w5, w5, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #28]
	ldr w12, [x3, #32]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #0]
	add w17, w17, w12
	str w17, [x3, #28]
	umov w12, v16.s[3]
	add w4, w4, w17
	add w4, w4, w12
	ror w12, w9, #6
	eor w12, w12, w9, ror #11
	eor w12, w12, w9, ror #25
	add w4, w4, w12
	eor w12, w10, w11
	and w12, w12, w9
	eor w12, w12, w11
	add w4, w4, w12
	add w8, w8, w4
	ror w12, w5, #2
	eor w12, w12, w5, ror #13
	eor w12, w12, w5, ror #22
	add w4, w4, w12
	eor w14, w5, w6
	and w13, w13, w14
	eor w13, w13, w6
	add w4, w4, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #32]
	ldr w12, [x3, #36]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #4]
	add w16, w16, w12
	str w16, [x3, #32]
	ldr q16, [x15, #224]
	umov w12, v16.s[0]
	add w11, w11, w16
	add w11, w11, w12
	ror w12, w8, #6
	eor w12, w12, w8, ror #11
	eor w12, w12, w8, ror #25
	add w11, w11, w12
	eor w12, w9, w10
	and w12, w12, w8
	eor w12, w12, w10
	add w11, w11, w12
	add w7, w7, w11
	ror w12, w4, #2
	eor w12, w12, w4, ror #13
	eor w12, w12, w4, ror #22
	add w11, w11, w12
	eor w13, w4, w5
	and w14, w14, w13
	eor w14, w14, w5
	add w11, w11, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #36]
	ldr w12, [x3, #40]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #8]
	add w17, w17, w12
	str w17, [x3, #36]
	umov w12, v16.s[1]
	add w10, w10, w17
	add w10, w10, w12
	ror w12, w7, #6
	eor w12, w12, w7, ror #11
	eor w12, w12, w7, ror #25
	add w10, w10, w12
	eor w12, w8, w9
	and w12, w12, w7
	eor w12, w12, w9
	add w10, w10, w12
	add w6, w6, w10
	ror w12, w11, #2
	eor w12, w12, w11, ror #13
	eor w12, w12, w11, ror #22
	add w10, w10, w12
	eor w14, w11, w4
	and w13, w13, w14
	eor w13, w13, w4
	add w10, w10, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #40]
	ldr w12, [x3, #44]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #12]
	add w16, w16, w12
	str w16, [x3, #40]
	umov w12, v16.s[2]
	add w9, w9, w16
	add w9, w9, w12
	ror w12, w6, #6
	eor w12, w12, w6, ror #11
	eor w12, w12, w6, ror #25
	add w9, w9, w12
	eor w12, w7, w8
	and w12, w12, w6
	eor w12, w12, w8
	add w9, w9, w12
	add w5, w5, w9
	ror w12, w10, #2
	eor w12, w12, w10, ror #13
	eor w12, w12, w10, ror #22
	add w9, w9, w12
	eor w13, w10, w11
	and w14, w14, w13
	eor w14, w14, w11
	add w9, w9, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #44]
	ldr w12, [x3, #48]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #16]
	add w17, w17, w12
	str w17, [x3, #44]
	umov w12, v16.s[3]
	add w8, w8, w17
	add w8, w8, w12
	ror w12, w5, #6
	eor w12, w12, w5, ror #11
	eor w12, w12, w5, ror #25
	add w8, w8, w12
	eor w12, w6, w7
	and w12, w12, w5
	eor w12, w12, w7
	add w8, w8, w12
	add w4, w4, w8
	ror w12, w9, #2
	eor w12, w12, w9, ror #13
	eor w12, w12, w9, ror #22
	add w8, w8, w12
	eor w14, w9, w10
	and w13, w13, w14
	eor w13, w13, w10
	add w8, w8, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #48]
	ldr w12, [x3, #52]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #20]
	add w16, w16, w12
	str w16, [x3, #48]
	ldr q16, [x15, #240]
	umov w12, v16.s[0]
	add w7, w7, w16
	add w7, w7, w12
	ror w12, w4, #6
	eor w12, w12, w4, ror #11
	eor w12, w12, w4, ror #25
	add w7, w7, w12
	eor w12, w5, w6
	and w12, w12, w4
	eor w12, w12, w6
	add w7, w7, w12
	add w11, w11, w7
	ror w12, w8, #2
	eor w12, w12, w8, ror #13
	eor w12, w12, w8, ror #22
	add w7, w7, w12
	eor w13, w8, w9
	and w14, w14, w13
	eor w14, w14, w9
	add w7, w7, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #52]
	ldr w12, [x3, #56]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #24]
	add w17, w17, w12
	str w17, [x3, #52]
	umov w12, v16.s[1]
	add w6, w6, w17
	add w6, w6, w12
	ror w12, w11, #6
	eor w12, w12, w11, ror #11
	eor w12, w12, w11, ror #25
	add w6, w6, w12
	eor w12, w4, w5
	and w12, w12, w11
	eor w12, w12, w5
	add w6, w6, w12
	add w10, w10, w6
	ror w12, w7, #2
	eor w12, w12, w7, ror #13
	eor w12, w12, w7, ror #22
	add w6, w6, w12
	eor w14, w7, w8
	and w13, w13, w14
	eor w13, w13, w8
	add w6, w6, w13
	lsr w13, w16, #10
	eor w13, w13, w16, ror #17
	eor w13, w13, w16, ror #19
	ldr w16, [x3, #56]
	ldr w12, [x3, #60]
	add w16, w16, w13
	lsr w13, w12, #3
	eor w13, w13, w12, ror #7
	eor w13, w13, w12, ror #18
	add w16, w16, w13
	ldr w12, [x3, #28]
	add w16, w16, w12
	str w16, [x3, #56]
	umov w12, v16.s[2]
	add w5, w5, w16
	add w5, w5, w12
	ror w12, w10, #6
	eor w12, w12, w10, ror #11
	eor w12, w12, w10, ror #25
	add w5, w5, w12
	eor w12, w11, w4
	and w12, w12, w10
	eor w12, w12, w4
	add w5, w5, w12
	add w9, w9, w5
	ror w12, w6, #2
	eor w12, w12, w6, ror #13
	eor w12, w12, w6, ror #22
	add w5, w5, w12
	eor w13, w6, w7
	and w14, w14, w13
	eor w14, w14, w7
	add w5, w5, w14
	lsr w14, w17, #10
	eor w14, w14, w17, ror #17
	eor w14, w14, w17, ror #19
	ldr w17, [x3, #60]
	ldr w12, [x3, #0]
	add w17, w17, w14
	lsr w14, w12, #3
	eor w14, w14, w12, ror #7
	eor w14, w14, w12, ror #18
	add w17, w17, w14
	ldr w12, [x3, #32]
	add w17, w17, w12
	str w17, [x3, #60]
	umov w12, v16.s[3]
	add w4, w4, w17
	add w4, w4, w12
	ror w12, w9, #6
	eor w12, w12, w9, ror #11
	eor w12, w12, w9, ror #25
	add w4, w4, w12
	eor w12, w10, w11
	and w12, w12, w9
	eor w12, w12, w11
	add w4, w4, w12
	add w8, w8, w4
	ror w12, w5, #2
	eor w12, w12, w5, ror #13
	eor w12, w12, w5, ror #22
	add w4, w4, w12
	eor w14, w5, w6
	and w13, w13, w14
	eor w13, w13, w6
	add w4, w4, w13
	ldr w12, [x0, #0]
	ldr w13, [x0, #4]
	ldr w14, [x0, #8]
	ldr w16, [x0, #12]
	add w4, w4, w12
	add w5, w5, w13
	add w6, w6, w14
	add w7, w7, w16
	ldr w12, [x0, #16]
	ldr w13, [x0, #20]
	ldr w14, [x0, #24]
	ldr w16, [x0, #28]
	add w8, w8, w12
	add w9, w9, w13
	add w10, w10, w14
	add w11, w11, w16
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
