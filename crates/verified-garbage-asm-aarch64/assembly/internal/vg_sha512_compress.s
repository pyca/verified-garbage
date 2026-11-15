// The functions of `src/internal/vg_sha512_compress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress:
	cbz x2, 20f
	adrp x15, {VG_SHA512_K}
	add x15, x15, {VG_SHA512_K}
22:
	ldr x4, [x0, #0]
	ldr x5, [x0, #8]
	ldr x6, [x0, #16]
	ldr x7, [x0, #24]
	ldr x8, [x0, #32]
	ldr x9, [x0, #40]
	ldr x10, [x0, #48]
	ldr x11, [x0, #56]
	eor x14, x5, x6
	ldr x16, [x1, #0]
	rev x16, x16
	str x16, [x3, #0]
	ldr q16, [x15, #0]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	ldr x17, [x1, #8]
	rev x17, x17
	str x17, [x3, #8]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	ldr x16, [x1, #16]
	rev x16, x16
	str x16, [x3, #16]
	ldr q16, [x15, #16]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	ldr x17, [x1, #24]
	rev x17, x17
	str x17, [x3, #24]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	ldr x16, [x1, #32]
	rev x16, x16
	str x16, [x3, #32]
	ldr q16, [x15, #32]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	ldr x17, [x1, #40]
	rev x17, x17
	str x17, [x3, #40]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	ldr x16, [x1, #48]
	rev x16, x16
	str x16, [x3, #48]
	ldr q16, [x15, #48]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	ldr x17, [x1, #56]
	rev x17, x17
	str x17, [x3, #56]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	ldr x16, [x1, #64]
	rev x16, x16
	str x16, [x3, #64]
	ldr q16, [x15, #64]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	ldr x17, [x1, #72]
	rev x17, x17
	str x17, [x3, #72]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	ldr x16, [x1, #80]
	rev x16, x16
	str x16, [x3, #80]
	ldr q16, [x15, #80]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	ldr x17, [x1, #88]
	rev x17, x17
	str x17, [x3, #88]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	ldr x16, [x1, #96]
	rev x16, x16
	str x16, [x3, #96]
	ldr q16, [x15, #96]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	ldr x17, [x1, #104]
	rev x17, x17
	str x17, [x3, #104]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	ldr x16, [x1, #112]
	rev x16, x16
	str x16, [x3, #112]
	ldr q16, [x15, #112]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	ldr x17, [x1, #120]
	rev x17, x17
	str x17, [x3, #120]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #0]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #72]
	add x16, x16, x12
	str x16, [x3, #0]
	ldr q16, [x15, #128]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #8]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #80]
	add x17, x17, x12
	str x17, [x3, #8]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #16]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #88]
	add x16, x16, x12
	str x16, [x3, #16]
	ldr q16, [x15, #144]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #24]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #96]
	add x17, x17, x12
	str x17, [x3, #24]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #32]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #104]
	add x16, x16, x12
	str x16, [x3, #32]
	ldr q16, [x15, #160]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #40]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #112]
	add x17, x17, x12
	str x17, [x3, #40]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #48]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #120]
	add x16, x16, x12
	str x16, [x3, #48]
	ldr q16, [x15, #176]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #56]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #0]
	add x17, x17, x12
	str x17, [x3, #56]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #64]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #8]
	add x16, x16, x12
	str x16, [x3, #64]
	ldr q16, [x15, #192]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #72]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #16]
	add x17, x17, x12
	str x17, [x3, #72]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #80]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #24]
	add x16, x16, x12
	str x16, [x3, #80]
	ldr q16, [x15, #208]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #88]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #32]
	add x17, x17, x12
	str x17, [x3, #88]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #96]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #40]
	add x16, x16, x12
	str x16, [x3, #96]
	ldr q16, [x15, #224]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #104]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #48]
	add x17, x17, x12
	str x17, [x3, #104]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #112]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #56]
	add x16, x16, x12
	str x16, [x3, #112]
	ldr q16, [x15, #240]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldr x17, [x3, #120]
	ldr x12, [x3, #0]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #64]
	add x17, x17, x12
	str x17, [x3, #120]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #0]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #72]
	add x16, x16, x12
	str x16, [x3, #0]
	ldr q16, [x15, #256]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #8]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #80]
	add x17, x17, x12
	str x17, [x3, #8]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #16]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #88]
	add x16, x16, x12
	str x16, [x3, #16]
	ldr q16, [x15, #272]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #24]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #96]
	add x17, x17, x12
	str x17, [x3, #24]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #32]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #104]
	add x16, x16, x12
	str x16, [x3, #32]
	ldr q16, [x15, #288]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #40]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #112]
	add x17, x17, x12
	str x17, [x3, #40]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #48]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #120]
	add x16, x16, x12
	str x16, [x3, #48]
	ldr q16, [x15, #304]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #56]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #0]
	add x17, x17, x12
	str x17, [x3, #56]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #64]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #8]
	add x16, x16, x12
	str x16, [x3, #64]
	ldr q16, [x15, #320]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #72]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #16]
	add x17, x17, x12
	str x17, [x3, #72]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #80]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #24]
	add x16, x16, x12
	str x16, [x3, #80]
	ldr q16, [x15, #336]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #88]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #32]
	add x17, x17, x12
	str x17, [x3, #88]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #96]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #40]
	add x16, x16, x12
	str x16, [x3, #96]
	ldr q16, [x15, #352]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #104]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #48]
	add x17, x17, x12
	str x17, [x3, #104]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #112]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #56]
	add x16, x16, x12
	str x16, [x3, #112]
	ldr q16, [x15, #368]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldr x17, [x3, #120]
	ldr x12, [x3, #0]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #64]
	add x17, x17, x12
	str x17, [x3, #120]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #0]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #72]
	add x16, x16, x12
	str x16, [x3, #0]
	ldr q16, [x15, #384]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #8]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #80]
	add x17, x17, x12
	str x17, [x3, #8]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #16]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #88]
	add x16, x16, x12
	str x16, [x3, #16]
	ldr q16, [x15, #400]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #24]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #96]
	add x17, x17, x12
	str x17, [x3, #24]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #32]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #104]
	add x16, x16, x12
	str x16, [x3, #32]
	ldr q16, [x15, #416]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #40]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #112]
	add x17, x17, x12
	str x17, [x3, #40]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #48]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #120]
	add x16, x16, x12
	str x16, [x3, #48]
	ldr q16, [x15, #432]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #56]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #0]
	add x17, x17, x12
	str x17, [x3, #56]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #64]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #8]
	add x16, x16, x12
	str x16, [x3, #64]
	ldr q16, [x15, #448]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #72]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #16]
	add x17, x17, x12
	str x17, [x3, #72]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #80]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #24]
	add x16, x16, x12
	str x16, [x3, #80]
	ldr q16, [x15, #464]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #88]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #32]
	add x17, x17, x12
	str x17, [x3, #88]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #96]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #40]
	add x16, x16, x12
	str x16, [x3, #96]
	ldr q16, [x15, #480]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #104]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #48]
	add x17, x17, x12
	str x17, [x3, #104]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #112]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #56]
	add x16, x16, x12
	str x16, [x3, #112]
	ldr q16, [x15, #496]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldr x17, [x3, #120]
	ldr x12, [x3, #0]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #64]
	add x17, x17, x12
	str x17, [x3, #120]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #0]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #72]
	add x16, x16, x12
	str x16, [x3, #0]
	ldr q16, [x15, #512]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #8]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #80]
	add x17, x17, x12
	str x17, [x3, #8]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #16]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #88]
	add x16, x16, x12
	str x16, [x3, #16]
	ldr q16, [x15, #528]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #24]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #96]
	add x17, x17, x12
	str x17, [x3, #24]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #32]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #104]
	add x16, x16, x12
	str x16, [x3, #32]
	ldr q16, [x15, #544]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #40]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #112]
	add x17, x17, x12
	str x17, [x3, #40]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #48]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #120]
	add x16, x16, x12
	str x16, [x3, #48]
	ldr q16, [x15, #560]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #56]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #0]
	add x17, x17, x12
	str x17, [x3, #56]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #64]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #8]
	add x16, x16, x12
	str x16, [x3, #64]
	ldr q16, [x15, #576]
	umov x13, v16.d[0]
	ror x12, x8, #14
	eor x12, x12, x8, ror #18
	eor x12, x12, x8, ror #41
	add x11, x11, x12
	eor x12, x9, x10
	and x12, x12, x8
	eor x12, x12, x10
	add x11, x11, x12
	add x11, x11, x13
	add x11, x11, x16
	add x7, x7, x11
	ror x12, x4, #28
	eor x12, x12, x4, ror #34
	eor x12, x12, x4, ror #39
	add x11, x11, x12
	eor x13, x4, x5
	and x14, x14, x13
	eor x14, x14, x5
	add x11, x11, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #72]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #16]
	add x17, x17, x12
	str x17, [x3, #72]
	umov x14, v16.d[1]
	ror x12, x7, #14
	eor x12, x12, x7, ror #18
	eor x12, x12, x7, ror #41
	add x10, x10, x12
	eor x12, x8, x9
	and x12, x12, x7
	eor x12, x12, x9
	add x10, x10, x12
	add x10, x10, x14
	add x10, x10, x17
	add x6, x6, x10
	ror x12, x11, #28
	eor x12, x12, x11, ror #34
	eor x12, x12, x11, ror #39
	add x10, x10, x12
	eor x14, x11, x4
	and x13, x13, x14
	eor x13, x13, x4
	add x10, x10, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #80]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #24]
	add x16, x16, x12
	str x16, [x3, #80]
	ldr q16, [x15, #592]
	umov x13, v16.d[0]
	ror x12, x6, #14
	eor x12, x12, x6, ror #18
	eor x12, x12, x6, ror #41
	add x9, x9, x12
	eor x12, x7, x8
	and x12, x12, x6
	eor x12, x12, x8
	add x9, x9, x12
	add x9, x9, x13
	add x9, x9, x16
	add x5, x5, x9
	ror x12, x10, #28
	eor x12, x12, x10, ror #34
	eor x12, x12, x10, ror #39
	add x9, x9, x12
	eor x13, x10, x11
	and x14, x14, x13
	eor x14, x14, x11
	add x9, x9, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #88]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #32]
	add x17, x17, x12
	str x17, [x3, #88]
	umov x14, v16.d[1]
	ror x12, x5, #14
	eor x12, x12, x5, ror #18
	eor x12, x12, x5, ror #41
	add x8, x8, x12
	eor x12, x6, x7
	and x12, x12, x5
	eor x12, x12, x7
	add x8, x8, x12
	add x8, x8, x14
	add x8, x8, x17
	add x4, x4, x8
	ror x12, x9, #28
	eor x12, x12, x9, ror #34
	eor x12, x12, x9, ror #39
	add x8, x8, x12
	eor x14, x9, x10
	and x13, x13, x14
	eor x13, x13, x10
	add x8, x8, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #96]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #40]
	add x16, x16, x12
	str x16, [x3, #96]
	ldr q16, [x15, #608]
	umov x13, v16.d[0]
	ror x12, x4, #14
	eor x12, x12, x4, ror #18
	eor x12, x12, x4, ror #41
	add x7, x7, x12
	eor x12, x5, x6
	and x12, x12, x4
	eor x12, x12, x6
	add x7, x7, x12
	add x7, x7, x13
	add x7, x7, x16
	add x11, x11, x7
	ror x12, x8, #28
	eor x12, x12, x8, ror #34
	eor x12, x12, x8, ror #39
	add x7, x7, x12
	eor x13, x8, x9
	and x14, x14, x13
	eor x14, x14, x9
	add x7, x7, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldp x17, x12, [x3, #104]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #48]
	add x17, x17, x12
	str x17, [x3, #104]
	umov x14, v16.d[1]
	ror x12, x11, #14
	eor x12, x12, x11, ror #18
	eor x12, x12, x11, ror #41
	add x6, x6, x12
	eor x12, x4, x5
	and x12, x12, x11
	eor x12, x12, x5
	add x6, x6, x12
	add x6, x6, x14
	add x6, x6, x17
	add x10, x10, x6
	ror x12, x7, #28
	eor x12, x12, x7, ror #34
	eor x12, x12, x7, ror #39
	add x6, x6, x12
	eor x14, x7, x8
	and x13, x13, x14
	eor x13, x13, x8
	add x6, x6, x13
	lsr x13, x16, #6
	eor x13, x13, x16, ror #19
	eor x13, x13, x16, ror #61
	ldp x16, x12, [x3, #112]
	add x16, x16, x13
	lsr x13, x12, #7
	eor x13, x13, x12, ror #1
	eor x13, x13, x12, ror #8
	add x16, x16, x13
	ldr x12, [x3, #56]
	add x16, x16, x12
	str x16, [x3, #112]
	ldr q16, [x15, #624]
	umov x13, v16.d[0]
	ror x12, x10, #14
	eor x12, x12, x10, ror #18
	eor x12, x12, x10, ror #41
	add x5, x5, x12
	eor x12, x11, x4
	and x12, x12, x10
	eor x12, x12, x4
	add x5, x5, x12
	add x5, x5, x13
	add x5, x5, x16
	add x9, x9, x5
	ror x12, x6, #28
	eor x12, x12, x6, ror #34
	eor x12, x12, x6, ror #39
	add x5, x5, x12
	eor x13, x6, x7
	and x14, x14, x13
	eor x14, x14, x7
	add x5, x5, x14
	lsr x14, x17, #6
	eor x14, x14, x17, ror #19
	eor x14, x14, x17, ror #61
	ldr x17, [x3, #120]
	ldr x12, [x3, #0]
	add x17, x17, x14
	lsr x14, x12, #7
	eor x14, x14, x12, ror #1
	eor x14, x14, x12, ror #8
	add x17, x17, x14
	ldr x12, [x3, #64]
	add x17, x17, x12
	str x17, [x3, #120]
	umov x14, v16.d[1]
	ror x12, x9, #14
	eor x12, x12, x9, ror #18
	eor x12, x12, x9, ror #41
	add x4, x4, x12
	eor x12, x10, x11
	and x12, x12, x9
	eor x12, x12, x11
	add x4, x4, x12
	add x4, x4, x14
	add x4, x4, x17
	add x8, x8, x4
	ror x12, x5, #28
	eor x12, x12, x5, ror #34
	eor x12, x12, x5, ror #39
	add x4, x4, x12
	eor x14, x5, x6
	and x13, x13, x14
	eor x13, x13, x6
	add x4, x4, x13
	ldr x12, [x0, #0]
	ldr x13, [x0, #8]
	ldr x14, [x0, #16]
	ldr x16, [x0, #24]
	add x4, x4, x12
	add x5, x5, x13
	add x6, x6, x14
	add x7, x7, x16
	ldr x12, [x0, #32]
	ldr x13, [x0, #40]
	ldr x14, [x0, #48]
	ldr x16, [x0, #56]
	add x8, x8, x12
	add x9, x9, x13
	add x10, x10, x14
	add x11, x11, x16
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
