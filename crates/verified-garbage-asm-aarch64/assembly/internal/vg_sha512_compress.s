// The functions of `src/internal/vg_sha512_compress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_compress:
	cbz x2, 20f
	mov v18.d[0], x19
	mov v18.d[1], x20
	mov v19.d[0], x21
	mov v19.d[1], x22
	mov v20.d[0], x23
	mov v20.d[1], x24
	mov v21.d[0], x25
	mov v21.d[1], x26
	mov v22.d[0], x27
	mov v22.d[1], x28
	mov v16.d[0], x0
	mov v16.d[1], x1
	mov v17.d[0], x2
	adrp x3, {VG_SHA512_K}
	add x3, x3, {VG_SHA512_K}
22:
	umov x0, v16.d[1]
	ldp x12, x13, [x0, #0]
	ldp x14, x15, [x0, #16]
	ldp x16, x17, [x0, #32]
	ldp x19, x20, [x0, #48]
	ldp x21, x22, [x0, #64]
	ldp x23, x24, [x0, #80]
	ldp x25, x26, [x0, #96]
	ldp x27, x28, [x0, #112]
	rev x12, x12
	rev x13, x13
	rev x14, x14
	rev x15, x15
	rev x16, x16
	rev x17, x17
	rev x19, x19
	rev x20, x20
	rev x21, x21
	rev x22, x22
	rev x23, x23
	rev x24, x24
	rev x25, x25
	rev x26, x26
	rev x27, x27
	rev x28, x28
	add x0, x0, #128
	mov v16.d[1], x0
	umov x0, v16.d[0]
	ldp x4, x5, [x0, #0]
	ldp x6, x7, [x0, #16]
	ldp x8, x9, [x0, #32]
	ldp x10, x11, [x0, #48]
	eor x2, x5, x6
	ldr x0, [x3, #0]
	add x11, x11, x12
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	ldr x0, [x3, #8]
	add x10, x10, x13
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	ldr x0, [x3, #16]
	add x9, x9, x14
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	ldr x0, [x3, #24]
	add x8, x8, x15
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	ldr x0, [x3, #32]
	add x7, x7, x16
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	ldr x0, [x3, #40]
	add x6, x6, x17
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	ldr x0, [x3, #48]
	add x5, x5, x19
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	ldr x0, [x3, #56]
	add x4, x4, x20
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	ldr x0, [x3, #64]
	add x11, x11, x21
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	ldr x0, [x3, #72]
	add x10, x10, x22
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	ldr x0, [x3, #80]
	add x9, x9, x23
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	ldr x0, [x3, #88]
	add x8, x8, x24
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	ldr x0, [x3, #96]
	add x7, x7, x25
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	ldr x0, [x3, #104]
	add x6, x6, x26
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	ldr x0, [x3, #112]
	add x5, x5, x27
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	ldr x0, [x3, #120]
	add x4, x4, x28
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	lsr x0, x13, #7
	eor x0, x0, x13, ror #1
	eor x0, x0, x13, ror #8
	add x12, x12, x0
	lsr x0, x27, #6
	eor x0, x0, x27, ror #19
	eor x0, x0, x27, ror #61
	add x12, x12, x22
	add x12, x12, x0
	ldr x0, [x3, #128]
	add x11, x11, x12
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	lsr x0, x14, #7
	eor x0, x0, x14, ror #1
	eor x0, x0, x14, ror #8
	add x13, x13, x0
	lsr x0, x28, #6
	eor x0, x0, x28, ror #19
	eor x0, x0, x28, ror #61
	add x13, x13, x23
	add x13, x13, x0
	ldr x0, [x3, #136]
	add x10, x10, x13
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	lsr x0, x15, #7
	eor x0, x0, x15, ror #1
	eor x0, x0, x15, ror #8
	add x14, x14, x0
	lsr x0, x12, #6
	eor x0, x0, x12, ror #19
	eor x0, x0, x12, ror #61
	add x14, x14, x24
	add x14, x14, x0
	ldr x0, [x3, #144]
	add x9, x9, x14
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	lsr x0, x16, #7
	eor x0, x0, x16, ror #1
	eor x0, x0, x16, ror #8
	add x15, x15, x0
	lsr x0, x13, #6
	eor x0, x0, x13, ror #19
	eor x0, x0, x13, ror #61
	add x15, x15, x25
	add x15, x15, x0
	ldr x0, [x3, #152]
	add x8, x8, x15
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	lsr x0, x17, #7
	eor x0, x0, x17, ror #1
	eor x0, x0, x17, ror #8
	add x16, x16, x0
	lsr x0, x14, #6
	eor x0, x0, x14, ror #19
	eor x0, x0, x14, ror #61
	add x16, x16, x26
	add x16, x16, x0
	ldr x0, [x3, #160]
	add x7, x7, x16
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	lsr x0, x19, #7
	eor x0, x0, x19, ror #1
	eor x0, x0, x19, ror #8
	add x17, x17, x0
	lsr x0, x15, #6
	eor x0, x0, x15, ror #19
	eor x0, x0, x15, ror #61
	add x17, x17, x27
	add x17, x17, x0
	ldr x0, [x3, #168]
	add x6, x6, x17
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	lsr x0, x20, #7
	eor x0, x0, x20, ror #1
	eor x0, x0, x20, ror #8
	add x19, x19, x0
	lsr x0, x16, #6
	eor x0, x0, x16, ror #19
	eor x0, x0, x16, ror #61
	add x19, x19, x28
	add x19, x19, x0
	ldr x0, [x3, #176]
	add x5, x5, x19
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	lsr x0, x21, #7
	eor x0, x0, x21, ror #1
	eor x0, x0, x21, ror #8
	add x20, x20, x0
	lsr x0, x17, #6
	eor x0, x0, x17, ror #19
	eor x0, x0, x17, ror #61
	add x20, x20, x12
	add x20, x20, x0
	ldr x0, [x3, #184]
	add x4, x4, x20
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	lsr x0, x22, #7
	eor x0, x0, x22, ror #1
	eor x0, x0, x22, ror #8
	add x21, x21, x0
	lsr x0, x19, #6
	eor x0, x0, x19, ror #19
	eor x0, x0, x19, ror #61
	add x21, x21, x13
	add x21, x21, x0
	ldr x0, [x3, #192]
	add x11, x11, x21
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	lsr x0, x23, #7
	eor x0, x0, x23, ror #1
	eor x0, x0, x23, ror #8
	add x22, x22, x0
	lsr x0, x20, #6
	eor x0, x0, x20, ror #19
	eor x0, x0, x20, ror #61
	add x22, x22, x14
	add x22, x22, x0
	ldr x0, [x3, #200]
	add x10, x10, x22
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	lsr x0, x24, #7
	eor x0, x0, x24, ror #1
	eor x0, x0, x24, ror #8
	add x23, x23, x0
	lsr x0, x21, #6
	eor x0, x0, x21, ror #19
	eor x0, x0, x21, ror #61
	add x23, x23, x15
	add x23, x23, x0
	ldr x0, [x3, #208]
	add x9, x9, x23
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	lsr x0, x25, #7
	eor x0, x0, x25, ror #1
	eor x0, x0, x25, ror #8
	add x24, x24, x0
	lsr x0, x22, #6
	eor x0, x0, x22, ror #19
	eor x0, x0, x22, ror #61
	add x24, x24, x16
	add x24, x24, x0
	ldr x0, [x3, #216]
	add x8, x8, x24
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	lsr x0, x26, #7
	eor x0, x0, x26, ror #1
	eor x0, x0, x26, ror #8
	add x25, x25, x0
	lsr x0, x23, #6
	eor x0, x0, x23, ror #19
	eor x0, x0, x23, ror #61
	add x25, x25, x17
	add x25, x25, x0
	ldr x0, [x3, #224]
	add x7, x7, x25
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	lsr x0, x27, #7
	eor x0, x0, x27, ror #1
	eor x0, x0, x27, ror #8
	add x26, x26, x0
	lsr x0, x24, #6
	eor x0, x0, x24, ror #19
	eor x0, x0, x24, ror #61
	add x26, x26, x19
	add x26, x26, x0
	ldr x0, [x3, #232]
	add x6, x6, x26
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	lsr x0, x28, #7
	eor x0, x0, x28, ror #1
	eor x0, x0, x28, ror #8
	add x27, x27, x0
	lsr x0, x25, #6
	eor x0, x0, x25, ror #19
	eor x0, x0, x25, ror #61
	add x27, x27, x20
	add x27, x27, x0
	ldr x0, [x3, #240]
	add x5, x5, x27
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	lsr x0, x12, #7
	eor x0, x0, x12, ror #1
	eor x0, x0, x12, ror #8
	add x28, x28, x0
	lsr x0, x26, #6
	eor x0, x0, x26, ror #19
	eor x0, x0, x26, ror #61
	add x28, x28, x21
	add x28, x28, x0
	ldr x0, [x3, #248]
	add x4, x4, x28
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	lsr x0, x13, #7
	eor x0, x0, x13, ror #1
	eor x0, x0, x13, ror #8
	add x12, x12, x0
	lsr x0, x27, #6
	eor x0, x0, x27, ror #19
	eor x0, x0, x27, ror #61
	add x12, x12, x22
	add x12, x12, x0
	ldr x0, [x3, #256]
	add x11, x11, x12
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	lsr x0, x14, #7
	eor x0, x0, x14, ror #1
	eor x0, x0, x14, ror #8
	add x13, x13, x0
	lsr x0, x28, #6
	eor x0, x0, x28, ror #19
	eor x0, x0, x28, ror #61
	add x13, x13, x23
	add x13, x13, x0
	ldr x0, [x3, #264]
	add x10, x10, x13
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	lsr x0, x15, #7
	eor x0, x0, x15, ror #1
	eor x0, x0, x15, ror #8
	add x14, x14, x0
	lsr x0, x12, #6
	eor x0, x0, x12, ror #19
	eor x0, x0, x12, ror #61
	add x14, x14, x24
	add x14, x14, x0
	ldr x0, [x3, #272]
	add x9, x9, x14
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	lsr x0, x16, #7
	eor x0, x0, x16, ror #1
	eor x0, x0, x16, ror #8
	add x15, x15, x0
	lsr x0, x13, #6
	eor x0, x0, x13, ror #19
	eor x0, x0, x13, ror #61
	add x15, x15, x25
	add x15, x15, x0
	ldr x0, [x3, #280]
	add x8, x8, x15
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	lsr x0, x17, #7
	eor x0, x0, x17, ror #1
	eor x0, x0, x17, ror #8
	add x16, x16, x0
	lsr x0, x14, #6
	eor x0, x0, x14, ror #19
	eor x0, x0, x14, ror #61
	add x16, x16, x26
	add x16, x16, x0
	ldr x0, [x3, #288]
	add x7, x7, x16
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	lsr x0, x19, #7
	eor x0, x0, x19, ror #1
	eor x0, x0, x19, ror #8
	add x17, x17, x0
	lsr x0, x15, #6
	eor x0, x0, x15, ror #19
	eor x0, x0, x15, ror #61
	add x17, x17, x27
	add x17, x17, x0
	ldr x0, [x3, #296]
	add x6, x6, x17
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	lsr x0, x20, #7
	eor x0, x0, x20, ror #1
	eor x0, x0, x20, ror #8
	add x19, x19, x0
	lsr x0, x16, #6
	eor x0, x0, x16, ror #19
	eor x0, x0, x16, ror #61
	add x19, x19, x28
	add x19, x19, x0
	ldr x0, [x3, #304]
	add x5, x5, x19
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	lsr x0, x21, #7
	eor x0, x0, x21, ror #1
	eor x0, x0, x21, ror #8
	add x20, x20, x0
	lsr x0, x17, #6
	eor x0, x0, x17, ror #19
	eor x0, x0, x17, ror #61
	add x20, x20, x12
	add x20, x20, x0
	ldr x0, [x3, #312]
	add x4, x4, x20
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	lsr x0, x22, #7
	eor x0, x0, x22, ror #1
	eor x0, x0, x22, ror #8
	add x21, x21, x0
	lsr x0, x19, #6
	eor x0, x0, x19, ror #19
	eor x0, x0, x19, ror #61
	add x21, x21, x13
	add x21, x21, x0
	ldr x0, [x3, #320]
	add x11, x11, x21
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	lsr x0, x23, #7
	eor x0, x0, x23, ror #1
	eor x0, x0, x23, ror #8
	add x22, x22, x0
	lsr x0, x20, #6
	eor x0, x0, x20, ror #19
	eor x0, x0, x20, ror #61
	add x22, x22, x14
	add x22, x22, x0
	ldr x0, [x3, #328]
	add x10, x10, x22
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	lsr x0, x24, #7
	eor x0, x0, x24, ror #1
	eor x0, x0, x24, ror #8
	add x23, x23, x0
	lsr x0, x21, #6
	eor x0, x0, x21, ror #19
	eor x0, x0, x21, ror #61
	add x23, x23, x15
	add x23, x23, x0
	ldr x0, [x3, #336]
	add x9, x9, x23
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	lsr x0, x25, #7
	eor x0, x0, x25, ror #1
	eor x0, x0, x25, ror #8
	add x24, x24, x0
	lsr x0, x22, #6
	eor x0, x0, x22, ror #19
	eor x0, x0, x22, ror #61
	add x24, x24, x16
	add x24, x24, x0
	ldr x0, [x3, #344]
	add x8, x8, x24
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	lsr x0, x26, #7
	eor x0, x0, x26, ror #1
	eor x0, x0, x26, ror #8
	add x25, x25, x0
	lsr x0, x23, #6
	eor x0, x0, x23, ror #19
	eor x0, x0, x23, ror #61
	add x25, x25, x17
	add x25, x25, x0
	ldr x0, [x3, #352]
	add x7, x7, x25
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	lsr x0, x27, #7
	eor x0, x0, x27, ror #1
	eor x0, x0, x27, ror #8
	add x26, x26, x0
	lsr x0, x24, #6
	eor x0, x0, x24, ror #19
	eor x0, x0, x24, ror #61
	add x26, x26, x19
	add x26, x26, x0
	ldr x0, [x3, #360]
	add x6, x6, x26
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	lsr x0, x28, #7
	eor x0, x0, x28, ror #1
	eor x0, x0, x28, ror #8
	add x27, x27, x0
	lsr x0, x25, #6
	eor x0, x0, x25, ror #19
	eor x0, x0, x25, ror #61
	add x27, x27, x20
	add x27, x27, x0
	ldr x0, [x3, #368]
	add x5, x5, x27
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	lsr x0, x12, #7
	eor x0, x0, x12, ror #1
	eor x0, x0, x12, ror #8
	add x28, x28, x0
	lsr x0, x26, #6
	eor x0, x0, x26, ror #19
	eor x0, x0, x26, ror #61
	add x28, x28, x21
	add x28, x28, x0
	ldr x0, [x3, #376]
	add x4, x4, x28
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	lsr x0, x13, #7
	eor x0, x0, x13, ror #1
	eor x0, x0, x13, ror #8
	add x12, x12, x0
	lsr x0, x27, #6
	eor x0, x0, x27, ror #19
	eor x0, x0, x27, ror #61
	add x12, x12, x22
	add x12, x12, x0
	ldr x0, [x3, #384]
	add x11, x11, x12
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	lsr x0, x14, #7
	eor x0, x0, x14, ror #1
	eor x0, x0, x14, ror #8
	add x13, x13, x0
	lsr x0, x28, #6
	eor x0, x0, x28, ror #19
	eor x0, x0, x28, ror #61
	add x13, x13, x23
	add x13, x13, x0
	ldr x0, [x3, #392]
	add x10, x10, x13
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	lsr x0, x15, #7
	eor x0, x0, x15, ror #1
	eor x0, x0, x15, ror #8
	add x14, x14, x0
	lsr x0, x12, #6
	eor x0, x0, x12, ror #19
	eor x0, x0, x12, ror #61
	add x14, x14, x24
	add x14, x14, x0
	ldr x0, [x3, #400]
	add x9, x9, x14
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	lsr x0, x16, #7
	eor x0, x0, x16, ror #1
	eor x0, x0, x16, ror #8
	add x15, x15, x0
	lsr x0, x13, #6
	eor x0, x0, x13, ror #19
	eor x0, x0, x13, ror #61
	add x15, x15, x25
	add x15, x15, x0
	ldr x0, [x3, #408]
	add x8, x8, x15
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	lsr x0, x17, #7
	eor x0, x0, x17, ror #1
	eor x0, x0, x17, ror #8
	add x16, x16, x0
	lsr x0, x14, #6
	eor x0, x0, x14, ror #19
	eor x0, x0, x14, ror #61
	add x16, x16, x26
	add x16, x16, x0
	ldr x0, [x3, #416]
	add x7, x7, x16
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	lsr x0, x19, #7
	eor x0, x0, x19, ror #1
	eor x0, x0, x19, ror #8
	add x17, x17, x0
	lsr x0, x15, #6
	eor x0, x0, x15, ror #19
	eor x0, x0, x15, ror #61
	add x17, x17, x27
	add x17, x17, x0
	ldr x0, [x3, #424]
	add x6, x6, x17
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	lsr x0, x20, #7
	eor x0, x0, x20, ror #1
	eor x0, x0, x20, ror #8
	add x19, x19, x0
	lsr x0, x16, #6
	eor x0, x0, x16, ror #19
	eor x0, x0, x16, ror #61
	add x19, x19, x28
	add x19, x19, x0
	ldr x0, [x3, #432]
	add x5, x5, x19
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	lsr x0, x21, #7
	eor x0, x0, x21, ror #1
	eor x0, x0, x21, ror #8
	add x20, x20, x0
	lsr x0, x17, #6
	eor x0, x0, x17, ror #19
	eor x0, x0, x17, ror #61
	add x20, x20, x12
	add x20, x20, x0
	ldr x0, [x3, #440]
	add x4, x4, x20
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	lsr x0, x22, #7
	eor x0, x0, x22, ror #1
	eor x0, x0, x22, ror #8
	add x21, x21, x0
	lsr x0, x19, #6
	eor x0, x0, x19, ror #19
	eor x0, x0, x19, ror #61
	add x21, x21, x13
	add x21, x21, x0
	ldr x0, [x3, #448]
	add x11, x11, x21
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	lsr x0, x23, #7
	eor x0, x0, x23, ror #1
	eor x0, x0, x23, ror #8
	add x22, x22, x0
	lsr x0, x20, #6
	eor x0, x0, x20, ror #19
	eor x0, x0, x20, ror #61
	add x22, x22, x14
	add x22, x22, x0
	ldr x0, [x3, #456]
	add x10, x10, x22
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	lsr x0, x24, #7
	eor x0, x0, x24, ror #1
	eor x0, x0, x24, ror #8
	add x23, x23, x0
	lsr x0, x21, #6
	eor x0, x0, x21, ror #19
	eor x0, x0, x21, ror #61
	add x23, x23, x15
	add x23, x23, x0
	ldr x0, [x3, #464]
	add x9, x9, x23
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	lsr x0, x25, #7
	eor x0, x0, x25, ror #1
	eor x0, x0, x25, ror #8
	add x24, x24, x0
	lsr x0, x22, #6
	eor x0, x0, x22, ror #19
	eor x0, x0, x22, ror #61
	add x24, x24, x16
	add x24, x24, x0
	ldr x0, [x3, #472]
	add x8, x8, x24
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	lsr x0, x26, #7
	eor x0, x0, x26, ror #1
	eor x0, x0, x26, ror #8
	add x25, x25, x0
	lsr x0, x23, #6
	eor x0, x0, x23, ror #19
	eor x0, x0, x23, ror #61
	add x25, x25, x17
	add x25, x25, x0
	ldr x0, [x3, #480]
	add x7, x7, x25
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	lsr x0, x27, #7
	eor x0, x0, x27, ror #1
	eor x0, x0, x27, ror #8
	add x26, x26, x0
	lsr x0, x24, #6
	eor x0, x0, x24, ror #19
	eor x0, x0, x24, ror #61
	add x26, x26, x19
	add x26, x26, x0
	ldr x0, [x3, #488]
	add x6, x6, x26
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	lsr x0, x28, #7
	eor x0, x0, x28, ror #1
	eor x0, x0, x28, ror #8
	add x27, x27, x0
	lsr x0, x25, #6
	eor x0, x0, x25, ror #19
	eor x0, x0, x25, ror #61
	add x27, x27, x20
	add x27, x27, x0
	ldr x0, [x3, #496]
	add x5, x5, x27
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	lsr x0, x12, #7
	eor x0, x0, x12, ror #1
	eor x0, x0, x12, ror #8
	add x28, x28, x0
	lsr x0, x26, #6
	eor x0, x0, x26, ror #19
	eor x0, x0, x26, ror #61
	add x28, x28, x21
	add x28, x28, x0
	ldr x0, [x3, #504]
	add x4, x4, x28
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	lsr x0, x13, #7
	eor x0, x0, x13, ror #1
	eor x0, x0, x13, ror #8
	add x12, x12, x0
	lsr x0, x27, #6
	eor x0, x0, x27, ror #19
	eor x0, x0, x27, ror #61
	add x12, x12, x22
	add x12, x12, x0
	ldr x0, [x3, #512]
	add x11, x11, x12
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	lsr x0, x14, #7
	eor x0, x0, x14, ror #1
	eor x0, x0, x14, ror #8
	add x13, x13, x0
	lsr x0, x28, #6
	eor x0, x0, x28, ror #19
	eor x0, x0, x28, ror #61
	add x13, x13, x23
	add x13, x13, x0
	ldr x0, [x3, #520]
	add x10, x10, x13
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	lsr x0, x15, #7
	eor x0, x0, x15, ror #1
	eor x0, x0, x15, ror #8
	add x14, x14, x0
	lsr x0, x12, #6
	eor x0, x0, x12, ror #19
	eor x0, x0, x12, ror #61
	add x14, x14, x24
	add x14, x14, x0
	ldr x0, [x3, #528]
	add x9, x9, x14
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	lsr x0, x16, #7
	eor x0, x0, x16, ror #1
	eor x0, x0, x16, ror #8
	add x15, x15, x0
	lsr x0, x13, #6
	eor x0, x0, x13, ror #19
	eor x0, x0, x13, ror #61
	add x15, x15, x25
	add x15, x15, x0
	ldr x0, [x3, #536]
	add x8, x8, x15
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	lsr x0, x17, #7
	eor x0, x0, x17, ror #1
	eor x0, x0, x17, ror #8
	add x16, x16, x0
	lsr x0, x14, #6
	eor x0, x0, x14, ror #19
	eor x0, x0, x14, ror #61
	add x16, x16, x26
	add x16, x16, x0
	ldr x0, [x3, #544]
	add x7, x7, x16
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	lsr x0, x19, #7
	eor x0, x0, x19, ror #1
	eor x0, x0, x19, ror #8
	add x17, x17, x0
	lsr x0, x15, #6
	eor x0, x0, x15, ror #19
	eor x0, x0, x15, ror #61
	add x17, x17, x27
	add x17, x17, x0
	ldr x0, [x3, #552]
	add x6, x6, x17
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	lsr x0, x20, #7
	eor x0, x0, x20, ror #1
	eor x0, x0, x20, ror #8
	add x19, x19, x0
	lsr x0, x16, #6
	eor x0, x0, x16, ror #19
	eor x0, x0, x16, ror #61
	add x19, x19, x28
	add x19, x19, x0
	ldr x0, [x3, #560]
	add x5, x5, x19
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	lsr x0, x21, #7
	eor x0, x0, x21, ror #1
	eor x0, x0, x21, ror #8
	add x20, x20, x0
	lsr x0, x17, #6
	eor x0, x0, x17, ror #19
	eor x0, x0, x17, ror #61
	add x20, x20, x12
	add x20, x20, x0
	ldr x0, [x3, #568]
	add x4, x4, x20
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	lsr x0, x22, #7
	eor x0, x0, x22, ror #1
	eor x0, x0, x22, ror #8
	add x21, x21, x0
	lsr x0, x19, #6
	eor x0, x0, x19, ror #19
	eor x0, x0, x19, ror #61
	add x21, x21, x13
	add x21, x21, x0
	ldr x0, [x3, #576]
	add x11, x11, x21
	add x11, x11, x0
	ror x0, x8, #14
	eor x0, x0, x8, ror #18
	eor x0, x0, x8, ror #41
	add x11, x11, x0
	eor x0, x9, x10
	and x0, x0, x8
	eor x0, x0, x10
	add x11, x11, x0
	add x7, x7, x11
	ror x0, x4, #28
	eor x0, x0, x4, ror #34
	eor x0, x0, x4, ror #39
	add x11, x11, x0
	eor x1, x4, x5
	and x2, x2, x1
	eor x2, x2, x5
	add x11, x11, x2
	lsr x0, x23, #7
	eor x0, x0, x23, ror #1
	eor x0, x0, x23, ror #8
	add x22, x22, x0
	lsr x0, x20, #6
	eor x0, x0, x20, ror #19
	eor x0, x0, x20, ror #61
	add x22, x22, x14
	add x22, x22, x0
	ldr x0, [x3, #584]
	add x10, x10, x22
	add x10, x10, x0
	ror x0, x7, #14
	eor x0, x0, x7, ror #18
	eor x0, x0, x7, ror #41
	add x10, x10, x0
	eor x0, x8, x9
	and x0, x0, x7
	eor x0, x0, x9
	add x10, x10, x0
	add x6, x6, x10
	ror x0, x11, #28
	eor x0, x0, x11, ror #34
	eor x0, x0, x11, ror #39
	add x10, x10, x0
	eor x2, x11, x4
	and x1, x1, x2
	eor x1, x1, x4
	add x10, x10, x1
	lsr x0, x24, #7
	eor x0, x0, x24, ror #1
	eor x0, x0, x24, ror #8
	add x23, x23, x0
	lsr x0, x21, #6
	eor x0, x0, x21, ror #19
	eor x0, x0, x21, ror #61
	add x23, x23, x15
	add x23, x23, x0
	ldr x0, [x3, #592]
	add x9, x9, x23
	add x9, x9, x0
	ror x0, x6, #14
	eor x0, x0, x6, ror #18
	eor x0, x0, x6, ror #41
	add x9, x9, x0
	eor x0, x7, x8
	and x0, x0, x6
	eor x0, x0, x8
	add x9, x9, x0
	add x5, x5, x9
	ror x0, x10, #28
	eor x0, x0, x10, ror #34
	eor x0, x0, x10, ror #39
	add x9, x9, x0
	eor x1, x10, x11
	and x2, x2, x1
	eor x2, x2, x11
	add x9, x9, x2
	lsr x0, x25, #7
	eor x0, x0, x25, ror #1
	eor x0, x0, x25, ror #8
	add x24, x24, x0
	lsr x0, x22, #6
	eor x0, x0, x22, ror #19
	eor x0, x0, x22, ror #61
	add x24, x24, x16
	add x24, x24, x0
	ldr x0, [x3, #600]
	add x8, x8, x24
	add x8, x8, x0
	ror x0, x5, #14
	eor x0, x0, x5, ror #18
	eor x0, x0, x5, ror #41
	add x8, x8, x0
	eor x0, x6, x7
	and x0, x0, x5
	eor x0, x0, x7
	add x8, x8, x0
	add x4, x4, x8
	ror x0, x9, #28
	eor x0, x0, x9, ror #34
	eor x0, x0, x9, ror #39
	add x8, x8, x0
	eor x2, x9, x10
	and x1, x1, x2
	eor x1, x1, x10
	add x8, x8, x1
	lsr x0, x26, #7
	eor x0, x0, x26, ror #1
	eor x0, x0, x26, ror #8
	add x25, x25, x0
	lsr x0, x23, #6
	eor x0, x0, x23, ror #19
	eor x0, x0, x23, ror #61
	add x25, x25, x17
	add x25, x25, x0
	ldr x0, [x3, #608]
	add x7, x7, x25
	add x7, x7, x0
	ror x0, x4, #14
	eor x0, x0, x4, ror #18
	eor x0, x0, x4, ror #41
	add x7, x7, x0
	eor x0, x5, x6
	and x0, x0, x4
	eor x0, x0, x6
	add x7, x7, x0
	add x11, x11, x7
	ror x0, x8, #28
	eor x0, x0, x8, ror #34
	eor x0, x0, x8, ror #39
	add x7, x7, x0
	eor x1, x8, x9
	and x2, x2, x1
	eor x2, x2, x9
	add x7, x7, x2
	lsr x0, x27, #7
	eor x0, x0, x27, ror #1
	eor x0, x0, x27, ror #8
	add x26, x26, x0
	lsr x0, x24, #6
	eor x0, x0, x24, ror #19
	eor x0, x0, x24, ror #61
	add x26, x26, x19
	add x26, x26, x0
	ldr x0, [x3, #616]
	add x6, x6, x26
	add x6, x6, x0
	ror x0, x11, #14
	eor x0, x0, x11, ror #18
	eor x0, x0, x11, ror #41
	add x6, x6, x0
	eor x0, x4, x5
	and x0, x0, x11
	eor x0, x0, x5
	add x6, x6, x0
	add x10, x10, x6
	ror x0, x7, #28
	eor x0, x0, x7, ror #34
	eor x0, x0, x7, ror #39
	add x6, x6, x0
	eor x2, x7, x8
	and x1, x1, x2
	eor x1, x1, x8
	add x6, x6, x1
	lsr x0, x28, #7
	eor x0, x0, x28, ror #1
	eor x0, x0, x28, ror #8
	add x27, x27, x0
	lsr x0, x25, #6
	eor x0, x0, x25, ror #19
	eor x0, x0, x25, ror #61
	add x27, x27, x20
	add x27, x27, x0
	ldr x0, [x3, #624]
	add x5, x5, x27
	add x5, x5, x0
	ror x0, x10, #14
	eor x0, x0, x10, ror #18
	eor x0, x0, x10, ror #41
	add x5, x5, x0
	eor x0, x11, x4
	and x0, x0, x10
	eor x0, x0, x4
	add x5, x5, x0
	add x9, x9, x5
	ror x0, x6, #28
	eor x0, x0, x6, ror #34
	eor x0, x0, x6, ror #39
	add x5, x5, x0
	eor x1, x6, x7
	and x2, x2, x1
	eor x2, x2, x7
	add x5, x5, x2
	lsr x0, x12, #7
	eor x0, x0, x12, ror #1
	eor x0, x0, x12, ror #8
	add x28, x28, x0
	lsr x0, x26, #6
	eor x0, x0, x26, ror #19
	eor x0, x0, x26, ror #61
	add x28, x28, x21
	add x28, x28, x0
	ldr x0, [x3, #632]
	add x4, x4, x28
	add x4, x4, x0
	ror x0, x9, #14
	eor x0, x0, x9, ror #18
	eor x0, x0, x9, ror #41
	add x4, x4, x0
	eor x0, x10, x11
	and x0, x0, x9
	eor x0, x0, x11
	add x4, x4, x0
	add x8, x8, x4
	ror x0, x5, #28
	eor x0, x0, x5, ror #34
	eor x0, x0, x5, ror #39
	add x4, x4, x0
	eor x2, x5, x6
	and x1, x1, x2
	eor x1, x1, x6
	add x4, x4, x1
	umov x0, v16.d[0]
	ldp x12, x13, [x0, #0]
	ldp x14, x15, [x0, #16]
	ldp x16, x17, [x0, #32]
	ldp x19, x20, [x0, #48]
	add x4, x4, x12
	add x5, x5, x13
	add x6, x6, x14
	add x7, x7, x15
	add x8, x8, x16
	add x9, x9, x17
	add x10, x10, x19
	add x11, x11, x20
	stp x4, x5, [x0, #0]
	stp x6, x7, [x0, #16]
	stp x8, x9, [x0, #32]
	stp x10, x11, [x0, #48]
	umov x0, v17.d[0]
	sub x0, x0, #1
	mov v17.d[0], x0
	cbnz x0, 22b
	umov x19, v18.d[0]
	umov x20, v18.d[1]
	umov x21, v19.d[0]
	umov x22, v19.d[1]
	umov x23, v20.d[0]
	umov x24, v20.d[1]
	umov x25, v21.d[0]
	umov x26, v21.d[1]
	umov x27, v22.d[0]
	umov x28, v22.d[1]
	umov x1, v16.d[1]
	b 21f
20:
21:
	ret
	.p2align 6
