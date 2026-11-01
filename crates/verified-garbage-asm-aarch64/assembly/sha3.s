// The functions of `src/sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_absorb_scratch:
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	dup v0.2d, x19
	dup v1.2d, x20
	dup v2.2d, x21
	dup v3.2d, x22
	dup v4.2d, x23
	dup v5.2d, x24
	dup v6.2d, x25
	dup v7.2d, x26
	dup v16.2d, x27
	dup v17.2d, x28
	dup v18.2d, x30
	dup v30.2d, x0
	dup v31.2d, x1
	dup v19.2d, x3
	dup v20.2d, x4
	dup v21.2d, x6
	add x30, x0, #0
	ldr x0, [x30, #0]
	ldr x1, [x30, #8]
	ldr x2, [x30, #16]
	ldr x3, [x30, #24]
	ldr x4, [x30, #32]
	ldr x5, [x30, #40]
	ldr x6, [x30, #48]
	ldr x7, [x30, #56]
	ldr x8, [x30, #64]
	ldr x9, [x30, #72]
	ldr x10, [x30, #80]
	ldr x11, [x30, #88]
	ldr x12, [x30, #96]
	ldr x13, [x30, #104]
	ldr x14, [x30, #112]
	ldr x15, [x30, #120]
	ldr x16, [x30, #128]
	ldr x17, [x30, #136]
	ldr x25, [x30, #144]
	ldr x19, [x30, #152]
	ldr x20, [x30, #160]
	ldr x21, [x30, #168]
	ldr x22, [x30, #176]
	ldr x23, [x30, #184]
	ldr x24, [x30, #192]
24:
	umov x27, v19.d[0]
	umov x28, v21.d[0]
	sub x26, x28, #72
	cbz x26, 25f
	sub x26, x28, #104
	cbz x26, 27f
	sub x26, x28, #136
	cbz x26, 29f
	sub x26, x28, #144
	cbz x26, 211f
	ldr x26, [x27, #0]
	eor x0, x0, x26
	ldr x26, [x27, #8]
	eor x1, x1, x26
	ldr x26, [x27, #16]
	eor x2, x2, x26
	ldr x26, [x27, #24]
	eor x3, x3, x26
	ldr x26, [x27, #32]
	eor x4, x4, x26
	ldr x26, [x27, #40]
	eor x5, x5, x26
	ldr x26, [x27, #48]
	eor x6, x6, x26
	ldr x26, [x27, #56]
	eor x7, x7, x26
	ldr x26, [x27, #64]
	eor x8, x8, x26
	ldr x26, [x27, #72]
	eor x9, x9, x26
	ldr x26, [x27, #80]
	eor x10, x10, x26
	ldr x26, [x27, #88]
	eor x11, x11, x26
	ldr x26, [x27, #96]
	eor x12, x12, x26
	ldr x26, [x27, #104]
	eor x13, x13, x26
	ldr x26, [x27, #112]
	eor x14, x14, x26
	ldr x26, [x27, #120]
	eor x15, x15, x26
	ldr x26, [x27, #128]
	eor x16, x16, x26
	ldr x26, [x27, #136]
	eor x17, x17, x26
	ldr x26, [x27, #144]
	eor x25, x25, x26
	ldr x26, [x27, #152]
	eor x19, x19, x26
	ldr x26, [x27, #160]
	eor x20, x20, x26
	b 212f
211:
	ldr x26, [x27, #0]
	eor x0, x0, x26
	ldr x26, [x27, #8]
	eor x1, x1, x26
	ldr x26, [x27, #16]
	eor x2, x2, x26
	ldr x26, [x27, #24]
	eor x3, x3, x26
	ldr x26, [x27, #32]
	eor x4, x4, x26
	ldr x26, [x27, #40]
	eor x5, x5, x26
	ldr x26, [x27, #48]
	eor x6, x6, x26
	ldr x26, [x27, #56]
	eor x7, x7, x26
	ldr x26, [x27, #64]
	eor x8, x8, x26
	ldr x26, [x27, #72]
	eor x9, x9, x26
	ldr x26, [x27, #80]
	eor x10, x10, x26
	ldr x26, [x27, #88]
	eor x11, x11, x26
	ldr x26, [x27, #96]
	eor x12, x12, x26
	ldr x26, [x27, #104]
	eor x13, x13, x26
	ldr x26, [x27, #112]
	eor x14, x14, x26
	ldr x26, [x27, #120]
	eor x15, x15, x26
	ldr x26, [x27, #128]
	eor x16, x16, x26
	ldr x26, [x27, #136]
	eor x17, x17, x26
212:
	b 210f
29:
	ldr x26, [x27, #0]
	eor x0, x0, x26
	ldr x26, [x27, #8]
	eor x1, x1, x26
	ldr x26, [x27, #16]
	eor x2, x2, x26
	ldr x26, [x27, #24]
	eor x3, x3, x26
	ldr x26, [x27, #32]
	eor x4, x4, x26
	ldr x26, [x27, #40]
	eor x5, x5, x26
	ldr x26, [x27, #48]
	eor x6, x6, x26
	ldr x26, [x27, #56]
	eor x7, x7, x26
	ldr x26, [x27, #64]
	eor x8, x8, x26
	ldr x26, [x27, #72]
	eor x9, x9, x26
	ldr x26, [x27, #80]
	eor x10, x10, x26
	ldr x26, [x27, #88]
	eor x11, x11, x26
	ldr x26, [x27, #96]
	eor x12, x12, x26
	ldr x26, [x27, #104]
	eor x13, x13, x26
	ldr x26, [x27, #112]
	eor x14, x14, x26
	ldr x26, [x27, #120]
	eor x15, x15, x26
	ldr x26, [x27, #128]
	eor x16, x16, x26
210:
	b 28f
27:
	ldr x26, [x27, #0]
	eor x0, x0, x26
	ldr x26, [x27, #8]
	eor x1, x1, x26
	ldr x26, [x27, #16]
	eor x2, x2, x26
	ldr x26, [x27, #24]
	eor x3, x3, x26
	ldr x26, [x27, #32]
	eor x4, x4, x26
	ldr x26, [x27, #40]
	eor x5, x5, x26
	ldr x26, [x27, #48]
	eor x6, x6, x26
	ldr x26, [x27, #56]
	eor x7, x7, x26
	ldr x26, [x27, #64]
	eor x8, x8, x26
	ldr x26, [x27, #72]
	eor x9, x9, x26
	ldr x26, [x27, #80]
	eor x10, x10, x26
	ldr x26, [x27, #88]
	eor x11, x11, x26
	ldr x26, [x27, #96]
	eor x12, x12, x26
28:
	b 26f
25:
	ldr x26, [x27, #0]
	eor x0, x0, x26
	ldr x26, [x27, #8]
	eor x1, x1, x26
	ldr x26, [x27, #16]
	eor x2, x2, x26
	ldr x26, [x27, #24]
	eor x3, x3, x26
	ldr x26, [x27, #32]
	eor x4, x4, x26
	ldr x26, [x27, #40]
	eor x5, x5, x26
	ldr x26, [x27, #48]
	eor x6, x6, x26
	ldr x26, [x27, #56]
	eor x7, x7, x26
	ldr x26, [x27, #64]
	eor x8, x8, x26
26:
	eor x26, x0, x5, ror #0
	dup v24.2d, x4
	dup v25.2d, x9
	eor x27, x1, x6, ror #0
	eor x28, x2, x7, ror #0
	eor x30, x3, x8, ror #0
	eor x4, x4, x9, ror #0
	eor x26, x26, x10, ror #0
	eor x27, x27, x11, ror #0
	eor x28, x28, x12, ror #0
	eor x30, x30, x13, ror #0
	eor x4, x4, x14, ror #0
	eor x26, x26, x15, ror #0
	eor x27, x27, x16, ror #0
	eor x28, x28, x17, ror #0
	eor x30, x30, x25, ror #0
	eor x4, x4, x19, ror #0
	eor x26, x26, x20, ror #0
	eor x27, x27, x21, ror #0
	eor x28, x28, x22, ror #0
	eor x30, x30, x23, ror #0
	eor x4, x4, x24, ror #0
	eor x9, x26, x28, ror #63
	eor x1, x1, x9, ror #0
	eor x6, x6, x9, ror #0
	eor x11, x11, x9, ror #0
	eor x16, x16, x9, ror #0
	eor x21, x21, x9, ror #0
	eor x9, x27, x30, ror #63
	eor x28, x28, x4, ror #63
	eor x30, x30, x26, ror #63
	eor x4, x4, x27, ror #63
	eor x2, x2, x9, ror #0
	eor x7, x7, x9, ror #0
	eor x12, x12, x9, ror #0
	eor x17, x17, x9, ror #0
	eor x22, x22, x9, ror #0
	eor x0, x0, x4, ror #0
	eor x5, x5, x4, ror #0
	eor x10, x10, x4, ror #0
	eor x15, x15, x4, ror #0
	eor x20, x20, x4, ror #0
	umov x4, v24.d[0]
	umov x9, v25.d[0]
	eor x3, x3, x28, ror #0
	eor x8, x8, x28, ror #0
	eor x13, x13, x28, ror #0
	eor x25, x25, x28, ror #0
	eor x23, x23, x28, ror #0
	eor x4, x4, x30, ror #0
	eor x9, x9, x30, ror #0
	eor x14, x14, x30, ror #0
	eor x19, x19, x30, ror #0
	eor x24, x24, x30, ror #0
	bic x26, x12, x6, ror #63
	bic x27, x25, x12, ror #42
	bic x28, x0, x24, ror #50
	bic x30, x6, x0, ror #44
	eor x0, x0, x26, ror #21
	bic x26, x24, x25, ror #57
	eor x6, x6, x27, ror #23
	eor x25, x25, x28, ror #21
	eor x24, x24, x30, ror #34
	eor x12, x12, x26, ror #29
	bic x26, x10, x9, ror #47
	bic x27, x16, x10, ror #42
	bic x28, x3, x22, ror #31
	bic x30, x9, x3, ror #56
	eor x3, x3, x26, ror #25
	bic x26, x22, x16, ror #16
	eor x9, x9, x27, ror #39
	eor x16, x16, x28, ror #17
	eor x22, x22, x30, ror #41
	eor x10, x10, x26, ror #6
	bic x26, x13, x7, ror #19
	bic x27, x19, x13, ror #47
	bic x28, x1, x20, ror #47
	bic x30, x7, x1, ror #5
	eor x1, x1, x26, ror #40
	bic x26, x20, x19, ror #10
	eor x7, x7, x27, ror #62
	eor x19, x19, x28, ror #7
	eor x20, x20, x30, ror #12
	eor x13, x13, x26, ror #7
	bic x26, x11, x5, ror #38
	bic x27, x17, x11, ror #5
	bic x28, x4, x23, ror #35
	bic x30, x5, x4, ror #9
	eor x4, x4, x26, ror #17
	bic x26, x23, x17, ror #41
	eor x5, x5, x27, ror #21
	eor x17, x17, x28, ror #52
	eor x23, x23, x30, ror #20
	eor x11, x11, x26, ror #18
	bic x26, x14, x8, ror #48
	bic x27, x15, x14, ror #2
	bic x28, x2, x21, ror #60
	bic x30, x8, x2, ror #57
	eor x2, x2, x26, ror #23
	bic x26, x21, x15, ror #25
	eor x8, x8, x27, ror #14
	eor x15, x15, x28, ror #43
	eor x21, x21, x30, ror #11
	eor x14, x14, x26, ror #37
	movz x26, #1, lsl #0
	eor x0, x0, x26, ror #0
	eor x26, x0, x3, ror #36
	dup v24.2d, x24
	dup v25.2d, x22
	eor x27, x6, x9, ror #24
	eor x28, x12, x10, ror #40
	eor x30, x25, x16, ror #40
	eor x24, x24, x22, ror #17
	eor x26, x26, x1, ror #63
	eor x27, x27, x7, ror #38
	eor x28, x28, x13, ror #18
	eor x30, x30, x19, ror #13
	eor x24, x24, x20, ror #60
	eor x26, x26, x4, ror #37
	eor x27, x27, x5, ror #8
	eor x28, x28, x11, ror #33
	eor x30, x30, x17, ror #6
	eor x24, x24, x23, ror #22
	eor x26, x26, x2, ror #2
	eor x27, x27, x8, ror #53
	eor x28, x28, x14, ror #4
	eor x30, x30, x15, ror #44
	eor x24, x24, x21, ror #12
	eor x22, x26, x28, ror #20
	eor x6, x6, x22, ror #44
	eor x9, x9, x22, ror #20
	eor x7, x7, x22, ror #6
	eor x5, x5, x22, ror #36
	eor x8, x8, x22, ror #55
	eor x22, x27, x30, ror #22
	eor x28, x28, x24, ror #28
	eor x30, x30, x26, ror #20
	eor x24, x24, x27, ror #33
	eor x12, x12, x22, ror #63
	eor x10, x10, x22, ror #23
	eor x13, x13, x22, ror #45
	eor x11, x11, x22, ror #30
	eor x14, x14, x22, ror #59
	eor x0, x0, x24, ror #50
	eor x3, x3, x24, ror #14
	eor x1, x1, x24, ror #51
	eor x4, x4, x24, ror #13
	eor x2, x2, x24, ror #48
	umov x22, v24.d[0]
	umov x24, v25.d[0]
	eor x25, x25, x28, ror #42
	eor x16, x16, x28, ror #2
	eor x19, x19, x28, ror #29
	eor x17, x17, x28, ror #36
	eor x15, x15, x28, ror #62
	eor x22, x22, x30, ror #57
	eor x24, x24, x30, ror #40
	eor x20, x20, x30, ror #61
	eor x23, x23, x30, ror #35
	eor x21, x21, x30, ror #45
	bic x26, x13, x9, ror #4
	bic x27, x17, x13, ror #32
	bic x28, x0, x21, ror #48
	bic x30, x9, x0, ror #0
	eor x0, x0, x26, ror #60
	bic x26, x21, x17, ror #44
	eor x9, x9, x27, ror #28
	eor x17, x17, x28, ror #36
	eor x21, x21, x30, ror #16
	eor x13, x13, x26, ror #52
	bic x26, x1, x24, ror #51
	bic x27, x5, x1, ror #13
	bic x28, x25, x14, ror #13
	bic x30, x24, x25, ror #32
	eor x25, x25, x26, ror #45
	bic x26, x14, x5, ror #19
	eor x24, x24, x27, ror #0
	eor x5, x5, x28, ror #32
	eor x14, x14, x30, ror #19
	eor x1, x1, x26, ror #32
	bic x26, x19, x10, ror #24
	bic x27, x23, x19, ror #31
	bic x28, x6, x2, ror #29
	bic x30, x10, x6, ror #28
	eor x6, x6, x26, ror #12
	bic x26, x2, x23, ror #16
	eor x10, x10, x27, ror #9
	eor x23, x23, x28, ror #19
	eor x2, x2, x30, ror #7
	eor x19, x19, x26, ror #17
	bic x26, x7, x3, ror #16
	bic x27, x11, x7, ror #9
	bic x28, x22, x15, ror #8
	bic x30, x3, x22, ror #23
	eor x22, x22, x26, ror #25
	bic x26, x15, x11, ror #8
	eor x3, x3, x27, ror #39
	eor x11, x11, x28, ror #48
	eor x15, x15, x30, ror #33
	eor x7, x7, x26, ror #47
	bic x26, x20, x16, ror #21
	bic x27, x4, x20, ror #11
	bic x28, x12, x8, ror #48
	bic x30, x16, x12, ror #59
	eor x12, x12, x26, ror #48
	bic x26, x8, x4, ror #53
	eor x16, x16, x27, ror #32
	eor x4, x4, x28, ror #27
	eor x8, x8, x30, ror #21
	eor x20, x20, x26, ror #0
	movz x26, #32898, lsl #0
	eor x0, x0, x26, ror #0
	eor x26, x0, x25, ror #15
	dup v24.2d, x21
	dup v25.2d, x14
	eor x27, x9, x24, ror #47
	eor x28, x13, x1, ror #0
	eor x30, x17, x5, ror #19
	eor x21, x21, x14, ror #44
	eor x26, x26, x6, ror #19
	eor x27, x27, x10, ror #55
	eor x28, x28, x19, ror #35
	eor x30, x30, x23, ror #36
	eor x21, x21, x2, ror #0
	eor x26, x26, x22, ror #23
	eor x27, x27, x3, ror #0
	eor x28, x28, x7, ror #52
	eor x30, x30, x11, ror #11
	eor x21, x21, x15, ror #47
	eor x26, x26, x12, ror #23
	eor x27, x27, x16, ror #28
	eor x28, x28, x20, ror #11
	eor x30, x30, x4, ror #32
	eor x21, x21, x8, ror #23
	eor x14, x26, x28, ror #59
	eor x9, x9, x14, ror #0
	eor x24, x24, x14, ror #17
	eor x10, x10, x14, ror #9
	eor x3, x3, x14, ror #0
	eor x16, x16, x14, ror #36
	eor x14, x27, x30, ror #27
	eor x28, x28, x21, ror #51
	eor x30, x30, x26, ror #35
	eor x21, x21, x27, ror #15
	eor x13, x13, x14, ror #4
	eor x1, x1, x14, ror #4
	eor x19, x19, x14, ror #33
	eor x7, x7, x14, ror #16
	eor x20, x20, x14, ror #57
	eor x0, x0, x21, ror #48
	eor x25, x25, x21, ror #33
	eor x6, x6, x21, ror #29
	eor x22, x22, x21, ror #25
	eor x12, x12, x21, ror #25
	umov x14, v24.d[0]
	umov x21, v25.d[0]
	eor x17, x17, x28, ror #32
	eor x5, x5, x28, ror #13
	eor x23, x23, x28, ror #60
	eor x11, x11, x28, ror #21
	eor x4, x4, x28, ror #0
	eor x14, x14, x30, ror #44
	eor x21, x21, x30, ror #0
	eor x2, x2, x30, ror #44
	eor x15, x15, x30, ror #61
	eor x8, x8, x30, ror #21
	bic x26, x19, x24, ror #15
	bic x27, x11, x19, ror #34
	bic x28, x0, x8, ror #57
	bic x30, x24, x0, ror #61
	eor x0, x0, x26, ror #52
	bic x26, x8, x11, ror #25
	eor x24, x24, x27, ror #15
	eor x11, x11, x28, ror #46
	eor x8, x8, x30, ror #10
	eor x19, x19, x26, ror #5
	bic x26, x6, x21, ror #56
	bic x27, x3, x6, ror #61
	bic x28, x17, x20, ror #10
	bic x30, x21, x17, ror #56
	eor x17, x17, x26, ror #16
	bic x26, x20, x3, ror #9
	eor x21, x21, x27, ror #11
	eor x3, x3, x28, ror #45
	eor x20, x20, x30, ror #62
	eor x6, x6, x26, ror #58
	bic x26, x23, x1, ror #15
	bic x27, x15, x23, ror #16
	bic x28, x9, x12, ror #6
	bic x30, x1, x9, ror #9
	eor x9, x9, x26, ror #40
	bic x26, x12, x15, ror #18
	eor x1, x1, x27, ror #33
	eor x15, x15, x28, ror #40
	eor x12, x12, x30, ror #49
	eor x23, x23, x26, ror #30
	bic x26, x10, x25, ror #62
	bic x27, x7, x10, ror #12
	bic x28, x14, x4, ror #47
	bic x30, x25, x14, ror #42
	eor x14, x14, x26, ror #24
	bic x26, x4, x7, ror #29
	eor x25, x25, x27, ror #54
	eor x7, x7, x28, ror #52
	eor x4, x4, x30, ror #39
	eor x10, x10, x26, ror #23
	bic x26, x2, x5, ror #47
	bic x27, x22, x2, ror #27
	bic x28, x13, x16, ror #28
	bic x30, x5, x13, ror #6
	eor x13, x13, x26, ror #11
	bic x26, x16, x22, ror #20
	eor x5, x5, x27, ror #54
	eor x22, x22, x28, ror #16
	eor x16, x16, x30, ror #30
	eor x2, x2, x26, ror #17
	movz x26, #32906, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x17, ror #0
	dup v24.2d, x8
	dup v25.2d, x20
	eor x27, x24, x21, ror #5
	eor x28, x19, x6, ror #28
	eor x30, x11, x3, ror #1
	eor x8, x8, x20, ror #17
	eor x26, x26, x9, ror #63
	eor x27, x27, x1, ror #51
	eor x28, x28, x23, ror #51
	eor x30, x30, x15, ror #5
	eor x8, x8, x12, ror #12
	eor x26, x26, x14, ror #21
	eor x27, x27, x25, ror #40
	eor x28, x28, x10, ror #57
	eor x30, x30, x7, ror #15
	eor x8, x8, x4, ror #11
	eor x26, x26, x13, ror #62
	eor x27, x27, x5, ror #53
	eor x28, x28, x2, ror #21
	eor x30, x30, x22, ror #28
	eor x8, x8, x16, ror #33
	eor x20, x26, x28, ror #51
	eor x24, x24, x20, ror #61
	eor x21, x21, x20, ror #56
	eor x1, x1, x20, ror #10
	eor x25, x25, x20, ror #21
	eor x5, x5, x20, ror #8
	eor x20, x27, x30, ror #14
	eor x28, x28, x8, ror #4
	eor x30, x30, x26, ror #45
	eor x8, x8, x27, ror #9
	eor x19, x19, x20, ror #15
	eor x6, x6, x20, ror #51
	eor x23, x23, x20, ror #28
	eor x10, x10, x20, ror #22
	eor x2, x2, x20, ror #58
	eor x0, x0, x8, ror #57
	eor x17, x17, x8, ror #57
	eor x9, x9, x8, ror #58
	eor x14, x14, x8, ror #36
	eor x13, x13, x8, ror #59
	umov x8, v24.d[0]
	umov x20, v25.d[0]
	eor x11, x11, x28, ror #34
	eor x3, x3, x28, ror #33
	eor x15, x15, x28, ror #29
	eor x7, x7, x28, ror #19
	eor x22, x22, x28, ror #6
	eor x8, x8, x30, ror #25
	eor x20, x20, x30, ror #8
	eor x12, x12, x30, ror #13
	eor x4, x4, x30, ror #14
	eor x16, x16, x30, ror #56
	bic x26, x23, x21, ror #32
	bic x27, x7, x23, ror #48
	bic x28, x0, x16, ror #12
	bic x30, x21, x0, ror #36
	eor x0, x0, x26, ror #60
	bic x26, x16, x7, ror #0
	eor x21, x21, x27, ror #48
	eor x7, x7, x28, ror #52
	eor x16, x16, x30, ror #16
	eor x23, x23, x26, ror #16
	bic x26, x9, x20, ror #58
	bic x27, x25, x9, ror #62
	bic x28, x11, x2, ror #22
	bic x30, x20, x11, ror #0
	eor x11, x11, x26, ror #6
	bic x26, x2, x25, ror #50
	eor x20, x20, x27, ror #8
	eor x25, x25, x28, ror #56
	eor x2, x2, x30, ror #42
	eor x9, x9, x26, ror #16
	bic x26, x15, x6, ror #12
	bic x27, x4, x15, ror #2
	bic x28, x24, x13, ror #42
	bic x30, x6, x24, ror #56
	eor x24, x24, x26, ror #60
	bic x26, x13, x4, ror #16
	eor x6, x6, x27, ror #50
	eor x4, x4, x28, ror #6
	eor x13, x13, x30, ror #30
	eor x15, x15, x26, ror #46
	bic x26, x1, x17, ror #48
	bic x27, x10, x1, ror #14
	bic x28, x8, x22, ror #24
	bic x30, x17, x8, ror #2
	eor x8, x8, x26, ror #14
	bic x26, x22, x10, ror #40
	eor x17, x17, x27, ror #2
	eor x10, x10, x28, ror #0
	eor x22, x22, x30, ror #38
	eor x1, x1, x26, ror #10
	bic x26, x12, x3, ror #62
	bic x27, x14, x12, ror #50
	bic x28, x19, x5, ror #0
	bic x30, x3, x19, ror #26
	eor x19, x19, x26, ror #40
	bic x26, x5, x14, ror #54
	eor x3, x3, x27, ror #16
	eor x14, x14, x28, ror #10
	eor x5, x5, x30, ror #38
	eor x12, x12, x26, ror #24
	movz x26, #32768, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x11, ror #54
	dup v24.2d, x16
	dup v25.2d, x2
	eor x27, x21, x20, ror #26
	eor x28, x23, x9, ror #0
	eor x30, x7, x25, ror #50
	eor x16, x16, x2, ror #0
	eor x26, x26, x24, ror #2
	eor x27, x27, x6, ror #46
	eor x28, x28, x15, ror #2
	eor x30, x30, x4, ror #48
	eor x16, x16, x13, ror #32
	eor x26, x26, x8, ror #30
	eor x27, x27, x17, ror #0
	eor x28, x28, x1, ror #48
	eor x30, x30, x10, ror #18
	eor x16, x16, x22, ror #42
	eor x26, x26, x19, ror #54
	eor x27, x27, x3, ror #0
	eor x28, x28, x12, ror #34
	eor x30, x30, x14, ror #32
	eor x16, x16, x5, ror #42
	eor x2, x26, x28, ror #59
	eor x21, x21, x2, ror #36
	eor x20, x20, x2, ror #10
	eor x6, x6, x2, ror #54
	eor x17, x17, x2, ror #36
	eor x3, x3, x2, ror #36
	eor x2, x27, x30, ror #47
	eor x28, x28, x16, ror #15
	eor x30, x30, x26, ror #51
	eor x16, x16, x27, ror #15
	eor x23, x23, x2, ror #32
	eor x9, x9, x2, ror #32
	eor x15, x15, x2, ror #30
	eor x1, x1, x2, ror #48
	eor x12, x12, x2, ror #62
	eor x0, x0, x16, ror #12
	eor x11, x11, x16, ror #22
	eor x24, x24, x16, ror #10
	eor x8, x8, x16, ror #46
	eor x19, x19, x16, ror #22
	umov x2, v24.d[0]
	umov x16, v25.d[0]
	eor x7, x7, x28, ror #48
	eor x25, x25, x28, ror #62
	eor x4, x4, x28, ror #0
	eor x10, x10, x28, ror #30
	eor x14, x14, x28, ror #16
	eor x2, x2, x30, ror #0
	eor x16, x16, x30, ror #0
	eor x13, x13, x30, ror #32
	eor x22, x22, x30, ror #22
	eor x5, x5, x30, ror #22
	bic x26, x15, x20, ror #55
	bic x27, x10, x15, ror #10
	bic x28, x0, x5, ror #40
	bic x30, x20, x0, ror #54
	eor x0, x0, x26, ror #19
	bic x26, x5, x10, ror #33
	eor x20, x20, x27, ror #63
	eor x10, x10, x28, ror #55
	eor x5, x5, x30, ror #34
	eor x15, x15, x26, ror #21
	bic x26, x24, x16, ror #57
	bic x27, x17, x24, ror #16
	bic x28, x7, x12, ror #49
	bic x30, x16, x7, ror #56
	eor x7, x7, x26, ror #15
	bic x26, x12, x17, ror #14
	eor x16, x16, x27, ror #55
	eor x17, x17, x28, ror #1
	eor x12, x12, x30, ror #23
	eor x24, x24, x26, ror #34
	bic x26, x4, x9, ror #19
	bic x27, x22, x4, ror #53
	bic x28, x21, x19, ror #9
	bic x30, x9, x21, ror #37
	eor x21, x21, x26, ror #8
	bic x26, x19, x22, ror #10
	eor x9, x9, x27, ror #56
	eor x22, x22, x28, ror #45
	eor x19, x19, x30, ror #18
	eor x4, x4, x26, ror #1
	bic x26, x6, x11, ror #18
	bic x27, x1, x6, ror #35
	bic x28, x2, x14, ror #3
	bic x30, x11, x2, ror #31
	eor x2, x2, x26, ror #15
	bic x26, x14, x1, ror #41
	eor x11, x11, x27, ror #11
	eor x1, x1, x28, ror #20
	eor x14, x14, x30, ror #30
	eor x6, x6, x26, ror #52
	bic x26, x13, x25, ror #2
	bic x27, x8, x13, ror #16
	bic x28, x23, x3, ror #28
	bic x30, x25, x23, ror #55
	eor x23, x23, x26, ror #7
	bic x26, x3, x8, ror #27
	eor x25, x25, x27, ror #46
	eor x8, x8, x28, ror #9
	eor x3, x3, x30, ror #45
	eor x13, x13, x26, ror #21
	movz x26, #32907, lsl #0
	eor x0, x0, x26, ror #0
	eor x26, x0, x7, ror #48
	dup v24.2d, x5
	dup v25.2d, x12
	eor x27, x20, x16, ror #46
	eor x28, x15, x24, ror #44
	eor x30, x10, x17, ror #38
	eor x5, x5, x12, ror #57
	eor x26, x26, x21, ror #27
	eor x27, x27, x9, ror #44
	eor x28, x28, x4, ror #16
	eor x30, x30, x22, ror #37
	eor x5, x5, x19, ror #60
	eor x26, x26, x2, ror #49
	eor x27, x27, x11, ror #8
	eor x28, x28, x6, ror #45
	eor x30, x30, x1, ror #20
	eor x5, x5, x14, ror #12
	eor x26, x26, x23, ror #62
	eor x27, x27, x25, ror #61
	eor x28, x28, x13, ror #50
	eor x30, x30, x8, ror #44
	eor x5, x5, x3, ror #50
	eor x12, x26, x28, ror #18
	eor x20, x20, x12, ror #54
	eor x16, x16, x12, ror #8
	eor x9, x9, x12, ror #10
	eor x11, x11, x12, ror #46
	eor x25, x25, x12, ror #57
	eor x12, x27, x30, ror #62
	eor x28, x28, x5, ror #20
	eor x30, x30, x26, ror #54
	eor x5, x5, x27, ror #33
	eor x15, x15, x12, ror #55
	eor x24, x24, x12, ror #11
	eor x4, x4, x12, ror #39
	eor x6, x6, x12, ror #10
	eor x13, x13, x12, ror #5
	eor x0, x0, x5, ror #40
	eor x7, x7, x5, ror #56
	eor x21, x21, x5, ror #13
	eor x2, x2, x5, ror #55
	eor x23, x23, x5, ror #42
	umov x5, v24.d[0]
	umov x12, v25.d[0]
	eor x10, x10, x28, ror #10
	eor x17, x17, x28, ror #36
	eor x22, x22, x28, ror #37
	eor x1, x1, x28, ror #54
	eor x8, x8, x28, ror #30
	eor x5, x5, x30, ror #33
	eor x12, x12, x30, ror #40
	eor x19, x19, x30, ror #37
	eor x14, x14, x30, ror #21
	eor x3, x3, x30, ror #47
	bic x26, x4, x16, ror #20
	bic x27, x1, x4, ror #48
	bic x28, x0, x3, ror #12
	bic x30, x16, x0, ror #52
	eor x0, x0, x26, ror #56
	bic x26, x3, x1, ror #60
	eor x16, x16, x27, ror #60
	eor x1, x1, x28, ror #56
	eor x3, x3, x30, ror #0
	eor x4, x4, x26, ror #20
	bic x26, x21, x12, ror #53
	bic x27, x11, x21, ror #51
	bic x28, x10, x13, ror #27
	bic x30, x12, x10, ror #32
	eor x10, x10, x26, ror #43
	bic x26, x13, x11, ror #29
	eor x12, x12, x27, ror #24
	eor x11, x11, x28, ror #8
	eor x13, x13, x30, ror #5
	eor x21, x21, x26, ror #48
	bic x26, x22, x24, ror #36
	bic x27, x14, x22, ror #41
	bic x28, x20, x23, ror #35
	bic x30, x24, x20, ror #16
	eor x20, x20, x26, ror #12
	bic x26, x23, x14, ror #0
	eor x24, x24, x27, ror #51
	eor x14, x14, x28, ror #29
	eor x23, x23, x30, ror #13
	eor x22, x22, x26, ror #23
	bic x26, x9, x7, ror #32
	bic x27, x6, x9, ror #59
	bic x28, x5, x8, ror #48
	bic x30, x7, x5, ror #1
	eor x5, x5, x26, ror #31
	bic x26, x8, x6, ror #52
	eor x7, x7, x27, ror #37
	eor x6, x6, x28, ror #28
	eor x8, x8, x30, ror #15
	eor x9, x9, x26, ror #17
	bic x26, x19, x17, ror #59
	bic x27, x2, x19, ror #53
	bic x28, x15, x25, ror #48
	bic x30, x17, x15, ror #29
	eor x15, x15, x26, ror #40
	bic x26, x25, x2, ror #3
	eor x17, x17, x27, ror #16
	eor x2, x2, x28, ror #13
	eor x25, x25, x30, ror #51
	eor x19, x19, x26, ror #8
	movz x26, #1, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26, ror #0
	eor x26, x0, x10, ror #45
	dup v24.2d, x3
	dup v25.2d, x13
	eor x27, x16, x12, ror #1
	eor x28, x4, x21, ror #32
	eor x30, x1, x11, ror #29
	eor x3, x3, x13, ror #60
	eor x26, x26, x20, ror #9
	eor x27, x27, x24, ror #45
	eor x28, x28, x22, ror #29
	eor x30, x30, x14, ror #36
	eor x3, x3, x23, ror #32
	eor x26, x26, x5, ror #13
	eor x27, x27, x7, ror #0
	eor x28, x28, x9, ror #52
	eor x30, x30, x6, ror #41
	eor x3, x3, x8, ror #49
	eor x26, x26, x15, ror #21
	eor x27, x27, x17, ror #44
	eor x28, x28, x19, ror #5
	eor x30, x30, x2, ror #0
	eor x3, x3, x25, ror #57
	eor x13, x26, x28, ror #55
	eor x16, x16, x13, ror #52
	eor x12, x12, x13, ror #51
	eor x24, x24, x13, ror #7
	eor x7, x7, x13, ror #52
	eor x17, x17, x13, ror #8
	eor x13, x27, x30, ror #59
	eor x28, x28, x3, ror #19
	eor x30, x30, x26, ror #55
	eor x3, x3, x27, ror #63
	eor x4, x4, x13, ror #20
	eor x21, x21, x13, ror #52
	eor x22, x22, x13, ror #55
	eor x9, x9, x13, ror #32
	eor x19, x19, x13, ror #15
	eor x0, x0, x3, ror #12
	eor x10, x10, x3, ror #31
	eor x20, x20, x3, ror #3
	eor x5, x5, x3, ror #63
	eor x15, x15, x3, ror #55
	umov x3, v24.d[0]
	umov x13, v25.d[0]
	eor x1, x1, x28, ror #48
	eor x11, x11, x28, ror #19
	eor x14, x14, x28, ror #12
	eor x6, x6, x28, ror #7
	eor x2, x2, x28, ror #48
	eor x3, x3, x30, ror #60
	eor x13, x13, x30, ror #0
	eor x23, x23, x30, ror #28
	eor x8, x8, x30, ror #11
	eor x25, x25, x30, ror #3
	bic x26, x22, x12, ror #55
	bic x27, x6, x22, ror #14
	bic x28, x0, x25, ror #55
	bic x30, x12, x0, ror #31
	eor x0, x0, x26, ror #42
	bic x26, x25, x6, ror #37
	eor x12, x12, x27, ror #59
	eor x6, x6, x28, ror #36
	eor x25, x25, x30, ror #42
	eor x22, x22, x26, ror #13
	bic x26, x20, x13, ror #46
	bic x27, x7, x20, ror #39
	bic x28, x1, x19, ror #20
	bic x30, x13, x1, ror #56
	eor x1, x1, x26, ror #26
	bic x26, x19, x7, ror #31
	eor x13, x13, x27, ror #43
	eor x7, x7, x28, ror #13
	eor x19, x19, x30, ror #52
	eor x20, x20, x26, ror #58
	bic x26, x14, x21, ror #63
	bic x27, x8, x14, ror #30
	bic x28, x16, x15, ror #56
	bic x30, x21, x16, ror #57
	eor x16, x16, x26, ror #8
	bic x26, x15, x8, ror #50
	eor x21, x21, x27, ror #35
	eor x8, x8, x28, ror #22
	eor x15, x15, x30, ror #15
	eor x14, x14, x26, ror #48
	bic x26, x24, x10, ror #26
	bic x27, x9, x24, ror #18
	bic x28, x3, x2, ror #31
	bic x30, x10, x3, ror #40
	eor x3, x3, x26, ror #62
	bic x26, x2, x9, ror #13
	eor x10, x10, x27, ror #20
	eor x9, x9, x28, ror #20
	eor x2, x2, x30, ror #57
	eor x24, x24, x26, ror #33
	bic x26, x23, x11, ror #41
	bic x27, x5, x23, ror #33
	bic x28, x4, x17, ror #60
	bic x30, x11, x4, ror #12
	eor x4, x4, x26, ror #11
	bic x26, x17, x5, ror #46
	eor x11, x11, x27, ror #54
	eor x5, x5, x28, ror #22
	eor x17, x17, x30, ror #56
	eor x23, x23, x26, ror #49
	movz x26, #32897, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x1, ror #44
	dup v24.2d, x25
	dup v25.2d, x19
	eor x27, x12, x13, ror #19
	eor x28, x22, x20, ror #28
	eor x30, x6, x7, ror #3
	eor x25, x25, x19, ror #9
	eor x26, x26, x16, ror #11
	eor x27, x27, x21, ror #49
	eor x28, x28, x14, ror #41
	eor x30, x30, x8, ror #25
	eor x25, x25, x15, ror #12
	eor x26, x26, x3, ror #49
	eor x27, x27, x10, ror #40
	eor x28, x28, x24, ror #5
	eor x30, x30, x9, ror #1
	eor x25, x25, x2, ror #25
	eor x26, x26, x4, ror #58
	eor x27, x27, x11, ror #13
	eor x28, x28, x23, ror #27
	eor x30, x30, x5, ror #8
	eor x25, x25, x17, ror #63
	eor x19, x26, x28, ror #41
	eor x12, x12, x19, ror #31
	eor x13, x13, x19, ror #12
	eor x21, x21, x19, ror #46
	eor x10, x10, x19, ror #55
	eor x11, x11, x19, ror #18
	eor x19, x27, x30, ror #58
	eor x28, x28, x25, ror #12
	eor x30, x30, x26, ror #35
	eor x25, x25, x27, ror #41
	eor x22, x22, x19, ror #55
	eor x20, x20, x19, ror #27
	eor x14, x14, x19, ror #14
	eor x24, x24, x19, ror #50
	eor x23, x23, x19, ror #28
	eor x0, x0, x25, ror #55
	eor x1, x1, x25, ror #11
	eor x16, x16, x25, ror #44
	eor x3, x3, x25, ror #6
	eor x4, x4, x25, ror #61
	umov x19, v24.d[0]
	umov x25, v25.d[0]
	eor x6, x6, x28, ror #14
	eor x7, x7, x28, ror #11
	eor x8, x8, x28, ror #53
	eor x9, x9, x28, ror #13
	eor x5, x5, x28, ror #6
	eor x19, x19, x30, ror #37
	eor x25, x25, x30, ror #28
	eor x15, x15, x30, ror #25
	eor x2, x2, x30, ror #12
	eor x17, x17, x30, ror #38
	bic x26, x14, x13, ror #32
	bic x27, x9, x14, ror #32
	bic x28, x0, x17, ror #40
	bic x30, x13, x0, ror #56
	eor x0, x0, x26, ror #40
	bic x26, x17, x9, ror #32
	eor x13, x13, x27, ror #0
	eor x9, x9, x28, ror #56
	eor x17, x17, x30, ror #32
	eor x14, x14, x26, ror #0
	bic x26, x16, x25, ror #36
	bic x27, x10, x16, ror #44
	bic x28, x6, x23, ror #8
	bic x30, x25, x6, ror #20
	eor x6, x6, x26, ror #8
	bic x26, x23, x10, ror #20
	eor x25, x25, x27, ror #48
	eor x10, x10, x28, ror #36
	eor x23, x23, x30, ror #36
	eor x16, x16, x26, ror #0
	bic x26, x8, x20, ror #36
	bic x27, x2, x8, ror #20
	bic x28, x12, x4, ror #8
	bic x30, x20, x12, ror #32
	eor x12, x12, x26, ror #60
	bic x26, x4, x2, ror #32
	eor x20, x20, x27, ror #8
	eor x2, x2, x28, ror #24
	eor x4, x4, x30, ror #24
	eor x8, x8, x26, ror #12
	bic x26, x21, x1, ror #0
	bic x27, x24, x21, ror #40
	bic x28, x19, x5, ror #16
	bic x30, x1, x19, ror #20
	eor x19, x19, x26, ror #44
	bic x26, x5, x24, ror #52
	eor x1, x1, x27, ror #24
	eor x24, x24, x28, ror #60
	eor x5, x5, x30, ror #28
	eor x21, x21, x26, ror #36
	bic x26, x15, x7, ror #12
	bic x27, x3, x15, ror #20
	bic x28, x22, x11, ror #0
	bic x30, x7, x22, ror #4
	eor x22, x22, x26, ror #48
	bic x26, x11, x3, ror #28
	eor x7, x7, x27, ror #32
	eor x3, x3, x28, ror #36
	eor x11, x11, x30, ror #60
	eor x15, x15, x26, ror #16
	movz x26, #32777, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x6, ror #0
	dup v24.2d, x17
	dup v25.2d, x23
	eor x27, x13, x25, ror #36
	eor x28, x14, x16, ror #32
	eor x30, x9, x10, ror #20
	eor x17, x17, x23, ror #32
	eor x26, x26, x12, ror #32
	eor x27, x27, x20, ror #56
	eor x28, x28, x8, ror #52
	eor x30, x30, x2, ror #0
	eor x17, x17, x4, ror #0
	eor x26, x26, x19, ror #28
	eor x27, x27, x1, ror #0
	eor x28, x28, x21, ror #32
	eor x30, x30, x24, ror #24
	eor x17, x17, x5, ror #4
	eor x26, x26, x22, ror #44
	eor x27, x27, x7, ror #32
	eor x28, x28, x15, ror #52
	eor x30, x30, x3, ror #0
	eor x17, x17, x11, ror #4
	eor x23, x26, x28, ror #39
	eor x13, x13, x23, ror #56
	eor x25, x25, x23, ror #20
	eor x20, x20, x23, ror #0
	eor x1, x1, x23, ror #56
	eor x7, x7, x23, ror #24
	eor x23, x27, x30, ror #63
	eor x28, x28, x17, ror #63
	eor x30, x30, x26, ror #55
	eor x17, x17, x27, ror #31
	eor x14, x14, x23, ror #32
	eor x16, x16, x23, ror #0
	eor x8, x8, x23, ror #44
	eor x21, x21, x23, ror #0
	eor x15, x15, x23, ror #44
	eor x0, x0, x17, ror #40
	eor x6, x6, x17, ror #40
	eor x12, x12, x17, ror #8
	eor x19, x19, x17, ror #12
	eor x22, x22, x17, ror #60
	umov x17, v24.d[0]
	umov x23, v25.d[0]
	eor x9, x9, x28, ror #32
	eor x10, x10, x28, ror #12
	eor x2, x2, x28, ror #32
	eor x24, x24, x28, ror #8
	eor x3, x3, x28, ror #32
	eor x17, x17, x30, ror #32
	eor x23, x23, x30, ror #0
	eor x4, x4, x30, ror #32
	eor x5, x5, x30, ror #28
	eor x11, x11, x30, ror #28
	bic x26, x8, x25, ror #15
	bic x27, x24, x8, ror #38
	bic x28, x0, x11, ror #30
	bic x30, x25, x0, ror #0
	eor x0, x0, x26, ror #49
	bic x26, x11, x24, ror #45
	eor x25, x25, x27, ror #11
	eor x24, x24, x28, ror #53
	eor x11, x11, x30, ror #34
	eor x8, x8, x26, ror #45
	bic x26, x12, x23, ror #23
	bic x27, x1, x12, ror #2
	bic x28, x9, x15, ror #51
	bic x30, x23, x9, ror #56
	eor x9, x9, x26, ror #49
	bic x26, x15, x1, ror #60
	eor x23, x23, x27, ror #39
	eor x1, x1, x28, ror #17
	eor x15, x15, x30, ror #21
	eor x12, x12, x26, ror #2
	bic x26, x2, x16, ror #19
	bic x27, x5, x2, ror #11
	bic x28, x13, x22, ror #19
	bic x30, x16, x13, ror #5
	eor x13, x13, x26, ror #40
	bic x26, x22, x5, ror #10
	eor x16, x16, x27, ror #34
	eor x5, x5, x28, ror #35
	eor x22, x22, x30, ror #40
	eor x2, x2, x26, ror #43
	bic x26, x20, x6, ror #38
	bic x27, x21, x20, ror #61
	bic x28, x17, x3, ror #3
	bic x30, x6, x17, ror #49
	eor x17, x17, x26, ror #41
	bic x26, x3, x21, ror #41
	eor x6, x6, x27, ror #29
	eor x21, x21, x28, ror #20
	eor x3, x3, x30, ror #12
	eor x20, x20, x26, ror #26
	bic x26, x4, x10, ror #36
	bic x27, x19, x4, ror #14
	bic x28, x14, x7, ror #60
	bic x30, x10, x14, ror #5
	eor x14, x14, x26, ror #23
	bic x26, x7, x19, ror #13
	eor x10, x10, x27, ror #14
	eor x19, x19, x28, ror #55
	eor x7, x7, x30, ror #63
	eor x4, x4, x26, ror #37
	movz x26, #138, lsl #0
	eor x0, x0, x26, ror #0
	eor x26, x0, x9, ror #44
	dup v24.2d, x11
	dup v25.2d, x15
	eor x27, x25, x23, ror #52
	eor x28, x8, x12, ror #44
	eor x30, x24, x1, ror #16
	eor x11, x11, x15, ror #1
	eor x26, x26, x13, ror #7
	eor x27, x27, x16, ror #2
	eor x28, x28, x2, ror #62
	eor x30, x30, x5, ror #25
	eor x11, x11, x22, ror #60
	eor x26, x26, x17, ror #13
	eor x27, x27, x6, ror #28
	eor x28, x28, x20, ror #5
	eor x30, x30, x21, ror #46
	eor x11, x11, x3, ror #50
	eor x26, x26, x14, ror #42
	eor x27, x27, x10, ror #37
	eor x28, x28, x4, ror #16
	eor x30, x30, x19, ror #40
	eor x11, x11, x7, ror #8
	eor x15, x26, x28, ror #48
	eor x25, x25, x15, ror #0
	eor x23, x23, x15, ror #12
	eor x16, x16, x15, ror #62
	eor x6, x6, x15, ror #36
	eor x10, x10, x15, ror #27
	eor x15, x27, x30, ror #10
	eor x28, x28, x11, ror #44
	eor x30, x30, x26, ror #52
	eor x11, x11, x27, ror #33
	eor x8, x8, x15, ror #15
	eor x12, x12, x15, ror #35
	eor x2, x2, x15, ror #17
	eor x20, x20, x15, ror #10
	eor x4, x4, x15, ror #63
	eor x0, x0, x11, ror #30
	eor x9, x9, x11, ror #50
	eor x13, x13, x11, ror #23
	eor x17, x17, x11, ror #17
	eor x14, x14, x11, ror #52
	umov x11, v24.d[0]
	umov x15, v25.d[0]
	eor x24, x24, x28, ror #38
	eor x1, x1, x28, ror #22
	eor x5, x5, x28, ror #13
	eor x21, x21, x28, ror #56
	eor x19, x19, x28, ror #62
	eor x11, x11, x30, ror #45
	eor x15, x15, x30, ror #44
	eor x22, x22, x30, ror #49
	eor x3, x3, x30, ror #59
	eor x7, x7, x30, ror #37
	bic x26, x2, x23, ror #4
	bic x27, x21, x2, ror #32
	bic x28, x0, x7, ror #24
	bic x30, x23, x0, ror #56
	eor x0, x0, x26, ror #4
	bic x26, x7, x21, ror #12
	eor x23, x23, x27, ror #28
	eor x21, x21, x28, ror #28
	eor x7, x7, x30, ror #48
	eor x2, x2, x26, ror #20
	bic x26, x13, x15, ror #7
	bic x27, x6, x13, ror #21
	bic x28, x24, x4, ror #21
	bic x30, x15, x24, ror #36
	eor x24, x24, x26, ror #21
	bic x26, x4, x6, ror #43
	eor x15, x15, x27, ror #36
	eor x6, x6, x28, ror #0
	eor x4, x4, x30, ror #7
	eor x13, x13, x26, ror #0
	bic x26, x5, x12, ror #12
	bic x27, x3, x5, ror #3
	bic x28, x25, x14, ror #25
	bic x30, x12, x25, ror #40
	eor x25, x25, x26, ror #12
	bic x26, x14, x3, ror #48
	eor x12, x12, x27, ror #49
	eor x3, x3, x28, ror #55
	eor x14, x14, x30, ror #63
	eor x5, x5, x26, ror #13
	bic x26, x16, x9, ror #16
	bic x27, x20, x16, ror #17
	bic x28, x11, x19, ror #56
	bic x30, x9, x11, ror #59
	eor x11, x11, x26, ror #53
	bic x26, x19, x20, ror #44
	eor x9, x9, x27, ror #31
	eor x20, x20, x28, ror #28
	eor x19, x19, x30, ror #13
	eor x16, x16, x26, ror #3
	bic x26, x22, x1, ror #49
	bic x27, x17, x22, ror #15
	bic x28, x8, x10, ror #48
	bic x30, x1, x8, ror #15
	eor x8, x8, x26, ror #0
	bic x26, x10, x17, ror #1
	eor x1, x1, x27, ror #0
	eor x17, x17, x28, ror #15
	eor x10, x10, x30, ror #1
	eor x22, x22, x26, ror #48
	movz x26, #136, lsl #0
	eor x0, x0, x26, ror #0
	eor x26, x0, x24, ror #47
	dup v24.2d, x7
	dup v25.2d, x4
	eor x27, x23, x15, ror #3
	eor x28, x2, x13, ror #0
	eor x30, x21, x6, ror #11
	eor x7, x7, x4, ror #44
	eor x26, x26, x25, ror #63
	eor x27, x27, x12, ror #15
	eor x28, x28, x5, ror #7
	eor x30, x30, x3, ror #36
	eor x7, x7, x14, ror #0
	eor x26, x26, x11, ror #3
	eor x27, x27, x9, ror #0
	eor x28, x28, x16, ror #52
	eor x30, x30, x20, ror #3
	eor x7, x7, x19, ror #35
	eor x26, x26, x8, ror #51
	eor x27, x27, x1, ror #28
	eor x28, x28, x22, ror #47
	eor x30, x30, x17, ror #0
	eor x7, x7, x10, ror #11
	eor x4, x26, x28, ror #3
	eor x23, x23, x4, ror #56
	eor x15, x15, x4, ror #53
	eor x12, x12, x4, ror #41
	eor x9, x9, x4, ror #56
	eor x1, x1, x4, ror #28
	eor x4, x27, x30, ror #27
	eor x28, x28, x7, ror #19
	eor x30, x30, x26, ror #27
	eor x7, x7, x27, ror #47
	eor x2, x2, x4, ror #4
	eor x13, x13, x4, ror #4
	eor x5, x5, x4, ror #61
	eor x16, x16, x4, ror #16
	eor x22, x22, x4, ror #21
	eor x0, x0, x7, ror #24
	eor x24, x24, x7, ror #41
	eor x25, x25, x7, ror #25
	eor x11, x11, x7, ror #21
	eor x8, x8, x7, ror #37
	umov x4, v24.d[0]
	umov x7, v25.d[0]
	eor x21, x21, x28, ror #32
	eor x6, x6, x28, ror #21
	eor x3, x3, x28, ror #60
	eor x20, x20, x28, ror #29
	eor x17, x17, x28, ror #32
	eor x4, x4, x30, ror #12
	eor x7, x7, x30, ror #32
	eor x14, x14, x30, ror #12
	eor x19, x19, x30, ror #41
	eor x10, x10, x30, ror #1
	bic x26, x5, x15, ror #63
	bic x27, x20, x5, ror #14
	bic x28, x0, x10, ror #21
	bic x30, x15, x0, ror #33
	eor x0, x0, x26, ror #32
	bic x26, x10, x20, ror #61
	eor x15, x15, x27, ror #51
	eor x20, x20, x28, ror #46
	eor x10, x10, x30, ror #10
	eor x5, x5, x26, ror #53
	bic x26, x25, x7, ror #52
	bic x27, x9, x25, ror #33
	bic x28, x21, x22, ror #46
	bic x30, x7, x21, ror #24
	eor x21, x21, x26, ror #52
	bic x26, x22, x9, ror #37
	eor x7, x7, x27, ror #43
	eor x9, x9, x28, ror #45
	eor x22, x22, x30, ror #58
	eor x25, x25, x26, ror #58
	bic x26, x3, x13, ror #15
	bic x27, x19, x3, ror #60
	bic x28, x23, x8, ror #26
	bic x30, x13, x23, ror #9
	eor x23, x23, x26, ror #40
	bic x26, x8, x19, ror #18
	eor x13, x13, x27, ror #53
	eor x19, x19, x28, ror #20
	eor x8, x8, x30, ror #29
	eor x3, x3, x26, ror #50
	bic x26, x12, x24, ror #62
	bic x27, x16, x12, ror #36
	bic x28, x4, x17, ror #47
	bic x30, x24, x4, ror #50
	eor x4, x4, x26, ror #16
	bic x26, x17, x16, ror #61
	eor x24, x24, x27, ror #30
	eor x16, x16, x28, ror #20
	eor x17, x17, x30, ror #31
	eor x12, x12, x26, ror #31
	bic x26, x14, x6, ror #7
	bic x27, x11, x14, ror #23
	bic x28, x2, x1, ror #28
	bic x30, x6, x2, ror #14
	eor x2, x2, x26, ror #43
	bic x26, x1, x11, ror #56
	eor x6, x6, x27, ror #34
	eor x11, x11, x28, ror #44
	eor x1, x1, x30, ror #22
	eor x14, x14, x26, ror #49
	movz x26, #32777, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26, ror #0
	eor x26, x0, x21, ror #8
	dup v24.2d, x10
	dup v25.2d, x22
	eor x27, x15, x7, ror #17
	eor x28, x5, x25, ror #28
	eor x30, x20, x9, ror #9
	eor x10, x10, x22, ror #33
	eor x26, x26, x23, ror #7
	eor x27, x27, x13, ror #31
	eor x28, x28, x3, ror #15
	eor x30, x30, x19, ror #33
	eor x10, x10, x8, ror #12
	eor x26, x26, x4, ror #61
	eor x27, x27, x24, ror #44
	eor x28, x28, x12, ror #45
	eor x30, x30, x16, ror #23
	eor x10, x10, x17, ror #23
	eor x26, x26, x2, ror #6
	eor x27, x27, x6, ror #25
	eor x28, x28, x14, ror #17
	eor x30, x30, x11, ror #8
	eor x10, x10, x1, ror #13
	eor x22, x26, x28, ror #31
	eor x15, x15, x22, ror #33
	eor x7, x7, x22, ror #16
	eor x13, x13, x22, ror #2
	eor x24, x24, x22, ror #53
	eor x6, x6, x22, ror #8
	eor x22, x27, x30, ror #50
	eor x28, x28, x10, ror #52
	eor x30, x30, x26, ror #45
	eor x10, x10, x27, ror #9
	eor x5, x5, x22, ror #63
	eor x25, x25, x22, ror #35
	eor x3, x3, x22, ror #48
	eor x12, x12, x22, ror #18
	eor x14, x14, x22, ror #46
	eor x0, x0, x10, ror #21
	eor x21, x21, x10, ror #13
	eor x23, x23, x10, ror #14
	eor x4, x4, x10, ror #24
	eor x2, x2, x10, ror #15
	umov x10, v24.d[0]
	umov x22, v25.d[0]
	eor x20, x20, x28, ror #14
	eor x9, x9, x28, ror #5
	eor x19, x19, x28, ror #45
	eor x16, x16, x28, ror #55
	eor x11, x11, x28, ror #6
	eor x10, x10, x30, ror #61
	eor x22, x22, x30, ror #28
	eor x8, x8, x30, ror #49
	eor x17, x17, x30, ror #38
	eor x1, x1, x30, ror #48
	bic x26, x3, x7, ror #0
	bic x27, x16, x3, ror #48
	bic x28, x0, x1, ror #20
	bic x30, x7, x0, ror #60
	eor x0, x0, x26, ror #4
	bic x26, x1, x16, ror #0
	eor x7, x7, x27, ror #16
	eor x16, x16, x28, ror #44
	eor x1, x1, x30, ror #48
	eor x3, x3, x26, ror #16
	bic x26, x23, x22, ror #30
	bic x27, x24, x23, ror #38
	bic x28, x20, x14, ror #62
	bic x30, x22, x20, ror #20
	eor x20, x20, x26, ror #14
	bic x26, x14, x24, ror #42
	eor x22, x22, x27, ror #60
	eor x24, x24, x28, ror #24
	eor x14, x14, x30, ror #46
	eor x23, x23, x26, ror #48
	bic x26, x19, x25, ror #28
	bic x27, x17, x19, ror #54
	bic x28, x15, x2, ror #22
	bic x30, x25, x15, ror #40
	eor x15, x15, x26, ror #60
	bic x26, x2, x17, ror #48
	eor x25, x25, x27, ror #46
	eor x17, x17, x28, ror #58
	eor x2, x2, x30, ror #2
	eor x19, x19, x26, ror #26
	bic x26, x13, x21, ror #48
	bic x27, x12, x13, ror #54
	bic x28, x10, x11, ror #40
	bic x30, x21, x10, ror #22
	eor x10, x10, x26, ror #58
	bic x26, x11, x12, ror #28
	eor x21, x21, x27, ror #26
	eor x12, x12, x28, ror #60
	eor x11, x11, x30, ror #2
	eor x13, x13, x26, ror #46
	bic x26, x8, x9, ror #42
	bic x27, x4, x8, ror #38
	bic x28, x5, x6, ror #20
	bic x30, x9, x5, ror #62
	eor x5, x5, x26, ror #24
	bic x26, x6, x4, ror #30
	eor x9, x9, x27, ror #48
	eor x4, x4, x28, ror #14
	eor x6, x6, x30, ror #46
	eor x8, x8, x26, ror #60
	movz x26, #10, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26, ror #0
	eor x26, x0, x20, ror #54
	dup v24.2d, x1
	dup v25.2d, x14
	eor x27, x7, x22, ror #30
	eor x28, x3, x23, ror #0
	eor x30, x16, x24, ror #10
	eor x1, x1, x14, ror #32
	eor x26, x26, x15, ror #30
	eor x27, x27, x25, ror #50
	eor x28, x28, x19, ror #22
	eor x30, x30, x17, ror #16
	eor x1, x1, x2, ror #32
	eor x26, x26, x10, ror #58
	eor x27, x27, x21, ror #32
	eor x28, x28, x13, ror #48
	eor x30, x30, x12, ror #42
	eor x1, x1, x11, ror #14
	eor x26, x26, x5, ror #34
	eor x27, x27, x9, ror #32
	eor x28, x28, x8, ror #54
	eor x30, x30, x4, ror #0
	eor x1, x1, x6, ror #34
	eor x14, x26, x28, ror #3
	eor x7, x7, x14, ror #60
	eor x22, x22, x14, ror #30
	eor x25, x25, x14, ror #10
	eor x21, x21, x14, ror #28
	eor x9, x9, x14, ror #28
	eor x14, x27, x30, ror #15
	eor x28, x28, x1, ror #15
	eor x30, x30, x26, ror #43
	eor x1, x1, x27, ror #47
	eor x3, x3, x14, ror #0
	eor x23, x23, x14, ror #0
	eor x19, x19, x14, ror #42
	eor x13, x13, x14, ror #16
	eor x8, x8, x14, ror #10
	eor x0, x0, x1, ror #20
	eor x20, x20, x1, ror #30
	eor x15, x15, x1, ror #54
	eor x10, x10, x1, ror #26
	eor x5, x5, x1, ror #50
	umov x1, v24.d[0]
	umov x14, v25.d[0]
	eor x16, x16, x28, ror #48
	eor x24, x24, x28, ror #38
	eor x17, x17, x28, ror #32
	eor x12, x12, x28, ror #6
	eor x4, x4, x28, ror #48
	eor x1, x1, x30, ror #0
	eor x14, x14, x30, ror #32
	eor x2, x2, x30, ror #32
	eor x11, x11, x30, ror #50
	eor x6, x6, x30, ror #30
	bic x26, x19, x22, ror #7
	bic x27, x12, x19, ror #6
	bic x28, x0, x6, ror #40
	bic x30, x22, x0, ror #10
	eor x0, x0, x26, ror #47
	bic x26, x6, x12, ror #1
	eor x22, x22, x27, ror #51
	eor x12, x12, x28, ror #23
	eor x6, x6, x30, ror #14
	eor x19, x19, x26, ror #57
	bic x26, x15, x14, ror #5
	bic x27, x21, x15, ror #36
	bic x28, x16, x8, ror #5
	bic x30, x14, x16, ror #24
	eor x16, x16, x26, ror #35
	bic x26, x8, x21, ror #58
	eor x14, x14, x27, ror #23
	eor x21, x21, x28, ror #1
	eor x8, x8, x30, ror #35
	eor x15, x15, x26, ror #34
	bic x26, x17, x23, ror #51
	bic x27, x11, x17, ror #49
	bic x28, x7, x5, ror #13
	bic x30, x23, x7, ror #5
	eor x7, x7, x26, ror #8
	bic x26, x5, x11, ror #10
	eor x23, x23, x27, ror #28
	eor x11, x11, x28, ror #41
	eor x5, x5, x30, ror #46
	eor x17, x17, x26, ror #5
	bic x26, x25, x20, ror #38
	bic x27, x13, x25, ror #7
	bic x28, x1, x4, ror #35
	bic x30, x20, x1, ror #39
	eor x1, x1, x26, ror #51
	bic x26, x4, x13, ror #9
	eor x20, x20, x27, ror #19
	eor x13, x13, x28, ror #20
	eor x4, x4, x30, ror #54
	eor x25, x25, x26, ror #48
	bic x26, x2, x24, ror #26
	bic x27, x10, x2, ror #60
	bic x28, x3, x9, ror #28
	bic x30, x24, x3, ror #31
	eor x3, x3, x26, ror #7
	bic x26, x9, x10, ror #47
	eor x24, x24, x27, ror #42
	eor x10, x10, x28, ror #53
	eor x9, x9, x30, ror #5
	eor x2, x2, x26, ror #21
	movz x26, #32907, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26, ror #0
	eor x26, x0, x16, ror #56
	dup v24.2d, x6
	dup v25.2d, x8
	eor x27, x22, x14, ror #42
	eor x28, x19, x15, ror #44
	eor x30, x12, x21, ror #14
	eor x6, x6, x8, ror #21
	eor x26, x26, x7, ror #3
	eor x27, x27, x23, ror #8
	eor x28, x28, x17, ror #28
	eor x30, x30, x11, ror #49
	eor x6, x6, x5, ror #40
	eor x26, x26, x1, ror #57
	eor x27, x27, x20, ror #28
	eor x28, x28, x25, ror #61
	eor x30, x30, x13, ror #60
	eor x6, x6, x4, ror #52
	eor x26, x26, x3, ror #6
	eor x27, x27, x24, ror #49
	eor x28, x28, x2, ror #30
	eor x30, x30, x10, ror #40
	eor x6, x6, x9, ror #58
	eor x8, x26, x28, ror #46
	eor x22, x22, x8, ror #10
	eor x14, x14, x8, ror #32
	eor x23, x23, x8, ror #2
	eor x20, x20, x8, ror #46
	eor x24, x24, x8, ror #25
	eor x8, x27, x30, ror #50
	eor x28, x28, x6, ror #56
	eor x30, x30, x26, ror #22
	eor x6, x6, x27, ror #13
	eor x19, x19, x8, ror #7
	eor x15, x15, x8, ror #27
	eor x17, x17, x8, ror #43
	eor x25, x25, x8, ror #10
	eor x2, x2, x8, ror #41
	eor x0, x0, x6, ror #40
	eor x16, x16, x6, ror #48
	eor x7, x7, x6, ror #37
	eor x1, x1, x6, ror #47
	eor x3, x3, x6, ror #34
	umov x6, v24.d[0]
	umov x8, v25.d[0]
	eor x12, x12, x28, ror #6
	eor x21, x21, x28, ror #56
	eor x11, x11, x28, ror #21
	eor x13, x13, x28, ror #10
	eor x10, x10, x28, ror #30
	eor x6, x6, x30, ror #1
	eor x8, x8, x30, ror #44
	eor x5, x5, x30, ror #25
	eor x4, x4, x30, ror #13
	eor x9, x9, x30, ror #7
	bic x26, x17, x14, ror #20
	bic x27, x13, x17, ror #16
	bic x28, x0, x9, ror #20
	bic x30, x14, x0, ror #12
	eor x0, x0, x26, ror #32
	bic x26, x9, x13, ror #60
	eor x14, x14, x27, ror #28
	eor x13, x13, x28, ror #48
	eor x9, x9, x30, ror #32
	eor x17, x17, x26, ror #52
	bic x26, x7, x8, ror #41
	bic x27, x20, x7, ror #27
	bic x28, x12, x2, ror #3
	bic x30, x8, x12, ror #36
	eor x12, x12, x26, ror #51
	bic x26, x2, x20, ror #21
	eor x8, x8, x27, ror #60
	eor x20, x20, x28, ror #40
	eor x2, x2, x30, ror #25
	eor x7, x7, x26, ror #16
	bic x26, x11, x15, ror #20
	bic x27, x4, x11, ror #45
	bic x28, x22, x3, ror #63
	bic x30, x15, x22, ror #32
	eor x22, x22, x26, ror #12
	bic x26, x3, x4, ror #32
	eor x15, x15, x27, ror #63
	eor x4, x4, x28, ror #33
	eor x3, x3, x30, ror #33
	eor x11, x11, x26, ror #51
	bic x26, x23, x16, ror #32
	bic x27, x25, x23, ror #23
	bic x28, x6, x10, ror #12
	bic x30, x16, x6, ror #57
	eor x6, x6, x26, ror #39
	bic x26, x10, x25, ror #4
	eor x16, x16, x27, ror #9
	eor x25, x25, x28, ror #48
	eor x10, x10, x30, ror #59
	eor x23, x23, x26, ror #37
	bic x26, x5, x21, ror #23
	bic x27, x1, x5, ror #25
	bic x28, x19, x24, ror #52
	bic x30, x21, x19, ror #49
	eor x19, x19, x26, ror #56
	bic x26, x24, x1, ror #43
	eor x21, x21, x27, ror #16
	eor x1, x1, x28, ror #33
	eor x24, x24, x30, ror #27
	eor x5, x5, x26, ror #60
	movz x26, #139, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x12, ror #13
	dup v24.2d, x9
	dup v25.2d, x2
	eor x27, x14, x8, ror #53
	eor x28, x17, x7, ror #32
	eor x30, x13, x20, ror #21
	eor x9, x9, x2, ror #60
	eor x26, x26, x22, ror #53
	eor x27, x27, x15, ror #33
	eor x28, x28, x11, ror #33
	eor x30, x30, x4, ror #4
	eor x9, x9, x3, ror #32
	eor x26, x26, x6, ror #13
	eor x27, x27, x16, ror #32
	eor x28, x28, x23, ror #20
	eor x30, x30, x25, ror #13
	eor x9, x9, x10, ror #5
	eor x26, x26, x19, ror #49
	eor x27, x27, x21, ror #12
	eor x28, x28, x5, ror #9
	eor x30, x30, x1, ror #0
	eor x9, x9, x24, ror #17
	eor x2, x26, x28, ror #31
	eor x14, x14, x2, ror #12
	eor x8, x8, x2, ror #23
	eor x15, x15, x2, ror #43
	eor x16, x16, x2, ror #44
	eor x21, x21, x2, ror #0
	eor x2, x27, x30, ror #27
	eor x28, x28, x9, ror #51
	eor x30, x30, x26, ror #47
	eor x9, x9, x27, ror #31
	eor x17, x17, x2, ror #20
	eor x7, x7, x2, ror #52
	eor x11, x11, x2, ror #51
	eor x23, x23, x2, ror #0
	eor x5, x5, x2, ror #11
	eor x0, x0, x9, ror #20
	eor x12, x12, x9, ror #7
	eor x22, x22, x9, ror #31
	eor x6, x6, x9, ror #7
	eor x19, x19, x9, ror #35
	umov x2, v24.d[0]
	umov x9, v25.d[0]
	eor x13, x13, x28, ror #16
	eor x20, x20, x28, ror #59
	eor x4, x4, x28, ror #12
	eor x25, x25, x28, ror #3
	eor x1, x1, x28, ror #16
	eor x2, x2, x30, ror #60
	eor x9, x9, x30, ror #0
	eor x3, x3, x30, ror #28
	eor x10, x10, x30, ror #55
	eor x24, x24, x30, ror #43
	bic x26, x11, x8, ror #39
	bic x27, x25, x11, ror #14
	bic x28, x0, x24, ror #23
	bic x30, x8, x0, ror #3
	eor x0, x0, x26, ror #22
	bic x26, x24, x25, ror #49
	eor x8, x8, x27, ror #11
	eor x25, x25, x28, ror #56
	eor x24, x24, x30, ror #38
	eor x11, x11, x26, ror #1
	bic x26, x22, x9, ror #10
	bic x27, x16, x22, ror #11
	bic x28, x13, x5, ror #56
	bic x30, x9, x13, ror #56
	eor x13, x13, x26, ror #62
	bic x26, x5, x16, ror #59
	eor x9, x9, x27, ror #43
	eor x16, x16, x28, ror #13
	eor x5, x5, x30, ror #16
	eor x22, x22, x26, ror #58
	bic x26, x4, x7, ror #63
	bic x27, x10, x4, ror #42
	bic x28, x14, x19, ror #44
	bic x30, x7, x14, ror #57
	eor x14, x14, x26, ror #8
	bic x26, x19, x10, ror #50
	eor x7, x7, x27, ror #23
	eor x10, x10, x28, ror #34
	eor x19, x19, x30, ror #27
	eor x4, x4, x26, ror #36
	bic x26, x15, x12, ror #30
	bic x27, x23, x15, ror #38
	bic x28, x2, x1, ror #31
	bic x30, x12, x2, ror #16
	eor x2, x2, x26, ror #18
	bic x26, x1, x23, ror #13
	eor x12, x12, x27, ror #60
	eor x23, x23, x28, ror #20
	eor x1, x1, x30, ror #17
	eor x15, x15, x26, ror #13
	bic x26, x3, x20, ror #33
	bic x27, x6, x3, ror #41
	bic x28, x17, x21, ror #28
	bic x30, x20, x17, ror #52
	eor x17, x17, x26, ror #43
	bic x26, x21, x6, ror #38
	eor x20, x20, x27, ror #54
	eor x6, x6, x28, ror #62
	eor x21, x21, x30, ror #48
	eor x3, x3, x26, ror #49
	movz x26, #32905, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x13, ror #52
	dup v24.2d, x24
	dup v25.2d, x5
	eor x27, x8, x9, ror #63
	eor x28, x11, x22, ror #28
	eor x30, x25, x16, ror #31
	eor x24, x24, x5, ror #21
	eor x26, x26, x14, ror #51
	eor x27, x27, x7, ror #61
	eor x28, x28, x4, ror #37
	eor x30, x30, x10, ror #9
	eor x24, x24, x19, ror #8
	eor x26, x26, x2, ror #57
	eor x27, x27, x12, ror #44
	eor x28, x28, x15, ror #53
	eor x30, x30, x23, ror #29
	eor x24, x24, x1, ror #1
	eor x26, x26, x17, ror #34
	eor x27, x27, x20, ror #49
	eor x28, x28, x3, ror #55
	eor x30, x30, x6, ror #28
	eor x24, x24, x21, ror #39
	eor x5, x26, x28, ror #21
	eor x8, x8, x5, ror #3
	eor x9, x9, x5, ror #4
	eor x7, x7, x5, ror #6
	eor x12, x12, x5, ror #23
	eor x20, x20, x5, ror #18
	eor x5, x27, x30, ror #10
	eor x28, x28, x24, ror #0
	eor x30, x30, x26, ror #55
	eor x24, x24, x27, ror #37
	eor x11, x11, x5, ror #39
	eor x22, x22, x5, ror #11
	eor x4, x4, x5, ror #2
	eor x15, x15, x5, ror #50
	eor x3, x3, x5, ror #48
	eor x0, x0, x24, ror #23
	eor x13, x13, x24, ror #35
	eor x14, x14, x24, ror #36
	eor x2, x2, x24, ror #30
	eor x17, x17, x24, ror #53
	umov x5, v24.d[0]
	umov x24, v25.d[0]
	eor x25, x25, x28, ror #14
	eor x16, x16, x28, ror #47
	eor x10, x10, x28, ror #5
	eor x23, x23, x28, ror #49
	eor x6, x6, x28, ror #50
	eor x5, x5, x30, ror #49
	eor x24, x24, x30, ror #28
	eor x19, x19, x30, ror #41
	eor x1, x1, x30, ror #48
	eor x21, x21, x30, ror #10
	bic x26, x4, x9, ror #0
	bic x27, x23, x4, ror #0
	bic x28, x0, x21, ror #48
	bic x30, x9, x0, ror #48
	eor x0, x0, x26, ror #16
	bic x26, x21, x23, ror #32
	eor x9, x9, x27, ror #0
	eor x23, x23, x28, ror #48
	eor x21, x21, x30, ror #32
	eor x4, x4, x26, ror #32
	bic x26, x14, x24, ror #40
	bic x27, x12, x14, ror #52
	bic x28, x25, x3, ror #36
	bic x30, x24, x25, ror #20
	eor x25, x25, x26, ror #4
	bic x26, x3, x12, ror #44
	eor x24, x24, x27, ror #36
	eor x12, x12, x28, ror #48
	eor x3, x3, x30, ror #8
	eor x14, x14, x26, ror #32
	bic x26, x10, x22, ror #52
	bic x27, x1, x10, ror #40
	bic x28, x8, x17, ror #20
	bic x30, x22, x8, ror #16
	eor x8, x8, x26, ror #60
	bic x26, x17, x1, ror #0
	eor x22, x22, x27, ror #36
	eor x1, x1, x28, ror #44
	eor x17, x17, x30, ror #28
	eor x10, x10, x26, ror #24
	bic x26, x7, x13, ror #32
	bic x27, x15, x7, ror #52
	bic x28, x5, x6, ror #48
	bic x30, x13, x5, ror #44
	eor x5, x5, x26, ror #52
	bic x26, x6, x15, ror #16
	eor x13, x13, x27, ror #44
	eor x15, x15, x28, ror #0
	eor x6, x6, x30, ror #36
	eor x7, x7, x26, ror #60
	bic x26, x19, x16, ror #56
	bic x27, x2, x19, ror #40
	bic x28, x11, x20, ror #20
	bic x30, x16, x11, ror #40
	eor x11, x11, x26, ror #32
	bic x26, x20, x2, ror #36
	eor x16, x16, x27, ror #32
	eor x2, x2, x28, ror #8
	eor x20, x20, x30, ror #4
	eor x19, x19, x26, ror #52
	movz x26, #32771, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x25, ror #44
	dup v24.2d, x21
	dup v25.2d, x3
	eor x27, x9, x24, ror #8
	eor x28, x4, x14, ror #32
	eor x30, x23, x12, ror #44
	eor x21, x21, x3, ror #32
	eor x26, x26, x8, ror #60
	eor x27, x27, x22, ror #28
	eor x28, x28, x10, ror #40
	eor x30, x30, x1, ror #0
	eor x21, x21, x17, ror #32
	eor x26, x26, x5, ror #60
	eor x27, x27, x13, ror #0
	eor x28, x28, x7, ror #32
	eor x30, x30, x15, ror #44
	eor x21, x21, x6, ror #60
	eor x26, x26, x11, ror #24
	eor x27, x27, x16, ror #32
	eor x28, x28, x19, ror #40
	eor x30, x30, x2, ror #0
	eor x21, x21, x20, ror #60
	eor x3, x26, x28, ror #15
	eor x9, x9, x3, ror #48
	eor x24, x24, x3, ror #40
	eor x22, x22, x3, ror #20
	eor x13, x13, x3, ror #48
	eor x16, x16, x3, ror #16
	eor x3, x27, x30, ror #63
	eor x28, x28, x21, ror #31
	eor x30, x30, x26, ror #47
	eor x21, x21, x27, ror #31
	eor x4, x4, x3, ror #0
	eor x14, x14, x3, ror #32
	eor x10, x10, x3, ror #24
	eor x7, x7, x3, ror #32
	eor x19, x19, x3, ror #24
	eor x0, x0, x21, ror #48
	eor x25, x25, x21, ror #4
	eor x8, x8, x21, ror #52
	eor x5, x5, x21, ror #52
	eor x11, x11, x21, ror #24
	umov x3, v24.d[0]
	umov x21, v25.d[0]
	eor x23, x23, x28, ror #0
	eor x12, x12, x28, ror #20
	eor x1, x1, x28, ror #0
	eor x15, x15, x28, ror #20
	eor x2, x2, x28, ror #0
	eor x3, x3, x30, ror #32
	eor x21, x21, x30, ror #0
	eor x17, x17, x30, ror #0
	eor x6, x6, x30, ror #36
	eor x20, x20, x30, ror #36
	bic x26, x10, x24, ror #31
	bic x27, x15, x10, ror #38
	bic x28, x0, x20, ror #30
	bic x30, x24, x0, ror #20
	eor x0, x0, x26, ror #13
	bic x26, x20, x15, ror #9
	eor x24, x24, x27, ror #59
	eor x15, x15, x28, ror #25
	eor x20, x20, x30, ror #14
	eor x10, x10, x26, ror #17
	bic x26, x8, x21, ror #3
	bic x27, x13, x8, ror #22
	bic x28, x23, x19, ror #7
	bic x30, x21, x23, ror #56
	eor x23, x23, x26, ror #5
	bic x26, x19, x13, ror #40
	eor x21, x21, x27, ror #39
	eor x13, x13, x28, ror #17
	eor x19, x19, x30, ror #1
	eor x8, x8, x26, ror #2
	bic x26, x1, x14, ror #51
	bic x27, x6, x1, ror #19
	bic x28, x9, x11, ror #55
	bic x30, x14, x9, ror #37
	eor x9, x9, x26, ror #40
	bic x26, x11, x6, ror #30
	eor x14, x14, x27, ror #58
	eor x6, x6, x28, ror #43
	eor x11, x11, x30, ror #36
	eor x1, x1, x26, ror #15
	bic x26, x22, x25, ror #38
	bic x27, x7, x22, ror #1
	bic x28, x3, x2, ror #3
	bic x30, x25, x3, ror #13
	eor x3, x3, x26, ror #13
	bic x26, x2, x7, ror #9
	eor x25, x25, x27, ror #25
	eor x7, x7, x28, ror #52
	eor x2, x2, x30, ror #48
	eor x22, x22, x26, ror #54
	bic x26, x17, x12, ror #28
	bic x27, x5, x17, ror #22
	bic x28, x4, x16, ror #28
	bic x30, x12, x4, ror #13
	eor x4, x4, x26, ror #23
	bic x26, x16, x5, ror #37
	eor x12, x12, x27, ror #14
	eor x5, x5, x28, ror #63
	eor x16, x16, x30, ror #23
	eor x17, x17, x26, ror #5
	movz x26, #32770, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x23, ror #52
	dup v24.2d, x20
	dup v25.2d, x19
	eor x27, x24, x21, ror #16
	eor x28, x10, x8, ror #44
	eor x30, x15, x13, ror #60
	eor x20, x20, x19, ror #29
	eor x26, x26, x9, ror #15
	eor x27, x27, x14, ror #62
	eor x28, x28, x1, ror #42
	eor x30, x30, x6, ror #61
	eor x20, x20, x11, ror #40
	eor x26, x26, x3, ror #21
	eor x27, x27, x25, ror #28
	eor x28, x28, x22, ror #21
	eor x30, x30, x7, ror #58
	eor x20, x20, x2, ror #58
	eor x26, x26, x4, ror #18
	eor x27, x27, x12, ror #25
	eor x28, x28, x17, ror #28
	eor x30, x30, x5, ror #44
	eor x20, x20, x16, ror #16
	eor x19, x26, x28, ror #12
	eor x24, x24, x19, ror #20
	eor x21, x21, x19, ror #4
	eor x14, x14, x19, ror #22
	eor x25, x25, x19, ror #56
	eor x12, x12, x19, ror #59
	eor x19, x27, x30, ror #58
	eor x28, x28, x20, ror #16
	eor x30, x30, x26, ror #24
	eor x20, x20, x27, ror #13
	eor x10, x10, x19, ror #31
	eor x8, x8, x19, ror #51
	eor x1, x1, x19, ror #53
	eor x22, x22, x19, ror #10
	eor x17, x17, x19, ror #3
	eor x0, x0, x20, ror #30
	eor x23, x23, x20, ror #42
	eor x9, x9, x20, ror #15
	eor x3, x3, x20, ror #9
	eor x4, x4, x20, ror #12
	umov x19, v24.d[0]
	umov x20, v25.d[0]
	eor x15, x15, x28, ror #38
	eor x13, x13, x28, ror #42
	eor x6, x6, x28, ror #41
	eor x7, x7, x28, ror #44
	eor x5, x5, x28, ror #58
	eor x19, x19, x30, ror #9
	eor x20, x20, x30, ror #44
	eor x11, x11, x30, ror #33
	eor x2, x2, x30, ror #15
	eor x16, x16, x30, ror #57
	bic x26, x1, x21, ror #4
	bic x27, x7, x1, ror #0
	bic x28, x0, x16, ror #32
	bic x30, x21, x0, ror #48
	eor x0, x0, x26, ror #12
	bic x26, x16, x7, ror #44
	eor x21, x21, x27, ror #60
	eor x7, x7, x28, ror #52
	eor x16, x16, x30, ror #48
	eor x1, x1, x26, ror #20
	bic x26, x9, x20, ror #27
	bic x27, x25, x9, ror #49
	bic x28, x15, x17, ror #33
	bic x30, x20, x15, ror #36
	eor x15, x15, x26, ror #1
	bic x26, x17, x25, ror #47
	eor x20, x20, x27, ror #52
	eor x25, x25, x28, ror #48
	eor x17, x17, x30, ror #59
	eor x9, x9, x26, ror #32
	bic x26, x6, x8, ror #40
	bic x27, x2, x6, ror #59
	bic x28, x24, x4, ror #21
	bic x30, x8, x24, ror #56
	eor x24, x24, x26, ror #32
	bic x26, x4, x2, ror #16
	eor x8, x8, x27, ror #29
	eor x2, x2, x28, ror #27
	eor x4, x4, x30, ror #51
	eor x6, x6, x26, ror #53
	bic x26, x14, x23, ror #48
	bic x27, x22, x14, ror #13
	bic x28, x19, x5, ror #24
	bic x30, x23, x19, ror #51
	eor x19, x19, x26, ror #29
	bic x26, x5, x22, ror #56
	eor x23, x23, x27, ror #3
	eor x22, x22, x28, ror #48
	eor x5, x5, x30, ror #53
	eor x14, x14, x26, ror #59
	bic x26, x11, x13, ror #13
	bic x27, x3, x11, ror #51
	bic x28, x10, x12, ror #52
	bic x30, x13, x10, ror #35
	eor x10, x10, x26, ror #16
	bic x26, x12, x3, ror #41
	eor x13, x13, x27, ror #0
	eor x3, x3, x28, ror #35
	eor x12, x12, x30, ror #41
	eor x11, x11, x26, ror #36
	movz x26, #128, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x15, ror #11
	dup v24.2d, x16
	dup v25.2d, x17
	eor x27, x21, x20, ror #23
	eor x28, x1, x9, ror #0
	eor x30, x7, x25, ror #15
	eor x16, x16, x17, ror #12
	eor x26, x26, x24, ror #43
	eor x27, x27, x8, ror #35
	eor x28, x28, x6, ror #63
	eor x30, x30, x2, ror #4
	eor x16, x16, x4, ror #32
	eor x26, x26, x19, ror #3
	eor x27, x27, x23, ror #0
	eor x28, x28, x14, ror #20
	eor x30, x30, x22, ror #7
	eor x16, x16, x5, ror #59
	eor x26, x26, x10, ror #15
	eor x27, x27, x13, ror #28
	eor x28, x28, x11, ror #19
	eor x30, x30, x3, ror #32
	eor x16, x16, x12, ror #35
	eor x17, x26, x28, ror #11
	eor x21, x21, x17, ror #48
	eor x20, x20, x17, ror #25
	eor x8, x8, x17, ror #13
	eor x23, x23, x17, ror #48
	eor x13, x13, x17, ror #20
	eor x17, x27, x30, ror #59
	eor x28, x28, x16, ror #19
	eor x30, x30, x26, ror #51
	eor x16, x16, x27, ror #47
	eor x1, x1, x17, ror #4
	eor x9, x9, x17, ror #4
	eor x6, x6, x17, ror #5
	eor x14, x14, x17, ror #48
	eor x11, x11, x17, ror #49
	eor x0, x0, x16, ror #32
	eor x15, x15, x16, ror #21
	eor x24, x24, x16, ror #53
	eor x19, x19, x16, ror #29
	eor x10, x10, x16, ror #17
	umov x16, v24.d[0]
	umov x17, v25.d[0]
	eor x7, x7, x28, ror #0
	eor x25, x25, x28, ror #49
	eor x2, x2, x28, ror #60
	eor x22, x22, x28, ror #57
	eor x3, x3, x28, ror #32
	eor x16, x16, x30, ror #44
	eor x17, x17, x30, ror #32
	eor x4, x4, x30, ror #12
	eor x5, x5, x30, ror #49
	eor x12, x12, x30, ror #9
	bic x26, x6, x20, ror #27
	bic x27, x22, x6, ror #34
	bic x28, x0, x12, ror #53
	bic x30, x20, x0, ror #5
	eor x0, x0, x26, ror #32
	bic x26, x12, x22, ror #9
	eor x20, x20, x27, ror #3
	eor x22, x22, x28, ror #2
	eor x12, x12, x30, ror #6
	eor x6, x6, x26, ror #21
	bic x26, x24, x17, ror #48
	bic x27, x23, x24, ror #5
	bic x28, x7, x11, ror #50
	bic x30, x17, x7, ror #24
	eor x7, x7, x26, ror #56
	bic x26, x11, x23, ror #1
	eor x17, x17, x27, ror #11
	eor x23, x23, x28, ror #13
	eor x11, x11, x30, ror #54
	eor x24, x24, x26, ror #58
	bic x26, x2, x9, ror #15
	bic x27, x5, x2, ror #36
	bic x28, x21, x10, ror #46
	bic x30, x9, x21, ror #9
	eor x21, x21, x26, ror #40
	bic x26, x10, x5, ror #22
	eor x9, x9, x27, ror #13
	eor x5, x5, x28, ror #60
	eor x10, x10, x30, ror #9
	eor x2, x2, x26, ror #6
	bic x26, x8, x15, ror #62
	bic x27, x14, x8, ror #24
	bic x28, x16, x3, ror #47
	bic x30, x15, x16, ror #30
	eor x16, x16, x26, ror #36
	bic x26, x3, x14, ror #29
	eor x15, x15, x27, ror #42
	eor x14, x14, x28, ror #52
	eor x3, x3, x30, ror #51
	eor x8, x8, x26, ror #11
	bic x26, x4, x25, ror #11
	bic x27, x19, x4, ror #63
	bic x28, x1, x13, ror #28
	bic x30, x25, x1, ror #42
	eor x1, x1, x26, ror #11
	bic x26, x13, x19, ror #48
	eor x25, x25, x27, ror #54
	eor x19, x19, x28, ror #52
	eor x13, x13, x30, ror #58
	eor x4, x4, x26, ror #17
	movz x26, #32778, lsl #0
	eor x0, x0, x26, ror #0
	eor x26, x0, x7, ror #48
	dup v24.2d, x12
	dup v25.2d, x11
	eor x27, x20, x17, ror #29
	eor x28, x6, x24, ror #8
	eor x30, x22, x23, ror #37
	eor x12, x12, x11, ror #45
	eor x26, x26, x21, ror #15
	eor x27, x27, x9, ror #11
	eor x28, x28, x2, ror #23
	eor x30, x30, x5, ror #21
	eor x12, x12, x10, ror #8
	eor x26, x26, x16, ror #5
	eor x27, x27, x15, ror #44
	eor x28, x28, x8, ror #9
	eor x30, x30, x14, ror #19
	eor x12, x12, x3, ror #63
	eor x26, x26, x1, ror #14
	eor x27, x27, x25, ror #41
	eor x28, x28, x4, ror #57
	eor x30, x30, x19, ror #28
	eor x12, x12, x13, ror #53
	eor x11, x26, x28, ror #31
	eor x20, x20, x11, ror #5
	eor x17, x17, x11, ror #40
	eor x9, x9, x11, ror #58
	eor x15, x15, x11, ror #25
	eor x25, x25, x11, ror #28
	eor x11, x27, x30, ror #2
	eor x28, x28, x12, ror #20
	eor x30, x30, x26, ror #1
	eor x12, x12, x27, ror #5
	eor x6, x6, x11, ror #27
	eor x24, x24, x11, ror #19
	eor x2, x2, x11, ror #4
	eor x8, x8, x11, ror #18
	eor x4, x4, x11, ror #34
	eor x0, x0, x12, ror #53
	eor x7, x7, x12, ror #5
	eor x21, x21, x12, ror #38
	eor x16, x16, x12, ror #48
	eor x1, x1, x12, ror #39
	umov x11, v24.d[0]
	umov x12, v25.d[0]
	eor x22, x22, x28, ror #34
	eor x23, x23, x28, ror #61
	eor x5, x5, x28, ror #13
	eor x14, x14, x28, ror #15
	eor x19, x19, x28, ror #6
	eor x11, x11, x30, ror #9
	eor x12, x12, x30, ror #28
	eor x10, x10, x30, ror #1
	eor x3, x3, x30, ror #10
	eor x13, x13, x30, ror #20
	bic x26, x2, x17, ror #32
	bic x27, x14, x2, ror #16
	bic x28, x0, x13, ror #28
	bic x30, x17, x0, ror #20
	eor x0, x0, x26, ror #12
	bic x26, x13, x14, ror #32
	eor x17, x17, x27, ror #16
	eor x14, x14, x28, ror #4
	eor x13, x13, x30, ror #16
	eor x2, x2, x26, ror #16
	bic x26, x21, x12, ror #2
	bic x27, x15, x21, ror #18
	bic x28, x22, x4, ror #58
	bic x30, x12, x22, ror #20
	eor x22, x22, x26, ror #42
	bic x26, x4, x15, ror #30
	eor x12, x12, x27, ror #44
	eor x15, x15, x28, ror #40
	eor x4, x4, x30, ror #50
	eor x21, x21, x26, ror #16
	bic x26, x5, x24, ror #40
	bic x27, x3, x5, ror #14
	bic x28, x20, x1, ror #2
	bic x30, x24, x20, ror #24
	eor x20, x20, x26, ror #0
	bic x26, x1, x3, ror #48
	eor x24, x24, x27, ror #10
	eor x3, x3, x28, ror #14
	eor x1, x1, x30, ror #38
	eor x5, x5, x26, ror #2
	bic x26, x9, x7, ror #16
	bic x27, x8, x9, ror #34
	bic x28, x11, x19, ror #8
	bic x30, x7, x11, ror #14
	eor x11, x11, x26, ror #34
	bic x26, x19, x8, ror #56
	eor x7, x7, x27, ror #14
	eor x8, x8, x28, ror #0
	eor x19, x19, x30, ror #42
	eor x9, x9, x26, ror #38
	bic x26, x10, x23, ror #22
	bic x27, x16, x10, ror #58
	bic x28, x6, x25, ror #0
	bic x30, x23, x6, ror #54
	eor x6, x6, x26, ror #52
	bic x26, x25, x16, ror #58
	eor x23, x23, x27, ror #48
	eor x16, x16, x28, ror #6
	eor x25, x25, x30, ror #10
	eor x10, x10, x26, ror #12
	movz x26, #10, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x22, ror #34
	dup v24.2d, x13
	dup v25.2d, x4
	eor x27, x17, x12, ror #34
	eor x28, x2, x21, ror #0
	eor x30, x14, x15, ror #62
	eor x13, x13, x4, ror #0
	eor x26, x26, x20, ror #58
	eor x27, x27, x24, ror #54
	eor x28, x28, x5, ror #46
	eor x30, x30, x3, ror #48
	eor x13, x13, x1, ror #32
	eor x26, x26, x11, ror #26
	eor x27, x27, x7, ror #32
	eor x28, x28, x9, ror #48
	eor x30, x30, x8, ror #30
	eor x13, x13, x19, ror #6
	eor x26, x26, x6, ror #34
	eor x27, x27, x23, ror #0
	eor x28, x28, x10, ror #10
	eor x30, x30, x16, ror #32
	eor x13, x13, x25, ror #6
	eor x4, x26, x28, ror #11
	eor x17, x17, x4, ror #20
	eor x12, x12, x4, ror #50
	eor x24, x24, x4, ror #30
	eor x7, x7, x4, ror #52
	eor x23, x23, x4, ror #20
	eor x4, x27, x30, ror #15
	eor x28, x28, x13, ror #15
	eor x30, x30, x26, ror #3
	eor x13, x13, x27, ror #15
	eor x2, x2, x4, ror #32
	eor x21, x21, x4, ror #32
	eor x5, x5, x4, ror #50
	eor x9, x9, x4, ror #48
	eor x10, x10, x4, ror #22
	eor x0, x0, x13, ror #28
	eor x22, x22, x13, ror #58
	eor x20, x20, x13, ror #34
	eor x11, x11, x13, ror #2
	eor x6, x6, x13, ror #58
	umov x4, v24.d[0]
	umov x13, v25.d[0]
	eor x14, x14, x28, ror #16
	eor x15, x15, x28, ror #18
	eor x3, x3, x28, ror #32
	eor x8, x8, x28, ror #50
	eor x16, x16, x28, ror #48
	eor x4, x4, x30, ror #32
	eor x13, x13, x30, ror #32
	eor x1, x1, x30, ror #0
	eor x19, x19, x30, ror #26
	eor x25, x25, x30, ror #26
	bic x26, x5, x12, ror #19
	bic x27, x8, x5, ror #10
	bic x28, x0, x25, ror #20
	bic x30, x12, x0, ror #30
	eor x0, x0, x26, ror #15
	bic x26, x25, x8, ror #49
	eor x12, x12, x27, ror #35
	eor x8, x8, x28, ror #59
	eor x25, x25, x30, ror #14
	eor x5, x5, x26, ror #5
	bic x26, x20, x13, ror #17
	bic x27, x7, x20, ror #24
	bic x28, x14, x10, ror #57
	bic x30, x13, x14, ror #24
	eor x14, x14, x26, ror #23
	bic x26, x10, x7, ror #6
	eor x13, x13, x27, ror #23
	eor x7, x7, x28, ror #1
	eor x10, x10, x30, ror #47
	eor x20, x20, x26, ror #34
	bic x26, x3, x21, ror #51
	bic x27, x19, x3, ror #57
	bic x28, x17, x6, ror #37
	bic x30, x21, x17, ror #37
	eor x17, x17, x26, ror #40
	bic x26, x6, x19, ror #10
	eor x21, x21, x27, ror #20
	eor x19, x19, x28, ror #17
	eor x6, x6, x30, ror #54
	eor x3, x3, x26, ror #61
	bic x26, x24, x22, ror #38
	bic x27, x9, x24, ror #43
	bic x28, x4, x16, ror #35
	bic x30, x22, x4, ror #3
	eor x4, x4, x26, ror #23
	bic x26, x16, x9, ror #9
	eor x22, x22, x27, ror #47
	eor x9, x9, x28, ror #20
	eor x16, x16, x30, ror #26
	eor x24, x24, x26, ror #12
	bic x26, x1, x15, ror #46
	bic x27, x11, x1, ror #36
	bic x28, x2, x23, ror #28
	bic x30, x15, x2, ror #11
	eor x2, x2, x26, ror #7
	bic x26, x23, x11, ror #7
	eor x15, x15, x27, ror #46
	eor x11, x11, x28, ror #29
	eor x23, x23, x30, ror #25
	eor x1, x1, x26, ror #21
	movz x26, #32897, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x14, ror #32
	dup v24.2d, x25
	dup v25.2d, x10
	eor x27, x12, x13, ror #38
	eor x28, x5, x20, ror #40
	eor x30, x8, x7, ror #26
	eor x25, x25, x10, ror #5
	eor x26, x26, x17, ror #43
	eor x27, x27, x21, ror #36
	eor x28, x28, x3, ror #4
	eor x30, x30, x19, ror #21
	eor x25, x25, x6, ror #60
	eor x26, x26, x4, ror #1
	eor x27, x27, x22, ror #28
	eor x28, x28, x24, ror #9
	eor x30, x30, x9, ror #40
	eor x25, x25, x16, ror #16
	eor x26, x26, x2, ror #14
	eor x27, x27, x15, ror #33
	eor x28, x28, x1, ror #6
	eor x30, x30, x11, ror #44
	eor x25, x25, x23, ror #22
	eor x10, x26, x28, ror #14
	eor x12, x12, x10, ror #30
	eor x13, x13, x10, ror #56
	eor x21, x21, x10, ror #58
	eor x22, x22, x10, ror #2
	eor x15, x15, x10, ror #61
	eor x10, x27, x30, ror #34
	eor x28, x28, x25, ror #4
	eor x30, x30, x26, ror #58
	eor x25, x25, x27, ror #13
	eor x5, x5, x10, ror #19
	eor x20, x20, x10, ror #43
	eor x3, x3, x10, ror #15
	eor x24, x24, x10, ror #10
	eor x1, x1, x10, ror #13
	eor x0, x0, x25, ror #20
	eor x14, x14, x25, ror #52
	eor x17, x17, x25, ror #41
	eor x4, x4, x25, ror #19
	eor x2, x2, x25, ror #6
	umov x10, v24.d[0]
	umov x25, v25.d[0]
	eor x8, x8, x28, ror #10
	eor x7, x7, x28, ror #48
	eor x19, x19, x28, ror #53
	eor x9, x9, x28, ror #34
	eor x11, x11, x28, ror #30
	eor x10, x10, x30, ror #49
	eor x25, x25, x30, ror #44
	eor x6, x6, x30, ror #53
	eor x16, x16, x30, ror #33
	eor x23, x23, x30, ror #27
	bic x26, x3, x13, ror #52
	bic x27, x9, x3, ror #16
	bic x28, x0, x23, ror #28
	bic x30, x13, x0, ror #36
	eor x0, x0, x26, ror #40
	bic x26, x23, x9, ror #60
	eor x13, x13, x27, ror #60
	eor x9, x9, x28, ror #40
	eor x23, x23, x30, ror #0
	eor x3, x3, x26, ror #52
	bic x26, x17, x25, ror #29
	bic x27, x22, x17, ror #23
	bic x28, x8, x1, ror #47
	bic x30, x25, x8, ror #36
	eor x8, x8, x26, ror #63
	bic x26, x1, x22, ror #57
	eor x25, x25, x27, ror #12
	eor x22, x22, x28, ror #24
	eor x1, x1, x30, ror #45
	eor x17, x17, x26, ror #48
	bic x26, x19, x20, ror #48
	bic x27, x16, x19, ror #37
	bic x28, x12, x2, ror #27
	bic x30, x20, x12, ror #48
	eor x12, x12, x26, ror #32
	bic x26, x2, x16, ror #32
	eor x20, x20, x27, ror #43
	eor x16, x16, x28, ror #5
	eor x2, x2, x30, ror #53
	eor x19, x19, x26, ror #59
	bic x26, x21, x14, ror #0
	bic x27, x24, x21, ror #51
	bic x28, x10, x11, ror #0
	bic x30, x14, x10, ror #61
	eor x10, x10, x26, ror #3
	bic x26, x11, x24, ror #16
	eor x14, x14, x27, ror #13
	eor x24, x24, x28, ror #48
	eor x11, x11, x30, ror #3
	eor x21, x21, x26, ror #61
	bic x26, x6, x7, ror #63
	bic x27, x4, x6, ror #17
	bic x28, x5, x15, ror #48
	bic x30, x7, x5, ror #41
	eor x5, x5, x26, ror #24
	bic x26, x15, x4, ror #23
	eor x7, x7, x27, ror #48
	eor x4, x4, x28, ror #57
	eor x15, x15, x30, ror #39
	eor x6, x6, x26, ror #24
	movz x26, #32896, lsl #0
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	eor x26, x0, x8, ror #41
	dup v24.2d, x23
	dup v25.2d, x1
	eor x27, x13, x25, ror #41
	eor x28, x3, x17, ror #0
	eor x30, x9, x22, ror #57
	eor x23, x23, x1, ror #60
	eor x26, x26, x12, ror #33
	eor x27, x27, x20, ror #21
	eor x28, x28, x19, ror #25
	eor x30, x30, x16, ror #4
	eor x23, x23, x2, ror #32
	eor x26, x26, x10, ror #57
	eor x27, x27, x14, ror #32
	eor x28, x28, x21, ror #20
	eor x30, x30, x24, ror #49
	eor x23, x23, x11, ror #29
	eor x26, x26, x5, ror #17
	eor x27, x27, x7, ror #12
	eor x28, x28, x6, ror #1
	eor x30, x30, x4, ror #0
	eor x23, x23, x15, ror #37
	eor x1, x26, x28, ror #39
	eor x13, x13, x1, ror #36
	eor x25, x25, x1, ror #59
	eor x20, x20, x1, ror #15
	eor x14, x14, x1, ror #4
	eor x7, x7, x1, ror #24
	eor x1, x27, x30, ror #59
	eor x28, x28, x23, ror #51
	eor x30, x30, x26, ror #39
	eor x23, x23, x27, ror #63
	eor x3, x3, x1, ror #52
	eor x17, x17, x1, ror #52
	eor x19, x19, x1, ror #27
	eor x21, x21, x1, ror #32
	eor x6, x6, x1, ror #51
	eor x0, x0, x23, ror #28
	eor x8, x8, x23, ror #51
	eor x12, x12, x23, ror #59
	eor x10, x10, x23, ror #35
	eor x5, x5, x23, ror #11
	umov x1, v24.d[0]
	umov x23, v25.d[0]
	eor x9, x9, x28, ror #16
	eor x22, x22, x28, ror #23
	eor x16, x16, x28, ror #12
	eor x24, x24, x28, ror #31
	eor x4, x4, x28, ror #16
	eor x1, x1, x30, ror #60
	eor x23, x23, x30, ror #0
	eor x2, x2, x30, ror #28
	eor x11, x11, x30, ror #31
	eor x15, x15, x30, ror #23
	bic x26, x19, x25, ror #3
	bic x27, x24, x19, ror #34
	bic x28, x0, x15, ror #51
	bic x30, x25, x0, ror #39
	eor x0, x0, x26, ror #22
	bic x26, x15, x24, ror #1
	eor x25, x25, x27, ror #27
	eor x24, x24, x28, ror #12
	eor x15, x15, x30, ror #38
	eor x19, x19, x26, ror #29
	bic x26, x12, x23, ror #38
	bic x27, x14, x12, ror #15
	bic x28, x9, x6, ror #48
	bic x30, x23, x9, ror #56
	eor x9, x9, x26, ror #34
	bic x26, x6, x14, ror #35
	eor x23, x23, x27, ror #11
	eor x14, x14, x28, ror #45
	eor x6, x6, x30, ror #24
	eor x12, x12, x26, ror #14
	bic x26, x16, x17, ror #31
	bic x27, x11, x16, ror #18
	bic x28, x13, x5, ror #36
	bic x30, x17, x13, ror #57
	eor x13, x13, x26, ror #40
	bic x26, x5, x11, ror #50
	eor x17, x17, x27, ror #15
	eor x11, x11, x28, ror #42
	eor x5, x5, x30, ror #35
	eor x16, x16, x26, ror #60
	bic x26, x20, x8, ror #30
	bic x27, x21, x20, ror #58
	bic x28, x1, x4, ror #31
	bic x30, x8, x1, ror #60
	eor x1, x1, x26, ror #38
	bic x26, x4, x21, ror #13
	eor x8, x8, x27, ror #40
	eor x21, x21, x28, ror #20
	eor x4, x4, x30, ror #37
	eor x20, x20, x26, ror #57
	bic x26, x2, x22, ror #5
	bic x27, x10, x2, ror #5
	bic x28, x3, x7, ror #60
	bic x30, x22, x3, ror #16
	eor x3, x3, x26, ror #43
	bic x26, x7, x10, ror #42
	eor x22, x22, x27, ror #54
	eor x10, x10, x28, ror #26
	eor x7, x7, x30, ror #52
	eor x2, x2, x26, ror #17
	movz x26, #1, lsl #0
	movk x26, #32768, lsl #16
	eor x0, x0, x26, ror #0
	eor x26, x0, x9, ror #60
	dup v24.2d, x15
	dup v25.2d, x6
	eor x27, x25, x23, ror #43
	eor x28, x19, x12, ror #8
	eor x30, x24, x14, ror #27
	eor x15, x15, x6, ror #57
	eor x26, x26, x13, ror #27
	eor x27, x27, x17, ror #9
	eor x28, x28, x16, ror #45
	eor x30, x30, x11, ror #61
	eor x15, x15, x5, ror #12
	eor x26, x26, x1, ror #1
	eor x27, x27, x8, ror #44
	eor x28, x28, x20, ror #17
	eor x30, x30, x21, ror #57
	eor x15, x15, x4, ror #45
	eor x26, x26, x3, ror #42
	eor x27, x27, x22, ror #1
	eor x28, x28, x2, ror #63
	eor x30, x30, x10, ror #28
	eor x15, x15, x7, ror #51
	eor x6, x26, x28, ror #21
	eor x25, x25, x6, ror #39
	eor x23, x23, x6, ror #60
	eor x17, x17, x6, ror #30
	eor x8, x8, x6, ror #59
	eor x22, x22, x6, ror #38
	eor x6, x27, x30, ror #26
	eor x28, x28, x15, ror #28
	eor x30, x30, x26, ror #11
	eor x15, x15, x27, ror #37
	eor x19, x19, x6, ror #3
	eor x12, x12, x6, ror #59
	eor x16, x16, x6, ror #22
	eor x20, x20, x6, ror #50
	eor x2, x2, x6, ror #4
	eor x0, x0, x15, ror #51
	eor x9, x9, x15, ror #55
	eor x13, x13, x15, ror #24
	eor x1, x1, x15, ror #50
	eor x3, x3, x15, ror #9
	umov x6, v24.d[0]
	umov x15, v25.d[0]
	eor x24, x24, x28, ror #34
	eor x14, x14, x28, ror #7
	eor x11, x11, x28, ror #37
	eor x21, x21, x28, ror #41
	eor x10, x10, x28, ror #6
	eor x6, x6, x30, ror #1
	eor x15, x15, x30, ror #8
	eor x5, x5, x30, ror #53
	eor x4, x4, x30, ror #20
	eor x7, x7, x30, ror #14
	bic x26, x16, x23, ror #0
	bic x27, x21, x16, ror #0
	bic x28, x0, x7, ror #24
	bic x30, x23, x0, ror #40
	eor x0, x0, x26, ror #24
	bic x26, x7, x21, ror #0
	eor x23, x23, x27, ror #0
	eor x21, x21, x28, ror #40
	eor x7, x7, x30, ror #0
	eor x16, x16, x26, ror #0
	bic x26, x13, x15, ror #0
	bic x27, x8, x13, ror #0
	bic x28, x24, x2, ror #0
	bic x30, x15, x24, ror #0
	eor x24, x24, x26, ror #0
	bic x26, x2, x8, ror #0
	eor x15, x15, x27, ror #0
	eor x8, x8, x28, ror #0
	eor x2, x2, x30, ror #0
	eor x13, x13, x26, ror #0
	bic x26, x11, x12, ror #0
	bic x27, x4, x11, ror #0
	bic x28, x25, x3, ror #0
	bic x30, x12, x25, ror #0
	eor x25, x25, x26, ror #0
	bic x26, x3, x4, ror #0
	eor x12, x12, x27, ror #0
	eor x4, x4, x28, ror #0
	eor x3, x3, x30, ror #0
	eor x11, x11, x26, ror #0
	bic x26, x17, x9, ror #0
	bic x27, x20, x17, ror #0
	bic x28, x6, x10, ror #0
	bic x30, x9, x6, ror #0
	eor x6, x6, x26, ror #0
	bic x26, x10, x20, ror #0
	eor x9, x9, x27, ror #0
	eor x20, x20, x28, ror #0
	eor x10, x10, x30, ror #0
	eor x17, x17, x26, ror #0
	bic x26, x5, x14, ror #0
	bic x27, x1, x5, ror #0
	bic x28, x19, x22, ror #0
	bic x30, x14, x19, ror #0
	eor x19, x19, x26, ror #0
	bic x26, x22, x1, ror #0
	eor x14, x14, x27, ror #0
	eor x1, x1, x28, ror #0
	eor x22, x22, x30, ror #0
	eor x5, x5, x26, ror #0
	movz x26, #32776, lsl #0
	movk x26, #32768, lsl #16
	movk x26, #32768, lsl #48
	eor x0, x0, x26, ror #0
	ror x8, x8, #24
	ror x17, x17, #24
	add x26, x23, #0
	ror x23, x1, #24
	ror x1, x26, #24
	add x26, x16, #0
	ror x16, x9, #24
	ror x9, x2, #24
	ror x2, x26, #24
	add x26, x21, #0
	ror x21, x14, #24
	ror x14, x3, #24
	ror x3, x26, #24
	add x26, x7, #0
	ror x7, x13, #24
	ror x13, x4, #24
	ror x4, x26, #24
	add x26, x24, #0
	ror x24, x22, #24
	ror x22, x5, #24
	ror x5, x26, #24
	add x26, x15, #0
	ror x15, x6, #24
	ror x6, x26, #24
	add x26, x25, #0
	ror x25, x20, #24
	ror x20, x19, #24
	ror x19, x10, #24
	ror x10, x26, #24
	add x26, x12, #0
	ror x12, x11, #24
	ror x11, x26, #24
	add v19.2d, v19.2d, v21.2d
	sub v20.2d, v20.2d, v21.2d
	umov x27, v20.d[0]
	umov x28, v21.d[0]
	sub x26, x27, x28
	lsr x26, x26, #63
	cbz x26, 24b
	umov x30, v30.d[0]
	str x0, [x30, #0]
	str x1, [x30, #8]
	str x2, [x30, #16]
	str x3, [x30, #24]
	str x4, [x30, #32]
	str x5, [x30, #40]
	str x6, [x30, #48]
	str x7, [x30, #56]
	str x8, [x30, #64]
	str x9, [x30, #72]
	str x10, [x30, #80]
	str x11, [x30, #88]
	str x12, [x30, #96]
	str x13, [x30, #104]
	str x14, [x30, #112]
	str x15, [x30, #120]
	str x16, [x30, #128]
	str x17, [x30, #136]
	str x25, [x30, #144]
	str x19, [x30, #152]
	str x20, [x30, #160]
	str x21, [x30, #168]
	str x22, [x30, #176]
	str x23, [x30, #184]
	str x24, [x30, #192]
	umov x19, v0.d[0]
	umov x20, v1.d[0]
	umov x21, v2.d[0]
	umov x22, v3.d[0]
	umov x23, v4.d[0]
	umov x24, v5.d[0]
	umov x25, v6.d[0]
	umov x26, v7.d[0]
	umov x27, v16.d[0]
	umov x28, v17.d[0]
	umov x30, v18.d[0]
	umov x0, v30.d[0]
	umov x1, v31.d[0]
	umov x3, v19.d[0]
	umov x4, v20.d[0]
	umov x6, v21.d[0]
	add x5, x1, #0
	movz x2, #0, lsl #0
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 213f
215:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 216f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 217f
216:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
217:
	cbz x9, 218f
	b 219f
218:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
219:
	cbnz x24, 215b
	b 214f
213:
214:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_keccak_pad:
	sub sp, sp, #640
	add x4, sp, #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600}
	ldr x30, [sp], #16
	add sp, sp, #640
	ret
	.p2align 6

vg_keccak_squeeze:
	sub sp, sp, #640
	add x5, sp, #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	ret
	.p2align 6

vg_keccak_absorb_scratch_sha3:
	.arch_extension sha3
	cbz x2, 20f
	b 21f
20:
	add x6, x1, #0
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 22f
	b 23f
22:
	add x1, x5, #0
	str q8, [x1, #0]
	str q9, [x1, #16]
	str q10, [x1, #32]
	str q11, [x1, #48]
	str q12, [x1, #64]
	str q13, [x1, #80]
	str q14, [x1, #96]
	str q15, [x1, #112]
	ldr q0, [x0, #0]
	ext v1.16b, v0.16b, v0.16b, #8
	ldr q2, [x0, #16]
	ext v3.16b, v2.16b, v2.16b, #8
	ldr q4, [x0, #32]
	ext v5.16b, v4.16b, v4.16b, #8
	ldr q6, [x0, #48]
	ext v7.16b, v6.16b, v6.16b, #8
	ldr q8, [x0, #64]
	ext v9.16b, v8.16b, v8.16b, #8
	ldr q10, [x0, #80]
	ext v11.16b, v10.16b, v10.16b, #8
	ldr q12, [x0, #96]
	ext v13.16b, v12.16b, v12.16b, #8
	ldr q14, [x0, #112]
	ext v15.16b, v14.16b, v14.16b, #8
	ldr q16, [x0, #128]
	ext v17.16b, v16.16b, v16.16b, #8
	ldr q18, [x0, #144]
	ext v19.16b, v18.16b, v18.16b, #8
	ldr q20, [x0, #160]
	ext v21.16b, v20.16b, v20.16b, #8
	ldr q22, [x0, #176]
	ext v23.16b, v22.16b, v22.16b, #8
	ldr x17, [x0, #192]
	dup v24.2d, x17
24:
	sub x7, x6, #72
	cbz x7, 25f
	sub x7, x6, #104
	cbz x7, 27f
	sub x7, x6, #136
	cbz x7, 29f
	sub x7, x6, #144
	cbz x7, 211f
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
	ldr q25, [x3, #144]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v18.16b, v18.16b, v25.16b
	eor v19.16b, v19.16b, v26.16b
	ldr x17, [x3, #160]
	dup v25.2d, x17
	eor v20.16b, v20.16b, v25.16b
	b 212f
211:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr q25, [x3, #128]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v16.16b, v16.16b, v25.16b
	eor v17.16b, v17.16b, v26.16b
212:
	b 210f
29:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr q25, [x3, #96]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v12.16b, v12.16b, v25.16b
	eor v13.16b, v13.16b, v26.16b
	ldr q25, [x3, #112]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v14.16b, v14.16b, v25.16b
	eor v15.16b, v15.16b, v26.16b
	ldr x17, [x3, #128]
	dup v25.2d, x17
	eor v16.16b, v16.16b, v25.16b
210:
	b 28f
27:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr q25, [x3, #64]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v8.16b, v8.16b, v25.16b
	eor v9.16b, v9.16b, v26.16b
	ldr q25, [x3, #80]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v10.16b, v10.16b, v25.16b
	eor v11.16b, v11.16b, v26.16b
	ldr x17, [x3, #96]
	dup v25.2d, x17
	eor v12.16b, v12.16b, v25.16b
28:
	b 26f
25:
	ldr q25, [x3, #0]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v0.16b, v0.16b, v25.16b
	eor v1.16b, v1.16b, v26.16b
	ldr q25, [x3, #16]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v2.16b, v2.16b, v25.16b
	eor v3.16b, v3.16b, v26.16b
	ldr q25, [x3, #32]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v4.16b, v4.16b, v25.16b
	eor v5.16b, v5.16b, v26.16b
	ldr q25, [x3, #48]
	ext v26.16b, v25.16b, v25.16b, #8
	eor v6.16b, v6.16b, v25.16b
	eor v7.16b, v7.16b, v26.16b
	ldr x17, [x3, #64]
	dup v25.2d, x17
	eor v8.16b, v8.16b, v25.16b
26:
	movz x16, #1, lsl #0
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32898, lsl #0
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32906, lsl #0
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32768, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #138, lsl #0
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #136, lsl #0
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32777, lsl #0
	movk x16, #32768, lsl #16
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32907, lsl #0
	movk x16, #32768, lsl #16
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #139, lsl #0
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32905, lsl #0
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32771, lsl #0
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32770, lsl #0
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #128, lsl #0
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32778, lsl #0
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #10, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32897, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32896, lsl #0
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #1, lsl #0
	movk x16, #32768, lsl #16
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	movz x16, #32776, lsl #0
	movk x16, #32768, lsl #16
	movk x16, #32768, lsl #48
	eor3 v25.16b, v20.16b, v15.16b, v10.16b
	eor3 v26.16b, v21.16b, v16.16b, v11.16b
	eor3 v27.16b, v22.16b, v17.16b, v12.16b
	eor3 v28.16b, v23.16b, v18.16b, v13.16b
	eor3 v29.16b, v24.16b, v19.16b, v14.16b
	eor3 v25.16b, v25.16b, v5.16b, v0.16b
	eor3 v26.16b, v26.16b, v6.16b, v1.16b
	eor3 v27.16b, v27.16b, v7.16b, v2.16b
	eor3 v28.16b, v28.16b, v8.16b, v3.16b
	eor3 v29.16b, v29.16b, v9.16b, v4.16b
	rax1 v30.2d, v25.2d, v27.2d
	rax1 v31.2d, v26.2d, v28.2d
	rax1 v27.2d, v27.2d, v29.2d
	rax1 v28.2d, v28.2d, v25.2d
	rax1 v29.2d, v29.2d, v26.2d
	xar v25.2d, v1.2d, v30.2d, #63
	xar v1.2d, v6.2d, v30.2d, #20
	xar v6.2d, v9.2d, v28.2d, #44
	xar v9.2d, v22.2d, v31.2d, #3
	xar v22.2d, v14.2d, v28.2d, #25
	xar v14.2d, v20.2d, v29.2d, #46
	xar v26.2d, v2.2d, v31.2d, #2
	xar v2.2d, v12.2d, v31.2d, #21
	xar v12.2d, v13.2d, v27.2d, #39
	xar v13.2d, v19.2d, v28.2d, #56
	xar v19.2d, v23.2d, v27.2d, #8
	xar v23.2d, v15.2d, v29.2d, #23
	xar v15.2d, v4.2d, v28.2d, #37
	xar v28.2d, v24.2d, v28.2d, #50
	xar v24.2d, v21.2d, v30.2d, #62
	xar v8.2d, v8.2d, v27.2d, #9
	xar v4.2d, v16.2d, v30.2d, #19
	xar v16.2d, v5.2d, v29.2d, #28
	xar v5.2d, v3.2d, v27.2d, #36
	eor v0.16b, v0.16b, v29.16b
	xar v27.2d, v18.2d, v27.2d, #43
	xar v3.2d, v17.2d, v31.2d, #49
	xar v30.2d, v11.2d, v30.2d, #54
	xar v31.2d, v7.2d, v31.2d, #58
	xar v29.2d, v10.2d, v29.2d, #61
	bcax v20.16b, v26.16b, v22.16b, v8.16b
	bcax v21.16b, v8.16b, v23.16b, v22.16b
	bcax v22.16b, v22.16b, v24.16b, v23.16b
	bcax v23.16b, v23.16b, v26.16b, v24.16b
	bcax v24.16b, v24.16b, v8.16b, v26.16b
	bcax v17.16b, v30.16b, v19.16b, v3.16b
	bcax v18.16b, v3.16b, v15.16b, v19.16b
	bcax v19.16b, v19.16b, v16.16b, v15.16b
	bcax v15.16b, v15.16b, v30.16b, v16.16b
	bcax v16.16b, v16.16b, v3.16b, v30.16b
	bcax v10.16b, v25.16b, v12.16b, v31.16b
	bcax v11.16b, v31.16b, v13.16b, v12.16b
	bcax v12.16b, v12.16b, v14.16b, v13.16b
	bcax v13.16b, v13.16b, v25.16b, v14.16b
	bcax v14.16b, v14.16b, v31.16b, v25.16b
	bcax v7.16b, v29.16b, v9.16b, v4.16b
	bcax v8.16b, v4.16b, v5.16b, v9.16b
	bcax v9.16b, v9.16b, v6.16b, v5.16b
	bcax v5.16b, v5.16b, v29.16b, v6.16b
	bcax v6.16b, v6.16b, v4.16b, v29.16b
	bcax v3.16b, v27.16b, v0.16b, v28.16b
	bcax v4.16b, v28.16b, v1.16b, v0.16b
	bcax v0.16b, v0.16b, v2.16b, v1.16b
	bcax v1.16b, v1.16b, v27.16b, v2.16b
	bcax v2.16b, v2.16b, v28.16b, v27.16b
	dup v26.2d, x16
	eor v0.16b, v0.16b, v26.16b
	add x3, x3, x6
	sub x4, x4, x6
	sub x7, x4, x6
	lsr x7, x7, #63
	cbz x7, 24b
	zip1 v25.2d, v0.2d, v1.2d
	str q25, [x0, #0]
	zip1 v25.2d, v2.2d, v3.2d
	str q25, [x0, #16]
	zip1 v25.2d, v4.2d, v5.2d
	str q25, [x0, #32]
	zip1 v25.2d, v6.2d, v7.2d
	str q25, [x0, #48]
	zip1 v25.2d, v8.2d, v9.2d
	str q25, [x0, #64]
	zip1 v25.2d, v10.2d, v11.2d
	str q25, [x0, #80]
	zip1 v25.2d, v12.2d, v13.2d
	str q25, [x0, #96]
	zip1 v25.2d, v14.2d, v15.2d
	str q25, [x0, #112]
	zip1 v25.2d, v16.2d, v17.2d
	str q25, [x0, #128]
	zip1 v25.2d, v18.2d, v19.2d
	str q25, [x0, #144]
	zip1 v25.2d, v20.2d, v21.2d
	str q25, [x0, #160]
	zip1 v25.2d, v22.2d, v23.2d
	str q25, [x0, #176]
	umov x17, v24.d[0]
	str x17, [x0, #192]
	ldr q8, [x1, #0]
	ldr q9, [x1, #16]
	ldr q10, [x1, #32]
	ldr q11, [x1, #48]
	ldr q12, [x1, #64]
	ldr q13, [x1, #80]
	ldr q14, [x1, #96]
	ldr q15, [x1, #112]
	add x1, x6, #0
23:
21:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 213f
215:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 216f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 217f
216:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
217:
	cbz x9, 218f
	b 219f
218:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
219:
	cbnz x24, 215b
	b 214f
213:
214:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	ret
	.arch_extension nosha3
	.p2align 6

vg_keccak_pad_sha3:
	.arch_extension sha3
	sub sp, sp, #640
	add x4, sp, #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600_sha3}
	ldr x30, [sp], #16
	add sp, sp, #640
	ret
	.arch_extension nosha3
	.p2align 6

vg_keccak_squeeze_sha3:
	.arch_extension sha3
	sub sp, sp, #640
	add x5, sp, #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	ret
	.arch_extension nosha3
	.p2align 6
