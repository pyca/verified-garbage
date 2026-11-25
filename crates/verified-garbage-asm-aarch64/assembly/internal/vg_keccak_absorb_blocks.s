// The functions of `src/internal/vg_keccak_absorb_blocks.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_absorb_blocks:
	dup v16.2d, x19
	dup v17.2d, x20
	dup v18.2d, x21
	dup v19.2d, x22
	dup v20.2d, x23
	dup v21.2d, x24
	dup v22.2d, x25
	dup v23.2d, x26
	dup v24.2d, x27
	dup v25.2d, x28
	dup v26.2d, x30
	dup v29.2d, x0
	dup v30.2d, x4
	dup v0.2d, x1
	dup v1.2d, x2
	dup v2.2d, x3
	umov x16, v29.d[0]
	ldr x0, [x16, #0]
	ldr x1, [x16, #8]
	ror x1, x1, #18
	ldr x2, [x16, #16]
	ror x2, x2, #33
	ldr x3, [x16, #24]
	ldr x4, [x16, #32]
	ror x4, x4, #33
	ldr x5, [x16, #40]
	ror x5, x5, #28
	ldr x6, [x16, #48]
	ror x6, x6, #38
	ldr x7, [x16, #56]
	ror x7, x7, #18
	ldr x8, [x16, #64]
	ror x8, x8, #28
	ldr x9, [x16, #72]
	ror x9, x9, #18
	ldr x10, [x16, #80]
	ror x10, x10, #56
	ldr x11, [x16, #88]
	ror x11, x11, #31
	ldr x12, [x16, #96]
	ror x12, x12, #49
	ldr x13, [x16, #104]
	ror x13, x13, #31
	ldr x14, [x16, #112]
	ror x14, x14, #49
	ldr x15, [x16, #120]
	ror x15, x15, #60
	ldr x19, [x16, #128]
	ldr x20, [x16, #136]
	ror x20, x20, #41
	ldr x21, [x16, #144]
	ror x21, x21, #56
	ldr x22, [x16, #152]
	ror x22, x22, #23
	ldr x23, [x16, #160]
	ror x23, x23, #31
	ldr x24, [x16, #168]
	ror x24, x24, #19
	ldr x25, [x16, #176]
	ror x25, x25, #21
	ldr x26, [x16, #184]
	ror x26, x26, #31
	ldr x27, [x16, #192]
	ror x27, x27, #19
20:
	umov x16, v1.d[0]
	ldr x17, [x16, #0]
	eor x0, x0, x17
	ldr x17, [x16, #8]
	eor x1, x1, x17, ror #18
	ldr x17, [x16, #16]
	eor x2, x2, x17, ror #33
	ldr x17, [x16, #24]
	eor x3, x3, x17
	ldr x17, [x16, #32]
	eor x4, x4, x17, ror #33
	ldr x17, [x16, #40]
	eor x5, x5, x17, ror #28
	ldr x17, [x16, #48]
	eor x6, x6, x17, ror #38
	ldr x17, [x16, #56]
	eor x7, x7, x17, ror #18
	ldr x17, [x16, #64]
	eor x8, x8, x17, ror #28
	umov x17, v0.d[0]
	sub x17, x17, #72
	cbz x17, 21f
	ldr x17, [x16, #72]
	eor x9, x9, x17, ror #18
	ldr x17, [x16, #80]
	eor x10, x10, x17, ror #56
	ldr x17, [x16, #88]
	eor x11, x11, x17, ror #31
	ldr x17, [x16, #96]
	eor x12, x12, x17, ror #49
	umov x17, v0.d[0]
	sub x17, x17, #104
	cbz x17, 23f
	ldr x17, [x16, #104]
	eor x13, x13, x17, ror #31
	ldr x17, [x16, #112]
	eor x14, x14, x17, ror #49
	ldr x17, [x16, #120]
	eor x15, x15, x17, ror #60
	ldr x17, [x16, #128]
	eor x19, x19, x17
	umov x17, v0.d[0]
	sub x17, x17, #136
	cbz x17, 25f
	ldr x17, [x16, #136]
	eor x20, x20, x17, ror #41
	umov x17, v0.d[0]
	sub x17, x17, #144
	cbz x17, 27f
	ldr x17, [x16, #144]
	eor x21, x21, x17, ror #56
	ldr x17, [x16, #152]
	eor x22, x22, x17, ror #23
	ldr x17, [x16, #160]
	eor x23, x23, x17, ror #31
	b 28f
27:
28:
	b 26f
25:
26:
	b 24f
23:
24:
	b 22f
21:
22:
	umov x16, v1.d[0]
	umov x17, v0.d[0]
	add x16, x16, x17
	dup v1.2d, x16
	umov x28, v30.d[0]
	bl {vg_keccak_f1600_lanes}
	umov x16, v2.d[0]
	umov x17, v0.d[0]
	sub x16, x16, x17
	dup v2.2d, x16
	sub x17, x16, x17
	lsr x17, x17, #63
	cbz x17, 20b
	umov x16, v29.d[0]
	str x0, [x16, #0]
	ror x1, x1, #46
	str x1, [x16, #8]
	ror x2, x2, #31
	str x2, [x16, #16]
	str x3, [x16, #24]
	ror x4, x4, #31
	str x4, [x16, #32]
	ror x5, x5, #36
	str x5, [x16, #40]
	ror x6, x6, #26
	str x6, [x16, #48]
	ror x7, x7, #46
	str x7, [x16, #56]
	ror x8, x8, #36
	str x8, [x16, #64]
	ror x9, x9, #46
	str x9, [x16, #72]
	ror x10, x10, #8
	str x10, [x16, #80]
	ror x11, x11, #33
	str x11, [x16, #88]
	ror x12, x12, #15
	str x12, [x16, #96]
	ror x13, x13, #33
	str x13, [x16, #104]
	ror x14, x14, #15
	str x14, [x16, #112]
	ror x15, x15, #4
	str x15, [x16, #120]
	str x19, [x16, #128]
	ror x20, x20, #23
	str x20, [x16, #136]
	ror x21, x21, #8
	str x21, [x16, #144]
	ror x22, x22, #41
	str x22, [x16, #152]
	ror x23, x23, #33
	str x23, [x16, #160]
	ror x24, x24, #45
	str x24, [x16, #168]
	ror x25, x25, #43
	str x25, [x16, #176]
	ror x26, x26, #33
	str x26, [x16, #184]
	ror x27, x27, #45
	str x27, [x16, #192]
	umov x19, v16.d[0]
	umov x20, v17.d[0]
	umov x21, v18.d[0]
	umov x22, v19.d[0]
	umov x23, v20.d[0]
	umov x24, v21.d[0]
	umov x25, v22.d[0]
	umov x26, v23.d[0]
	umov x27, v24.d[0]
	umov x28, v25.d[0]
	umov x30, v26.d[0]
	umov x0, v2.d[0]
	ret
	.p2align 6
