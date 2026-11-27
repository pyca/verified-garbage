// The functions of `src/internal/vg_keccak_f1600.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600:
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
	dup v30.2d, x1
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
	umov x28, v30.d[0]
	bl {vg_keccak_f1600_lanes}
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
	ret
	.p2align 6
