// The functions of `src/internal/vg_keccak_f1600.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_f1600:
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
	dup v24.2d, x16
	dup v25.2d, x17
	bl {vg_keccak_scalar_core}
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
	ret
	.p2align 6
