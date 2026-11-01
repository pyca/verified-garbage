// The functions of `src/internal/vg_blake2b_finalize_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_finalize_scratch:
	str x30, [sp, #-16]!
	str x19, [x3, #512]
	str x20, [x3, #520]
	str x21, [x3, #528]
	str x22, [x3, #536]
	str x23, [x3, #544]
	str x24, [x3, #552]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x24, x1, #0
	sub x23, x24, #1
	movz x9, #127, lsl #0
	and x23, x23, x9
	add x23, x23, #1
	cbz x24, 20f
	b 21f
20:
	movz x23, #0, lsl #0
21:
	movz x9, #0, lsl #0
	movz x11, #128, lsl #0
	sub x11, x11, x23
	cbz x11, 22f
24:
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 24b
	b 23f
22:
23:
	add x0, x19, #0
	add x1, x19, #64
	movz x2, #1, lsl #0
	add x3, x24, #0
	movz x4, #1, lsl #0
	add x5, x20, #0
	bl {vg_blake2b_compress}
	ldr x9, [x19, #0]
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	str x9, [x21, #56]
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	ret
	.p2align 6
