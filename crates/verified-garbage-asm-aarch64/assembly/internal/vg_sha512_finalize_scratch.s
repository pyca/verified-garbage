// The functions of `src/internal/vg_sha512_finalize_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_finalize_scratch:
	str x30, [sp, #-16]!
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	str x22, [x3, #664]
	str x23, [x3, #672]
	str x24, [x3, #680]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #127, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	add x24, x23, #15
	lsr x24, x24, #7
20:
	movz x11, #128, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #112, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
210:
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	ret
	.p2align 6
