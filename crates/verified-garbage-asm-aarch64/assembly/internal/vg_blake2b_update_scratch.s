// The functions of `src/internal/vg_blake2b_update_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_update_scratch:
	str x30, [sp, #-16]!
	str x19, [x4, #512]
	str x20, [x4, #520]
	str x21, [x4, #528]
	str x22, [x4, #536]
	str x23, [x4, #544]
	str x24, [x4, #552]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x2, #0
	add x22, x3, #0
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
	cbz x22, 22f
	cbz x23, 24f
	movz x11, #128, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #7
	cbz x9, 26f
	b 27f
26:
	add x9, x22, x23
	lsr x9, x9, #7
	cbz x9, 28f
	b 29f
28:
	add x11, x22, #0
29:
27:
	sub x22, x22, x11
	add x24, x24, x11
	cbz x11, 210f
212:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #64]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 212b
	b 211f
210:
211:
	cbz x22, 213f
	add x0, x19, #0
	add x1, x19, #64
	movz x2, #1, lsl #0
	add x3, x24, #0
	movz x4, #0, lsl #0
	add x5, x20, #0
	bl {vg_blake2b_compress}
	movz x23, #0, lsl #0
	b 214f
213:
214:
	b 25f
24:
25:
	cbz x22, 215f
	sub x9, x22, #1
	lsr x10, x9, #7
	cbz x10, 217f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x10, #0
	add x3, x24, #128
	movz x4, #0, lsl #0
	add x5, x20, #0
	bl {vg_blake2b_compress}
	sub x9, x22, #1
	movz x10, #127, lsl #0
	and x9, x9, x10
	add x9, x9, #1
	sub x10, x22, x9
	add x21, x21, x10
	add x24, x24, x10
	add x22, x9, #0
	b 218f
217:
218:
	add x11, x22, #0
	add x24, x24, x22
	movz x22, #0, lsl #0
219:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #64]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 219b
	b 216f
215:
216:
	b 23f
22:
23:
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	ret
	.p2align 6
