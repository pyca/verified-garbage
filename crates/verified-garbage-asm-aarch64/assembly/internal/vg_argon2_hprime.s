// The functions of `src/internal/vg_argon2_hprime.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_hprime:
	str x19, [x4, #840]
	str x20, [x4, #848]
	str x21, [x4, #856]
	str x22, [x4, #864]
	str x23, [x4, #872]
	str x30, [x4, #888]
	str x24, [x4, #880]
	add x24, x4, #0
	add x20, x0, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	str w3, [x24, #832]
	add x1, x23, #0
	sub x9, x1, #65
	lsr x9, x9, #63
	cbnz x9, 20f
	movz x1, #64, lsl #0
	b 21f
20:
21:
	add x0, x24, #0
	add x2, x24, #0
	add x2, x2, #832
	movz x3, #0, lsl #0
	bl {vg_blake2b_init}
	movz x1, #0, lsl #0
	add x2, x24, #0
	add x2, x2, #832
	movz x3, #4, lsl #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	movz x1, #4, lsl #0
	add x2, x20, #0
	add x3, x21, #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	add x1, x21, #0
	add x1, x1, #4
	add x0, x24, #0
	add x2, x24, #0
	add x2, x2, #768
	add x3, x24, #0
	add x3, x3, #192
	bl {vg_blake2b_finalize_scratch}
	sub x9, x23, #65
	lsr x9, x9, #63
	cbnz x9, 22f
	movz x8, #32, lsl #0
	add x2, x24, #0
	add x2, x2, #768
24:
	ldrb w3, [x2, #0]
	strb w3, [x22, #0]
	add x2, x2, #1
	add x22, x22, #1
	sub x8, x8, #1
	cbnz x8, 24b
	sub x23, x23, #32
	sub x9, x23, #65
	lsr x9, x9, #63
	cbnz x9, 25f
27:
	movz x1, #64, lsl #0
	add x0, x24, #0
	add x2, x24, #0
	add x2, x2, #832
	movz x3, #0, lsl #0
	bl {vg_blake2b_init}
	movz x1, #0, lsl #0
	add x2, x24, #0
	add x2, x2, #768
	movz x3, #64, lsl #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	movz x1, #64, lsl #0
	add x0, x24, #0
	add x2, x24, #0
	add x2, x2, #768
	add x3, x24, #0
	add x3, x3, #192
	bl {vg_blake2b_finalize_scratch}
	movz x8, #32, lsl #0
	add x2, x24, #0
	add x2, x2, #768
28:
	ldrb w3, [x2, #0]
	strb w3, [x22, #0]
	add x2, x2, #1
	add x22, x22, #1
	sub x8, x8, #1
	cbnz x8, 28b
	sub x23, x23, #32
	sub x9, x23, #65
	lsr x9, x9, #63
	cbz x9, 27b
	b 26f
25:
26:
	add x1, x23, #0
	add x0, x24, #0
	add x2, x24, #0
	add x2, x2, #832
	movz x3, #0, lsl #0
	bl {vg_blake2b_init}
	movz x1, #0, lsl #0
	add x2, x24, #0
	add x2, x2, #768
	movz x3, #64, lsl #0
	add x0, x24, #0
	add x4, x24, #0
	add x4, x4, #192
	bl {vg_blake2b_update_scratch}
	movz x1, #64, lsl #0
	add x0, x24, #0
	add x2, x24, #0
	add x2, x2, #768
	add x3, x24, #0
	add x3, x3, #192
	bl {vg_blake2b_finalize_scratch}
	b 23f
22:
23:
	add x8, x23, #0
	add x2, x24, #0
	add x2, x2, #768
29:
	ldrb w3, [x2, #0]
	strb w3, [x22, #0]
	add x2, x2, #1
	add x22, x22, #1
	sub x8, x8, #1
	cbnz x8, 29b
	ldr x19, [x24, #840]
	ldr x20, [x24, #848]
	ldr x21, [x24, #856]
	ldr x22, [x24, #864]
	ldr x23, [x24, #872]
	ldr x30, [x24, #888]
	ldr x24, [x24, #880]
	ret
	.p2align 6
