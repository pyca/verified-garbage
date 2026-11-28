// The functions of `src/internal/vg_slhdsa_shake_levels_n16.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_levels_n16:
	str x19, [x0, #1408]
	str x20, [x0, #1416]
	str x21, [x0, #1424]
	str x22, [x0, #1432]
	str x23, [x0, #1440]
	str x24, [x0, #1448]
	str x25, [x0, #1456]
	str x26, [x0, #1464]
	str x27, [x0, #1472]
	str x30, [x0, #1480]
	add x19, x0, #0
	add x20, x1, #0
	add x23, x2, #0
	add x22, x3, #0
	add x21, x4, #0
	add x25, x5, #0
	ldr x26, [x19, #1496]
	ldr x27, [x19, #1504]
	lsr x27, x27, #1
	cbz x22, 20f
	add x9, x22, #0
22:
	lsr x25, x25, #1
	lsr x26, x26, #1
	lsr x27, x27, #1
	sub x9, x9, #1
	cbnz x9, 22b
	b 21f
20:
21:
23:
	movz x9, #1, lsl #0
	eor x13, x25, x9
	movz x24, #0, lsl #0
	add x10, x20, #0
24:
	add x11, x26, x24
	eor x11, x11, x13
	sub x11, x11, #1
	lsr x11, x11, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	ldr x12, [x10, #0]
	and x12, x12, x11
	ldr x14, [x21, #0]
	eor x14, x14, x12
	str x14, [x21, #0]
	ldr x12, [x10, #8]
	and x12, x12, x11
	ldr x14, [x21, #8]
	eor x14, x14, x12
	str x14, [x21, #8]
	add x10, x10, #16
	add x24, x24, #1
	sub x9, x24, x23
	cbnz x9, 24b
	lsr x23, x23, #1
	movz x24, #0, lsl #0
25:
	add x10, x22, #1
	add x11, x27, x24
	add x12, x24, #0
	lsl x12, x12, #4
	add x12, x12, x12
	add x12, x12, x20
	ldr w13, [x19, #1512]
	rev w9, w13
	str w9, [x19, #3168]
	ldr w13, [x19, #1520]
	rev w9, w13
	str w9, [x19, #3172]
	rev w9, w10
	str w9, [x19, #3176]
	add x13, x11, #0
	rev w9, w13
	str w9, [x19, #3180]
	ldr q16, [x12, #0]
	str q16, [x19, #3184]
	ldr q16, [x12, #16]
	str q16, [x19, #3200]
	ldr w13, [x19, #1512]
	rev w9, w13
	str w9, [x19, #3296]
	ldr w13, [x19, #1520]
	rev w9, w13
	str w9, [x19, #3300]
	rev w9, w10
	str w9, [x19, #3304]
	add x13, x11, #1
	rev w9, w13
	str w9, [x19, #3308]
	ldr q16, [x12, #32]
	str q16, [x19, #3312]
	ldr q16, [x12, #48]
	str q16, [x19, #3328]
	ldr w13, [x19, #1512]
	rev w9, w13
	str w9, [x19, #3424]
	ldr w13, [x19, #1520]
	rev w9, w13
	str w9, [x19, #3428]
	rev w9, w10
	str w9, [x19, #3432]
	add x13, x11, #2
	rev w9, w13
	str w9, [x19, #3436]
	ldr q16, [x12, #64]
	str q16, [x19, #3440]
	ldr q16, [x12, #80]
	str q16, [x19, #3456]
	ldr w13, [x19, #1512]
	rev w9, w13
	str w9, [x19, #3552]
	ldr w13, [x19, #1520]
	rev w9, w13
	str w9, [x19, #3556]
	rev w9, w10
	str w9, [x19, #3560]
	add x13, x11, #3
	rev w9, w13
	str w9, [x19, #3564]
	ldr q16, [x12, #96]
	str q16, [x19, #3568]
	ldr q16, [x12, #112]
	str q16, [x19, #3584]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #80, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16}
	add x10, x24, #0
	lsl x10, x10, #4
	add x10, x10, x20
	ldr q16, [x19, #3184]
	str q16, [x10, #0]
	ldr q16, [x19, #3312]
	str q16, [x10, #16]
	ldr q16, [x19, #3440]
	str q16, [x10, #32]
	ldr q16, [x19, #3568]
	str q16, [x10, #48]
	add x24, x24, #4
	sub x9, x24, x23
	lsr x9, x9, #63
	cbnz x9, 25b
	add x21, x21, #16
	add x22, x22, #1
	lsr x25, x25, #1
	lsr x26, x26, #1
	lsr x27, x27, #1
	sub x9, x23, #1
	cbnz x9, 23b
	ldr x20, [x19, #1416]
	ldr x21, [x19, #1424]
	ldr x22, [x19, #1432]
	ldr x23, [x19, #1440]
	ldr x24, [x19, #1448]
	ldr x25, [x19, #1456]
	ldr x26, [x19, #1464]
	ldr x27, [x19, #1472]
	ldr x30, [x19, #1480]
	ldr x19, [x19, #1408]
	ret
	.p2align 6
