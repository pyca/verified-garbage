// The functions of `src/internal/vg_slhdsa_shake_wots4_n32.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_wots4_n32:
	str x19, [x0, #1024]
	str x20, [x0, #1032]
	str x21, [x0, #1040]
	str x22, [x0, #1048]
	str x23, [x0, #1056]
	str x24, [x0, #1064]
	str x30, [x0, #1072]
	add x19, x0, #0
	add x20, x1, #0
	add x23, x2, #0
	add x24, x3, #0
	add x10, x20, #0
	rev w9, w10
	str w9, [x19, #3188]
	rev w9, w10
	str w9, [x19, #3700]
	movz w9, #256, lsl #16
	str w9, [x19, #3696]
	movz w9, #0, lsl #16
	str w9, [x19, #3704]
	movz w9, #0, lsl #16
	str w9, [x19, #3708]
	add x10, x20, #1
	rev w9, w10
	str w9, [x19, #3316]
	rev w9, w10
	str w9, [x19, #5908]
	movz w9, #256, lsl #16
	str w9, [x19, #5904]
	movz w9, #0, lsl #16
	str w9, [x19, #5912]
	movz w9, #0, lsl #16
	str w9, [x19, #5916]
	add x10, x20, #2
	rev w9, w10
	str w9, [x19, #3444]
	rev w9, w10
	str w9, [x19, #8116]
	movz w9, #256, lsl #16
	str w9, [x19, #8112]
	movz w9, #0, lsl #16
	str w9, [x19, #8120]
	movz w9, #0, lsl #16
	str w9, [x19, #8124]
	add x10, x20, #3
	rev w9, w10
	str w9, [x19, #3572]
	rev w9, w10
	str w9, [x19, #10324]
	movz w9, #256, lsl #16
	str w9, [x19, #10320]
	movz w9, #0, lsl #16
	str w9, [x19, #10328]
	movz w9, #0, lsl #16
	str w9, [x19, #10332]
	movz x21, #0, lsl #0
20:
	movz w9, #1280, lsl #16
	str w9, [x19, #3184]
	rev w9, w21
	str w9, [x19, #3192]
	movz w9, #0, lsl #16
	str w9, [x19, #3196]
	ldr q16, [x19, #1664]
	str q16, [x19, #3200]
	ldr q16, [x19, #1680]
	str q16, [x19, #3216]
	movz w9, #1280, lsl #16
	str w9, [x19, #3312]
	rev w9, w21
	str w9, [x19, #3320]
	movz w9, #0, lsl #16
	str w9, [x19, #3324]
	ldr q16, [x19, #1664]
	str q16, [x19, #3328]
	ldr q16, [x19, #1680]
	str q16, [x19, #3344]
	movz w9, #1280, lsl #16
	str w9, [x19, #3440]
	rev w9, w21
	str w9, [x19, #3448]
	movz w9, #0, lsl #16
	str w9, [x19, #3452]
	ldr q16, [x19, #1664]
	str q16, [x19, #3456]
	ldr q16, [x19, #1680]
	str q16, [x19, #3472]
	movz w9, #1280, lsl #16
	str w9, [x19, #3568]
	rev w9, w21
	str w9, [x19, #3576]
	movz w9, #0, lsl #16
	str w9, [x19, #3580]
	ldr q16, [x19, #1664]
	str q16, [x19, #3584]
	ldr q16, [x19, #1680]
	str q16, [x19, #3600]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #96, lsl #0
	add x3, x0, #64
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n32}
	movz w9, #0, lsl #16
	str w9, [x19, #3184]
	movz w9, #0, lsl #16
	str w9, [x19, #3312]
	movz w9, #0, lsl #16
	str w9, [x19, #3440]
	movz w9, #0, lsl #16
	str w9, [x19, #3568]
	movz x22, #0, lsl #0
21:
	add x9, x19, x21
	ldrb w9, [x9, #1856]
	eor x10, x22, x9
	add x11, x21, #0
	lsl x11, x11, #5
	add x11, x11, x24
	add x12, x20, #0
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3200]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3208]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3216]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	ldr x13, [x11, #24]
	ldr x14, [x19, #3224]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #24]
	add x12, x20, #1
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3328]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3336]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3344]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	ldr x13, [x11, #24]
	ldr x14, [x19, #3352]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #24]
	add x12, x20, #2
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3456]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3464]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3472]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	ldr x13, [x11, #24]
	ldr x14, [x19, #3480]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #24]
	add x12, x20, #3
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3584]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3592]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3600]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	ldr x13, [x11, #24]
	ldr x14, [x19, #3608]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #24]
	rev w9, w22
	str w9, [x19, #3196]
	rev w9, w22
	str w9, [x19, #3324]
	rev w9, w22
	str w9, [x19, #3452]
	rev w9, w22
	str w9, [x19, #3580]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #96, lsl #0
	add x3, x0, #64
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n32}
	add x22, x22, #1
	sub x9, x22, #15
	cbnz x9, 21b
	add x9, x19, x21
	ldrb w9, [x9, #1856]
	eor x10, x22, x9
	add x11, x21, #0
	lsl x11, x11, #5
	add x11, x11, x24
	add x12, x20, #0
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3200]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3208]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3216]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	ldr x13, [x11, #24]
	ldr x14, [x19, #3224]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #24]
	add x12, x20, #1
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3328]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3336]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3344]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	ldr x13, [x11, #24]
	ldr x14, [x19, #3352]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #24]
	add x12, x20, #2
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3456]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3464]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3472]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	ldr x13, [x11, #24]
	ldr x14, [x19, #3480]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #24]
	add x12, x20, #3
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3584]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3592]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3600]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	ldr x13, [x11, #24]
	ldr x14, [x19, #3608]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #24]
	add x10, x21, #0
	lsl x10, x10, #5
	add x10, x10, x19
	ldr q16, [x19, #3200]
	str q16, [x10, #3712]
	ldr q16, [x19, #3216]
	str q16, [x10, #3728]
	ldr q16, [x19, #3328]
	str q16, [x10, #5920]
	ldr q16, [x19, #3344]
	str q16, [x10, #5936]
	ldr q16, [x19, #3456]
	str q16, [x10, #8128]
	ldr q16, [x19, #3472]
	str q16, [x10, #8144]
	ldr q16, [x19, #3584]
	str q16, [x10, #10336]
	ldr q16, [x19, #3600]
	str q16, [x10, #10352]
	add x21, x21, #1
	sub x9, x21, #67
	cbnz x9, 20b
	add x0, x19, #3648
	movz x1, #2208, lsl #0
	movz x2, #2208, lsl #0
	add x3, x0, #64
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n32}
	add x10, x20, #0
	lsl x10, x10, #5
	add x10, x10, x19
	ldr q16, [x19, #3712]
	str q16, [x10, #12480]
	ldr q16, [x19, #3728]
	str q16, [x10, #12496]
	ldr q16, [x19, #5920]
	str q16, [x10, #12512]
	ldr q16, [x19, #5936]
	str q16, [x10, #12528]
	ldr q16, [x19, #8128]
	str q16, [x10, #12544]
	ldr q16, [x19, #8144]
	str q16, [x10, #12560]
	ldr q16, [x19, #10336]
	str q16, [x10, #12576]
	ldr q16, [x19, #10352]
	str q16, [x10, #12592]
	ldr x20, [x19, #1032]
	ldr x21, [x19, #1040]
	ldr x22, [x19, #1048]
	ldr x23, [x19, #1056]
	ldr x24, [x19, #1064]
	ldr x30, [x19, #1072]
	ldr x19, [x19, #1024]
	ret
	.p2align 6
