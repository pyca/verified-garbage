// The functions of `src/internal/vg_slhdsa_shake_wots4_n24.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_wots4_n24:
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
	str w9, [x19, #3180]
	rev w9, w10
	str w9, [x19, #3692]
	movz w9, #256, lsl #16
	str w9, [x19, #3688]
	movz w9, #0, lsl #16
	str w9, [x19, #3696]
	movz w9, #0, lsl #16
	str w9, [x19, #3700]
	add x10, x20, #1
	rev w9, w10
	str w9, [x19, #3308]
	rev w9, w10
	str w9, [x19, #5900]
	movz w9, #256, lsl #16
	str w9, [x19, #5896]
	movz w9, #0, lsl #16
	str w9, [x19, #5904]
	movz w9, #0, lsl #16
	str w9, [x19, #5908]
	add x10, x20, #2
	rev w9, w10
	str w9, [x19, #3436]
	rev w9, w10
	str w9, [x19, #8108]
	movz w9, #256, lsl #16
	str w9, [x19, #8104]
	movz w9, #0, lsl #16
	str w9, [x19, #8112]
	movz w9, #0, lsl #16
	str w9, [x19, #8116]
	add x10, x20, #3
	rev w9, w10
	str w9, [x19, #3564]
	rev w9, w10
	str w9, [x19, #10316]
	movz w9, #256, lsl #16
	str w9, [x19, #10312]
	movz w9, #0, lsl #16
	str w9, [x19, #10320]
	movz w9, #0, lsl #16
	str w9, [x19, #10324]
	movz x21, #0, lsl #0
20:
	movz w9, #1280, lsl #16
	str w9, [x19, #3176]
	rev w9, w21
	str w9, [x19, #3184]
	movz w9, #0, lsl #16
	str w9, [x19, #3188]
	ldr x14, [x19, #1664]
	str x14, [x19, #3192]
	ldr x14, [x19, #1672]
	str x14, [x19, #3200]
	ldr x14, [x19, #1680]
	str x14, [x19, #3208]
	movz w9, #1280, lsl #16
	str w9, [x19, #3304]
	rev w9, w21
	str w9, [x19, #3312]
	movz w9, #0, lsl #16
	str w9, [x19, #3316]
	ldr x14, [x19, #1664]
	str x14, [x19, #3320]
	ldr x14, [x19, #1672]
	str x14, [x19, #3328]
	ldr x14, [x19, #1680]
	str x14, [x19, #3336]
	movz w9, #1280, lsl #16
	str w9, [x19, #3432]
	rev w9, w21
	str w9, [x19, #3440]
	movz w9, #0, lsl #16
	str w9, [x19, #3444]
	ldr x14, [x19, #1664]
	str x14, [x19, #3448]
	ldr x14, [x19, #1672]
	str x14, [x19, #3456]
	ldr x14, [x19, #1680]
	str x14, [x19, #3464]
	movz w9, #1280, lsl #16
	str w9, [x19, #3560]
	rev w9, w21
	str w9, [x19, #3568]
	movz w9, #0, lsl #16
	str w9, [x19, #3572]
	ldr x14, [x19, #1664]
	str x14, [x19, #3576]
	ldr x14, [x19, #1672]
	str x14, [x19, #3584]
	ldr x14, [x19, #1680]
	str x14, [x19, #3592]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #80, lsl #0
	add x3, x0, #56
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n24}
	movz w9, #0, lsl #16
	str w9, [x19, #3176]
	movz w9, #0, lsl #16
	str w9, [x19, #3304]
	movz w9, #0, lsl #16
	str w9, [x19, #3432]
	movz w9, #0, lsl #16
	str w9, [x19, #3560]
	movz x22, #0, lsl #0
21:
	add x9, x19, x21
	ldrb w9, [x9, #1856]
	eor x10, x22, x9
	add x11, x21, #0
	lsl x12, x11, #3
	lsl x11, x11, #4
	add x11, x11, x12
	add x11, x11, x24
	add x12, x20, #0
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3192]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3200]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3208]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	add x12, x20, #1
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3320]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3328]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3336]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	add x12, x20, #2
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3448]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3456]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3464]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	add x12, x20, #3
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3576]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3584]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3592]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	rev w9, w22
	str w9, [x19, #3188]
	rev w9, w22
	str w9, [x19, #3316]
	rev w9, w22
	str w9, [x19, #3444]
	rev w9, w22
	str w9, [x19, #3572]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #80, lsl #0
	add x3, x0, #56
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n24}
	add x22, x22, #1
	sub x9, x22, #15
	cbnz x9, 21b
	add x9, x19, x21
	ldrb w9, [x9, #1856]
	eor x10, x22, x9
	add x11, x21, #0
	lsl x12, x11, #3
	lsl x11, x11, #4
	add x11, x11, x12
	add x11, x11, x24
	add x12, x20, #0
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3192]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3200]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3208]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	add x12, x20, #1
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3320]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3328]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3336]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	add x12, x20, #2
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3448]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3456]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3464]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	add x12, x20, #3
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3576]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3584]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	ldr x13, [x11, #16]
	ldr x14, [x19, #3592]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #16]
	add x10, x21, #0
	lsl x11, x10, #3
	lsl x10, x10, #4
	add x10, x10, x11
	add x10, x10, x19
	ldr x14, [x19, #3192]
	str x14, [x10, #3704]
	ldr q16, [x19, #3200]
	str q16, [x10, #3712]
	ldr x14, [x19, #3320]
	str x14, [x10, #5912]
	ldr q16, [x19, #3328]
	str q16, [x10, #5920]
	ldr x14, [x19, #3448]
	str x14, [x10, #8120]
	ldr q16, [x19, #3456]
	str q16, [x10, #8128]
	ldr x14, [x19, #3576]
	str x14, [x10, #10328]
	ldr q16, [x19, #3584]
	str q16, [x10, #10336]
	add x21, x21, #1
	sub x9, x21, #51
	cbnz x9, 20b
	add x0, x19, #3648
	movz x1, #2208, lsl #0
	movz x2, #1280, lsl #0
	add x3, x0, #56
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n24}
	add x10, x20, #0
	lsl x11, x10, #3
	lsl x10, x10, #4
	add x10, x10, x11
	add x10, x10, x19
	ldr x14, [x19, #3704]
	str x14, [x10, #12480]
	ldr x14, [x19, #3712]
	str x14, [x10, #12488]
	ldr x14, [x19, #3720]
	str x14, [x10, #12496]
	ldr x14, [x19, #5912]
	str x14, [x10, #12504]
	ldr q16, [x19, #5920]
	str q16, [x10, #12512]
	ldr x14, [x19, #8120]
	str x14, [x10, #12528]
	ldr x14, [x19, #8128]
	str x14, [x10, #12536]
	ldr x14, [x19, #8136]
	str x14, [x10, #12544]
	ldr x14, [x19, #10328]
	str x14, [x10, #12552]
	ldr q16, [x19, #10336]
	str q16, [x10, #12560]
	ldr x20, [x19, #1032]
	ldr x21, [x19, #1040]
	ldr x22, [x19, #1048]
	ldr x23, [x19, #1056]
	ldr x24, [x19, #1064]
	ldr x30, [x19, #1072]
	ldr x19, [x19, #1024]
	ret
	.p2align 6
