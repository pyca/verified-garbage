// The functions of `src/internal/vg_slhdsa_shake_wots4_n16_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_wots4_n16_sha3:
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
	str w9, [x19, #3172]
	rev w9, w10
	str w9, [x19, #3684]
	movz w9, #256, lsl #16
	str w9, [x19, #3680]
	movz w9, #0, lsl #16
	str w9, [x19, #3688]
	movz w9, #0, lsl #16
	str w9, [x19, #3692]
	add x10, x20, #1
	rev w9, w10
	str w9, [x19, #3300]
	rev w9, w10
	str w9, [x19, #5892]
	movz w9, #256, lsl #16
	str w9, [x19, #5888]
	movz w9, #0, lsl #16
	str w9, [x19, #5896]
	movz w9, #0, lsl #16
	str w9, [x19, #5900]
	add x10, x20, #2
	rev w9, w10
	str w9, [x19, #3428]
	rev w9, w10
	str w9, [x19, #8100]
	movz w9, #256, lsl #16
	str w9, [x19, #8096]
	movz w9, #0, lsl #16
	str w9, [x19, #8104]
	movz w9, #0, lsl #16
	str w9, [x19, #8108]
	add x10, x20, #3
	rev w9, w10
	str w9, [x19, #3556]
	rev w9, w10
	str w9, [x19, #10308]
	movz w9, #256, lsl #16
	str w9, [x19, #10304]
	movz w9, #0, lsl #16
	str w9, [x19, #10312]
	movz w9, #0, lsl #16
	str w9, [x19, #10316]
	movz x21, #0, lsl #0
20:
	movz w9, #1280, lsl #16
	str w9, [x19, #3168]
	rev w9, w21
	str w9, [x19, #3176]
	movz w9, #0, lsl #16
	str w9, [x19, #3180]
	ldr q16, [x19, #1664]
	str q16, [x19, #3184]
	movz w9, #1280, lsl #16
	str w9, [x19, #3296]
	rev w9, w21
	str w9, [x19, #3304]
	movz w9, #0, lsl #16
	str w9, [x19, #3308]
	ldr q16, [x19, #1664]
	str q16, [x19, #3312]
	movz w9, #1280, lsl #16
	str w9, [x19, #3424]
	rev w9, w21
	str w9, [x19, #3432]
	movz w9, #0, lsl #16
	str w9, [x19, #3436]
	ldr q16, [x19, #1664]
	str q16, [x19, #3440]
	movz w9, #1280, lsl #16
	str w9, [x19, #3552]
	rev w9, w21
	str w9, [x19, #3560]
	movz w9, #0, lsl #16
	str w9, [x19, #3564]
	ldr q16, [x19, #1664]
	str q16, [x19, #3568]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #64, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16_sha3}
	movz w9, #0, lsl #16
	str w9, [x19, #3168]
	movz w9, #0, lsl #16
	str w9, [x19, #3296]
	movz w9, #0, lsl #16
	str w9, [x19, #3424]
	movz w9, #0, lsl #16
	str w9, [x19, #3552]
	movz x22, #0, lsl #0
21:
	add x9, x19, x21
	ldrb w9, [x9, #1856]
	eor x10, x22, x9
	add x11, x21, #0
	lsl x11, x11, #4
	add x11, x11, x24
	add x12, x20, #0
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3184]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3192]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	add x12, x20, #1
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3312]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3320]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	add x12, x20, #2
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3440]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3448]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	add x12, x20, #3
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3568]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3576]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	rev w9, w22
	str w9, [x19, #3180]
	rev w9, w22
	str w9, [x19, #3308]
	rev w9, w22
	str w9, [x19, #3436]
	rev w9, w22
	str w9, [x19, #3564]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #64, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16_sha3}
	add x22, x22, #1
	sub x9, x22, #15
	cbnz x9, 21b
	add x9, x19, x21
	ldrb w9, [x9, #1856]
	eor x10, x22, x9
	add x11, x21, #0
	lsl x11, x11, #4
	add x11, x11, x24
	add x12, x20, #0
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3184]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3192]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	add x12, x20, #1
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3312]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3320]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	add x12, x20, #2
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3440]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3448]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	add x12, x20, #3
	eor x12, x12, x23
	orr x12, x12, x10
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x11, #0]
	ldr x14, [x19, #3568]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #0]
	ldr x13, [x11, #8]
	ldr x14, [x19, #3576]
	eor x14, x14, x13
	and x14, x14, x12
	eor x13, x13, x14
	str x13, [x11, #8]
	add x10, x21, #0
	lsl x10, x10, #4
	add x10, x10, x19
	ldr q16, [x19, #3184]
	str q16, [x10, #3696]
	ldr q16, [x19, #3312]
	str q16, [x10, #5904]
	ldr q16, [x19, #3440]
	str q16, [x10, #8112]
	ldr q16, [x19, #3568]
	str q16, [x10, #10320]
	add x21, x21, #1
	sub x9, x21, #35
	cbnz x9, 20b
	add x0, x19, #3648
	movz x1, #2208, lsl #0
	movz x2, #608, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16_sha3}
	add x10, x20, #0
	lsl x10, x10, #4
	add x10, x10, x19
	ldr q16, [x19, #3696]
	str q16, [x10, #12480]
	ldr q16, [x19, #5904]
	str q16, [x10, #12496]
	ldr q16, [x19, #8112]
	str q16, [x10, #12512]
	ldr q16, [x19, #10320]
	str q16, [x10, #12528]
	ldr x20, [x19, #1032]
	ldr x21, [x19, #1040]
	ldr x22, [x19, #1048]
	ldr x23, [x19, #1056]
	ldr x24, [x19, #1064]
	ldr x30, [x19, #1072]
	ldr x19, [x19, #1024]
	ret
	.p2align 6
