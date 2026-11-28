// The functions of `src/internal/vg_slhdsa_shake_xmsspk_128s.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_xmsspk_128s:
	str x19, [x0, #1152]
	str x20, [x0, #1160]
	str x21, [x0, #1168]
	str x22, [x0, #1176]
	str x23, [x0, #1184]
	str x24, [x0, #1192]
	str x25, [x0, #1200]
	str x26, [x0, #1208]
	str x30, [x0, #1216]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	movz x12, #0, lsl #0
	movz x11, #15, lsl #0
	ldrb w9, [x19, #1984]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1856]
	strb w9, [x19, #1857]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1985]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1858]
	strb w9, [x19, #1859]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1986]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1860]
	strb w9, [x19, #1861]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1987]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1862]
	strb w9, [x19, #1863]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1988]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1864]
	strb w9, [x19, #1865]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1989]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1866]
	strb w9, [x19, #1867]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1990]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1868]
	strb w9, [x19, #1869]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1991]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1870]
	strb w9, [x19, #1871]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1992]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1872]
	strb w9, [x19, #1873]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1993]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1874]
	strb w9, [x19, #1875]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1994]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1876]
	strb w9, [x19, #1877]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1995]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1878]
	strb w9, [x19, #1879]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1996]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1880]
	strb w9, [x19, #1881]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1997]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1882]
	strb w9, [x19, #1883]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1998]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1884]
	strb w9, [x19, #1885]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #1999]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1886]
	strb w9, [x19, #1887]
	add x12, x12, x10
	add x12, x12, x9
	movz x13, #480, lsl #0
	sub x13, x13, x12
	lsr x10, x13, #8
	and x10, x10, x11
	strb w10, [x19, #1888]
	lsr x10, x13, #4
	and x10, x10, x11
	strb w10, [x19, #1889]
	and x10, x13, x11
	strb w10, [x19, #1890]
	movz x22, #0, lsl #0
20:
	movz x24, #15, lsl #0
	add x10, x22, #0
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	movz w9, #0, lsl #16
	str w9, [x19, #3168]
	rev w9, w20
	str w9, [x19, #3172]
	rev w9, w10
	str w9, [x19, #3176]
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x21
	ldr q16, [x12, #0]
	str q16, [x19, #3184]
	sub x13, x24, x11
	lsr x13, x13, #63
	movz x15, #0, lsl #0
	sub x15, x15, x13
	eor x13, x11, x24
	and x13, x13, x15
	eor x24, x13, x11
	add x10, x22, #1
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	movz w9, #0, lsl #16
	str w9, [x19, #3296]
	rev w9, w20
	str w9, [x19, #3300]
	rev w9, w10
	str w9, [x19, #3304]
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x21
	ldr q16, [x12, #0]
	str q16, [x19, #3312]
	sub x13, x24, x11
	lsr x13, x13, #63
	movz x15, #0, lsl #0
	sub x15, x15, x13
	eor x13, x11, x24
	and x13, x13, x15
	eor x24, x13, x11
	add x10, x22, #2
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	movz w9, #0, lsl #16
	str w9, [x19, #3424]
	rev w9, w20
	str w9, [x19, #3428]
	rev w9, w10
	str w9, [x19, #3432]
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x21
	ldr q16, [x12, #0]
	str q16, [x19, #3440]
	sub x13, x24, x11
	lsr x13, x13, #63
	movz x15, #0, lsl #0
	sub x15, x15, x13
	eor x13, x11, x24
	and x13, x13, x15
	eor x24, x13, x11
	add x10, x22, #3
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	movz w9, #0, lsl #16
	str w9, [x19, #3552]
	rev w9, w20
	str w9, [x19, #3556]
	rev w9, w10
	str w9, [x19, #3560]
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x21
	ldr q16, [x12, #0]
	str q16, [x19, #3568]
	sub x13, x24, x11
	lsr x13, x13, #63
	movz x15, #0, lsl #0
	sub x15, x15, x13
	eor x13, x11, x24
	and x13, x13, x15
	eor x24, x13, x11
	add x23, x24, #0
	sub x9, x24, #15
	cbz x9, 21f
23:
	rev w9, w23
	str w9, [x19, #3180]
	rev w9, w23
	str w9, [x19, #3308]
	rev w9, w23
	str w9, [x19, #3436]
	rev w9, w23
	str w9, [x19, #3564]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #64, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16}
	add x10, x22, #0
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	sub x13, x23, x11
	lsr x13, x13, #63
	cbz x13, 24f
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x21
	ldr q16, [x12, #0]
	str q16, [x19, #3184]
	b 25f
24:
25:
	add x10, x22, #1
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	sub x13, x23, x11
	lsr x13, x13, #63
	cbz x13, 26f
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x21
	ldr q16, [x12, #0]
	str q16, [x19, #3312]
	b 27f
26:
27:
	add x10, x22, #2
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	sub x13, x23, x11
	lsr x13, x13, #63
	cbz x13, 28f
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x21
	ldr q16, [x12, #0]
	str q16, [x19, #3440]
	b 29f
28:
29:
	add x10, x22, #3
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	sub x13, x23, x11
	lsr x13, x13, #63
	cbz x13, 210f
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x21
	ldr q16, [x12, #0]
	str q16, [x19, #3568]
	b 211f
210:
211:
	add x23, x23, #1
	sub x9, x23, #15
	cbnz x9, 23b
	b 22f
21:
22:
	add x10, x22, #0
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x19
	ldr q16, [x19, #3184]
	str q16, [x12, #3696]
	add x10, x22, #1
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x19
	ldr q16, [x19, #3312]
	str q16, [x12, #3696]
	add x10, x22, #2
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x19
	ldr q16, [x19, #3440]
	str q16, [x12, #3696]
	add x10, x22, #3
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x19, x10
	ldrb w11, [x11, #1856]
	add x12, x10, #0
	lsl x12, x12, #4
	add x12, x12, x19
	ldr q16, [x19, #3568]
	str q16, [x12, #3696]
	add x22, x22, #4
	sub x9, x22, #35
	lsr x9, x9, #63
	cbnz x9, 20b
	movz w9, #256, lsl #16
	str w9, [x19, #3680]
	rev w9, w20
	str w9, [x19, #3684]
	movz w9, #0, lsl #16
	str w9, [x19, #3688]
	movz w9, #0, lsl #16
	str w9, [x19, #3692]
	add x0, x19, #3648
	movz x1, #2208, lsl #0
	movz x2, #608, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16}
	ldr q16, [x19, #3696]
	str q16, [x19, #3184]
	movz x25, #0, lsl #0
	add x26, x20, #0
212:
	add x12, x25, #0
	lsl x12, x12, #4
	add x12, x12, x21
	add x12, x12, #560
	movz x9, #1, lsl #0
	and x9, x26, x9
	cbz x9, 213f
	ldr q16, [x19, #3184]
	str q16, [x19, #3200]
	ldr q16, [x12, #0]
	str q16, [x19, #3184]
	b 214f
213:
	ldr q16, [x12, #0]
	str q16, [x19, #3200]
214:
	movz w9, #512, lsl #16
	str w9, [x19, #3168]
	movz w9, #0, lsl #16
	str w9, [x19, #3172]
	add x10, x25, #1
	rev w9, w10
	str w9, [x19, #3176]
	lsr x26, x26, #1
	rev w9, w26
	str w9, [x19, #3180]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #80, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16}
	add x25, x25, #1
	sub x9, x25, #9
	cbnz x9, 212b
	ldr q16, [x19, #3184]
	str q16, [x19, #1984]
	ldr x20, [x19, #1160]
	ldr x21, [x19, #1168]
	ldr x22, [x19, #1176]
	ldr x23, [x19, #1184]
	ldr x24, [x19, #1192]
	ldr x25, [x19, #1200]
	ldr x26, [x19, #1208]
	ldr x30, [x19, #1216]
	ldr x19, [x19, #1152]
	ret
	.p2align 6
