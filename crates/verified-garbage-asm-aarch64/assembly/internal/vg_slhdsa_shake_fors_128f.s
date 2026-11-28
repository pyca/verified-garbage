// The functions of `src/internal/vg_slhdsa_shake_fors_128f.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_fors_128f:
	str x19, [x0, #1280]
	str x20, [x0, #1288]
	str x21, [x0, #1296]
	str x23, [x0, #1304]
	str x24, [x0, #1312]
	str x25, [x0, #1320]
	str x26, [x0, #1328]
	str x27, [x0, #1336]
	str x30, [x0, #1344]
	add x19, x0, #0
	add x24, x1, #0
	add x20, x2, #0
	ldrb w9, [x19, #1792]
	lsl x9, x9, #16
	ldrb w10, [x19, #1793]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1794]
	orr x9, x9, x10
	lsr x9, x9, #18
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2048]
	ldrb w9, [x19, #1792]
	lsl x9, x9, #16
	ldrb w10, [x19, #1793]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1794]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2056]
	ldrb w9, [x19, #1793]
	lsl x9, x9, #16
	ldrb w10, [x19, #1794]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1795]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2064]
	ldrb w9, [x19, #1794]
	lsl x9, x9, #16
	ldrb w10, [x19, #1795]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1796]
	orr x9, x9, x10
	lsr x9, x9, #16
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2072]
	ldrb w9, [x19, #1795]
	lsl x9, x9, #16
	ldrb w10, [x19, #1796]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1797]
	orr x9, x9, x10
	lsr x9, x9, #18
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2080]
	ldrb w9, [x19, #1795]
	lsl x9, x9, #16
	ldrb w10, [x19, #1796]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1797]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2088]
	ldrb w9, [x19, #1796]
	lsl x9, x9, #16
	ldrb w10, [x19, #1797]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1798]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2096]
	ldrb w9, [x19, #1797]
	lsl x9, x9, #16
	ldrb w10, [x19, #1798]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1799]
	orr x9, x9, x10
	lsr x9, x9, #16
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2104]
	ldrb w9, [x19, #1798]
	lsl x9, x9, #16
	ldrb w10, [x19, #1799]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1800]
	orr x9, x9, x10
	lsr x9, x9, #18
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2112]
	ldrb w9, [x19, #1798]
	lsl x9, x9, #16
	ldrb w10, [x19, #1799]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1800]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2120]
	ldrb w9, [x19, #1799]
	lsl x9, x9, #16
	ldrb w10, [x19, #1800]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1801]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2128]
	ldrb w9, [x19, #1800]
	lsl x9, x9, #16
	ldrb w10, [x19, #1801]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1802]
	orr x9, x9, x10
	lsr x9, x9, #16
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2136]
	ldrb w9, [x19, #1801]
	lsl x9, x9, #16
	ldrb w10, [x19, #1802]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1803]
	orr x9, x9, x10
	lsr x9, x9, #18
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2144]
	ldrb w9, [x19, #1801]
	lsl x9, x9, #16
	ldrb w10, [x19, #1802]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1803]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2152]
	ldrb w9, [x19, #1802]
	lsl x9, x9, #16
	ldrb w10, [x19, #1803]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1804]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2160]
	ldrb w9, [x19, #1803]
	lsl x9, x9, #16
	ldrb w10, [x19, #1804]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1805]
	orr x9, x9, x10
	lsr x9, x9, #16
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2168]
	ldrb w9, [x19, #1804]
	lsl x9, x9, #16
	ldrb w10, [x19, #1805]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1806]
	orr x9, x9, x10
	lsr x9, x9, #18
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2176]
	ldrb w9, [x19, #1804]
	lsl x9, x9, #16
	ldrb w10, [x19, #1805]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1806]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2184]
	ldrb w9, [x19, #1805]
	lsl x9, x9, #16
	ldrb w10, [x19, #1806]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1807]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2192]
	ldrb w9, [x19, #1806]
	lsl x9, x9, #16
	ldrb w10, [x19, #1807]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1808]
	orr x9, x9, x10
	lsr x9, x9, #16
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2200]
	ldrb w9, [x19, #1807]
	lsl x9, x9, #16
	ldrb w10, [x19, #1808]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1809]
	orr x9, x9, x10
	lsr x9, x9, #18
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2208]
	ldrb w9, [x19, #1807]
	lsl x9, x9, #16
	ldrb w10, [x19, #1808]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1809]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2216]
	ldrb w9, [x19, #1808]
	lsl x9, x9, #16
	ldrb w10, [x19, #1809]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1810]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2224]
	ldrb w9, [x19, #1809]
	lsl x9, x9, #16
	ldrb w10, [x19, #1810]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1811]
	orr x9, x9, x10
	lsr x9, x9, #16
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2232]
	ldrb w9, [x19, #1810]
	lsl x9, x9, #16
	ldrb w10, [x19, #1811]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1812]
	orr x9, x9, x10
	lsr x9, x9, #18
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2240]
	ldrb w9, [x19, #1810]
	lsl x9, x9, #16
	ldrb w10, [x19, #1811]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1812]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2248]
	ldrb w9, [x19, #1811]
	lsl x9, x9, #16
	ldrb w10, [x19, #1812]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1813]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2256]
	ldrb w9, [x19, #1812]
	lsl x9, x9, #16
	ldrb w10, [x19, #1813]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1814]
	orr x9, x9, x10
	lsr x9, x9, #16
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2264]
	ldrb w9, [x19, #1813]
	lsl x9, x9, #16
	ldrb w10, [x19, #1814]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1815]
	orr x9, x9, x10
	lsr x9, x9, #18
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2272]
	ldrb w9, [x19, #1813]
	lsl x9, x9, #16
	ldrb w10, [x19, #1814]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1815]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2280]
	ldrb w9, [x19, #1814]
	lsl x9, x9, #16
	ldrb w10, [x19, #1815]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1816]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2288]
	ldrb w9, [x19, #1815]
	lsl x9, x9, #16
	ldrb w10, [x19, #1816]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1817]
	orr x9, x9, x10
	lsr x9, x9, #16
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2296]
	ldrb w9, [x19, #1816]
	lsl x9, x9, #16
	ldrb w10, [x19, #1817]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1818]
	orr x9, x9, x10
	lsr x9, x9, #18
	movz x10, #63, lsl #0
	and x9, x9, x10
	str x9, [x19, #2304]
	movz x23, #0, lsl #0
	movz x27, #0, lsl #0
20:
	lsl x9, x23, #3
	add x9, x9, x19
	ldr x21, [x9, #2048]
	movi v16.2d, #0
	str q16, [x24, #0]
	str q16, [x24, #16]
	str q16, [x24, #32]
	str q16, [x24, #48]
	str q16, [x24, #64]
	str q16, [x24, #80]
	str q16, [x24, #96]
	movz x25, #0, lsl #0
21:
	movz x26, #0, lsl #0
22:
	add x10, x27, x25
	add x10, x10, x26
	movz w9, #1536, lsl #16
	str w9, [x19, #3168]
	rev w9, w20
	str w9, [x19, #3172]
	movz w9, #0, lsl #16
	str w9, [x19, #3176]
	add x11, x10, #0
	rev w9, w11
	str w9, [x19, #3180]
	ldr q16, [x19, #1664]
	str q16, [x19, #3184]
	movz w9, #1536, lsl #16
	str w9, [x19, #3296]
	rev w9, w20
	str w9, [x19, #3300]
	movz w9, #0, lsl #16
	str w9, [x19, #3304]
	add x11, x10, #1
	rev w9, w11
	str w9, [x19, #3308]
	ldr q16, [x19, #1664]
	str q16, [x19, #3312]
	movz w9, #1536, lsl #16
	str w9, [x19, #3424]
	rev w9, w20
	str w9, [x19, #3428]
	movz w9, #0, lsl #16
	str w9, [x19, #3432]
	add x11, x10, #2
	rev w9, w11
	str w9, [x19, #3436]
	ldr q16, [x19, #1664]
	str q16, [x19, #3440]
	movz w9, #1536, lsl #16
	str w9, [x19, #3552]
	rev w9, w20
	str w9, [x19, #3556]
	movz w9, #0, lsl #16
	str w9, [x19, #3560]
	add x11, x10, #3
	rev w9, w11
	str w9, [x19, #3564]
	ldr q16, [x19, #1664]
	str q16, [x19, #3568]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #64, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16}
	add x11, x25, x26
	add x12, x11, #0
	eor x12, x12, x21
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x19, #3184]
	and x13, x13, x12
	ldr x14, [x24, #0]
	eor x14, x14, x13
	str x14, [x24, #0]
	ldr x13, [x19, #3192]
	and x13, x13, x12
	ldr x14, [x24, #8]
	eor x14, x14, x13
	str x14, [x24, #8]
	add x12, x11, #1
	eor x12, x12, x21
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x19, #3312]
	and x13, x13, x12
	ldr x14, [x24, #0]
	eor x14, x14, x13
	str x14, [x24, #0]
	ldr x13, [x19, #3320]
	and x13, x13, x12
	ldr x14, [x24, #8]
	eor x14, x14, x13
	str x14, [x24, #8]
	add x12, x11, #2
	eor x12, x12, x21
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x19, #3440]
	and x13, x13, x12
	ldr x14, [x24, #0]
	eor x14, x14, x13
	str x14, [x24, #0]
	ldr x13, [x19, #3448]
	and x13, x13, x12
	ldr x14, [x24, #8]
	eor x14, x14, x13
	str x14, [x24, #8]
	add x12, x11, #3
	eor x12, x12, x21
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x19, #3568]
	and x13, x13, x12
	ldr x14, [x24, #0]
	eor x14, x14, x13
	str x14, [x24, #0]
	ldr x13, [x19, #3576]
	and x13, x13, x12
	ldr x14, [x24, #8]
	eor x14, x14, x13
	str x14, [x24, #8]
	movz w9, #768, lsl #16
	str w9, [x19, #3168]
	movz w9, #768, lsl #16
	str w9, [x19, #3296]
	movz w9, #768, lsl #16
	str w9, [x19, #3424]
	movz w9, #768, lsl #16
	str w9, [x19, #3552]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #64, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16}
	add x10, x26, #0
	lsl x10, x10, #4
	add x10, x10, x19
	ldr q16, [x19, #3184]
	str q16, [x10, #12480]
	ldr q16, [x19, #3312]
	str q16, [x10, #12496]
	ldr q16, [x19, #3440]
	str q16, [x10, #12512]
	ldr q16, [x19, #3568]
	str q16, [x10, #12528]
	add x26, x26, #4
	sub x9, x26, #64
	cbnz x9, 22b
	add x10, x24, #16
	add x11, x27, x25
	add x9, x25, #0
	str x9, [x19, #1496]
	add x9, x11, #0
	str x9, [x19, #1504]
	movz x9, #3, lsl #0
	str x9, [x19, #1512]
	add x9, x20, #0
	str x9, [x19, #1520]
	add x0, x19, #0
	movz x1, #12480, lsl #0
	add x1, x19, x1
	movz x2, #64, lsl #0
	movz x3, #0, lsl #0
	add x4, x10, #0
	add x5, x21, #0
	bl {vg_slhdsa_shake_levels_n16}
	lsr x10, x25, #6
	lsl x10, x10, #4
	add x10, x10, x19
	ldr q16, [x19, #12480]
	str q16, [x10, #29120]
	add x25, x25, #64
	movz x10, #64, lsl #0
	sub x9, x25, x10
	cbnz x9, 21b
	add x10, x23, #0
	lsl x10, x10, #4
	add x10, x10, x19
	ldr q16, [x19, #29120]
	str q16, [x10, #3696]
	add x24, x24, #112
	movz x10, #64, lsl #0
	add x27, x27, x10
	add x23, x23, #1
	sub x9, x23, #33
	cbnz x9, 20b
	movz w9, #1024, lsl #16
	str w9, [x19, #3680]
	rev w9, w20
	str w9, [x19, #3684]
	movz w9, #0, lsl #16
	str w9, [x19, #3688]
	movz w9, #0, lsl #16
	str w9, [x19, #3692]
	add x0, x19, #3648
	movz x1, #2208, lsl #0
	movz x2, #576, lsl #0
	add x3, x0, #48
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n16}
	ldr q16, [x19, #3696]
	str q16, [x19, #1984]
	ldr x20, [x19, #1288]
	ldr x21, [x19, #1296]
	ldr x23, [x19, #1304]
	ldr x24, [x19, #1312]
	ldr x25, [x19, #1320]
	ldr x26, [x19, #1328]
	ldr x27, [x19, #1336]
	ldr x30, [x19, #1344]
	ldr x19, [x19, #1280]
	ret
	.p2align 6
