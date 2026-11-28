// The functions of `src/internal/vg_slhdsa_shake_forspk_256f.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_forspk_256f:
	str x19, [x0, #1280]
	str x20, [x0, #1288]
	str x21, [x0, #1296]
	str x22, [x0, #1304]
	str x23, [x0, #1312]
	str x24, [x0, #1320]
	str x25, [x0, #1328]
	str x26, [x0, #1336]
	str x27, [x0, #1344]
	str x30, [x0, #1352]
	add x19, x0, #0
	add x21, x1, #0
	add x20, x2, #0
	ldrb w9, [x19, #1792]
	lsl x9, x9, #16
	ldrb w10, [x19, #1793]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1794]
	orr x9, x9, x10
	lsr x9, x9, #15
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2048]
	ldrb w9, [x19, #1793]
	lsl x9, x9, #16
	ldrb w10, [x19, #1794]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1795]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2056]
	ldrb w9, [x19, #1794]
	lsl x9, x9, #16
	ldrb w10, [x19, #1795]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1796]
	orr x9, x9, x10
	lsr x9, x9, #13
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2064]
	ldrb w9, [x19, #1795]
	lsl x9, x9, #16
	ldrb w10, [x19, #1796]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1797]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2072]
	ldrb w9, [x19, #1796]
	lsl x9, x9, #16
	ldrb w10, [x19, #1797]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1798]
	orr x9, x9, x10
	lsr x9, x9, #11
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2080]
	ldrb w9, [x19, #1797]
	lsl x9, x9, #16
	ldrb w10, [x19, #1798]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1799]
	orr x9, x9, x10
	lsr x9, x9, #10
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2088]
	ldrb w9, [x19, #1798]
	lsl x9, x9, #16
	ldrb w10, [x19, #1799]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1800]
	orr x9, x9, x10
	lsr x9, x9, #9
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2096]
	ldrb w9, [x19, #1799]
	lsl x9, x9, #16
	ldrb w10, [x19, #1800]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1801]
	orr x9, x9, x10
	lsr x9, x9, #8
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2104]
	ldrb w9, [x19, #1801]
	lsl x9, x9, #16
	ldrb w10, [x19, #1802]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1803]
	orr x9, x9, x10
	lsr x9, x9, #15
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2112]
	ldrb w9, [x19, #1802]
	lsl x9, x9, #16
	ldrb w10, [x19, #1803]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1804]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2120]
	ldrb w9, [x19, #1803]
	lsl x9, x9, #16
	ldrb w10, [x19, #1804]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1805]
	orr x9, x9, x10
	lsr x9, x9, #13
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2128]
	ldrb w9, [x19, #1804]
	lsl x9, x9, #16
	ldrb w10, [x19, #1805]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1806]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2136]
	ldrb w9, [x19, #1805]
	lsl x9, x9, #16
	ldrb w10, [x19, #1806]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1807]
	orr x9, x9, x10
	lsr x9, x9, #11
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2144]
	ldrb w9, [x19, #1806]
	lsl x9, x9, #16
	ldrb w10, [x19, #1807]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1808]
	orr x9, x9, x10
	lsr x9, x9, #10
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2152]
	ldrb w9, [x19, #1807]
	lsl x9, x9, #16
	ldrb w10, [x19, #1808]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1809]
	orr x9, x9, x10
	lsr x9, x9, #9
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2160]
	ldrb w9, [x19, #1808]
	lsl x9, x9, #16
	ldrb w10, [x19, #1809]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1810]
	orr x9, x9, x10
	lsr x9, x9, #8
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2168]
	ldrb w9, [x19, #1810]
	lsl x9, x9, #16
	ldrb w10, [x19, #1811]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1812]
	orr x9, x9, x10
	lsr x9, x9, #15
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2176]
	ldrb w9, [x19, #1811]
	lsl x9, x9, #16
	ldrb w10, [x19, #1812]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1813]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2184]
	ldrb w9, [x19, #1812]
	lsl x9, x9, #16
	ldrb w10, [x19, #1813]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1814]
	orr x9, x9, x10
	lsr x9, x9, #13
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2192]
	ldrb w9, [x19, #1813]
	lsl x9, x9, #16
	ldrb w10, [x19, #1814]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1815]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2200]
	ldrb w9, [x19, #1814]
	lsl x9, x9, #16
	ldrb w10, [x19, #1815]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1816]
	orr x9, x9, x10
	lsr x9, x9, #11
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2208]
	ldrb w9, [x19, #1815]
	lsl x9, x9, #16
	ldrb w10, [x19, #1816]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1817]
	orr x9, x9, x10
	lsr x9, x9, #10
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2216]
	ldrb w9, [x19, #1816]
	lsl x9, x9, #16
	ldrb w10, [x19, #1817]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1818]
	orr x9, x9, x10
	lsr x9, x9, #9
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2224]
	ldrb w9, [x19, #1817]
	lsl x9, x9, #16
	ldrb w10, [x19, #1818]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1819]
	orr x9, x9, x10
	lsr x9, x9, #8
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2232]
	ldrb w9, [x19, #1819]
	lsl x9, x9, #16
	ldrb w10, [x19, #1820]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1821]
	orr x9, x9, x10
	lsr x9, x9, #15
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2240]
	ldrb w9, [x19, #1820]
	lsl x9, x9, #16
	ldrb w10, [x19, #1821]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1822]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2248]
	ldrb w9, [x19, #1821]
	lsl x9, x9, #16
	ldrb w10, [x19, #1822]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1823]
	orr x9, x9, x10
	lsr x9, x9, #13
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2256]
	ldrb w9, [x19, #1822]
	lsl x9, x9, #16
	ldrb w10, [x19, #1823]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1824]
	orr x9, x9, x10
	lsr x9, x9, #12
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2264]
	ldrb w9, [x19, #1823]
	lsl x9, x9, #16
	ldrb w10, [x19, #1824]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1825]
	orr x9, x9, x10
	lsr x9, x9, #11
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2272]
	ldrb w9, [x19, #1824]
	lsl x9, x9, #16
	ldrb w10, [x19, #1825]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1826]
	orr x9, x9, x10
	lsr x9, x9, #10
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2280]
	ldrb w9, [x19, #1825]
	lsl x9, x9, #16
	ldrb w10, [x19, #1826]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1827]
	orr x9, x9, x10
	lsr x9, x9, #9
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2288]
	ldrb w9, [x19, #1826]
	lsl x9, x9, #16
	ldrb w10, [x19, #1827]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1828]
	orr x9, x9, x10
	lsr x9, x9, #8
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2296]
	ldrb w9, [x19, #1828]
	lsl x9, x9, #16
	ldrb w10, [x19, #1829]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1830]
	orr x9, x9, x10
	lsr x9, x9, #15
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2304]
	ldrb w9, [x19, #1829]
	lsl x9, x9, #16
	ldrb w10, [x19, #1830]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1831]
	orr x9, x9, x10
	lsr x9, x9, #14
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2312]
	ldrb w9, [x19, #1830]
	lsl x9, x9, #16
	ldrb w10, [x19, #1831]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1832]
	orr x9, x9, x10
	lsr x9, x9, #13
	movz x10, #511, lsl #0
	and x9, x9, x10
	str x9, [x19, #2320]
	movz x22, #0, lsl #0
20:
	add x10, x22, #0
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	lsl x11, x10, #3
	add x11, x11, x19
	ldr x11, [x11, #2048]
	lsl x13, x10, #9
	add x24, x11, x13
	movz x13, #320, lsl #0
	mul x12, x10, x13
	add x12, x12, x21
	movz w9, #768, lsl #16
	str w9, [x19, #3184]
	rev w9, w20
	str w9, [x19, #3188]
	movz w9, #0, lsl #16
	str w9, [x19, #3192]
	rev w9, w24
	str w9, [x19, #3196]
	ldr q16, [x12, #0]
	str q16, [x19, #3200]
	ldr q16, [x12, #16]
	str q16, [x19, #3216]
	add x10, x22, #1
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	lsl x11, x10, #3
	add x11, x11, x19
	ldr x11, [x11, #2048]
	lsl x13, x10, #9
	add x25, x11, x13
	movz x13, #320, lsl #0
	mul x12, x10, x13
	add x12, x12, x21
	movz w9, #768, lsl #16
	str w9, [x19, #3312]
	rev w9, w20
	str w9, [x19, #3316]
	movz w9, #0, lsl #16
	str w9, [x19, #3320]
	rev w9, w25
	str w9, [x19, #3324]
	ldr q16, [x12, #0]
	str q16, [x19, #3328]
	ldr q16, [x12, #16]
	str q16, [x19, #3344]
	add x10, x22, #2
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	lsl x11, x10, #3
	add x11, x11, x19
	ldr x11, [x11, #2048]
	lsl x13, x10, #9
	add x26, x11, x13
	movz x13, #320, lsl #0
	mul x12, x10, x13
	add x12, x12, x21
	movz w9, #768, lsl #16
	str w9, [x19, #3440]
	rev w9, w20
	str w9, [x19, #3444]
	movz w9, #0, lsl #16
	str w9, [x19, #3448]
	rev w9, w26
	str w9, [x19, #3452]
	ldr q16, [x12, #0]
	str q16, [x19, #3456]
	ldr q16, [x12, #16]
	str q16, [x19, #3472]
	add x10, x22, #3
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	lsl x11, x10, #3
	add x11, x11, x19
	ldr x11, [x11, #2048]
	lsl x13, x10, #9
	add x27, x11, x13
	movz x13, #320, lsl #0
	mul x12, x10, x13
	add x12, x12, x21
	movz w9, #768, lsl #16
	str w9, [x19, #3568]
	rev w9, w20
	str w9, [x19, #3572]
	movz w9, #0, lsl #16
	str w9, [x19, #3576]
	rev w9, w27
	str w9, [x19, #3580]
	ldr q16, [x12, #0]
	str q16, [x19, #3584]
	ldr q16, [x12, #16]
	str q16, [x19, #3600]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #96, lsl #0
	add x3, x0, #64
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n32}
	movz x23, #0, lsl #0
21:
	add x10, x22, #0
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	movz x13, #320, lsl #0
	mul x12, x10, x13
	add x12, x12, x21
	add x13, x23, #0
	lsl x13, x13, #5
	add x12, x12, x13
	add x12, x12, #32
	movz x9, #1, lsl #0
	and x9, x24, x9
	cbz x9, 22f
	ldr q16, [x19, #3200]
	str q16, [x19, #3232]
	ldr q16, [x19, #3216]
	str q16, [x19, #3248]
	ldr q16, [x12, #0]
	str q16, [x19, #3200]
	ldr q16, [x12, #16]
	str q16, [x19, #3216]
	b 23f
22:
	ldr q16, [x12, #0]
	str q16, [x19, #3232]
	ldr q16, [x12, #16]
	str q16, [x19, #3248]
23:
	lsr x24, x24, #1
	add x10, x23, #1
	rev w9, w10
	str w9, [x19, #3192]
	rev w9, w24
	str w9, [x19, #3196]
	add x10, x22, #1
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	movz x13, #320, lsl #0
	mul x12, x10, x13
	add x12, x12, x21
	add x13, x23, #0
	lsl x13, x13, #5
	add x12, x12, x13
	add x12, x12, #32
	movz x9, #1, lsl #0
	and x9, x25, x9
	cbz x9, 24f
	ldr q16, [x19, #3328]
	str q16, [x19, #3360]
	ldr q16, [x19, #3344]
	str q16, [x19, #3376]
	ldr q16, [x12, #0]
	str q16, [x19, #3328]
	ldr q16, [x12, #16]
	str q16, [x19, #3344]
	b 25f
24:
	ldr q16, [x12, #0]
	str q16, [x19, #3360]
	ldr q16, [x12, #16]
	str q16, [x19, #3376]
25:
	lsr x25, x25, #1
	add x10, x23, #1
	rev w9, w10
	str w9, [x19, #3320]
	rev w9, w25
	str w9, [x19, #3324]
	add x10, x22, #2
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	movz x13, #320, lsl #0
	mul x12, x10, x13
	add x12, x12, x21
	add x13, x23, #0
	lsl x13, x13, #5
	add x12, x12, x13
	add x12, x12, #32
	movz x9, #1, lsl #0
	and x9, x26, x9
	cbz x9, 26f
	ldr q16, [x19, #3456]
	str q16, [x19, #3488]
	ldr q16, [x19, #3472]
	str q16, [x19, #3504]
	ldr q16, [x12, #0]
	str q16, [x19, #3456]
	ldr q16, [x12, #16]
	str q16, [x19, #3472]
	b 27f
26:
	ldr q16, [x12, #0]
	str q16, [x19, #3488]
	ldr q16, [x12, #16]
	str q16, [x19, #3504]
27:
	lsr x26, x26, #1
	add x10, x23, #1
	rev w9, w10
	str w9, [x19, #3448]
	rev w9, w26
	str w9, [x19, #3452]
	add x10, x22, #3
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	movz x13, #320, lsl #0
	mul x12, x10, x13
	add x12, x12, x21
	add x13, x23, #0
	lsl x13, x13, #5
	add x12, x12, x13
	add x12, x12, #32
	movz x9, #1, lsl #0
	and x9, x27, x9
	cbz x9, 28f
	ldr q16, [x19, #3584]
	str q16, [x19, #3616]
	ldr q16, [x19, #3600]
	str q16, [x19, #3632]
	ldr q16, [x12, #0]
	str q16, [x19, #3584]
	ldr q16, [x12, #16]
	str q16, [x19, #3600]
	b 29f
28:
	ldr q16, [x12, #0]
	str q16, [x19, #3616]
	ldr q16, [x12, #16]
	str q16, [x19, #3632]
29:
	lsr x27, x27, #1
	add x10, x23, #1
	rev w9, w10
	str w9, [x19, #3576]
	rev w9, w27
	str w9, [x19, #3580]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #128, lsl #0
	add x3, x0, #64
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n32}
	add x23, x23, #1
	sub x9, x23, #9
	cbnz x9, 21b
	add x10, x22, #0
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x10, #0
	lsl x11, x11, #5
	add x11, x11, x19
	ldr q16, [x19, #3200]
	str q16, [x11, #3712]
	ldr q16, [x19, #3216]
	str q16, [x11, #3728]
	add x10, x22, #1
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x10, #0
	lsl x11, x11, #5
	add x11, x11, x19
	ldr q16, [x19, #3328]
	str q16, [x11, #3712]
	ldr q16, [x19, #3344]
	str q16, [x11, #3728]
	add x10, x22, #2
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x10, #0
	lsl x11, x11, #5
	add x11, x11, x19
	ldr q16, [x19, #3456]
	str q16, [x11, #3712]
	ldr q16, [x19, #3472]
	str q16, [x11, #3728]
	add x10, x22, #3
	movz x13, #34, lsl #0
	sub x13, x13, x10
	lsr x13, x13, #63
	sub x14, x10, #34
	movz x15, #0, lsl #0
	sub x15, x15, x13
	and x14, x14, x15
	sub x10, x10, x14
	add x11, x10, #0
	lsl x11, x11, #5
	add x11, x11, x19
	ldr q16, [x19, #3584]
	str q16, [x11, #3712]
	ldr q16, [x19, #3600]
	str q16, [x11, #3728]
	add x22, x22, #4
	sub x9, x22, #35
	lsr x9, x9, #63
	cbnz x9, 20b
	movz w9, #1024, lsl #16
	str w9, [x19, #3696]
	rev w9, w20
	str w9, [x19, #3700]
	movz w9, #0, lsl #16
	str w9, [x19, #3704]
	movz w9, #0, lsl #16
	str w9, [x19, #3708]
	add x0, x19, #3648
	movz x1, #2208, lsl #0
	movz x2, #1184, lsl #0
	add x3, x0, #64
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n32}
	ldr q16, [x19, #3712]
	str q16, [x19, #1984]
	ldr q16, [x19, #3728]
	str q16, [x19, #2000]
	ldr x20, [x19, #1288]
	ldr x21, [x19, #1296]
	ldr x22, [x19, #1304]
	ldr x23, [x19, #1312]
	ldr x24, [x19, #1320]
	ldr x25, [x19, #1328]
	ldr x26, [x19, #1336]
	ldr x27, [x19, #1344]
	ldr x30, [x19, #1352]
	ldr x19, [x19, #1280]
	ret
	.p2align 6
