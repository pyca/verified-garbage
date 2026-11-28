// The functions of `src/internal/vg_slhdsa_shake_fors_192s.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_fors_192s:
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
	lsr x9, x9, #10
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2048]
	ldrb w9, [x19, #1793]
	lsl x9, x9, #16
	ldrb w10, [x19, #1794]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1795]
	orr x9, x9, x10
	lsr x9, x9, #4
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2056]
	ldrb w9, [x19, #1795]
	lsl x9, x9, #16
	ldrb w10, [x19, #1796]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1797]
	orr x9, x9, x10
	lsr x9, x9, #6
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2064]
	ldrb w9, [x19, #1797]
	lsl x9, x9, #16
	ldrb w10, [x19, #1798]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1799]
	orr x9, x9, x10
	lsr x9, x9, #8
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2072]
	ldrb w9, [x19, #1799]
	lsl x9, x9, #16
	ldrb w10, [x19, #1800]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1801]
	orr x9, x9, x10
	lsr x9, x9, #10
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2080]
	ldrb w9, [x19, #1800]
	lsl x9, x9, #16
	ldrb w10, [x19, #1801]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1802]
	orr x9, x9, x10
	lsr x9, x9, #4
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2088]
	ldrb w9, [x19, #1802]
	lsl x9, x9, #16
	ldrb w10, [x19, #1803]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1804]
	orr x9, x9, x10
	lsr x9, x9, #6
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2096]
	ldrb w9, [x19, #1804]
	lsl x9, x9, #16
	ldrb w10, [x19, #1805]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1806]
	orr x9, x9, x10
	lsr x9, x9, #8
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2104]
	ldrb w9, [x19, #1806]
	lsl x9, x9, #16
	ldrb w10, [x19, #1807]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1808]
	orr x9, x9, x10
	lsr x9, x9, #10
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2112]
	ldrb w9, [x19, #1807]
	lsl x9, x9, #16
	ldrb w10, [x19, #1808]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1809]
	orr x9, x9, x10
	lsr x9, x9, #4
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2120]
	ldrb w9, [x19, #1809]
	lsl x9, x9, #16
	ldrb w10, [x19, #1810]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1811]
	orr x9, x9, x10
	lsr x9, x9, #6
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2128]
	ldrb w9, [x19, #1811]
	lsl x9, x9, #16
	ldrb w10, [x19, #1812]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1813]
	orr x9, x9, x10
	lsr x9, x9, #8
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2136]
	ldrb w9, [x19, #1813]
	lsl x9, x9, #16
	ldrb w10, [x19, #1814]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1815]
	orr x9, x9, x10
	lsr x9, x9, #10
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2144]
	ldrb w9, [x19, #1814]
	lsl x9, x9, #16
	ldrb w10, [x19, #1815]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1816]
	orr x9, x9, x10
	lsr x9, x9, #4
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2152]
	ldrb w9, [x19, #1816]
	lsl x9, x9, #16
	ldrb w10, [x19, #1817]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1818]
	orr x9, x9, x10
	lsr x9, x9, #6
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2160]
	ldrb w9, [x19, #1818]
	lsl x9, x9, #16
	ldrb w10, [x19, #1819]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1820]
	orr x9, x9, x10
	lsr x9, x9, #8
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2168]
	ldrb w9, [x19, #1820]
	lsl x9, x9, #16
	ldrb w10, [x19, #1821]
	lsl x10, x10, #8
	orr x9, x9, x10
	ldrb w10, [x19, #1822]
	orr x9, x9, x10
	lsr x9, x9, #10
	movz x10, #16383, lsl #0
	and x9, x9, x10
	str x9, [x19, #2176]
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
	str q16, [x24, #112]
	str q16, [x24, #128]
	str q16, [x24, #144]
	str q16, [x24, #160]
	str q16, [x24, #176]
	str q16, [x24, #192]
	str q16, [x24, #208]
	str q16, [x24, #224]
	str q16, [x24, #240]
	str q16, [x24, #256]
	str q16, [x24, #272]
	str q16, [x24, #288]
	str q16, [x24, #304]
	str q16, [x24, #320]
	str q16, [x24, #336]
	movz x14, #0, lsl #0
	str x14, [x24, #352]
	movz x25, #0, lsl #0
21:
	movz x26, #0, lsl #0
22:
	add x10, x27, x25
	add x10, x10, x26
	movz w9, #1536, lsl #16
	str w9, [x19, #3176]
	rev w9, w20
	str w9, [x19, #3180]
	movz w9, #0, lsl #16
	str w9, [x19, #3184]
	add x11, x10, #0
	rev w9, w11
	str w9, [x19, #3188]
	ldr x14, [x19, #1664]
	str x14, [x19, #3192]
	ldr x14, [x19, #1672]
	str x14, [x19, #3200]
	ldr x14, [x19, #1680]
	str x14, [x19, #3208]
	movz w9, #1536, lsl #16
	str w9, [x19, #3304]
	rev w9, w20
	str w9, [x19, #3308]
	movz w9, #0, lsl #16
	str w9, [x19, #3312]
	add x11, x10, #1
	rev w9, w11
	str w9, [x19, #3316]
	ldr x14, [x19, #1664]
	str x14, [x19, #3320]
	ldr x14, [x19, #1672]
	str x14, [x19, #3328]
	ldr x14, [x19, #1680]
	str x14, [x19, #3336]
	movz w9, #1536, lsl #16
	str w9, [x19, #3432]
	rev w9, w20
	str w9, [x19, #3436]
	movz w9, #0, lsl #16
	str w9, [x19, #3440]
	add x11, x10, #2
	rev w9, w11
	str w9, [x19, #3444]
	ldr x14, [x19, #1664]
	str x14, [x19, #3448]
	ldr x14, [x19, #1672]
	str x14, [x19, #3456]
	ldr x14, [x19, #1680]
	str x14, [x19, #3464]
	movz w9, #1536, lsl #16
	str w9, [x19, #3560]
	rev w9, w20
	str w9, [x19, #3564]
	movz w9, #0, lsl #16
	str w9, [x19, #3568]
	add x11, x10, #3
	rev w9, w11
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
	add x11, x25, x26
	add x12, x11, #0
	eor x12, x12, x21
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x19, #3192]
	and x13, x13, x12
	ldr x14, [x24, #0]
	eor x14, x14, x13
	str x14, [x24, #0]
	ldr x13, [x19, #3200]
	and x13, x13, x12
	ldr x14, [x24, #8]
	eor x14, x14, x13
	str x14, [x24, #8]
	ldr x13, [x19, #3208]
	and x13, x13, x12
	ldr x14, [x24, #16]
	eor x14, x14, x13
	str x14, [x24, #16]
	add x12, x11, #1
	eor x12, x12, x21
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x19, #3320]
	and x13, x13, x12
	ldr x14, [x24, #0]
	eor x14, x14, x13
	str x14, [x24, #0]
	ldr x13, [x19, #3328]
	and x13, x13, x12
	ldr x14, [x24, #8]
	eor x14, x14, x13
	str x14, [x24, #8]
	ldr x13, [x19, #3336]
	and x13, x13, x12
	ldr x14, [x24, #16]
	eor x14, x14, x13
	str x14, [x24, #16]
	add x12, x11, #2
	eor x12, x12, x21
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x19, #3448]
	and x13, x13, x12
	ldr x14, [x24, #0]
	eor x14, x14, x13
	str x14, [x24, #0]
	ldr x13, [x19, #3456]
	and x13, x13, x12
	ldr x14, [x24, #8]
	eor x14, x14, x13
	str x14, [x24, #8]
	ldr x13, [x19, #3464]
	and x13, x13, x12
	ldr x14, [x24, #16]
	eor x14, x14, x13
	str x14, [x24, #16]
	add x12, x11, #3
	eor x12, x12, x21
	sub x12, x12, #1
	lsr x12, x12, #63
	movz x13, #0, lsl #0
	sub x12, x13, x12
	ldr x13, [x19, #3576]
	and x13, x13, x12
	ldr x14, [x24, #0]
	eor x14, x14, x13
	str x14, [x24, #0]
	ldr x13, [x19, #3584]
	and x13, x13, x12
	ldr x14, [x24, #8]
	eor x14, x14, x13
	str x14, [x24, #8]
	ldr x13, [x19, #3592]
	and x13, x13, x12
	ldr x14, [x24, #16]
	eor x14, x14, x13
	str x14, [x24, #16]
	movz w9, #768, lsl #16
	str w9, [x19, #3176]
	movz w9, #768, lsl #16
	str w9, [x19, #3304]
	movz w9, #768, lsl #16
	str w9, [x19, #3432]
	movz w9, #768, lsl #16
	str w9, [x19, #3560]
	add x0, x19, #3136
	movz x1, #128, lsl #0
	movz x2, #80, lsl #0
	add x3, x0, #56
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n24}
	add x10, x26, #0
	lsl x11, x10, #3
	lsl x10, x10, #4
	add x10, x10, x11
	add x10, x10, x19
	ldr x14, [x19, #3192]
	str x14, [x10, #12480]
	ldr x14, [x19, #3200]
	str x14, [x10, #12488]
	ldr x14, [x19, #3208]
	str x14, [x10, #12496]
	ldr x14, [x19, #3320]
	str x14, [x10, #12504]
	ldr q16, [x19, #3328]
	str q16, [x10, #12512]
	ldr x14, [x19, #3448]
	str x14, [x10, #12528]
	ldr x14, [x19, #3456]
	str x14, [x10, #12536]
	ldr x14, [x19, #3464]
	str x14, [x10, #12544]
	ldr x14, [x19, #3576]
	str x14, [x10, #12552]
	ldr q16, [x19, #3584]
	str q16, [x10, #12560]
	add x26, x26, #4
	sub x9, x26, #512
	cbnz x9, 22b
	add x10, x24, #24
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
	movz x2, #512, lsl #0
	movz x3, #0, lsl #0
	add x4, x10, #0
	add x5, x21, #0
	bl {vg_slhdsa_shake_levels_n24}
	lsr x10, x25, #9
	lsl x11, x10, #3
	lsl x10, x10, #4
	add x10, x10, x11
	add x10, x10, x19
	ldr q16, [x19, #12480]
	str q16, [x10, #29120]
	ldr x14, [x19, #12496]
	str x14, [x10, #29136]
	add x25, x25, #512
	movz x10, #16384, lsl #0
	sub x9, x25, x10
	cbnz x9, 21b
	ldr q16, [x19, #29120]
	str q16, [x19, #12480]
	ldr q16, [x19, #29136]
	str q16, [x19, #12496]
	ldr q16, [x19, #29152]
	str q16, [x19, #12512]
	ldr q16, [x19, #29168]
	str q16, [x19, #12528]
	ldr q16, [x19, #29184]
	str q16, [x19, #12544]
	ldr q16, [x19, #29200]
	str q16, [x19, #12560]
	ldr q16, [x19, #29216]
	str q16, [x19, #12576]
	ldr q16, [x19, #29232]
	str q16, [x19, #12592]
	ldr q16, [x19, #29248]
	str q16, [x19, #12608]
	ldr q16, [x19, #29264]
	str q16, [x19, #12624]
	ldr q16, [x19, #29280]
	str q16, [x19, #12640]
	ldr q16, [x19, #29296]
	str q16, [x19, #12656]
	ldr q16, [x19, #29312]
	str q16, [x19, #12672]
	ldr q16, [x19, #29328]
	str q16, [x19, #12688]
	ldr q16, [x19, #29344]
	str q16, [x19, #12704]
	ldr q16, [x19, #29360]
	str q16, [x19, #12720]
	ldr q16, [x19, #29376]
	str q16, [x19, #12736]
	ldr q16, [x19, #29392]
	str q16, [x19, #12752]
	ldr q16, [x19, #29408]
	str q16, [x19, #12768]
	ldr q16, [x19, #29424]
	str q16, [x19, #12784]
	ldr q16, [x19, #29440]
	str q16, [x19, #12800]
	ldr q16, [x19, #29456]
	str q16, [x19, #12816]
	ldr q16, [x19, #29472]
	str q16, [x19, #12832]
	ldr q16, [x19, #29488]
	str q16, [x19, #12848]
	ldr q16, [x19, #29504]
	str q16, [x19, #12864]
	ldr q16, [x19, #29520]
	str q16, [x19, #12880]
	ldr q16, [x19, #29536]
	str q16, [x19, #12896]
	ldr q16, [x19, #29552]
	str q16, [x19, #12912]
	ldr q16, [x19, #29568]
	str q16, [x19, #12928]
	ldr q16, [x19, #29584]
	str q16, [x19, #12944]
	ldr q16, [x19, #29600]
	str q16, [x19, #12960]
	ldr q16, [x19, #29616]
	str q16, [x19, #12976]
	ldr q16, [x19, #29632]
	str q16, [x19, #12992]
	ldr q16, [x19, #29648]
	str q16, [x19, #13008]
	ldr q16, [x19, #29664]
	str q16, [x19, #13024]
	ldr q16, [x19, #29680]
	str q16, [x19, #13040]
	ldr q16, [x19, #29696]
	str q16, [x19, #13056]
	ldr q16, [x19, #29712]
	str q16, [x19, #13072]
	ldr q16, [x19, #29728]
	str q16, [x19, #13088]
	ldr q16, [x19, #29744]
	str q16, [x19, #13104]
	ldr q16, [x19, #29760]
	str q16, [x19, #13120]
	ldr q16, [x19, #29776]
	str q16, [x19, #13136]
	ldr q16, [x19, #29792]
	str q16, [x19, #13152]
	ldr q16, [x19, #29808]
	str q16, [x19, #13168]
	ldr q16, [x19, #29824]
	str q16, [x19, #13184]
	ldr q16, [x19, #29840]
	str q16, [x19, #13200]
	ldr q16, [x19, #29856]
	str q16, [x19, #13216]
	ldr q16, [x19, #29872]
	str q16, [x19, #13232]
	add x10, x24, #240
	movz x9, #0, lsl #0
	str x9, [x19, #1496]
	add x9, x27, #0
	str x9, [x19, #1504]
	movz x9, #3, lsl #0
	str x9, [x19, #1512]
	add x9, x20, #0
	str x9, [x19, #1520]
	add x0, x19, #0
	movz x1, #12480, lsl #0
	add x1, x19, x1
	movz x2, #32, lsl #0
	movz x3, #9, lsl #0
	add x4, x10, #0
	add x5, x21, #0
	bl {vg_slhdsa_shake_levels_n24}
	add x10, x23, #0
	lsl x11, x10, #3
	lsl x10, x10, #4
	add x10, x10, x11
	add x10, x10, x19
	ldr x14, [x19, #12480]
	str x14, [x10, #3704]
	ldr x14, [x19, #12488]
	str x14, [x10, #3712]
	ldr x14, [x19, #12496]
	str x14, [x10, #3720]
	add x24, x24, #360
	movz x10, #16384, lsl #0
	add x27, x27, x10
	add x23, x23, #1
	sub x9, x23, #17
	cbnz x9, 20b
	movz w9, #1024, lsl #16
	str w9, [x19, #3688]
	rev w9, w20
	str w9, [x19, #3692]
	movz w9, #0, lsl #16
	str w9, [x19, #3696]
	movz w9, #0, lsl #16
	str w9, [x19, #3700]
	add x0, x19, #3648
	movz x1, #2208, lsl #0
	movz x2, #464, lsl #0
	add x3, x0, #56
	add x4, x19, #0
	bl {vg_slhdsa_shake_thash4_n24}
	ldr x14, [x19, #3704]
	str x14, [x19, #1984]
	ldr x14, [x19, #3712]
	str x14, [x19, #1992]
	ldr x14, [x19, #3720]
	str x14, [x19, #2000]
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
