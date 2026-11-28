// The functions of `src/internal/vg_slhdsa_shake_xmss_192s_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_xmss_192s_sha3:
	str x19, [x0, #1152]
	str x20, [x0, #1160]
	str x21, [x0, #1168]
	str x22, [x0, #1176]
	str x30, [x0, #1184]
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
	ldrb w9, [x19, #2000]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1888]
	strb w9, [x19, #1889]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #2001]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1890]
	strb w9, [x19, #1891]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #2002]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1892]
	strb w9, [x19, #1893]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #2003]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1894]
	strb w9, [x19, #1895]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #2004]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1896]
	strb w9, [x19, #1897]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #2005]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1898]
	strb w9, [x19, #1899]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #2006]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1900]
	strb w9, [x19, #1901]
	add x12, x12, x10
	add x12, x12, x9
	ldrb w9, [x19, #2007]
	lsr x10, x9, #4
	and x9, x9, x11
	strb w10, [x19, #1902]
	strb w9, [x19, #1903]
	add x12, x12, x10
	add x12, x12, x9
	movz x13, #720, lsl #0
	sub x13, x13, x12
	lsr x10, x13, #8
	and x10, x10, x11
	strb w10, [x19, #1904]
	lsr x10, x13, #4
	and x10, x10, x11
	strb w10, [x19, #1905]
	and x10, x13, x11
	strb w10, [x19, #1906]
	movz x22, #0, lsl #0
20:
	add x0, x19, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x21, #0
	bl {vg_slhdsa_shake_wots4_n24_sha3}
	add x22, x22, #4
	sub x9, x22, #512
	cbnz x9, 20b
	add x10, x21, #1224
	movi v16.2d, #0
	str q16, [x10, #0]
	str q16, [x10, #16]
	str q16, [x10, #32]
	str q16, [x10, #48]
	str q16, [x10, #64]
	str q16, [x10, #80]
	str q16, [x10, #96]
	str q16, [x10, #112]
	str q16, [x10, #128]
	str q16, [x10, #144]
	str q16, [x10, #160]
	str q16, [x10, #176]
	str q16, [x10, #192]
	movz x14, #0, lsl #0
	str x14, [x10, #208]
	movz x9, #0, lsl #0
	str x9, [x19, #1496]
	movz x9, #0, lsl #0
	str x9, [x19, #1504]
	movz x9, #2, lsl #0
	str x9, [x19, #1512]
	movz x9, #0, lsl #0
	str x9, [x19, #1520]
	add x0, x19, #0
	movz x1, #12480, lsl #0
	add x1, x19, x1
	movz x2, #512, lsl #0
	movz x3, #0, lsl #0
	add x4, x10, #0
	add x5, x20, #0
	bl {vg_slhdsa_shake_levels_n24_sha3}
	ldr q16, [x19, #12480]
	str q16, [x19, #1984]
	ldr x14, [x19, #12496]
	str x14, [x19, #2000]
	ldr x20, [x19, #1160]
	ldr x21, [x19, #1168]
	ldr x22, [x19, #1176]
	ldr x30, [x19, #1184]
	ldr x19, [x19, #1152]
	ret
	.p2align 6
