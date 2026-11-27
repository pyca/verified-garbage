// The functions of `src/internal/vg_ecdsa_p521_verify_digits.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p521_verify_digits:
	add x16, x0, x19
	ldrb w2, [x16, #4024]
	cbnz x2, 20f
	ldr x1, [x0, #1288]
	str x1, [x0, #1072]
	ldr x1, [x0, #1296]
	str x1, [x0, #1080]
	ldr x1, [x0, #1304]
	str x1, [x0, #1088]
	ldr x1, [x0, #1312]
	str x1, [x0, #1096]
	ldr x1, [x0, #1320]
	str x1, [x0, #1104]
	ldr x1, [x0, #1328]
	str x1, [x0, #1112]
	ldr x1, [x0, #1336]
	str x1, [x0, #1120]
	ldr x1, [x0, #1344]
	str x1, [x0, #1128]
	ldr x1, [x0, #1352]
	str x1, [x0, #1136]
	ldr x1, [x0, #1360]
	str x1, [x0, #1144]
	ldr x1, [x0, #1368]
	str x1, [x0, #1152]
	ldr x1, [x0, #1376]
	str x1, [x0, #1160]
	ldr x1, [x0, #1384]
	str x1, [x0, #1168]
	ldr x1, [x0, #1392]
	str x1, [x0, #1176]
	ldr x1, [x0, #1400]
	str x1, [x0, #1184]
	ldr x1, [x0, #1408]
	str x1, [x0, #1192]
	ldr x1, [x0, #1416]
	str x1, [x0, #1200]
	ldr x1, [x0, #1424]
	str x1, [x0, #1208]
	ldr x1, [x0, #1432]
	str x1, [x0, #1216]
	ldr x1, [x0, #1440]
	str x1, [x0, #1224]
	ldr x1, [x0, #1448]
	str x1, [x0, #1232]
	ldr x1, [x0, #1456]
	str x1, [x0, #1240]
	ldr x1, [x0, #1464]
	str x1, [x0, #1248]
	ldr x1, [x0, #1472]
	str x1, [x0, #1256]
	ldr x1, [x0, #1480]
	str x1, [x0, #1264]
	ldr x1, [x0, #1488]
	str x1, [x0, #1272]
	ldr x1, [x0, #1496]
	str x1, [x0, #1280]
	b 21f
20:
	lsr x3, x2, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	sub x2, x2, #1
	movz x17, #144, lsl #0
	mul x17, x2, x17
	add x16, x0, x17
	ldr x4, [x16, #6904]
	str x4, [x0, #1144]
	ldr x4, [x16, #6912]
	str x4, [x0, #1152]
	ldr x4, [x16, #6920]
	str x4, [x0, #1160]
	ldr x4, [x16, #6928]
	str x4, [x0, #1168]
	ldr x4, [x16, #6936]
	str x4, [x0, #1176]
	ldr x4, [x16, #6944]
	str x4, [x0, #1184]
	ldr x4, [x16, #6952]
	str x4, [x0, #1192]
	ldr x4, [x16, #6960]
	str x4, [x0, #1200]
	ldr x4, [x16, #6968]
	str x4, [x0, #1208]
	ldr x4, [x16, #6976]
	str x4, [x0, #1216]
	ldr x4, [x16, #6984]
	str x4, [x0, #1224]
	ldr x4, [x16, #6992]
	str x4, [x0, #1232]
	ldr x4, [x16, #7000]
	str x4, [x0, #1240]
	ldr x4, [x16, #7008]
	str x4, [x0, #1248]
	ldr x4, [x16, #7016]
	str x4, [x0, #1256]
	ldr x4, [x16, #7024]
	str x4, [x0, #1264]
	ldr x4, [x16, #7032]
	str x4, [x0, #1272]
	ldr x4, [x16, #7040]
	str x4, [x0, #1280]
	movz x17, #216, lsl #0
	mul x2, x2, x17
	add x16, x0, x2
	ldr x4, [x16, #5176]
	str x4, [x0, #1504]
	ldr x4, [x16, #5184]
	str x4, [x0, #1512]
	ldr x4, [x16, #5192]
	str x4, [x0, #1520]
	ldr x4, [x16, #5200]
	str x4, [x0, #1528]
	ldr x4, [x16, #5208]
	str x4, [x0, #1536]
	ldr x4, [x16, #5216]
	str x4, [x0, #1544]
	ldr x4, [x16, #5224]
	str x4, [x0, #1552]
	ldr x4, [x16, #5232]
	str x4, [x0, #1560]
	ldr x4, [x16, #5240]
	str x4, [x0, #1568]
	ldr x4, [x16, #5248]
	str x4, [x0, #1576]
	ldr x4, [x16, #5256]
	str x4, [x0, #1584]
	ldr x4, [x16, #5264]
	str x4, [x0, #1592]
	ldr x4, [x16, #5272]
	str x4, [x0, #1600]
	ldr x4, [x16, #5280]
	str x4, [x0, #1608]
	ldr x4, [x16, #5288]
	str x4, [x0, #1616]
	ldr x4, [x16, #5296]
	str x4, [x0, #1624]
	ldr x4, [x16, #5304]
	str x4, [x0, #1632]
	ldr x4, [x16, #5312]
	str x4, [x0, #1640]
	ldr x4, [x16, #5320]
	str x4, [x0, #1648]
	ldr x4, [x16, #5328]
	str x4, [x0, #1656]
	ldr x4, [x16, #5336]
	str x4, [x0, #1664]
	ldr x4, [x16, #5344]
	str x4, [x0, #1672]
	ldr x4, [x16, #5352]
	str x4, [x0, #1680]
	ldr x4, [x16, #5360]
	str x4, [x0, #1688]
	ldr x4, [x16, #5368]
	str x4, [x0, #1696]
	ldr x4, [x16, #5376]
	str x4, [x0, #1704]
	ldr x4, [x16, #5384]
	str x4, [x0, #1712]
	add x16, x0, x19
	ldrb w3, [x16, #4024]
	lsr x3, x3, #7
	cbnz x3, 22f
	b 23f
22:
	movz x7, #0, lsl #0
	ldr x8, [x0, #280]
	ldr x9, [x0, #288]
	ldr x10, [x0, #296]
	ldr x11, [x0, #304]
	ldr x12, [x0, #312]
	ldr x13, [x0, #320]
	ldr x14, [x0, #328]
	ldr x15, [x0, #336]
	ldr x21, [x0, #344]
	ldr x2, [x0, #1576]
	subs x8, x8, x2
	ldr x2, [x0, #1584]
	sbcs x9, x9, x2
	ldr x2, [x0, #1592]
	sbcs x10, x10, x2
	ldr x2, [x0, #1600]
	sbcs x11, x11, x2
	ldr x2, [x0, #1608]
	sbcs x12, x12, x2
	ldr x2, [x0, #1616]
	sbcs x13, x13, x2
	ldr x2, [x0, #1624]
	sbcs x14, x14, x2
	ldr x2, [x0, #1632]
	sbcs x15, x15, x2
	ldr x2, [x0, #1640]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1576]
	str x9, [x0, #1584]
	str x10, [x0, #1592]
	str x11, [x0, #1600]
	str x12, [x0, #1608]
	str x13, [x0, #1616]
	str x14, [x0, #1624]
	str x15, [x0, #1632]
	str x21, [x0, #1640]
23:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1432]
	ldr x2, [x0, #1440]
	orr x1, x1, x2
	ldr x2, [x0, #1448]
	orr x1, x1, x2
	ldr x2, [x0, #1456]
	orr x1, x1, x2
	ldr x2, [x0, #1464]
	orr x1, x1, x2
	ldr x2, [x0, #1472]
	orr x1, x1, x2
	ldr x2, [x0, #1480]
	orr x1, x1, x2
	ldr x2, [x0, #1488]
	orr x1, x1, x2
	ldr x2, [x0, #1496]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 24f
	movz x7, #0, lsl #0
	ldr x1, [x0, #1648]
	ldr x2, [x0, #1656]
	orr x1, x1, x2
	ldr x2, [x0, #1664]
	orr x1, x1, x2
	ldr x2, [x0, #1672]
	orr x1, x1, x2
	ldr x2, [x0, #1680]
	orr x1, x1, x2
	ldr x2, [x0, #1688]
	orr x1, x1, x2
	ldr x2, [x0, #1696]
	orr x1, x1, x2
	ldr x2, [x0, #1704]
	orr x1, x1, x2
	ldr x2, [x0, #1712]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 26f
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1288, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2008, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #1576, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x14, [x0, #2128]
	ldr x15, [x0, #2136]
	ldr x21, [x0, #2144]
	movz x7, #0, lsl #0
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #2080]
	str x9, [x0, #2088]
	str x10, [x0, #2096]
	str x11, [x0, #2104]
	str x12, [x0, #2112]
	str x13, [x0, #2120]
	str x14, [x0, #2128]
	str x15, [x0, #2136]
	str x21, [x0, #2144]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1936]
	ldr x2, [x0, #1944]
	orr x1, x1, x2
	ldr x2, [x0, #1952]
	orr x1, x1, x2
	ldr x2, [x0, #1960]
	orr x1, x1, x2
	ldr x2, [x0, #1968]
	orr x1, x1, x2
	ldr x2, [x0, #1976]
	orr x1, x1, x2
	ldr x2, [x0, #1984]
	orr x1, x1, x2
	ldr x2, [x0, #1992]
	orr x1, x1, x2
	ldr x2, [x0, #2000]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 28f
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1720, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #2080, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1144, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2008, lsl #0
	movz x2, #2008, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	b 29f
28:
	movz x7, #0, lsl #0
	ldr x1, [x0, #2080]
	ldr x2, [x0, #2088]
	orr x1, x1, x2
	ldr x2, [x0, #2096]
	orr x1, x1, x2
	ldr x2, [x0, #2104]
	orr x1, x1, x2
	ldr x2, [x0, #2112]
	orr x1, x1, x2
	ldr x2, [x0, #2120]
	orr x1, x1, x2
	ldr x2, [x0, #2128]
	orr x1, x1, x2
	ldr x2, [x0, #2136]
	orr x1, x1, x2
	ldr x2, [x0, #2144]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 210f
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1072]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1080]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1088]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1096]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1104]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1112]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1120]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1128]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1136]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #1144]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1152]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1160]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1168]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1176]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1184]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1192]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1200]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1208]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1216]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1224]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1248]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1256]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1280]
	b 211f
210:
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1288, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1720]
	subs x8, x8, x2
	ldr x2, [x0, #1728]
	sbcs x9, x9, x2
	ldr x2, [x0, #1736]
	sbcs x10, x10, x2
	ldr x2, [x0, #1744]
	sbcs x11, x11, x2
	ldr x2, [x0, #1752]
	sbcs x12, x12, x2
	ldr x2, [x0, #1760]
	sbcs x13, x13, x2
	ldr x2, [x0, #1768]
	sbcs x14, x14, x2
	ldr x2, [x0, #1776]
	sbcs x15, x15, x2
	ldr x2, [x0, #1784]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1720]
	adds x8, x8, x2
	ldr x2, [x0, #1728]
	adcs x9, x9, x2
	ldr x2, [x0, #1736]
	adcs x10, x10, x2
	ldr x2, [x0, #1744]
	adcs x11, x11, x2
	ldr x2, [x0, #1752]
	adcs x12, x12, x2
	ldr x2, [x0, #1760]
	adcs x13, x13, x2
	ldr x2, [x0, #1768]
	adcs x14, x14, x2
	ldr x2, [x0, #1776]
	adcs x15, x15, x2
	ldr x2, [x0, #1784]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1432, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x14, [x0, #1264]
	ldr x15, [x0, #1272]
	ldr x21, [x0, #1280]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1216]
	adds x8, x8, x2
	ldr x2, [x0, #1224]
	adcs x9, x9, x2
	ldr x2, [x0, #1232]
	adcs x10, x10, x2
	ldr x2, [x0, #1240]
	adcs x11, x11, x2
	ldr x2, [x0, #1248]
	adcs x12, x12, x2
	ldr x2, [x0, #1256]
	adcs x13, x13, x2
	ldr x2, [x0, #1264]
	adcs x14, x14, x2
	ldr x2, [x0, #1272]
	adcs x15, x15, x2
	ldr x2, [x0, #1280]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x14, [x0, #1264]
	str x15, [x0, #1272]
	str x21, [x0, #1280]
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	str x14, [x0, #1120]
	str x15, [x0, #1128]
	str x21, [x0, #1136]
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1072]
	subs x8, x8, x2
	ldr x2, [x0, #1080]
	sbcs x9, x9, x2
	ldr x2, [x0, #1088]
	sbcs x10, x10, x2
	ldr x2, [x0, #1096]
	sbcs x11, x11, x2
	ldr x2, [x0, #1104]
	sbcs x12, x12, x2
	ldr x2, [x0, #1112]
	sbcs x13, x13, x2
	ldr x2, [x0, #1120]
	sbcs x14, x14, x2
	ldr x2, [x0, #1128]
	sbcs x15, x15, x2
	ldr x2, [x0, #1136]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1144, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	ldr x8, [x0, #1144]
	ldr x9, [x0, #1152]
	ldr x10, [x0, #1160]
	ldr x11, [x0, #1168]
	ldr x12, [x0, #1176]
	ldr x13, [x0, #1184]
	ldr x14, [x0, #1192]
	ldr x15, [x0, #1200]
	ldr x21, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1144]
	str x9, [x0, #1152]
	str x10, [x0, #1160]
	str x11, [x0, #1168]
	str x12, [x0, #1176]
	str x13, [x0, #1184]
	str x14, [x0, #1192]
	str x15, [x0, #1200]
	str x21, [x0, #1208]
211:
29:
	b 27f
26:
	ldr x1, [x0, #1288]
	str x1, [x0, #1072]
	ldr x1, [x0, #1296]
	str x1, [x0, #1080]
	ldr x1, [x0, #1304]
	str x1, [x0, #1088]
	ldr x1, [x0, #1312]
	str x1, [x0, #1096]
	ldr x1, [x0, #1320]
	str x1, [x0, #1104]
	ldr x1, [x0, #1328]
	str x1, [x0, #1112]
	ldr x1, [x0, #1336]
	str x1, [x0, #1120]
	ldr x1, [x0, #1344]
	str x1, [x0, #1128]
	ldr x1, [x0, #1352]
	str x1, [x0, #1136]
	ldr x1, [x0, #1360]
	str x1, [x0, #1144]
	ldr x1, [x0, #1368]
	str x1, [x0, #1152]
	ldr x1, [x0, #1376]
	str x1, [x0, #1160]
	ldr x1, [x0, #1384]
	str x1, [x0, #1168]
	ldr x1, [x0, #1392]
	str x1, [x0, #1176]
	ldr x1, [x0, #1400]
	str x1, [x0, #1184]
	ldr x1, [x0, #1408]
	str x1, [x0, #1192]
	ldr x1, [x0, #1416]
	str x1, [x0, #1200]
	ldr x1, [x0, #1424]
	str x1, [x0, #1208]
	ldr x1, [x0, #1432]
	str x1, [x0, #1216]
	ldr x1, [x0, #1440]
	str x1, [x0, #1224]
	ldr x1, [x0, #1448]
	str x1, [x0, #1232]
	ldr x1, [x0, #1456]
	str x1, [x0, #1240]
	ldr x1, [x0, #1464]
	str x1, [x0, #1248]
	ldr x1, [x0, #1472]
	str x1, [x0, #1256]
	ldr x1, [x0, #1480]
	str x1, [x0, #1264]
	ldr x1, [x0, #1488]
	str x1, [x0, #1272]
	ldr x1, [x0, #1496]
	str x1, [x0, #1280]
27:
	b 25f
24:
	ldr x1, [x0, #1504]
	str x1, [x0, #1072]
	ldr x1, [x0, #1512]
	str x1, [x0, #1080]
	ldr x1, [x0, #1520]
	str x1, [x0, #1088]
	ldr x1, [x0, #1528]
	str x1, [x0, #1096]
	ldr x1, [x0, #1536]
	str x1, [x0, #1104]
	ldr x1, [x0, #1544]
	str x1, [x0, #1112]
	ldr x1, [x0, #1552]
	str x1, [x0, #1120]
	ldr x1, [x0, #1560]
	str x1, [x0, #1128]
	ldr x1, [x0, #1568]
	str x1, [x0, #1136]
	ldr x1, [x0, #1576]
	str x1, [x0, #1144]
	ldr x1, [x0, #1584]
	str x1, [x0, #1152]
	ldr x1, [x0, #1592]
	str x1, [x0, #1160]
	ldr x1, [x0, #1600]
	str x1, [x0, #1168]
	ldr x1, [x0, #1608]
	str x1, [x0, #1176]
	ldr x1, [x0, #1616]
	str x1, [x0, #1184]
	ldr x1, [x0, #1624]
	str x1, [x0, #1192]
	ldr x1, [x0, #1632]
	str x1, [x0, #1200]
	ldr x1, [x0, #1640]
	str x1, [x0, #1208]
	ldr x1, [x0, #1648]
	str x1, [x0, #1216]
	ldr x1, [x0, #1656]
	str x1, [x0, #1224]
	ldr x1, [x0, #1664]
	str x1, [x0, #1232]
	ldr x1, [x0, #1672]
	str x1, [x0, #1240]
	ldr x1, [x0, #1680]
	str x1, [x0, #1248]
	ldr x1, [x0, #1688]
	str x1, [x0, #1256]
	ldr x1, [x0, #1696]
	str x1, [x0, #1264]
	ldr x1, [x0, #1704]
	str x1, [x0, #1272]
	ldr x1, [x0, #1712]
	str x1, [x0, #1280]
25:
21:
	add x16, x0, x19
	ldrb w2, [x16, #3304]
	cbnz x2, 212f
	b 213f
212:
	lsr x3, x2, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	lsl x2, x2, #1
	sub x2, x2, #2
	movz x3, #144, lsl #0
	mul x2, x2, x3
	adrp x16, {VG_P521_COMB}
	add x16, x16, {VG_P521_COMB}
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #1504]
	ldr x4, [x16, #8]
	str x4, [x0, #1512]
	ldr x4, [x16, #16]
	str x4, [x0, #1520]
	ldr x4, [x16, #24]
	str x4, [x0, #1528]
	ldr x4, [x16, #32]
	str x4, [x0, #1536]
	ldr x4, [x16, #40]
	str x4, [x0, #1544]
	ldr x4, [x16, #48]
	str x4, [x0, #1552]
	ldr x4, [x16, #56]
	str x4, [x0, #1560]
	ldr x4, [x16, #64]
	str x4, [x0, #1568]
	ldr x4, [x16, #72]
	str x4, [x0, #1576]
	ldr x4, [x16, #80]
	str x4, [x0, #1584]
	ldr x4, [x16, #88]
	str x4, [x0, #1592]
	ldr x4, [x16, #96]
	str x4, [x0, #1600]
	ldr x4, [x16, #104]
	str x4, [x0, #1608]
	ldr x4, [x16, #112]
	str x4, [x0, #1616]
	ldr x4, [x16, #120]
	str x4, [x0, #1624]
	ldr x4, [x16, #128]
	str x4, [x0, #1632]
	ldr x4, [x16, #136]
	str x4, [x0, #1640]
	ldr x1, [x0, #424]
	str x1, [x0, #1648]
	ldr x1, [x0, #432]
	str x1, [x0, #1656]
	ldr x1, [x0, #440]
	str x1, [x0, #1664]
	ldr x1, [x0, #448]
	str x1, [x0, #1672]
	ldr x1, [x0, #456]
	str x1, [x0, #1680]
	ldr x1, [x0, #464]
	str x1, [x0, #1688]
	ldr x1, [x0, #472]
	str x1, [x0, #1696]
	ldr x1, [x0, #480]
	str x1, [x0, #1704]
	ldr x1, [x0, #488]
	str x1, [x0, #1712]
	add x16, x0, x19
	ldrb w3, [x16, #3304]
	lsr x3, x3, #7
	cbnz x3, 214f
	b 215f
214:
	movz x7, #0, lsl #0
	ldr x8, [x0, #280]
	ldr x9, [x0, #288]
	ldr x10, [x0, #296]
	ldr x11, [x0, #304]
	ldr x12, [x0, #312]
	ldr x13, [x0, #320]
	ldr x14, [x0, #328]
	ldr x15, [x0, #336]
	ldr x21, [x0, #344]
	ldr x2, [x0, #1576]
	subs x8, x8, x2
	ldr x2, [x0, #1584]
	sbcs x9, x9, x2
	ldr x2, [x0, #1592]
	sbcs x10, x10, x2
	ldr x2, [x0, #1600]
	sbcs x11, x11, x2
	ldr x2, [x0, #1608]
	sbcs x12, x12, x2
	ldr x2, [x0, #1616]
	sbcs x13, x13, x2
	ldr x2, [x0, #1624]
	sbcs x14, x14, x2
	ldr x2, [x0, #1632]
	sbcs x15, x15, x2
	ldr x2, [x0, #1640]
	sbcs x21, x21, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr x2, [x0, #112]
	and x2, x2, x17
	adcs x14, x14, x2
	ldr x2, [x0, #120]
	and x2, x2, x17
	adcs x15, x15, x2
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #1576]
	str x9, [x0, #1584]
	str x10, [x0, #1592]
	str x11, [x0, #1600]
	str x12, [x0, #1608]
	str x13, [x0, #1616]
	str x14, [x0, #1624]
	str x15, [x0, #1632]
	str x21, [x0, #1640]
215:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1216]
	ldr x2, [x0, #1224]
	orr x1, x1, x2
	ldr x2, [x0, #1232]
	orr x1, x1, x2
	ldr x2, [x0, #1240]
	orr x1, x1, x2
	ldr x2, [x0, #1248]
	orr x1, x1, x2
	ldr x2, [x0, #1256]
	orr x1, x1, x2
	ldr x2, [x0, #1264]
	orr x1, x1, x2
	ldr x2, [x0, #1272]
	orr x1, x1, x2
	ldr x2, [x0, #1280]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 216f
	ldr x1, [x0, #1072]
	str x1, [x0, #1864]
	ldr x1, [x0, #1080]
	str x1, [x0, #1872]
	ldr x1, [x0, #1088]
	str x1, [x0, #1880]
	ldr x1, [x0, #1096]
	str x1, [x0, #1888]
	ldr x1, [x0, #1104]
	str x1, [x0, #1896]
	ldr x1, [x0, #1112]
	str x1, [x0, #1904]
	ldr x1, [x0, #1120]
	str x1, [x0, #1912]
	ldr x1, [x0, #1128]
	str x1, [x0, #1920]
	ldr x1, [x0, #1136]
	str x1, [x0, #1928]
	ldr x1, [x0, #1144]
	str x1, [x0, #2008]
	ldr x1, [x0, #1152]
	str x1, [x0, #2016]
	ldr x1, [x0, #1160]
	str x1, [x0, #2024]
	ldr x1, [x0, #1168]
	str x1, [x0, #2032]
	ldr x1, [x0, #1176]
	str x1, [x0, #2040]
	ldr x1, [x0, #1184]
	str x1, [x0, #2048]
	ldr x1, [x0, #1192]
	str x1, [x0, #2056]
	ldr x1, [x0, #1200]
	str x1, [x0, #2064]
	ldr x1, [x0, #1208]
	str x1, [x0, #2072]
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #1576, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x14, [x0, #2128]
	ldr x15, [x0, #2136]
	ldr x21, [x0, #2144]
	movz x7, #0, lsl #0
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #2080]
	str x9, [x0, #2088]
	str x10, [x0, #2096]
	str x11, [x0, #2104]
	str x12, [x0, #2112]
	str x13, [x0, #2120]
	str x14, [x0, #2128]
	str x15, [x0, #2136]
	str x21, [x0, #2144]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1936]
	ldr x2, [x0, #1944]
	orr x1, x1, x2
	ldr x2, [x0, #1952]
	orr x1, x1, x2
	ldr x2, [x0, #1960]
	orr x1, x1, x2
	ldr x2, [x0, #1968]
	orr x1, x1, x2
	ldr x2, [x0, #1976]
	orr x1, x1, x2
	ldr x2, [x0, #1984]
	orr x1, x1, x2
	ldr x2, [x0, #1992]
	orr x1, x1, x2
	ldr x2, [x0, #2000]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 218f
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1720, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1864, lsl #0
	movz x3, #1720, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1288, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #2080, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1288]
	subs x8, x8, x2
	ldr x2, [x0, #1296]
	sbcs x9, x9, x2
	ldr x2, [x0, #1304]
	sbcs x10, x10, x2
	ldr x2, [x0, #1312]
	sbcs x11, x11, x2
	ldr x2, [x0, #1320]
	sbcs x12, x12, x2
	ldr x2, [x0, #1328]
	sbcs x13, x13, x2
	ldr x2, [x0, #1336]
	sbcs x14, x14, x2
	ldr x2, [x0, #1344]
	sbcs x15, x15, x2
	ldr x2, [x0, #1352]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2008, lsl #0
	movz x2, #2008, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1360]
	ldr x9, [x0, #1368]
	ldr x10, [x0, #1376]
	ldr x11, [x0, #1384]
	ldr x12, [x0, #1392]
	ldr x13, [x0, #1400]
	ldr x14, [x0, #1408]
	ldr x15, [x0, #1416]
	ldr x21, [x0, #1424]
	movz x7, #0, lsl #0
	ldr x2, [x0, #2008]
	subs x8, x8, x2
	ldr x2, [x0, #2016]
	sbcs x9, x9, x2
	ldr x2, [x0, #2024]
	sbcs x10, x10, x2
	ldr x2, [x0, #2032]
	sbcs x11, x11, x2
	ldr x2, [x0, #2040]
	sbcs x12, x12, x2
	ldr x2, [x0, #2048]
	sbcs x13, x13, x2
	ldr x2, [x0, #2056]
	sbcs x14, x14, x2
	ldr x2, [x0, #2064]
	sbcs x15, x15, x2
	ldr x2, [x0, #2072]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1432, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	b 219f
218:
	movz x7, #0, lsl #0
	ldr x1, [x0, #2080]
	ldr x2, [x0, #2088]
	orr x1, x1, x2
	ldr x2, [x0, #2096]
	orr x1, x1, x2
	ldr x2, [x0, #2104]
	orr x1, x1, x2
	ldr x2, [x0, #2112]
	orr x1, x1, x2
	ldr x2, [x0, #2120]
	orr x1, x1, x2
	ldr x2, [x0, #2128]
	orr x1, x1, x2
	ldr x2, [x0, #2136]
	orr x1, x1, x2
	ldr x2, [x0, #2144]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 220f
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1288]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1296]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1304]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1312]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1320]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1336]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1344]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1352]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #1360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1368]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1376]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1384]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1392]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1400]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1416]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1424]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1432]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1440]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1448]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1456]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1464]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1472]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1480]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1488]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1496]
	b 221f
220:
	mov v29.d[0], x30
	movz x1, #1720, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1144, lsl #0
	movz x3, #1144, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	mov v29.d[0], x30
	movz x1, #1864, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1720]
	subs x8, x8, x2
	ldr x2, [x0, #1728]
	sbcs x9, x9, x2
	ldr x2, [x0, #1736]
	sbcs x10, x10, x2
	ldr x2, [x0, #1744]
	sbcs x11, x11, x2
	ldr x2, [x0, #1752]
	sbcs x12, x12, x2
	ldr x2, [x0, #1760]
	sbcs x13, x13, x2
	ldr x2, [x0, #1768]
	sbcs x14, x14, x2
	ldr x2, [x0, #1776]
	sbcs x15, x15, x2
	ldr x2, [x0, #1784]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x14, [x0, #1120]
	ldr x15, [x0, #1128]
	ldr x21, [x0, #1136]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1720]
	adds x8, x8, x2
	ldr x2, [x0, #1728]
	adcs x9, x9, x2
	ldr x2, [x0, #1736]
	adcs x10, x10, x2
	ldr x2, [x0, #1744]
	adcs x11, x11, x2
	ldr x2, [x0, #1752]
	adcs x12, x12, x2
	ldr x2, [x0, #1760]
	adcs x13, x13, x2
	ldr x2, [x0, #1768]
	adcs x14, x14, x2
	ldr x2, [x0, #1776]
	adcs x15, x15, x2
	ldr x2, [x0, #1784]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1288, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1936]
	ldr x9, [x0, #1944]
	ldr x10, [x0, #1952]
	ldr x11, [x0, #1960]
	ldr x12, [x0, #1968]
	ldr x13, [x0, #1976]
	ldr x14, [x0, #1984]
	ldr x15, [x0, #1992]
	ldr x21, [x0, #2000]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1936]
	adds x8, x8, x2
	ldr x2, [x0, #1944]
	adcs x9, x9, x2
	ldr x2, [x0, #1952]
	adcs x10, x10, x2
	ldr x2, [x0, #1960]
	adcs x11, x11, x2
	ldr x2, [x0, #1968]
	adcs x12, x12, x2
	ldr x2, [x0, #1976]
	adcs x13, x13, x2
	ldr x2, [x0, #1984]
	adcs x14, x14, x2
	ldr x2, [x0, #1992]
	adcs x15, x15, x2
	ldr x2, [x0, #2000]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1936]
	str x9, [x0, #1944]
	str x10, [x0, #1952]
	str x11, [x0, #1960]
	str x12, [x0, #1968]
	str x13, [x0, #1976]
	str x14, [x0, #1984]
	str x15, [x0, #1992]
	str x21, [x0, #2000]
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	adds x8, x8, x2
	ldr x2, [x0, #1872]
	adcs x9, x9, x2
	ldr x2, [x0, #1880]
	adcs x10, x10, x2
	ldr x2, [x0, #1888]
	adcs x11, x11, x2
	ldr x2, [x0, #1896]
	adcs x12, x12, x2
	ldr x2, [x0, #1904]
	adcs x13, x13, x2
	ldr x2, [x0, #1912]
	adcs x14, x14, x2
	ldr x2, [x0, #1920]
	adcs x15, x15, x2
	ldr x2, [x0, #1928]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1864]
	str x9, [x0, #1872]
	str x10, [x0, #1880]
	str x11, [x0, #1888]
	str x12, [x0, #1896]
	str x13, [x0, #1904]
	str x14, [x0, #1912]
	str x15, [x0, #1920]
	str x21, [x0, #1928]
	mov v29.d[0], x30
	movz x1, #1432, lsl #0
	movz x2, #1144, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1432]
	ldr x9, [x0, #1440]
	ldr x10, [x0, #1448]
	ldr x11, [x0, #1456]
	ldr x12, [x0, #1464]
	ldr x13, [x0, #1472]
	ldr x14, [x0, #1480]
	ldr x15, [x0, #1488]
	ldr x21, [x0, #1496]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1432]
	adds x8, x8, x2
	ldr x2, [x0, #1440]
	adcs x9, x9, x2
	ldr x2, [x0, #1448]
	adcs x10, x10, x2
	ldr x2, [x0, #1456]
	adcs x11, x11, x2
	ldr x2, [x0, #1464]
	adcs x12, x12, x2
	ldr x2, [x0, #1472]
	adcs x13, x13, x2
	ldr x2, [x0, #1480]
	adcs x14, x14, x2
	ldr x2, [x0, #1488]
	adcs x15, x15, x2
	ldr x2, [x0, #1496]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1432]
	str x9, [x0, #1440]
	str x10, [x0, #1448]
	str x11, [x0, #1456]
	str x12, [x0, #1464]
	str x13, [x0, #1472]
	str x14, [x0, #1480]
	str x15, [x0, #1488]
	str x21, [x0, #1496]
	mov v29.d[0], x30
	movz x1, #1288, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	ldr x8, [x0, #1288]
	ldr x9, [x0, #1296]
	ldr x10, [x0, #1304]
	ldr x11, [x0, #1312]
	ldr x12, [x0, #1320]
	ldr x13, [x0, #1328]
	ldr x14, [x0, #1336]
	ldr x15, [x0, #1344]
	ldr x21, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1864]
	subs x8, x8, x2
	ldr x2, [x0, #1872]
	sbcs x9, x9, x2
	ldr x2, [x0, #1880]
	sbcs x10, x10, x2
	ldr x2, [x0, #1888]
	sbcs x11, x11, x2
	ldr x2, [x0, #1896]
	sbcs x12, x12, x2
	ldr x2, [x0, #1904]
	sbcs x13, x13, x2
	ldr x2, [x0, #1912]
	sbcs x14, x14, x2
	ldr x2, [x0, #1920]
	sbcs x15, x15, x2
	ldr x2, [x0, #1928]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1288]
	str x9, [x0, #1296]
	str x10, [x0, #1304]
	str x11, [x0, #1312]
	str x12, [x0, #1320]
	str x13, [x0, #1328]
	str x14, [x0, #1336]
	str x15, [x0, #1344]
	str x21, [x0, #1352]
	ldr x8, [x0, #1864]
	ldr x9, [x0, #1872]
	ldr x10, [x0, #1880]
	ldr x11, [x0, #1888]
	ldr x12, [x0, #1896]
	ldr x13, [x0, #1904]
	ldr x14, [x0, #1912]
	ldr x15, [x0, #1920]
	ldr x21, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1288]
	subs x8, x8, x2
	ldr x2, [x0, #1296]
	sbcs x9, x9, x2
	ldr x2, [x0, #1304]
	sbcs x10, x10, x2
	ldr x2, [x0, #1312]
	sbcs x11, x11, x2
	ldr x2, [x0, #1320]
	sbcs x12, x12, x2
	ldr x2, [x0, #1328]
	sbcs x13, x13, x2
	ldr x2, [x0, #1336]
	sbcs x14, x14, x2
	ldr x2, [x0, #1344]
	sbcs x15, x15, x2
	ldr x2, [x0, #1352]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p521_prod_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x21, [x0, #1856]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1792]
	adds x8, x8, x2
	ldr x2, [x0, #1800]
	adcs x9, x9, x2
	ldr x2, [x0, #1808]
	adcs x10, x10, x2
	ldr x2, [x0, #1816]
	adcs x11, x11, x2
	ldr x2, [x0, #1824]
	adcs x12, x12, x2
	ldr x2, [x0, #1832]
	adcs x13, x13, x2
	ldr x2, [x0, #1840]
	adcs x14, x14, x2
	ldr x2, [x0, #1848]
	adcs x15, x15, x2
	ldr x2, [x0, #1856]
	adcs x21, x21, x2
	movz x2, #1, lsl #0
	subs x1, x7, x2
	movz x2, #511, lsl #0
	subs x8, x8, x1
	sbcs x9, x9, x1
	sbcs x10, x10, x1
	sbcs x11, x11, x1
	sbcs x12, x12, x1
	sbcs x13, x13, x1
	sbcs x14, x14, x1
	sbcs x15, x15, x1
	sbcs x21, x21, x2
	sbcs x1, x7, x7
	and x2, x1, x2
	adds x8, x8, x1
	adcs x9, x9, x1
	adcs x10, x10, x1
	adcs x11, x11, x1
	adcs x12, x12, x1
	adcs x13, x13, x1
	adcs x14, x14, x1
	adcs x15, x15, x1
	adcs x21, x21, x2
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	str x21, [x0, #1856]
	ldr x8, [x0, #1360]
	ldr x9, [x0, #1368]
	ldr x10, [x0, #1376]
	ldr x11, [x0, #1384]
	ldr x12, [x0, #1392]
	ldr x13, [x0, #1400]
	ldr x14, [x0, #1408]
	ldr x15, [x0, #1416]
	ldr x21, [x0, #1424]
	movz x7, #0, lsl #0
	ldr x2, [x0, #1792]
	subs x8, x8, x2
	ldr x2, [x0, #1800]
	sbcs x9, x9, x2
	ldr x2, [x0, #1808]
	sbcs x10, x10, x2
	ldr x2, [x0, #1816]
	sbcs x11, x11, x2
	ldr x2, [x0, #1824]
	sbcs x12, x12, x2
	ldr x2, [x0, #1832]
	sbcs x13, x13, x2
	ldr x2, [x0, #1840]
	sbcs x14, x14, x2
	ldr x2, [x0, #1848]
	sbcs x15, x15, x2
	ldr x2, [x0, #1856]
	sbcs x21, x21, x2
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbcs x14, x14, x7
	sbcs x15, x15, x7
	sbcs x21, x21, x7
	movz x2, #511, lsl #0
	and x21, x21, x2
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	str x14, [x0, #1408]
	str x15, [x0, #1416]
	str x21, [x0, #1424]
221:
219:
	b 217f
216:
	ldr x1, [x0, #1504]
	str x1, [x0, #1288]
	ldr x1, [x0, #1512]
	str x1, [x0, #1296]
	ldr x1, [x0, #1520]
	str x1, [x0, #1304]
	ldr x1, [x0, #1528]
	str x1, [x0, #1312]
	ldr x1, [x0, #1536]
	str x1, [x0, #1320]
	ldr x1, [x0, #1544]
	str x1, [x0, #1328]
	ldr x1, [x0, #1552]
	str x1, [x0, #1336]
	ldr x1, [x0, #1560]
	str x1, [x0, #1344]
	ldr x1, [x0, #1568]
	str x1, [x0, #1352]
	ldr x1, [x0, #1576]
	str x1, [x0, #1360]
	ldr x1, [x0, #1584]
	str x1, [x0, #1368]
	ldr x1, [x0, #1592]
	str x1, [x0, #1376]
	ldr x1, [x0, #1600]
	str x1, [x0, #1384]
	ldr x1, [x0, #1608]
	str x1, [x0, #1392]
	ldr x1, [x0, #1616]
	str x1, [x0, #1400]
	ldr x1, [x0, #1624]
	str x1, [x0, #1408]
	ldr x1, [x0, #1632]
	str x1, [x0, #1416]
	ldr x1, [x0, #1640]
	str x1, [x0, #1424]
	ldr x1, [x0, #1648]
	str x1, [x0, #1432]
	ldr x1, [x0, #1656]
	str x1, [x0, #1440]
	ldr x1, [x0, #1664]
	str x1, [x0, #1448]
	ldr x1, [x0, #1672]
	str x1, [x0, #1456]
	ldr x1, [x0, #1680]
	str x1, [x0, #1464]
	ldr x1, [x0, #1688]
	str x1, [x0, #1472]
	ldr x1, [x0, #1696]
	str x1, [x0, #1480]
	ldr x1, [x0, #1704]
	str x1, [x0, #1488]
	ldr x1, [x0, #1712]
	str x1, [x0, #1496]
217:
	ldr x1, [x0, #1288]
	str x1, [x0, #1072]
	ldr x1, [x0, #1296]
	str x1, [x0, #1080]
	ldr x1, [x0, #1304]
	str x1, [x0, #1088]
	ldr x1, [x0, #1312]
	str x1, [x0, #1096]
	ldr x1, [x0, #1320]
	str x1, [x0, #1104]
	ldr x1, [x0, #1328]
	str x1, [x0, #1112]
	ldr x1, [x0, #1336]
	str x1, [x0, #1120]
	ldr x1, [x0, #1344]
	str x1, [x0, #1128]
	ldr x1, [x0, #1352]
	str x1, [x0, #1136]
	ldr x1, [x0, #1360]
	str x1, [x0, #1144]
	ldr x1, [x0, #1368]
	str x1, [x0, #1152]
	ldr x1, [x0, #1376]
	str x1, [x0, #1160]
	ldr x1, [x0, #1384]
	str x1, [x0, #1168]
	ldr x1, [x0, #1392]
	str x1, [x0, #1176]
	ldr x1, [x0, #1400]
	str x1, [x0, #1184]
	ldr x1, [x0, #1408]
	str x1, [x0, #1192]
	ldr x1, [x0, #1416]
	str x1, [x0, #1200]
	ldr x1, [x0, #1424]
	str x1, [x0, #1208]
	ldr x1, [x0, #1432]
	str x1, [x0, #1216]
	ldr x1, [x0, #1440]
	str x1, [x0, #1224]
	ldr x1, [x0, #1448]
	str x1, [x0, #1232]
	ldr x1, [x0, #1456]
	str x1, [x0, #1240]
	ldr x1, [x0, #1464]
	str x1, [x0, #1248]
	ldr x1, [x0, #1472]
	str x1, [x0, #1256]
	ldr x1, [x0, #1480]
	str x1, [x0, #1264]
	ldr x1, [x0, #1488]
	str x1, [x0, #1272]
	ldr x1, [x0, #1496]
	str x1, [x0, #1280]
213:
	ret
	.p2align 6
