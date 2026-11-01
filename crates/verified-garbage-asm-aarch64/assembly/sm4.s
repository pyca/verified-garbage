// The functions of `src/sm4.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_expand_key:
	sub sp, sp, #3168
	add x2, sp, #0
	add x5, x2, #0
	str x19, [x5, #3072]
	str x20, [x5, #3080]
	str x21, [x5, #3088]
	str x22, [x5, #3096]
	str x23, [x5, #3104]
	str x24, [x5, #3112]
	str x25, [x5, #3120]
	str x26, [x5, #3128]
	str x27, [x5, #3136]
	str x28, [x5, #3144]
	movz x21, #255, lsl #0
	movk x21, #255, lsl #16
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x5, #384]
	movz x21, #65280, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x5, #392]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #400]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1024]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1032]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1040]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #1048]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #1056]
	movz x21, #0, lsl #0
	str x21, [x5, #1064]
	movz x21, #0, lsl #0
	str x21, [x5, #1072]
	movz x21, #0, lsl #0
	str x21, [x5, #1080]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1088]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1096]
	movz x21, #65535, lsl #0
	str x21, [x5, #1104]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #1112]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #1120]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1128]
	movz x21, #0, lsl #0
	str x21, [x5, #1136]
	movz x21, #0, lsl #0
	str x21, [x5, #1144]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1152]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1160]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1168]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1176]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #1184]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #1192]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1200]
	movz x21, #0, lsl #0
	str x21, [x5, #1208]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1216]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1224]
	movz x21, #65535, lsl #0
	str x21, [x5, #1232]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1240]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #1248]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1256]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1264]
	movz x21, #0, lsl #0
	str x21, [x5, #1272]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1280]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1288]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1296]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #1304]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1312]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1320]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1328]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #1336]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1344]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1352]
	movz x21, #65535, lsl #0
	str x21, [x5, #1360]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #1368]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1376]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #1384]
	movz x21, #0, lsl #0
	str x21, [x5, #1392]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1400]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1408]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1416]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1424]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1432]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1440]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1448]
	movz x21, #0, lsl #0
	str x21, [x5, #1456]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1464]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1472]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1480]
	movz x21, #65535, lsl #0
	str x21, [x5, #1488]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1496]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1504]
	movz x21, #0, lsl #0
	str x21, [x5, #1512]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1520]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1528]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1536]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1544]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1552]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #1560]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #1568]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1576]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1584]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1592]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1600]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1608]
	movz x21, #65535, lsl #0
	str x21, [x5, #1616]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #1624]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #1632]
	movz x21, #65535, lsl #0
	str x21, [x5, #1640]
	movz x21, #65535, lsl #0
	str x21, [x5, #1648]
	movz x21, #65535, lsl #0
	str x21, [x5, #1656]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1664]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1672]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1680]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1688]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #1696]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1704]
	movz x21, #0, lsl #0
	str x21, [x5, #1712]
	movz x21, #0, lsl #0
	str x21, [x5, #1720]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1728]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1736]
	movz x21, #65535, lsl #0
	str x21, [x5, #1744]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1752]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #1760]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #1768]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1776]
	movz x21, #0, lsl #0
	str x21, [x5, #1784]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1792]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1800]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1808]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #1816]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1824]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #1832]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1840]
	movz x21, #0, lsl #0
	str x21, [x5, #1848]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1856]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1864]
	movz x21, #65535, lsl #0
	str x21, [x5, #1872]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #1880]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1888]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1896]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1904]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #1912]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1920]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1928]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1936]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1944]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1952]
	movz x21, #0, lsl #0
	str x21, [x5, #1960]
	movz x21, #0, lsl #0
	str x21, [x5, #1968]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #1976]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #1984]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #1992]
	movz x21, #65535, lsl #0
	str x21, [x5, #2000]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2008]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2016]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2024]
	movz x21, #0, lsl #0
	str x21, [x5, #2032]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2040]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2048]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2056]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2064]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #2072]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #2080]
	movz x21, #0, lsl #0
	str x21, [x5, #2088]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2096]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2104]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2112]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2120]
	movz x21, #65535, lsl #0
	str x21, [x5, #2128]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #2136]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #2144]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2152]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2160]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2168]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2176]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2184]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2192]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2200]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2208]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2216]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2224]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2232]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2240]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2248]
	movz x21, #65535, lsl #0
	str x21, [x5, #2256]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2264]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2272]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2280]
	movz x21, #0, lsl #0
	str x21, [x5, #2288]
	movz x21, #0, lsl #0
	str x21, [x5, #2296]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2304]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2312]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2320]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #2328]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2336]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2344]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #2352]
	movz x21, #0, lsl #0
	str x21, [x5, #2360]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2368]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2376]
	movz x21, #65535, lsl #0
	str x21, [x5, #2384]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #2392]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2400]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #2408]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2416]
	movz x21, #0, lsl #0
	str x21, [x5, #2424]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2432]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2440]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2448]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2456]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2464]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2472]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2480]
	movz x21, #0, lsl #0
	str x21, [x5, #2488]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2496]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2504]
	movz x21, #65535, lsl #0
	str x21, [x5, #2512]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2520]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2528]
	movz x21, #0, lsl #0
	str x21, [x5, #2536]
	movz x21, #0, lsl #0
	str x21, [x5, #2544]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2552]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2560]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2568]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2576]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #2584]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #2592]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2600]
	movz x21, #0, lsl #0
	str x21, [x5, #2608]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2616]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2624]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2632]
	movz x21, #65535, lsl #0
	str x21, [x5, #2640]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #2648]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #2656]
	movz x21, #65535, lsl #0
	str x21, [x5, #2664]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2672]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2680]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2688]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2696]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2704]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2712]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2720]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2728]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2736]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2744]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2752]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2760]
	movz x21, #65535, lsl #0
	str x21, [x5, #2768]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2776]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2784]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2792]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2800]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	str x21, [x5, #2808]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2816]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2824]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2832]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #2840]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2848]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #2856]
	movz x21, #0, lsl #0
	str x21, [x5, #2864]
	movz x21, #0, lsl #0
	str x21, [x5, #2872]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2880]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2888]
	movz x21, #65535, lsl #0
	str x21, [x5, #2896]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #32
	str x21, [x5, #2904]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2912]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2920]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #48
	str x21, [x5, #2928]
	movz x21, #0, lsl #0
	str x21, [x5, #2936]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2944]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #2952]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2960]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #2968]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2976]
	movz x21, #0, lsl #0
	str x21, [x5, #2984]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #2992]
	movz x21, #0, lsl #0
	str x21, [x5, #3000]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #3008]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	str x21, [x5, #3016]
	movz x21, #65535, lsl #0
	str x21, [x5, #3024]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #48
	str x21, [x5, #3032]
	movz x21, #0, lsl #0
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #3040]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #3048]
	movz x21, #65535, lsl #0
	movk x21, #65535, lsl #16
	movk x21, #65535, lsl #32
	movk x21, #65535, lsl #48
	str x21, [x5, #3056]
	movz x21, #0, lsl #0
	str x21, [x5, #3064]
	ldr x21, [x0, #0]
	movz x22, #45475, lsl #0
	movk x22, #50874, lsl #16
	movk x22, #43606, lsl #32
	movk x22, #20531, lsl #48
	eor x21, x21, x22
	str x21, [x5, #768]
	str x21, [x5, #784]
	str x21, [x5, #800]
	str x21, [x5, #816]
	str x21, [x5, #832]
	str x21, [x5, #848]
	str x21, [x5, #864]
	str x21, [x5, #880]
	str x21, [x5, #896]
	str x21, [x5, #912]
	str x21, [x5, #928]
	str x21, [x5, #944]
	str x21, [x5, #960]
	str x21, [x5, #976]
	str x21, [x5, #992]
	str x21, [x5, #1008]
	ldr x21, [x0, #8]
	movz x22, #32103, lsl #0
	movk x22, #38801, lsl #16
	movk x22, #28850, lsl #32
	movk x22, #56354, lsl #48
	eor x21, x21, x22
	str x21, [x5, #776]
	str x21, [x5, #792]
	str x21, [x5, #808]
	str x21, [x5, #824]
	str x21, [x5, #840]
	str x21, [x5, #856]
	str x21, [x5, #872]
	str x21, [x5, #888]
	str x21, [x5, #904]
	str x21, [x5, #920]
	str x21, [x5, #936]
	str x21, [x5, #952]
	str x21, [x5, #968]
	str x21, [x5, #984]
	str x21, [x5, #1000]
	str x21, [x5, #1016]
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	ldr x6, [x5, #768]
	ldr x10, [x5, #896]
	ldr x7, [x5, #784]
	ldr x11, [x5, #912]
	ldr x8, [x5, #800]
	ldr x12, [x5, #928]
	ldr x9, [x5, #816]
	ldr x13, [x5, #944]
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
	str x6, [x5, #768]
	str x10, [x5, #896]
	str x7, [x5, #784]
	str x11, [x5, #912]
	str x8, [x5, #800]
	str x12, [x5, #928]
	str x9, [x5, #816]
	str x13, [x5, #944]
	ldr x6, [x5, #832]
	ldr x10, [x5, #960]
	ldr x7, [x5, #848]
	ldr x11, [x5, #976]
	ldr x8, [x5, #864]
	ldr x12, [x5, #992]
	ldr x9, [x5, #880]
	ldr x13, [x5, #1008]
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
	str x6, [x5, #832]
	str x10, [x5, #960]
	str x7, [x5, #848]
	str x11, [x5, #976]
	str x8, [x5, #864]
	str x12, [x5, #992]
	str x9, [x5, #880]
	str x13, [x5, #1008]
	ldr x6, [x5, #776]
	ldr x10, [x5, #904]
	ldr x7, [x5, #792]
	ldr x11, [x5, #920]
	ldr x8, [x5, #808]
	ldr x12, [x5, #936]
	ldr x9, [x5, #824]
	ldr x13, [x5, #952]
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
	str x6, [x5, #776]
	str x10, [x5, #904]
	str x7, [x5, #792]
	str x11, [x5, #920]
	str x8, [x5, #808]
	str x12, [x5, #936]
	str x9, [x5, #824]
	str x13, [x5, #952]
	ldr x6, [x5, #840]
	ldr x10, [x5, #968]
	ldr x7, [x5, #856]
	ldr x11, [x5, #984]
	ldr x8, [x5, #872]
	ldr x12, [x5, #1000]
	ldr x9, [x5, #888]
	ldr x13, [x5, #1016]
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
	str x6, [x5, #840]
	str x10, [x5, #968]
	str x7, [x5, #856]
	str x11, [x5, #984]
	str x8, [x5, #872]
	str x12, [x5, #1000]
	str x9, [x5, #888]
	str x13, [x5, #1016]
	ldr x6, [x5, #768]
	ldr x7, [x5, #784]
	ldr x8, [x5, #800]
	ldr x9, [x5, #816]
	ldr x10, [x5, #832]
	ldr x11, [x5, #848]
	ldr x12, [x5, #864]
	ldr x13, [x5, #880]
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	ldr x6, [x5, #896]
	ldr x7, [x5, #912]
	ldr x8, [x5, #928]
	ldr x9, [x5, #944]
	ldr x10, [x5, #960]
	ldr x11, [x5, #976]
	ldr x12, [x5, #992]
	ldr x13, [x5, #1008]
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #776]
	ldr x7, [x5, #792]
	ldr x8, [x5, #808]
	ldr x9, [x5, #824]
	ldr x10, [x5, #840]
	ldr x11, [x5, #856]
	ldr x12, [x5, #872]
	ldr x13, [x5, #888]
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #640]
	str x7, [x5, #648]
	str x8, [x5, #656]
	str x9, [x5, #664]
	str x10, [x5, #672]
	str x11, [x5, #680]
	str x12, [x5, #688]
	str x13, [x5, #696]
	ldr x6, [x5, #904]
	ldr x7, [x5, #920]
	ldr x8, [x5, #936]
	ldr x9, [x5, #952]
	ldr x10, [x5, #968]
	ldr x11, [x5, #984]
	ldr x12, [x5, #1000]
	ldr x13, [x5, #1016]
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #704]
	str x7, [x5, #712]
	str x8, [x5, #720]
	str x9, [x5, #728]
	str x10, [x5, #736]
	str x11, [x5, #744]
	str x12, [x5, #752]
	str x13, [x5, #760]
	add x3, x5, #0
	add x3, x3, #3072
	add x4, x5, #0
	add x4, x4, #1024
20:
	ldr x6, [x5, #576]
	ldr x21, [x5, #640]
	eor x6, x6, x21
	ldr x21, [x5, #704]
	eor x6, x6, x21
	ldr x21, [x4, #0]
	eor x6, x6, x21
	ldr x7, [x5, #584]
	ldr x21, [x5, #648]
	eor x7, x7, x21
	ldr x21, [x5, #712]
	eor x7, x7, x21
	ldr x21, [x4, #8]
	eor x7, x7, x21
	ldr x8, [x5, #592]
	ldr x21, [x5, #656]
	eor x8, x8, x21
	ldr x21, [x5, #720]
	eor x8, x8, x21
	ldr x21, [x4, #16]
	eor x8, x8, x21
	ldr x9, [x5, #600]
	ldr x21, [x5, #664]
	eor x9, x9, x21
	ldr x21, [x5, #728]
	eor x9, x9, x21
	ldr x21, [x4, #24]
	eor x9, x9, x21
	ldr x10, [x5, #608]
	ldr x21, [x5, #672]
	eor x10, x10, x21
	ldr x21, [x5, #736]
	eor x10, x10, x21
	ldr x21, [x4, #32]
	eor x10, x10, x21
	ldr x11, [x5, #616]
	ldr x21, [x5, #680]
	eor x11, x11, x21
	ldr x21, [x5, #744]
	eor x11, x11, x21
	ldr x21, [x4, #40]
	eor x11, x11, x21
	ldr x12, [x5, #624]
	ldr x21, [x5, #688]
	eor x12, x12, x21
	ldr x21, [x5, #752]
	eor x12, x12, x21
	ldr x21, [x4, #48]
	eor x12, x12, x21
	ldr x13, [x5, #632]
	ldr x21, [x5, #696]
	eor x13, x13, x21
	ldr x21, [x5, #760]
	eor x13, x13, x21
	ldr x21, [x4, #56]
	eor x13, x13, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x9, x6
	eor x16, x7, x15
	eor x17, x13, x14
	eor x19, x11, x16
	eor x20, x12, x8
	eor x10, x13, x10
	eor x21, x11, x17
	eor x22, x12, x21
	eor x23, x13, x9
	eor x24, x12, x10
	eor x25, x11, x14
	eor x21, x7, x21
	eor x21, x21, x28
	eor x26, x15, x17
	eor x27, x6, x24
	eor x24, x19, x24
	str x24, [x5, #0]
	eor x24, x7, x20
	eor x12, x12, x26
	eor x6, x6, x17
	eor x6, x6, x28
	eor x26, x7, x23
	eor x9, x9, x25
	eor x9, x9, x28
	eor x10, x16, x10
	str x17, [x5, #8]
	eor x17, x14, x19
	str x17, [x5, #16]
	eor x17, x19, x20
	eor x8, x13, x8
	eor x8, x8, x28
	eor x27, x7, x27
	eor x27, x27, x28
	eor x15, x15, x25
	eor x11, x11, x23
	eor x11, x11, x28
	eor x23, x7, x22
	eor x14, x14, x16
	eor x14, x14, x28
	eor x13, x13, x16
	eor x13, x13, x28
	and x16, x23, x21
	and x25, x19, x9
	eor x25, x25, x16
	str x19, [x5, #24]
	and x19, x12, x26
	eor x19, x19, x16
	and x16, x7, x15
	str x7, [x5, #32]
	and x7, x20, x11
	eor x7, x7, x16
	str x20, [x5, #40]
	and x20, x24, x6
	eor x20, x20, x16
	and x16, x10, x14
	str x10, [x5, #48]
	and x10, x22, x13
	eor x10, x10, x16
	str x22, [x5, #56]
	ldr x22, [x5, #8]
	str x24, [x5, #64]
	and x24, x17, x22
	eor x24, x24, x16
	eor x25, x25, x10
	eor x19, x19, x24
	eor x7, x7, x10
	eor x20, x20, x24
	eor x25, x25, x8
	ldr x8, [x5, #0]
	eor x19, x19, x8
	ldr x8, [x5, #16]
	eor x7, x7, x8
	eor x20, x20, x27
	eor x27, x25, x19
	and x25, x25, x7
	eor x8, x20, x25
	and x24, x27, x8
	eor x24, x24, x19
	eor x10, x7, x20
	eor x19, x19, x25
	and x19, x19, x10
	eor x19, x19, x20
	eor x7, x7, x19
	eor x10, x8, x19
	and x20, x20, x10
	eor x7, x20, x7
	eor x8, x8, x20
	and x8, x24, x8
	eor x27, x27, x8
	eor x8, x27, x7
	eor x20, x24, x19
	eor x10, x24, x27
	eor x25, x19, x7
	eor x16, x20, x8
	and x21, x25, x21
	and x9, x7, x9
	and x26, x19, x26
	and x15, x10, x15
	and x11, x27, x11
	and x6, x24, x6
	and x14, x20, x14
	and x13, x16, x13
	and x22, x8, x22
	and x25, x25, x23
	ldr x23, [x5, #24]
	and x7, x7, x23
	and x19, x19, x12
	ldr x12, [x5, #32]
	and x10, x10, x12
	ldr x12, [x5, #40]
	and x27, x27, x12
	ldr x12, [x5, #64]
	and x24, x24, x12
	ldr x12, [x5, #48]
	and x20, x20, x12
	ldr x12, [x5, #56]
	and x16, x16, x12
	and x8, x8, x17
	eor x25, x25, x20
	eor x14, x14, x7
	eor x6, x21, x6
	eor x17, x27, x14
	eor x24, x24, x17
	eor x22, x9, x22
	eor x17, x13, x24
	eor x8, x8, x25
	eor x12, x11, x6
	eor x23, x17, x8
	str x11, [x5, #56]
	eor x11, x19, x12
	str x23, [x5, #48]
	eor x23, x16, x22
	eor x25, x25, x23
	eor x6, x15, x6
	eor x6, x25, x6
	eor x19, x19, x8
	eor x27, x27, x16
	eor x10, x10, x20
	eor x14, x14, x12
	eor x22, x22, x11
	eor x24, x24, x22
	eor x24, x24, x28
	eor x7, x7, x6
	eor x26, x26, x17
	eor x6, x13, x7
	eor x6, x6, x28
	eor x13, x27, x10
	eor x13, x13, x28
	eor x21, x21, x9
	ldr x9, [x5, #48]
	eor x15, x15, x9
	eor x9, x9, x21
	eor x12, x11, x26
	eor x12, x12, x28
	ldr x26, [x5, #56]
	eor x8, x26, x15
	eor x10, x25, x14
	eor x10, x10, x28
	add x11, x9, #0
	add x9, x19, #0
	add x7, x24, #0
	ror x21, x9, #32
	eor x21, x21, x6
	ror x22, x7, #48
	eor x21, x21, x22
	ldr x22, [x5, #512]
	eor x21, x21, x22
	str x21, [x5, #512]
	ror x21, x10, #32
	eor x21, x21, x7
	ror x22, x8, #48
	eor x21, x21, x22
	ldr x22, [x5, #520]
	eor x21, x21, x22
	str x21, [x5, #520]
	ror x21, x11, #32
	eor x21, x21, x8
	ror x22, x9, #48
	eor x21, x21, x22
	ldr x22, [x5, #528]
	eor x21, x21, x22
	str x21, [x5, #528]
	ror x21, x12, #32
	eor x21, x21, x9
	ror x22, x10, #48
	eor x21, x21, x22
	ldr x22, [x5, #536]
	eor x21, x21, x22
	str x21, [x5, #536]
	ror x21, x13, #32
	eor x21, x21, x10
	ror x22, x11, #48
	eor x21, x21, x22
	ldr x22, [x5, #544]
	eor x21, x21, x22
	str x21, [x5, #544]
	ror x21, x6, #16
	eor x21, x21, x11
	ror x22, x12, #48
	eor x21, x21, x22
	ldr x22, [x5, #552]
	eor x21, x21, x22
	str x21, [x5, #552]
	ror x21, x7, #16
	eor x21, x21, x12
	ror x22, x13, #48
	eor x21, x21, x22
	ldr x22, [x5, #560]
	eor x21, x21, x22
	str x21, [x5, #560]
	ror x21, x8, #16
	eor x21, x21, x13
	ror x22, x6, #32
	eor x21, x21, x22
	ldr x22, [x5, #568]
	eor x21, x21, x22
	str x21, [x5, #568]
	ldr x6, [x5, #640]
	ldr x21, [x5, #704]
	eor x6, x6, x21
	ldr x21, [x5, #512]
	eor x6, x6, x21
	ldr x21, [x4, #64]
	eor x6, x6, x21
	ldr x7, [x5, #648]
	ldr x21, [x5, #712]
	eor x7, x7, x21
	ldr x21, [x5, #520]
	eor x7, x7, x21
	ldr x21, [x4, #72]
	eor x7, x7, x21
	ldr x8, [x5, #656]
	ldr x21, [x5, #720]
	eor x8, x8, x21
	ldr x21, [x5, #528]
	eor x8, x8, x21
	ldr x21, [x4, #80]
	eor x8, x8, x21
	ldr x9, [x5, #664]
	ldr x21, [x5, #728]
	eor x9, x9, x21
	ldr x21, [x5, #536]
	eor x9, x9, x21
	ldr x21, [x4, #88]
	eor x9, x9, x21
	ldr x10, [x5, #672]
	ldr x21, [x5, #736]
	eor x10, x10, x21
	ldr x21, [x5, #544]
	eor x10, x10, x21
	ldr x21, [x4, #96]
	eor x10, x10, x21
	ldr x11, [x5, #680]
	ldr x21, [x5, #744]
	eor x11, x11, x21
	ldr x21, [x5, #552]
	eor x11, x11, x21
	ldr x21, [x4, #104]
	eor x11, x11, x21
	ldr x12, [x5, #688]
	ldr x21, [x5, #752]
	eor x12, x12, x21
	ldr x21, [x5, #560]
	eor x12, x12, x21
	ldr x21, [x4, #112]
	eor x12, x12, x21
	ldr x13, [x5, #696]
	ldr x21, [x5, #760]
	eor x13, x13, x21
	ldr x21, [x5, #568]
	eor x13, x13, x21
	ldr x21, [x4, #120]
	eor x13, x13, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x9, x6
	eor x16, x7, x15
	eor x17, x13, x14
	eor x19, x11, x16
	eor x20, x12, x8
	eor x10, x13, x10
	eor x21, x11, x17
	eor x22, x12, x21
	eor x23, x13, x9
	eor x24, x12, x10
	eor x25, x11, x14
	eor x21, x7, x21
	eor x21, x21, x28
	eor x26, x15, x17
	eor x27, x6, x24
	eor x24, x19, x24
	str x24, [x5, #0]
	eor x24, x7, x20
	eor x12, x12, x26
	eor x6, x6, x17
	eor x6, x6, x28
	eor x26, x7, x23
	eor x9, x9, x25
	eor x9, x9, x28
	eor x10, x16, x10
	str x17, [x5, #8]
	eor x17, x14, x19
	str x17, [x5, #16]
	eor x17, x19, x20
	eor x8, x13, x8
	eor x8, x8, x28
	eor x27, x7, x27
	eor x27, x27, x28
	eor x15, x15, x25
	eor x11, x11, x23
	eor x11, x11, x28
	eor x23, x7, x22
	eor x14, x14, x16
	eor x14, x14, x28
	eor x13, x13, x16
	eor x13, x13, x28
	and x16, x23, x21
	and x25, x19, x9
	eor x25, x25, x16
	str x19, [x5, #24]
	and x19, x12, x26
	eor x19, x19, x16
	and x16, x7, x15
	str x7, [x5, #32]
	and x7, x20, x11
	eor x7, x7, x16
	str x20, [x5, #40]
	and x20, x24, x6
	eor x20, x20, x16
	and x16, x10, x14
	str x10, [x5, #48]
	and x10, x22, x13
	eor x10, x10, x16
	str x22, [x5, #56]
	ldr x22, [x5, #8]
	str x24, [x5, #64]
	and x24, x17, x22
	eor x24, x24, x16
	eor x25, x25, x10
	eor x19, x19, x24
	eor x7, x7, x10
	eor x20, x20, x24
	eor x25, x25, x8
	ldr x8, [x5, #0]
	eor x19, x19, x8
	ldr x8, [x5, #16]
	eor x7, x7, x8
	eor x20, x20, x27
	eor x27, x25, x19
	and x25, x25, x7
	eor x8, x20, x25
	and x24, x27, x8
	eor x24, x24, x19
	eor x10, x7, x20
	eor x19, x19, x25
	and x19, x19, x10
	eor x19, x19, x20
	eor x7, x7, x19
	eor x10, x8, x19
	and x20, x20, x10
	eor x7, x20, x7
	eor x8, x8, x20
	and x8, x24, x8
	eor x27, x27, x8
	eor x8, x27, x7
	eor x20, x24, x19
	eor x10, x24, x27
	eor x25, x19, x7
	eor x16, x20, x8
	and x21, x25, x21
	and x9, x7, x9
	and x26, x19, x26
	and x15, x10, x15
	and x11, x27, x11
	and x6, x24, x6
	and x14, x20, x14
	and x13, x16, x13
	and x22, x8, x22
	and x25, x25, x23
	ldr x23, [x5, #24]
	and x7, x7, x23
	and x19, x19, x12
	ldr x12, [x5, #32]
	and x10, x10, x12
	ldr x12, [x5, #40]
	and x27, x27, x12
	ldr x12, [x5, #64]
	and x24, x24, x12
	ldr x12, [x5, #48]
	and x20, x20, x12
	ldr x12, [x5, #56]
	and x16, x16, x12
	and x8, x8, x17
	eor x25, x25, x20
	eor x14, x14, x7
	eor x6, x21, x6
	eor x17, x27, x14
	eor x24, x24, x17
	eor x22, x9, x22
	eor x17, x13, x24
	eor x8, x8, x25
	eor x12, x11, x6
	eor x23, x17, x8
	str x11, [x5, #56]
	eor x11, x19, x12
	str x23, [x5, #48]
	eor x23, x16, x22
	eor x25, x25, x23
	eor x6, x15, x6
	eor x6, x25, x6
	eor x19, x19, x8
	eor x27, x27, x16
	eor x10, x10, x20
	eor x14, x14, x12
	eor x22, x22, x11
	eor x24, x24, x22
	eor x24, x24, x28
	eor x7, x7, x6
	eor x26, x26, x17
	eor x6, x13, x7
	eor x6, x6, x28
	eor x13, x27, x10
	eor x13, x13, x28
	eor x21, x21, x9
	ldr x9, [x5, #48]
	eor x15, x15, x9
	eor x9, x9, x21
	eor x12, x11, x26
	eor x12, x12, x28
	ldr x26, [x5, #56]
	eor x8, x26, x15
	eor x10, x25, x14
	eor x10, x10, x28
	add x11, x9, #0
	add x9, x19, #0
	add x7, x24, #0
	ror x21, x9, #32
	eor x21, x21, x6
	ror x22, x7, #48
	eor x21, x21, x22
	ldr x22, [x5, #576]
	eor x21, x21, x22
	str x21, [x5, #576]
	ror x21, x10, #32
	eor x21, x21, x7
	ror x22, x8, #48
	eor x21, x21, x22
	ldr x22, [x5, #584]
	eor x21, x21, x22
	str x21, [x5, #584]
	ror x21, x11, #32
	eor x21, x21, x8
	ror x22, x9, #48
	eor x21, x21, x22
	ldr x22, [x5, #592]
	eor x21, x21, x22
	str x21, [x5, #592]
	ror x21, x12, #32
	eor x21, x21, x9
	ror x22, x10, #48
	eor x21, x21, x22
	ldr x22, [x5, #600]
	eor x21, x21, x22
	str x21, [x5, #600]
	ror x21, x13, #32
	eor x21, x21, x10
	ror x22, x11, #48
	eor x21, x21, x22
	ldr x22, [x5, #608]
	eor x21, x21, x22
	str x21, [x5, #608]
	ror x21, x6, #16
	eor x21, x21, x11
	ror x22, x12, #48
	eor x21, x21, x22
	ldr x22, [x5, #616]
	eor x21, x21, x22
	str x21, [x5, #616]
	ror x21, x7, #16
	eor x21, x21, x12
	ror x22, x13, #48
	eor x21, x21, x22
	ldr x22, [x5, #624]
	eor x21, x21, x22
	str x21, [x5, #624]
	ror x21, x8, #16
	eor x21, x21, x13
	ror x22, x6, #32
	eor x21, x21, x22
	ldr x22, [x5, #632]
	eor x21, x21, x22
	str x21, [x5, #632]
	ldr x6, [x5, #704]
	ldr x21, [x5, #512]
	eor x6, x6, x21
	ldr x21, [x5, #576]
	eor x6, x6, x21
	ldr x21, [x4, #128]
	eor x6, x6, x21
	ldr x7, [x5, #712]
	ldr x21, [x5, #520]
	eor x7, x7, x21
	ldr x21, [x5, #584]
	eor x7, x7, x21
	ldr x21, [x4, #136]
	eor x7, x7, x21
	ldr x8, [x5, #720]
	ldr x21, [x5, #528]
	eor x8, x8, x21
	ldr x21, [x5, #592]
	eor x8, x8, x21
	ldr x21, [x4, #144]
	eor x8, x8, x21
	ldr x9, [x5, #728]
	ldr x21, [x5, #536]
	eor x9, x9, x21
	ldr x21, [x5, #600]
	eor x9, x9, x21
	ldr x21, [x4, #152]
	eor x9, x9, x21
	ldr x10, [x5, #736]
	ldr x21, [x5, #544]
	eor x10, x10, x21
	ldr x21, [x5, #608]
	eor x10, x10, x21
	ldr x21, [x4, #160]
	eor x10, x10, x21
	ldr x11, [x5, #744]
	ldr x21, [x5, #552]
	eor x11, x11, x21
	ldr x21, [x5, #616]
	eor x11, x11, x21
	ldr x21, [x4, #168]
	eor x11, x11, x21
	ldr x12, [x5, #752]
	ldr x21, [x5, #560]
	eor x12, x12, x21
	ldr x21, [x5, #624]
	eor x12, x12, x21
	ldr x21, [x4, #176]
	eor x12, x12, x21
	ldr x13, [x5, #760]
	ldr x21, [x5, #568]
	eor x13, x13, x21
	ldr x21, [x5, #632]
	eor x13, x13, x21
	ldr x21, [x4, #184]
	eor x13, x13, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x9, x6
	eor x16, x7, x15
	eor x17, x13, x14
	eor x19, x11, x16
	eor x20, x12, x8
	eor x10, x13, x10
	eor x21, x11, x17
	eor x22, x12, x21
	eor x23, x13, x9
	eor x24, x12, x10
	eor x25, x11, x14
	eor x21, x7, x21
	eor x21, x21, x28
	eor x26, x15, x17
	eor x27, x6, x24
	eor x24, x19, x24
	str x24, [x5, #0]
	eor x24, x7, x20
	eor x12, x12, x26
	eor x6, x6, x17
	eor x6, x6, x28
	eor x26, x7, x23
	eor x9, x9, x25
	eor x9, x9, x28
	eor x10, x16, x10
	str x17, [x5, #8]
	eor x17, x14, x19
	str x17, [x5, #16]
	eor x17, x19, x20
	eor x8, x13, x8
	eor x8, x8, x28
	eor x27, x7, x27
	eor x27, x27, x28
	eor x15, x15, x25
	eor x11, x11, x23
	eor x11, x11, x28
	eor x23, x7, x22
	eor x14, x14, x16
	eor x14, x14, x28
	eor x13, x13, x16
	eor x13, x13, x28
	and x16, x23, x21
	and x25, x19, x9
	eor x25, x25, x16
	str x19, [x5, #24]
	and x19, x12, x26
	eor x19, x19, x16
	and x16, x7, x15
	str x7, [x5, #32]
	and x7, x20, x11
	eor x7, x7, x16
	str x20, [x5, #40]
	and x20, x24, x6
	eor x20, x20, x16
	and x16, x10, x14
	str x10, [x5, #48]
	and x10, x22, x13
	eor x10, x10, x16
	str x22, [x5, #56]
	ldr x22, [x5, #8]
	str x24, [x5, #64]
	and x24, x17, x22
	eor x24, x24, x16
	eor x25, x25, x10
	eor x19, x19, x24
	eor x7, x7, x10
	eor x20, x20, x24
	eor x25, x25, x8
	ldr x8, [x5, #0]
	eor x19, x19, x8
	ldr x8, [x5, #16]
	eor x7, x7, x8
	eor x20, x20, x27
	eor x27, x25, x19
	and x25, x25, x7
	eor x8, x20, x25
	and x24, x27, x8
	eor x24, x24, x19
	eor x10, x7, x20
	eor x19, x19, x25
	and x19, x19, x10
	eor x19, x19, x20
	eor x7, x7, x19
	eor x10, x8, x19
	and x20, x20, x10
	eor x7, x20, x7
	eor x8, x8, x20
	and x8, x24, x8
	eor x27, x27, x8
	eor x8, x27, x7
	eor x20, x24, x19
	eor x10, x24, x27
	eor x25, x19, x7
	eor x16, x20, x8
	and x21, x25, x21
	and x9, x7, x9
	and x26, x19, x26
	and x15, x10, x15
	and x11, x27, x11
	and x6, x24, x6
	and x14, x20, x14
	and x13, x16, x13
	and x22, x8, x22
	and x25, x25, x23
	ldr x23, [x5, #24]
	and x7, x7, x23
	and x19, x19, x12
	ldr x12, [x5, #32]
	and x10, x10, x12
	ldr x12, [x5, #40]
	and x27, x27, x12
	ldr x12, [x5, #64]
	and x24, x24, x12
	ldr x12, [x5, #48]
	and x20, x20, x12
	ldr x12, [x5, #56]
	and x16, x16, x12
	and x8, x8, x17
	eor x25, x25, x20
	eor x14, x14, x7
	eor x6, x21, x6
	eor x17, x27, x14
	eor x24, x24, x17
	eor x22, x9, x22
	eor x17, x13, x24
	eor x8, x8, x25
	eor x12, x11, x6
	eor x23, x17, x8
	str x11, [x5, #56]
	eor x11, x19, x12
	str x23, [x5, #48]
	eor x23, x16, x22
	eor x25, x25, x23
	eor x6, x15, x6
	eor x6, x25, x6
	eor x19, x19, x8
	eor x27, x27, x16
	eor x10, x10, x20
	eor x14, x14, x12
	eor x22, x22, x11
	eor x24, x24, x22
	eor x24, x24, x28
	eor x7, x7, x6
	eor x26, x26, x17
	eor x6, x13, x7
	eor x6, x6, x28
	eor x13, x27, x10
	eor x13, x13, x28
	eor x21, x21, x9
	ldr x9, [x5, #48]
	eor x15, x15, x9
	eor x9, x9, x21
	eor x12, x11, x26
	eor x12, x12, x28
	ldr x26, [x5, #56]
	eor x8, x26, x15
	eor x10, x25, x14
	eor x10, x10, x28
	add x11, x9, #0
	add x9, x19, #0
	add x7, x24, #0
	ror x21, x9, #32
	eor x21, x21, x6
	ror x22, x7, #48
	eor x21, x21, x22
	ldr x22, [x5, #640]
	eor x21, x21, x22
	str x21, [x5, #640]
	ror x21, x10, #32
	eor x21, x21, x7
	ror x22, x8, #48
	eor x21, x21, x22
	ldr x22, [x5, #648]
	eor x21, x21, x22
	str x21, [x5, #648]
	ror x21, x11, #32
	eor x21, x21, x8
	ror x22, x9, #48
	eor x21, x21, x22
	ldr x22, [x5, #656]
	eor x21, x21, x22
	str x21, [x5, #656]
	ror x21, x12, #32
	eor x21, x21, x9
	ror x22, x10, #48
	eor x21, x21, x22
	ldr x22, [x5, #664]
	eor x21, x21, x22
	str x21, [x5, #664]
	ror x21, x13, #32
	eor x21, x21, x10
	ror x22, x11, #48
	eor x21, x21, x22
	ldr x22, [x5, #672]
	eor x21, x21, x22
	str x21, [x5, #672]
	ror x21, x6, #16
	eor x21, x21, x11
	ror x22, x12, #48
	eor x21, x21, x22
	ldr x22, [x5, #680]
	eor x21, x21, x22
	str x21, [x5, #680]
	ror x21, x7, #16
	eor x21, x21, x12
	ror x22, x13, #48
	eor x21, x21, x22
	ldr x22, [x5, #688]
	eor x21, x21, x22
	str x21, [x5, #688]
	ror x21, x8, #16
	eor x21, x21, x13
	ror x22, x6, #32
	eor x21, x21, x22
	ldr x22, [x5, #696]
	eor x21, x21, x22
	str x21, [x5, #696]
	ldr x6, [x5, #512]
	ldr x21, [x5, #576]
	eor x6, x6, x21
	ldr x21, [x5, #640]
	eor x6, x6, x21
	ldr x21, [x4, #192]
	eor x6, x6, x21
	ldr x7, [x5, #520]
	ldr x21, [x5, #584]
	eor x7, x7, x21
	ldr x21, [x5, #648]
	eor x7, x7, x21
	ldr x21, [x4, #200]
	eor x7, x7, x21
	ldr x8, [x5, #528]
	ldr x21, [x5, #592]
	eor x8, x8, x21
	ldr x21, [x5, #656]
	eor x8, x8, x21
	ldr x21, [x4, #208]
	eor x8, x8, x21
	ldr x9, [x5, #536]
	ldr x21, [x5, #600]
	eor x9, x9, x21
	ldr x21, [x5, #664]
	eor x9, x9, x21
	ldr x21, [x4, #216]
	eor x9, x9, x21
	ldr x10, [x5, #544]
	ldr x21, [x5, #608]
	eor x10, x10, x21
	ldr x21, [x5, #672]
	eor x10, x10, x21
	ldr x21, [x4, #224]
	eor x10, x10, x21
	ldr x11, [x5, #552]
	ldr x21, [x5, #616]
	eor x11, x11, x21
	ldr x21, [x5, #680]
	eor x11, x11, x21
	ldr x21, [x4, #232]
	eor x11, x11, x21
	ldr x12, [x5, #560]
	ldr x21, [x5, #624]
	eor x12, x12, x21
	ldr x21, [x5, #688]
	eor x12, x12, x21
	ldr x21, [x4, #240]
	eor x12, x12, x21
	ldr x13, [x5, #568]
	ldr x21, [x5, #632]
	eor x13, x13, x21
	ldr x21, [x5, #696]
	eor x13, x13, x21
	ldr x21, [x4, #248]
	eor x13, x13, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x10, x8
	eor x15, x9, x6
	eor x16, x7, x15
	eor x17, x13, x14
	eor x19, x11, x16
	eor x20, x12, x8
	eor x10, x13, x10
	eor x21, x11, x17
	eor x22, x12, x21
	eor x23, x13, x9
	eor x24, x12, x10
	eor x25, x11, x14
	eor x21, x7, x21
	eor x21, x21, x28
	eor x26, x15, x17
	eor x27, x6, x24
	eor x24, x19, x24
	str x24, [x5, #0]
	eor x24, x7, x20
	eor x12, x12, x26
	eor x6, x6, x17
	eor x6, x6, x28
	eor x26, x7, x23
	eor x9, x9, x25
	eor x9, x9, x28
	eor x10, x16, x10
	str x17, [x5, #8]
	eor x17, x14, x19
	str x17, [x5, #16]
	eor x17, x19, x20
	eor x8, x13, x8
	eor x8, x8, x28
	eor x27, x7, x27
	eor x27, x27, x28
	eor x15, x15, x25
	eor x11, x11, x23
	eor x11, x11, x28
	eor x23, x7, x22
	eor x14, x14, x16
	eor x14, x14, x28
	eor x13, x13, x16
	eor x13, x13, x28
	and x16, x23, x21
	and x25, x19, x9
	eor x25, x25, x16
	str x19, [x5, #24]
	and x19, x12, x26
	eor x19, x19, x16
	and x16, x7, x15
	str x7, [x5, #32]
	and x7, x20, x11
	eor x7, x7, x16
	str x20, [x5, #40]
	and x20, x24, x6
	eor x20, x20, x16
	and x16, x10, x14
	str x10, [x5, #48]
	and x10, x22, x13
	eor x10, x10, x16
	str x22, [x5, #56]
	ldr x22, [x5, #8]
	str x24, [x5, #64]
	and x24, x17, x22
	eor x24, x24, x16
	eor x25, x25, x10
	eor x19, x19, x24
	eor x7, x7, x10
	eor x20, x20, x24
	eor x25, x25, x8
	ldr x8, [x5, #0]
	eor x19, x19, x8
	ldr x8, [x5, #16]
	eor x7, x7, x8
	eor x20, x20, x27
	eor x27, x25, x19
	and x25, x25, x7
	eor x8, x20, x25
	and x24, x27, x8
	eor x24, x24, x19
	eor x10, x7, x20
	eor x19, x19, x25
	and x19, x19, x10
	eor x19, x19, x20
	eor x7, x7, x19
	eor x10, x8, x19
	and x20, x20, x10
	eor x7, x20, x7
	eor x8, x8, x20
	and x8, x24, x8
	eor x27, x27, x8
	eor x8, x27, x7
	eor x20, x24, x19
	eor x10, x24, x27
	eor x25, x19, x7
	eor x16, x20, x8
	and x21, x25, x21
	and x9, x7, x9
	and x26, x19, x26
	and x15, x10, x15
	and x11, x27, x11
	and x6, x24, x6
	and x14, x20, x14
	and x13, x16, x13
	and x22, x8, x22
	and x25, x25, x23
	ldr x23, [x5, #24]
	and x7, x7, x23
	and x19, x19, x12
	ldr x12, [x5, #32]
	and x10, x10, x12
	ldr x12, [x5, #40]
	and x27, x27, x12
	ldr x12, [x5, #64]
	and x24, x24, x12
	ldr x12, [x5, #48]
	and x20, x20, x12
	ldr x12, [x5, #56]
	and x16, x16, x12
	and x8, x8, x17
	eor x25, x25, x20
	eor x14, x14, x7
	eor x6, x21, x6
	eor x17, x27, x14
	eor x24, x24, x17
	eor x22, x9, x22
	eor x17, x13, x24
	eor x8, x8, x25
	eor x12, x11, x6
	eor x23, x17, x8
	str x11, [x5, #56]
	eor x11, x19, x12
	str x23, [x5, #48]
	eor x23, x16, x22
	eor x25, x25, x23
	eor x6, x15, x6
	eor x6, x25, x6
	eor x19, x19, x8
	eor x27, x27, x16
	eor x10, x10, x20
	eor x14, x14, x12
	eor x22, x22, x11
	eor x24, x24, x22
	eor x24, x24, x28
	eor x7, x7, x6
	eor x26, x26, x17
	eor x6, x13, x7
	eor x6, x6, x28
	eor x13, x27, x10
	eor x13, x13, x28
	eor x21, x21, x9
	ldr x9, [x5, #48]
	eor x15, x15, x9
	eor x9, x9, x21
	eor x12, x11, x26
	eor x12, x12, x28
	ldr x26, [x5, #56]
	eor x8, x26, x15
	eor x10, x25, x14
	eor x10, x10, x28
	add x11, x9, #0
	add x9, x19, #0
	add x7, x24, #0
	ror x21, x9, #32
	eor x21, x21, x6
	ror x22, x7, #48
	eor x21, x21, x22
	ldr x22, [x5, #704]
	eor x21, x21, x22
	str x21, [x5, #704]
	ror x21, x10, #32
	eor x21, x21, x7
	ror x22, x8, #48
	eor x21, x21, x22
	ldr x22, [x5, #712]
	eor x21, x21, x22
	str x21, [x5, #712]
	ror x21, x11, #32
	eor x21, x21, x8
	ror x22, x9, #48
	eor x21, x21, x22
	ldr x22, [x5, #720]
	eor x21, x21, x22
	str x21, [x5, #720]
	ror x21, x12, #32
	eor x21, x21, x9
	ror x22, x10, #48
	eor x21, x21, x22
	ldr x22, [x5, #728]
	eor x21, x21, x22
	str x21, [x5, #728]
	ror x21, x13, #32
	eor x21, x21, x10
	ror x22, x11, #48
	eor x21, x21, x22
	ldr x22, [x5, #736]
	eor x21, x21, x22
	str x21, [x5, #736]
	ror x21, x6, #16
	eor x21, x21, x11
	ror x22, x12, #48
	eor x21, x21, x22
	ldr x22, [x5, #744]
	eor x21, x21, x22
	str x21, [x5, #744]
	ror x21, x7, #16
	eor x21, x21, x12
	ror x22, x13, #48
	eor x21, x21, x22
	ldr x22, [x5, #752]
	eor x21, x21, x22
	str x21, [x5, #752]
	ror x21, x8, #16
	eor x21, x21, x13
	ror x22, x6, #32
	eor x21, x21, x22
	ldr x22, [x5, #760]
	eor x21, x21, x22
	str x21, [x5, #760]
	add x4, x4, #256
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x16, #255, lsl #0
	movk x16, #255, lsl #16
	movk x16, #255, lsl #32
	movk x16, #255, lsl #48
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	ldr x6, [x5, #704]
	ldr x7, [x5, #712]
	ldr x8, [x5, #720]
	ldr x9, [x5, #728]
	ldr x10, [x5, #736]
	ldr x11, [x5, #744]
	ldr x12, [x5, #752]
	ldr x13, [x5, #760]
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #768]
	str x7, [x5, #784]
	str x8, [x5, #800]
	str x9, [x5, #816]
	str x10, [x5, #832]
	str x11, [x5, #848]
	str x12, [x5, #864]
	str x13, [x5, #880]
	ldr x6, [x5, #640]
	ldr x7, [x5, #648]
	ldr x8, [x5, #656]
	ldr x9, [x5, #664]
	ldr x10, [x5, #672]
	ldr x11, [x5, #680]
	ldr x12, [x5, #688]
	ldr x13, [x5, #696]
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #896]
	str x7, [x5, #912]
	str x8, [x5, #928]
	str x9, [x5, #944]
	str x10, [x5, #960]
	str x11, [x5, #976]
	str x12, [x5, #992]
	str x13, [x5, #1008]
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #776]
	str x7, [x5, #792]
	str x8, [x5, #808]
	str x9, [x5, #824]
	str x10, [x5, #840]
	str x11, [x5, #856]
	str x12, [x5, #872]
	str x13, [x5, #888]
	ldr x6, [x5, #512]
	ldr x7, [x5, #520]
	ldr x8, [x5, #528]
	ldr x9, [x5, #536]
	ldr x10, [x5, #544]
	ldr x11, [x5, #552]
	ldr x12, [x5, #560]
	ldr x13, [x5, #568]
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #904]
	str x7, [x5, #920]
	str x8, [x5, #936]
	str x9, [x5, #952]
	str x10, [x5, #968]
	str x11, [x5, #984]
	str x12, [x5, #1000]
	str x13, [x5, #1016]
	ldr x6, [x5, #768]
	ldr x10, [x5, #896]
	ldr x7, [x5, #784]
	ldr x11, [x5, #912]
	ldr x8, [x5, #800]
	ldr x12, [x5, #928]
	ldr x9, [x5, #816]
	ldr x13, [x5, #944]
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	str x6, [x5, #768]
	str x10, [x5, #896]
	str x7, [x5, #784]
	str x11, [x5, #912]
	str x8, [x5, #800]
	str x12, [x5, #928]
	str x9, [x5, #816]
	str x13, [x5, #944]
	ldr x6, [x5, #832]
	ldr x10, [x5, #960]
	ldr x7, [x5, #848]
	ldr x11, [x5, #976]
	ldr x8, [x5, #864]
	ldr x12, [x5, #992]
	ldr x9, [x5, #880]
	ldr x13, [x5, #1008]
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	str x6, [x5, #832]
	str x10, [x5, #960]
	str x7, [x5, #848]
	str x11, [x5, #976]
	str x8, [x5, #864]
	str x12, [x5, #992]
	str x9, [x5, #880]
	str x13, [x5, #1008]
	ldr x6, [x5, #776]
	ldr x10, [x5, #904]
	ldr x7, [x5, #792]
	ldr x11, [x5, #920]
	ldr x8, [x5, #808]
	ldr x12, [x5, #936]
	ldr x9, [x5, #824]
	ldr x13, [x5, #952]
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	str x6, [x5, #776]
	str x10, [x5, #904]
	str x7, [x5, #792]
	str x11, [x5, #920]
	str x8, [x5, #808]
	str x12, [x5, #936]
	str x9, [x5, #824]
	str x13, [x5, #952]
	ldr x6, [x5, #840]
	ldr x10, [x5, #968]
	ldr x7, [x5, #856]
	ldr x11, [x5, #984]
	ldr x8, [x5, #872]
	ldr x12, [x5, #1000]
	ldr x9, [x5, #888]
	ldr x13, [x5, #1016]
	lsr x21, x6, #8
	eor x21, x21, x10
	and x21, x21, x16
	eor x10, x10, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x11
	and x21, x21, x16
	eor x11, x11, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x12
	and x21, x21, x16
	eor x12, x12, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x13
	and x21, x21, x16
	eor x13, x13, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	str x6, [x5, #840]
	str x10, [x5, #968]
	str x7, [x5, #856]
	str x11, [x5, #984]
	str x8, [x5, #872]
	str x12, [x5, #1000]
	str x9, [x5, #888]
	str x13, [x5, #1016]
	ldr x21, [x5, #776]
	rev x21, x21
	str x21, [x1, #0]
	ldr x21, [x5, #768]
	rev x21, x21
	str x21, [x1, #8]
	add x1, x1, #16
	sub x21, x4, x3
	cbnz x21, 20b
	ldr x19, [x5, #3072]
	ldr x20, [x5, #3080]
	ldr x21, [x5, #3088]
	ldr x22, [x5, #3096]
	ldr x23, [x5, #3104]
	ldr x24, [x5, #3112]
	ldr x25, [x5, #3120]
	ldr x26, [x5, #3128]
	ldr x27, [x5, #3136]
	ldr x28, [x5, #3144]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1024
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1536
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #2048
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #2560
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #3072
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	add sp, sp, #3168
	ret
	.p2align 6

vg_sm4_ecb_encrypt:
	str x30, [sp, #-16]!
	movz x3, #0, lsl #0
	bl {vg_sm4_ecb}
	ldr x30, [sp], #16
	ret
	.p2align 6

vg_sm4_ecb_decrypt:
	str x30, [sp, #-16]!
	movz x3, #1, lsl #0
	bl {vg_sm4_ecb}
	ldr x30, [sp], #16
	ret
	.p2align 6
