// The functions of `src/internal/vg_ffdh_parameter_candidate.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_parameter_candidate:
	str x0, [x7, #128]
	str x1, [x7, #144]
	str x1, [x7, #168]
	str x1, [x7, #216]
	str x2, [x7, #136]
	str x3, [x7, #152]
	add w4, w4, #0
	str x4, [x7, #160]
	str x5, [x7, #192]
	str x6, [x7, #200]
	add x0, x7, #0
	ldr x1, [x0, #128]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
20:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 20b
	ldr x3, [x0, #200]
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 21f
	ldr x3, [x0, #152]
	add x4, x3, #7
	lsr x4, x4, #3
	str x4, [x0, #144]
	add x6, x3, #63
	lsr x6, x6, #6
	lsl x6, x6, #6
	add x8, x3, #64
	sub x6, x8, x6
	movz x5, #64, lsl #0
	movz x9, #128, lsl #0
	movz x8, #2049, lsl #0
	subs x8, x3, x8
	csel x5, x9, x5, hs
	str x5, [x0, #0]
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
	add x3, x12, #2
	lsl x3, x3, #3
	add x4, x0, #256
	str x4, [x0, #64]
	add x4, x4, x3
	str x4, [x0, #72]
	add x4, x4, x3
	str x4, [x0, #80]
	add x4, x4, x3
	str x4, [x0, #88]
	add x4, x4, x3
	str x4, [x0, #96]
	add x4, x4, x3
	str x4, [x0, #104]
	add x4, x4, x3
	str x4, [x0, #112]
	add x4, x4, x3
	str x4, [x0, #120]
	add x4, x4, x3
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	movz x9, #0, lsl #0
23:
	add x9, x9, x9
	add x9, x9, #1
	sub x6, x6, #1
	cbnz x6, 23b
	str x9, [x0, #16]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
24:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 24b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #192]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
25:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 26f
	b 27f
26:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
27:
	cbnz x2, 25b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x16, #0]
	ldr x6, [x5, #0]
	movz x9, #1, lsl #0
	orr x3, x3, x9
	and x6, x6, x4
	lsr x9, x4, #1
	add x9, x9, #1
	orr x6, x6, x9
	str x3, [x16, #0]
	str x6, [x5, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	lsl x5, x12, #3
	add x10, x16, x5
	add x14, x12, #0
	ldr x9, [x0, #160]
	movz x6, #3, lsl #0
	subs x8, x9, x6
	movz x13, #10, lsl #0
	movz x6, #24, lsl #0
	csel x13, x13, x6, hs
	movz x3, #0, lsl #0
	movz x7, #0, lsl #0
	sub x8, x7, #1
28:
	sub x10, x10, #8
	ldr x2, [x10, #0]
	movz x9, #64, lsl #0
29:
	adds x2, x2, x2
	adcs x3, x3, x3
	adc x4, x7, x7
	subs x5, x3, x13
	csel x6, x8, x7, hs
	sub x4, x7, x4
	orr x6, x6, x4
	eor x5, x5, x3
	and x5, x5, x6
	eor x3, x3, x5
	sub x9, x9, #1
	cbnz x9, 29b
	sub x14, x14, #1
	cbnz x14, 28b
	ldr x9, [x0, #160]
	movz x6, #3, lsl #0
	subs x8, x9, x6
	movz x4, #4, lsl #0
	orr x5, x3, x4
	csel x5, x5, x3, hs
	movz x6, #7, lsl #0
	movz x7, #11, lsl #0
	csel x6, x6, x7, hs
	eor x5, x5, x6
	str x5, [x0, #32]
	ldr x5, [x0, #32]
	cbz x5, 210f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 211f
210:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	movz x3, #3, lsl #0
	movk x3, #5, lsl #16
	movk x3, #7, lsl #32
	movk x3, #11, lsl #48
	str x3, [x9, #0]
	movz x3, #13, lsl #0
	movk x3, #17, lsl #16
	movk x3, #19, lsl #32
	movk x3, #23, lsl #48
	str x3, [x9, #8]
	movz x3, #29, lsl #0
	movk x3, #31, lsl #16
	movk x3, #37, lsl #32
	movk x3, #41, lsl #48
	str x3, [x9, #16]
	movz x3, #43, lsl #0
	movk x3, #47, lsl #16
	movk x3, #53, lsl #32
	movk x3, #59, lsl #48
	str x3, [x9, #24]
	movz x3, #61, lsl #0
	movk x3, #67, lsl #16
	movk x3, #71, lsl #32
	movk x3, #73, lsl #48
	str x3, [x9, #32]
	movz x3, #79, lsl #0
	movk x3, #83, lsl #16
	movk x3, #89, lsl #32
	movk x3, #97, lsl #48
	str x3, [x9, #40]
	movz x3, #101, lsl #0
	movk x3, #103, lsl #16
	movk x3, #107, lsl #32
	movk x3, #109, lsl #48
	str x3, [x9, #48]
	movz x3, #113, lsl #0
	movk x3, #127, lsl #16
	movk x3, #131, lsl #32
	movk x3, #137, lsl #48
	str x3, [x9, #56]
	movz x3, #139, lsl #0
	movk x3, #149, lsl #16
	movk x3, #151, lsl #32
	movk x3, #157, lsl #48
	str x3, [x9, #64]
	movz x3, #163, lsl #0
	movk x3, #167, lsl #16
	movk x3, #173, lsl #32
	movk x3, #179, lsl #48
	str x3, [x9, #72]
	movz x3, #181, lsl #0
	movk x3, #191, lsl #16
	movk x3, #193, lsl #32
	movk x3, #197, lsl #48
	str x3, [x9, #80]
	movz x3, #199, lsl #0
	movk x3, #211, lsl #16
	movk x3, #223, lsl #32
	movk x3, #227, lsl #48
	str x3, [x9, #88]
	movz x3, #229, lsl #0
	movk x3, #233, lsl #16
	movk x3, #239, lsl #32
	movk x3, #241, lsl #48
	str x3, [x9, #96]
	movz x3, #251, lsl #0
	movk x3, #257, lsl #16
	movk x3, #263, lsl #32
	movk x3, #269, lsl #48
	str x3, [x9, #104]
	movz x3, #271, lsl #0
	movk x3, #277, lsl #16
	movk x3, #281, lsl #32
	movk x3, #283, lsl #48
	str x3, [x9, #112]
	movz x3, #293, lsl #0
	movk x3, #307, lsl #16
	movk x3, #311, lsl #32
	movk x3, #313, lsl #48
	str x3, [x9, #120]
	movz x3, #317, lsl #0
	movk x3, #331, lsl #16
	movk x3, #337, lsl #32
	movk x3, #347, lsl #48
	str x3, [x9, #128]
	movz x3, #349, lsl #0
	movk x3, #353, lsl #16
	movk x3, #359, lsl #32
	movk x3, #367, lsl #48
	str x3, [x9, #136]
	movz x3, #373, lsl #0
	movk x3, #379, lsl #16
	movk x3, #383, lsl #32
	movk x3, #389, lsl #48
	str x3, [x9, #144]
	movz x3, #397, lsl #0
	movk x3, #401, lsl #16
	movk x3, #409, lsl #32
	movk x3, #419, lsl #48
	str x3, [x9, #152]
	movz x3, #421, lsl #0
	movk x3, #431, lsl #16
	movk x3, #433, lsl #32
	movk x3, #439, lsl #48
	str x3, [x9, #160]
	movz x3, #443, lsl #0
	movk x3, #449, lsl #16
	movk x3, #457, lsl #32
	movk x3, #461, lsl #48
	str x3, [x9, #168]
	movz x3, #463, lsl #0
	movk x3, #467, lsl #16
	movk x3, #479, lsl #32
	movk x3, #487, lsl #48
	str x3, [x9, #176]
	movz x3, #491, lsl #0
	movk x3, #499, lsl #16
	movk x3, #503, lsl #32
	movk x3, #509, lsl #48
	str x3, [x9, #184]
	movz x3, #521, lsl #0
	movk x3, #523, lsl #16
	movk x3, #541, lsl #32
	movk x3, #547, lsl #48
	str x3, [x9, #192]
	movz x3, #557, lsl #0
	movk x3, #563, lsl #16
	movk x3, #569, lsl #32
	movk x3, #571, lsl #48
	str x3, [x9, #200]
	movz x3, #577, lsl #0
	movk x3, #587, lsl #16
	movk x3, #593, lsl #32
	movk x3, #599, lsl #48
	str x3, [x9, #208]
	movz x3, #601, lsl #0
	movk x3, #607, lsl #16
	movk x3, #613, lsl #32
	movk x3, #617, lsl #48
	str x3, [x9, #216]
	movz x3, #619, lsl #0
	movk x3, #631, lsl #16
	movk x3, #641, lsl #32
	movk x3, #643, lsl #48
	str x3, [x9, #224]
	movz x3, #647, lsl #0
	movk x3, #653, lsl #16
	movk x3, #659, lsl #32
	movk x3, #661, lsl #48
	str x3, [x9, #232]
	movz x3, #673, lsl #0
	movk x3, #677, lsl #16
	movk x3, #683, lsl #32
	movk x3, #691, lsl #48
	str x3, [x9, #240]
	movz x3, #701, lsl #0
	movk x3, #709, lsl #16
	movk x3, #719, lsl #32
	movk x3, #727, lsl #48
	str x3, [x9, #248]
	movz x3, #733, lsl #0
	movk x3, #739, lsl #16
	movk x3, #743, lsl #32
	movk x3, #751, lsl #48
	str x3, [x9, #256]
	movz x3, #757, lsl #0
	movk x3, #761, lsl #16
	movk x3, #769, lsl #32
	movk x3, #773, lsl #48
	str x3, [x9, #264]
	movz x3, #787, lsl #0
	movk x3, #797, lsl #16
	movk x3, #809, lsl #32
	movk x3, #811, lsl #48
	str x3, [x9, #272]
	movz x3, #821, lsl #0
	movk x3, #823, lsl #16
	movk x3, #827, lsl #32
	movk x3, #829, lsl #48
	str x3, [x9, #280]
	movz x3, #839, lsl #0
	movk x3, #853, lsl #16
	movk x3, #857, lsl #32
	movk x3, #859, lsl #48
	str x3, [x9, #288]
	movz x3, #863, lsl #0
	movk x3, #877, lsl #16
	movk x3, #881, lsl #32
	movk x3, #883, lsl #48
	str x3, [x9, #296]
	movz x3, #887, lsl #0
	movk x3, #907, lsl #16
	movk x3, #911, lsl #32
	movk x3, #919, lsl #48
	str x3, [x9, #304]
	movz x3, #929, lsl #0
	movk x3, #937, lsl #16
	movk x3, #941, lsl #32
	movk x3, #947, lsl #48
	str x3, [x9, #312]
	movz x3, #953, lsl #0
	movk x3, #967, lsl #16
	movk x3, #971, lsl #32
	movk x3, #977, lsl #48
	str x3, [x9, #320]
	movz x3, #983, lsl #0
	movk x3, #991, lsl #16
	movk x3, #997, lsl #32
	movk x3, #1009, lsl #48
	str x3, [x9, #328]
	movz x3, #1013, lsl #0
	movk x3, #1019, lsl #16
	movk x3, #1021, lsl #32
	movk x3, #1031, lsl #48
	str x3, [x9, #336]
	movz x3, #1033, lsl #0
	movk x3, #1039, lsl #16
	movk x3, #1049, lsl #32
	movk x3, #1051, lsl #48
	str x3, [x9, #344]
	movz x3, #1061, lsl #0
	movk x3, #1063, lsl #16
	movk x3, #1069, lsl #32
	movk x3, #1087, lsl #48
	str x3, [x9, #352]
	movz x3, #1091, lsl #0
	movk x3, #1093, lsl #16
	movk x3, #1097, lsl #32
	movk x3, #1103, lsl #48
	str x3, [x9, #360]
	movz x3, #1109, lsl #0
	movk x3, #1117, lsl #16
	movk x3, #1123, lsl #32
	movk x3, #1129, lsl #48
	str x3, [x9, #368]
	movz x3, #1151, lsl #0
	movk x3, #1153, lsl #16
	movk x3, #1163, lsl #32
	movk x3, #1171, lsl #48
	str x3, [x9, #376]
	movz x3, #1181, lsl #0
	movk x3, #1187, lsl #16
	movk x3, #1193, lsl #32
	movk x3, #1201, lsl #48
	str x3, [x9, #384]
	movz x3, #1213, lsl #0
	movk x3, #1217, lsl #16
	movk x3, #1223, lsl #32
	movk x3, #1229, lsl #48
	str x3, [x9, #392]
	movz x3, #1231, lsl #0
	movk x3, #1237, lsl #16
	movk x3, #1249, lsl #32
	movk x3, #1259, lsl #48
	str x3, [x9, #400]
	movz x3, #1277, lsl #0
	movk x3, #1279, lsl #16
	movk x3, #1283, lsl #32
	movk x3, #1289, lsl #48
	str x3, [x9, #408]
	movz x3, #1291, lsl #0
	movk x3, #1297, lsl #16
	movk x3, #1301, lsl #32
	movk x3, #1303, lsl #48
	str x3, [x9, #416]
	movz x3, #1307, lsl #0
	movk x3, #1319, lsl #16
	movk x3, #1321, lsl #32
	movk x3, #1327, lsl #48
	str x3, [x9, #424]
	movz x3, #1361, lsl #0
	movk x3, #1367, lsl #16
	movk x3, #1373, lsl #32
	movk x3, #1381, lsl #48
	str x3, [x9, #432]
	movz x3, #1399, lsl #0
	movk x3, #1409, lsl #16
	movk x3, #1423, lsl #32
	movk x3, #1427, lsl #48
	str x3, [x9, #440]
	movz x3, #1429, lsl #0
	movk x3, #1433, lsl #16
	movk x3, #1439, lsl #32
	movk x3, #1447, lsl #48
	str x3, [x9, #448]
	movz x3, #1451, lsl #0
	movk x3, #1453, lsl #16
	movk x3, #1459, lsl #32
	movk x3, #1471, lsl #48
	str x3, [x9, #456]
	movz x3, #1481, lsl #0
	movk x3, #1483, lsl #16
	movk x3, #1487, lsl #32
	movk x3, #1489, lsl #48
	str x3, [x9, #464]
	movz x3, #1493, lsl #0
	movk x3, #1499, lsl #16
	movk x3, #1511, lsl #32
	movk x3, #1523, lsl #48
	str x3, [x9, #472]
	movz x3, #1531, lsl #0
	movk x3, #1543, lsl #16
	movk x3, #1549, lsl #32
	movk x3, #1553, lsl #48
	str x3, [x9, #480]
	movz x3, #1559, lsl #0
	movk x3, #1567, lsl #16
	movk x3, #1571, lsl #32
	movk x3, #1579, lsl #48
	str x3, [x9, #488]
	movz x3, #1583, lsl #0
	movk x3, #1597, lsl #16
	movk x3, #1601, lsl #32
	movk x3, #1607, lsl #48
	str x3, [x9, #496]
	movz x3, #1609, lsl #0
	movk x3, #1613, lsl #16
	movk x3, #1619, lsl #32
	movk x3, #1621, lsl #48
	str x3, [x9, #504]
	movz x3, #1627, lsl #0
	movk x3, #1637, lsl #16
	movk x3, #1657, lsl #32
	movk x3, #1663, lsl #48
	str x3, [x9, #512]
	movz x3, #1667, lsl #0
	movk x3, #1669, lsl #16
	movk x3, #1693, lsl #32
	movk x3, #1697, lsl #48
	str x3, [x9, #520]
	movz x3, #1699, lsl #0
	movk x3, #1709, lsl #16
	movk x3, #1721, lsl #32
	movk x3, #1723, lsl #48
	str x3, [x9, #528]
	movz x3, #1733, lsl #0
	movk x3, #1741, lsl #16
	movk x3, #1747, lsl #32
	movk x3, #1753, lsl #48
	str x3, [x9, #536]
	movz x3, #1759, lsl #0
	movk x3, #1777, lsl #16
	movk x3, #1783, lsl #32
	movk x3, #1787, lsl #48
	str x3, [x9, #544]
	movz x3, #1789, lsl #0
	movk x3, #1801, lsl #16
	movk x3, #1811, lsl #32
	movk x3, #1823, lsl #48
	str x3, [x9, #552]
	movz x3, #1831, lsl #0
	movk x3, #1847, lsl #16
	movk x3, #1861, lsl #32
	movk x3, #1867, lsl #48
	str x3, [x9, #560]
	movz x3, #1871, lsl #0
	movk x3, #1873, lsl #16
	movk x3, #1877, lsl #32
	movk x3, #1879, lsl #48
	str x3, [x9, #568]
	movz x3, #1889, lsl #0
	movk x3, #1901, lsl #16
	movk x3, #1907, lsl #32
	movk x3, #1913, lsl #48
	str x3, [x9, #576]
	movz x3, #1931, lsl #0
	movk x3, #1933, lsl #16
	movk x3, #1949, lsl #32
	movk x3, #1951, lsl #48
	str x3, [x9, #584]
	movz x3, #1973, lsl #0
	movk x3, #1979, lsl #16
	movk x3, #1987, lsl #32
	movk x3, #1993, lsl #48
	str x3, [x9, #592]
	movz x3, #1997, lsl #0
	movk x3, #1999, lsl #16
	movk x3, #2003, lsl #32
	movk x3, #2011, lsl #48
	str x3, [x9, #600]
	movz x3, #2017, lsl #0
	movk x3, #2027, lsl #16
	movk x3, #2029, lsl #32
	movk x3, #2039, lsl #48
	str x3, [x9, #608]
	movz x3, #2053, lsl #0
	movk x3, #2063, lsl #16
	movk x3, #2069, lsl #32
	movk x3, #2081, lsl #48
	str x3, [x9, #616]
	movz x3, #2083, lsl #0
	movk x3, #2087, lsl #16
	movk x3, #2089, lsl #32
	movk x3, #2099, lsl #48
	str x3, [x9, #624]
	movz x3, #2111, lsl #0
	movk x3, #2113, lsl #16
	movk x3, #2129, lsl #32
	movk x3, #2131, lsl #48
	str x3, [x9, #632]
	movz x3, #2137, lsl #0
	movk x3, #2141, lsl #16
	movk x3, #2143, lsl #32
	movk x3, #2153, lsl #48
	str x3, [x9, #640]
	movz x3, #2161, lsl #0
	movk x3, #2179, lsl #16
	movk x3, #2203, lsl #32
	movk x3, #2207, lsl #48
	str x3, [x9, #648]
	movz x3, #2213, lsl #0
	movk x3, #2221, lsl #16
	movk x3, #2237, lsl #32
	movk x3, #2239, lsl #48
	str x3, [x9, #656]
	movz x3, #2243, lsl #0
	movk x3, #2251, lsl #16
	movk x3, #2267, lsl #32
	movk x3, #2269, lsl #48
	str x3, [x9, #664]
	movz x3, #2273, lsl #0
	movk x3, #2281, lsl #16
	movk x3, #2287, lsl #32
	movk x3, #2293, lsl #48
	str x3, [x9, #672]
	movz x3, #2297, lsl #0
	movk x3, #2309, lsl #16
	movk x3, #2311, lsl #32
	movk x3, #2333, lsl #48
	str x3, [x9, #680]
	movz x3, #2339, lsl #0
	movk x3, #2341, lsl #16
	movk x3, #2347, lsl #32
	movk x3, #2351, lsl #48
	str x3, [x9, #688]
	movz x3, #2357, lsl #0
	movk x3, #2371, lsl #16
	movk x3, #2377, lsl #32
	movk x3, #2381, lsl #48
	str x3, [x9, #696]
	movz x3, #2383, lsl #0
	movk x3, #2389, lsl #16
	movk x3, #2393, lsl #32
	movk x3, #2399, lsl #48
	str x3, [x9, #704]
	movz x3, #2411, lsl #0
	movk x3, #2417, lsl #16
	movk x3, #2423, lsl #32
	movk x3, #2437, lsl #48
	str x3, [x9, #712]
	movz x3, #2441, lsl #0
	movk x3, #2447, lsl #16
	movk x3, #2459, lsl #32
	movk x3, #2467, lsl #48
	str x3, [x9, #720]
	movz x3, #2473, lsl #0
	movk x3, #2477, lsl #16
	movk x3, #2503, lsl #32
	movk x3, #2521, lsl #48
	str x3, [x9, #728]
	movz x3, #2531, lsl #0
	movk x3, #2539, lsl #16
	movk x3, #2543, lsl #32
	movk x3, #2549, lsl #48
	str x3, [x9, #736]
	movz x3, #2551, lsl #0
	movk x3, #2557, lsl #16
	movk x3, #2579, lsl #32
	movk x3, #2591, lsl #48
	str x3, [x9, #744]
	movz x3, #2593, lsl #0
	movk x3, #2609, lsl #16
	movk x3, #2617, lsl #32
	movk x3, #2621, lsl #48
	str x3, [x9, #752]
	movz x3, #2633, lsl #0
	movk x3, #2647, lsl #16
	movk x3, #2657, lsl #32
	movk x3, #2659, lsl #48
	str x3, [x9, #760]
	movz x3, #2663, lsl #0
	movk x3, #2671, lsl #16
	movk x3, #2677, lsl #32
	movk x3, #2683, lsl #48
	str x3, [x9, #768]
	movz x3, #2687, lsl #0
	movk x3, #2689, lsl #16
	movk x3, #2693, lsl #32
	movk x3, #2699, lsl #48
	str x3, [x9, #776]
	movz x3, #2707, lsl #0
	movk x3, #2711, lsl #16
	movk x3, #2713, lsl #32
	movk x3, #2719, lsl #48
	str x3, [x9, #784]
	movz x3, #2729, lsl #0
	movk x3, #2731, lsl #16
	movk x3, #2741, lsl #32
	movk x3, #2749, lsl #48
	str x3, [x9, #792]
	movz x3, #2753, lsl #0
	movk x3, #2767, lsl #16
	movk x3, #2777, lsl #32
	movk x3, #2789, lsl #48
	str x3, [x9, #800]
	movz x3, #2791, lsl #0
	movk x3, #2797, lsl #16
	movk x3, #2801, lsl #32
	movk x3, #2803, lsl #48
	str x3, [x9, #808]
	movz x3, #2819, lsl #0
	movk x3, #2833, lsl #16
	movk x3, #2837, lsl #32
	movk x3, #2843, lsl #48
	str x3, [x9, #816]
	movz x3, #2851, lsl #0
	movk x3, #2857, lsl #16
	movk x3, #2861, lsl #32
	movk x3, #2879, lsl #48
	str x3, [x9, #824]
	movz x3, #2887, lsl #0
	movk x3, #2897, lsl #16
	movk x3, #2903, lsl #32
	movk x3, #2909, lsl #48
	str x3, [x9, #832]
	movz x3, #2917, lsl #0
	movk x3, #2927, lsl #16
	movk x3, #2939, lsl #32
	movk x3, #2953, lsl #48
	str x3, [x9, #840]
	movz x3, #2957, lsl #0
	movk x3, #2963, lsl #16
	movk x3, #2969, lsl #32
	movk x3, #2971, lsl #48
	str x3, [x9, #848]
	movz x3, #2999, lsl #0
	movk x3, #3001, lsl #16
	movk x3, #3011, lsl #32
	movk x3, #3019, lsl #48
	str x3, [x9, #856]
	movz x3, #3023, lsl #0
	movk x3, #3037, lsl #16
	movk x3, #3041, lsl #32
	movk x3, #3049, lsl #48
	str x3, [x9, #864]
	movz x3, #3061, lsl #0
	movk x3, #3067, lsl #16
	movk x3, #3079, lsl #32
	movk x3, #3083, lsl #48
	str x3, [x9, #872]
	movz x3, #3089, lsl #0
	movk x3, #3109, lsl #16
	movk x3, #3119, lsl #32
	movk x3, #3121, lsl #48
	str x3, [x9, #880]
	movz x3, #3137, lsl #0
	movk x3, #3163, lsl #16
	movk x3, #3167, lsl #32
	movk x3, #3169, lsl #48
	str x3, [x9, #888]
	movz x3, #3181, lsl #0
	movk x3, #3187, lsl #16
	movk x3, #3191, lsl #32
	movk x3, #3203, lsl #48
	str x3, [x9, #896]
	movz x3, #3209, lsl #0
	movk x3, #3217, lsl #16
	movk x3, #3221, lsl #32
	movk x3, #3229, lsl #48
	str x3, [x9, #904]
	movz x3, #3251, lsl #0
	movk x3, #3253, lsl #16
	movk x3, #3257, lsl #32
	movk x3, #3259, lsl #48
	str x3, [x9, #912]
	movz x3, #3271, lsl #0
	movk x3, #3299, lsl #16
	movk x3, #3301, lsl #32
	movk x3, #3307, lsl #48
	str x3, [x9, #920]
	movz x3, #3313, lsl #0
	movk x3, #3319, lsl #16
	movk x3, #3323, lsl #32
	movk x3, #3329, lsl #48
	str x3, [x9, #928]
	movz x3, #3331, lsl #0
	movk x3, #3343, lsl #16
	movk x3, #3347, lsl #32
	movk x3, #3359, lsl #48
	str x3, [x9, #936]
	movz x3, #3361, lsl #0
	movk x3, #3371, lsl #16
	movk x3, #3373, lsl #32
	movk x3, #3389, lsl #48
	str x3, [x9, #944]
	movz x3, #3391, lsl #0
	movk x3, #3407, lsl #16
	movk x3, #3413, lsl #32
	movk x3, #3433, lsl #48
	str x3, [x9, #952]
	movz x3, #3449, lsl #0
	movk x3, #3457, lsl #16
	movk x3, #3461, lsl #32
	movk x3, #3463, lsl #48
	str x3, [x9, #960]
	movz x3, #3467, lsl #0
	movk x3, #3469, lsl #16
	movk x3, #3491, lsl #32
	movk x3, #3499, lsl #48
	str x3, [x9, #968]
	movz x3, #3511, lsl #0
	movk x3, #3517, lsl #16
	movk x3, #3527, lsl #32
	movk x3, #3529, lsl #48
	str x3, [x9, #976]
	movz x3, #3533, lsl #0
	movk x3, #3539, lsl #16
	movk x3, #3541, lsl #32
	movk x3, #3547, lsl #48
	str x3, [x9, #984]
	movz x3, #3557, lsl #0
	movk x3, #3559, lsl #16
	movk x3, #3571, lsl #32
	movk x3, #3581, lsl #48
	str x3, [x9, #992]
	movz x3, #3583, lsl #0
	movk x3, #3593, lsl #16
	movk x3, #3607, lsl #32
	movk x3, #3613, lsl #48
	str x3, [x9, #1000]
	movz x3, #3617, lsl #0
	movk x3, #3623, lsl #16
	movk x3, #3631, lsl #32
	movk x3, #3637, lsl #48
	str x3, [x9, #1008]
	movz x3, #3643, lsl #0
	movk x3, #3659, lsl #16
	movk x3, #3671, lsl #32
	movk x3, #3, lsl #48
	str x3, [x9, #1016]
	movz x3, #3673, lsl #0
	movk x3, #3677, lsl #16
	movk x3, #3691, lsl #32
	movk x3, #3697, lsl #48
	str x3, [x9, #1024]
	movz x3, #3701, lsl #0
	movk x3, #3709, lsl #16
	movk x3, #3719, lsl #32
	movk x3, #3727, lsl #48
	str x3, [x9, #1032]
	movz x3, #3733, lsl #0
	movk x3, #3739, lsl #16
	movk x3, #3761, lsl #32
	movk x3, #3767, lsl #48
	str x3, [x9, #1040]
	movz x3, #3769, lsl #0
	movk x3, #3779, lsl #16
	movk x3, #3793, lsl #32
	movk x3, #3797, lsl #48
	str x3, [x9, #1048]
	movz x3, #3803, lsl #0
	movk x3, #3821, lsl #16
	movk x3, #3823, lsl #32
	movk x3, #3833, lsl #48
	str x3, [x9, #1056]
	movz x3, #3847, lsl #0
	movk x3, #3851, lsl #16
	movk x3, #3853, lsl #32
	movk x3, #3863, lsl #48
	str x3, [x9, #1064]
	movz x3, #3877, lsl #0
	movk x3, #3881, lsl #16
	movk x3, #3889, lsl #32
	movk x3, #3907, lsl #48
	str x3, [x9, #1072]
	movz x3, #3911, lsl #0
	movk x3, #3917, lsl #16
	movk x3, #3919, lsl #32
	movk x3, #3923, lsl #48
	str x3, [x9, #1080]
	movz x3, #3929, lsl #0
	movk x3, #3931, lsl #16
	movk x3, #3943, lsl #32
	movk x3, #3947, lsl #48
	str x3, [x9, #1088]
	movz x3, #3967, lsl #0
	movk x3, #3989, lsl #16
	movk x3, #4001, lsl #32
	movk x3, #4003, lsl #48
	str x3, [x9, #1096]
	movz x3, #4007, lsl #0
	movk x3, #4013, lsl #16
	movk x3, #4019, lsl #32
	movk x3, #4021, lsl #48
	str x3, [x9, #1104]
	movz x3, #4027, lsl #0
	movk x3, #4049, lsl #16
	movk x3, #4051, lsl #32
	movk x3, #4057, lsl #48
	str x3, [x9, #1112]
	movz x3, #4073, lsl #0
	movk x3, #4079, lsl #16
	movk x3, #4091, lsl #32
	movk x3, #4093, lsl #48
	str x3, [x9, #1120]
	movz x3, #4099, lsl #0
	movk x3, #4111, lsl #16
	movk x3, #4127, lsl #32
	movk x3, #4129, lsl #48
	str x3, [x9, #1128]
	movz x3, #4133, lsl #0
	movk x3, #4139, lsl #16
	movk x3, #4153, lsl #32
	movk x3, #4157, lsl #48
	str x3, [x9, #1136]
	movz x3, #4159, lsl #0
	movk x3, #4177, lsl #16
	movk x3, #4201, lsl #32
	movk x3, #4211, lsl #48
	str x3, [x9, #1144]
	movz x3, #4217, lsl #0
	movk x3, #4219, lsl #16
	movk x3, #4229, lsl #32
	movk x3, #4231, lsl #48
	str x3, [x9, #1152]
	movz x3, #4241, lsl #0
	movk x3, #4243, lsl #16
	movk x3, #4253, lsl #32
	movk x3, #4259, lsl #48
	str x3, [x9, #1160]
	movz x3, #4261, lsl #0
	movk x3, #4271, lsl #16
	movk x3, #4273, lsl #32
	movk x3, #4283, lsl #48
	str x3, [x9, #1168]
	movz x3, #4289, lsl #0
	movk x3, #4297, lsl #16
	movk x3, #4327, lsl #32
	movk x3, #4337, lsl #48
	str x3, [x9, #1176]
	movz x3, #4339, lsl #0
	movk x3, #4349, lsl #16
	movk x3, #4357, lsl #32
	movk x3, #4363, lsl #48
	str x3, [x9, #1184]
	movz x3, #4373, lsl #0
	movk x3, #4391, lsl #16
	movk x3, #4397, lsl #32
	movk x3, #4409, lsl #48
	str x3, [x9, #1192]
	movz x3, #4421, lsl #0
	movk x3, #4423, lsl #16
	movk x3, #4441, lsl #32
	movk x3, #4447, lsl #48
	str x3, [x9, #1200]
	movz x3, #4451, lsl #0
	movk x3, #4457, lsl #16
	movk x3, #4463, lsl #32
	movk x3, #4481, lsl #48
	str x3, [x9, #1208]
	movz x3, #4483, lsl #0
	movk x3, #4493, lsl #16
	movk x3, #4507, lsl #32
	movk x3, #4513, lsl #48
	str x3, [x9, #1216]
	movz x3, #4517, lsl #0
	movk x3, #4519, lsl #16
	movk x3, #4523, lsl #32
	movk x3, #4547, lsl #48
	str x3, [x9, #1224]
	movz x3, #4549, lsl #0
	movk x3, #4561, lsl #16
	movk x3, #4567, lsl #32
	movk x3, #4583, lsl #48
	str x3, [x9, #1232]
	movz x3, #4591, lsl #0
	movk x3, #4597, lsl #16
	movk x3, #4603, lsl #32
	movk x3, #4621, lsl #48
	str x3, [x9, #1240]
	movz x3, #4637, lsl #0
	movk x3, #4639, lsl #16
	movk x3, #4643, lsl #32
	movk x3, #4649, lsl #48
	str x3, [x9, #1248]
	movz x3, #4651, lsl #0
	movk x3, #4657, lsl #16
	movk x3, #4663, lsl #32
	movk x3, #4673, lsl #48
	str x3, [x9, #1256]
	movz x3, #4679, lsl #0
	movk x3, #4691, lsl #16
	movk x3, #4703, lsl #32
	movk x3, #4721, lsl #48
	str x3, [x9, #1264]
	movz x3, #4723, lsl #0
	movk x3, #4729, lsl #16
	movk x3, #4733, lsl #32
	movk x3, #4751, lsl #48
	str x3, [x9, #1272]
	movz x3, #4759, lsl #0
	movk x3, #4783, lsl #16
	movk x3, #4787, lsl #32
	movk x3, #4789, lsl #48
	str x3, [x9, #1280]
	movz x3, #4793, lsl #0
	movk x3, #4799, lsl #16
	movk x3, #4801, lsl #32
	movk x3, #4813, lsl #48
	str x3, [x9, #1288]
	movz x3, #4817, lsl #0
	movk x3, #4831, lsl #16
	movk x3, #4861, lsl #32
	movk x3, #4871, lsl #48
	str x3, [x9, #1296]
	movz x3, #4877, lsl #0
	movk x3, #4889, lsl #16
	movk x3, #4903, lsl #32
	movk x3, #4909, lsl #48
	str x3, [x9, #1304]
	movz x3, #4919, lsl #0
	movk x3, #4931, lsl #16
	movk x3, #4933, lsl #32
	movk x3, #4937, lsl #48
	str x3, [x9, #1312]
	movz x3, #4943, lsl #0
	movk x3, #4951, lsl #16
	movk x3, #4957, lsl #32
	movk x3, #4967, lsl #48
	str x3, [x9, #1320]
	movz x3, #4969, lsl #0
	movk x3, #4973, lsl #16
	movk x3, #4987, lsl #32
	movk x3, #4993, lsl #48
	str x3, [x9, #1328]
	movz x3, #4999, lsl #0
	movk x3, #5003, lsl #16
	movk x3, #5009, lsl #32
	movk x3, #5011, lsl #48
	str x3, [x9, #1336]
	movz x3, #5021, lsl #0
	movk x3, #5023, lsl #16
	movk x3, #5039, lsl #32
	movk x3, #5051, lsl #48
	str x3, [x9, #1344]
	movz x3, #5059, lsl #0
	movk x3, #5077, lsl #16
	movk x3, #5081, lsl #32
	movk x3, #5087, lsl #48
	str x3, [x9, #1352]
	movz x3, #5099, lsl #0
	movk x3, #5101, lsl #16
	movk x3, #5107, lsl #32
	movk x3, #5113, lsl #48
	str x3, [x9, #1360]
	movz x3, #5119, lsl #0
	movk x3, #5147, lsl #16
	movk x3, #5153, lsl #32
	movk x3, #5167, lsl #48
	str x3, [x9, #1368]
	movz x3, #5171, lsl #0
	movk x3, #5179, lsl #16
	movk x3, #5189, lsl #32
	movk x3, #5197, lsl #48
	str x3, [x9, #1376]
	movz x3, #5209, lsl #0
	movk x3, #5227, lsl #16
	movk x3, #5231, lsl #32
	movk x3, #5233, lsl #48
	str x3, [x9, #1384]
	movz x3, #5237, lsl #0
	movk x3, #5261, lsl #16
	movk x3, #5273, lsl #32
	movk x3, #5279, lsl #48
	str x3, [x9, #1392]
	movz x3, #5281, lsl #0
	movk x3, #5297, lsl #16
	movk x3, #5303, lsl #32
	movk x3, #5309, lsl #48
	str x3, [x9, #1400]
	movz x3, #5323, lsl #0
	movk x3, #5333, lsl #16
	movk x3, #5347, lsl #32
	movk x3, #5351, lsl #48
	str x3, [x9, #1408]
	movz x3, #5381, lsl #0
	movk x3, #5387, lsl #16
	movk x3, #5393, lsl #32
	movk x3, #5399, lsl #48
	str x3, [x9, #1416]
	movz x3, #5407, lsl #0
	movk x3, #5413, lsl #16
	movk x3, #5417, lsl #32
	movk x3, #5419, lsl #48
	str x3, [x9, #1424]
	movz x3, #5431, lsl #0
	movk x3, #5437, lsl #16
	movk x3, #5441, lsl #32
	movk x3, #5443, lsl #48
	str x3, [x9, #1432]
	movz x3, #5449, lsl #0
	movk x3, #5471, lsl #16
	movk x3, #5477, lsl #32
	movk x3, #5479, lsl #48
	str x3, [x9, #1440]
	movz x3, #5483, lsl #0
	movk x3, #5501, lsl #16
	movk x3, #5503, lsl #32
	movk x3, #5507, lsl #48
	str x3, [x9, #1448]
	movz x3, #5519, lsl #0
	movk x3, #5521, lsl #16
	movk x3, #5527, lsl #32
	movk x3, #5531, lsl #48
	str x3, [x9, #1456]
	movz x3, #5557, lsl #0
	movk x3, #5563, lsl #16
	movk x3, #5569, lsl #32
	movk x3, #5573, lsl #48
	str x3, [x9, #1464]
	movz x3, #5581, lsl #0
	movk x3, #5591, lsl #16
	movk x3, #5623, lsl #32
	movk x3, #5639, lsl #48
	str x3, [x9, #1472]
	movz x3, #5641, lsl #0
	movk x3, #5647, lsl #16
	movk x3, #5651, lsl #32
	movk x3, #5653, lsl #48
	str x3, [x9, #1480]
	movz x3, #5657, lsl #0
	movk x3, #5659, lsl #16
	movk x3, #5669, lsl #32
	movk x3, #5683, lsl #48
	str x3, [x9, #1488]
	movz x3, #5689, lsl #0
	movk x3, #5693, lsl #16
	movk x3, #5701, lsl #32
	movk x3, #5711, lsl #48
	str x3, [x9, #1496]
	movz x3, #5717, lsl #0
	movk x3, #5737, lsl #16
	movk x3, #5741, lsl #32
	movk x3, #5743, lsl #48
	str x3, [x9, #1504]
	movz x3, #5749, lsl #0
	movk x3, #5779, lsl #16
	movk x3, #5783, lsl #32
	movk x3, #5791, lsl #48
	str x3, [x9, #1512]
	movz x3, #5801, lsl #0
	movk x3, #5807, lsl #16
	movk x3, #5813, lsl #32
	movk x3, #5821, lsl #48
	str x3, [x9, #1520]
	movz x3, #5827, lsl #0
	movk x3, #5839, lsl #16
	movk x3, #5843, lsl #32
	movk x3, #5849, lsl #48
	str x3, [x9, #1528]
	movz x3, #5851, lsl #0
	movk x3, #5857, lsl #16
	movk x3, #5861, lsl #32
	movk x3, #5867, lsl #48
	str x3, [x9, #1536]
	movz x3, #5869, lsl #0
	movk x3, #5879, lsl #16
	movk x3, #5881, lsl #32
	movk x3, #5897, lsl #48
	str x3, [x9, #1544]
	movz x3, #5903, lsl #0
	movk x3, #5923, lsl #16
	movk x3, #5927, lsl #32
	movk x3, #5939, lsl #48
	str x3, [x9, #1552]
	movz x3, #5953, lsl #0
	movk x3, #5981, lsl #16
	movk x3, #5987, lsl #32
	movk x3, #6007, lsl #48
	str x3, [x9, #1560]
	movz x3, #6011, lsl #0
	movk x3, #6029, lsl #16
	movk x3, #6037, lsl #32
	movk x3, #6043, lsl #48
	str x3, [x9, #1568]
	movz x3, #6047, lsl #0
	movk x3, #6053, lsl #16
	movk x3, #6067, lsl #32
	movk x3, #6073, lsl #48
	str x3, [x9, #1576]
	movz x3, #6079, lsl #0
	movk x3, #6089, lsl #16
	movk x3, #6091, lsl #32
	movk x3, #6101, lsl #48
	str x3, [x9, #1584]
	movz x3, #6113, lsl #0
	movk x3, #6121, lsl #16
	movk x3, #6131, lsl #32
	movk x3, #6133, lsl #48
	str x3, [x9, #1592]
	movz x3, #6143, lsl #0
	movk x3, #6151, lsl #16
	movk x3, #6163, lsl #32
	movk x3, #6173, lsl #48
	str x3, [x9, #1600]
	movz x3, #6197, lsl #0
	movk x3, #6199, lsl #16
	movk x3, #6203, lsl #32
	movk x3, #6211, lsl #48
	str x3, [x9, #1608]
	movz x3, #6217, lsl #0
	movk x3, #6221, lsl #16
	movk x3, #6229, lsl #32
	movk x3, #6247, lsl #48
	str x3, [x9, #1616]
	movz x3, #6257, lsl #0
	movk x3, #6263, lsl #16
	movk x3, #6269, lsl #32
	movk x3, #6271, lsl #48
	str x3, [x9, #1624]
	movz x3, #6277, lsl #0
	movk x3, #6287, lsl #16
	movk x3, #6299, lsl #32
	movk x3, #6301, lsl #48
	str x3, [x9, #1632]
	movz x3, #6311, lsl #0
	movk x3, #6317, lsl #16
	movk x3, #6323, lsl #32
	movk x3, #6329, lsl #48
	str x3, [x9, #1640]
	movz x3, #6337, lsl #0
	movk x3, #6343, lsl #16
	movk x3, #6353, lsl #32
	movk x3, #6359, lsl #48
	str x3, [x9, #1648]
	movz x3, #6361, lsl #0
	movk x3, #6367, lsl #16
	movk x3, #6373, lsl #32
	movk x3, #6379, lsl #48
	str x3, [x9, #1656]
	movz x3, #6389, lsl #0
	movk x3, #6397, lsl #16
	movk x3, #6421, lsl #32
	movk x3, #6427, lsl #48
	str x3, [x9, #1664]
	movz x3, #6449, lsl #0
	movk x3, #6451, lsl #16
	movk x3, #6469, lsl #32
	movk x3, #6473, lsl #48
	str x3, [x9, #1672]
	movz x3, #6481, lsl #0
	movk x3, #6491, lsl #16
	movk x3, #6521, lsl #32
	movk x3, #6529, lsl #48
	str x3, [x9, #1680]
	movz x3, #6547, lsl #0
	movk x3, #6551, lsl #16
	movk x3, #6553, lsl #32
	movk x3, #6563, lsl #48
	str x3, [x9, #1688]
	movz x3, #6569, lsl #0
	movk x3, #6571, lsl #16
	movk x3, #6577, lsl #32
	movk x3, #6581, lsl #48
	str x3, [x9, #1696]
	movz x3, #6599, lsl #0
	movk x3, #6607, lsl #16
	movk x3, #6619, lsl #32
	movk x3, #6637, lsl #48
	str x3, [x9, #1704]
	movz x3, #6653, lsl #0
	movk x3, #6659, lsl #16
	movk x3, #6661, lsl #32
	movk x3, #6673, lsl #48
	str x3, [x9, #1712]
	movz x3, #6679, lsl #0
	movk x3, #6689, lsl #16
	movk x3, #6691, lsl #32
	movk x3, #6701, lsl #48
	str x3, [x9, #1720]
	movz x3, #6703, lsl #0
	movk x3, #6709, lsl #16
	movk x3, #6719, lsl #32
	movk x3, #6733, lsl #48
	str x3, [x9, #1728]
	movz x3, #6737, lsl #0
	movk x3, #6761, lsl #16
	movk x3, #6763, lsl #32
	movk x3, #6779, lsl #48
	str x3, [x9, #1736]
	movz x3, #6781, lsl #0
	movk x3, #6791, lsl #16
	movk x3, #6793, lsl #32
	movk x3, #6803, lsl #48
	str x3, [x9, #1744]
	movz x3, #6823, lsl #0
	movk x3, #6827, lsl #16
	movk x3, #6829, lsl #32
	movk x3, #6833, lsl #48
	str x3, [x9, #1752]
	movz x3, #6841, lsl #0
	movk x3, #6857, lsl #16
	movk x3, #6863, lsl #32
	movk x3, #6869, lsl #48
	str x3, [x9, #1760]
	movz x3, #6871, lsl #0
	movk x3, #6883, lsl #16
	movk x3, #6899, lsl #32
	movk x3, #6907, lsl #48
	str x3, [x9, #1768]
	movz x3, #6911, lsl #0
	movk x3, #6917, lsl #16
	movk x3, #6947, lsl #32
	movk x3, #6949, lsl #48
	str x3, [x9, #1776]
	movz x3, #6959, lsl #0
	movk x3, #6961, lsl #16
	movk x3, #6967, lsl #32
	movk x3, #6971, lsl #48
	str x3, [x9, #1784]
	movz x3, #6977, lsl #0
	movk x3, #6983, lsl #16
	movk x3, #6991, lsl #32
	movk x3, #6997, lsl #48
	str x3, [x9, #1792]
	movz x3, #7001, lsl #0
	movk x3, #7013, lsl #16
	movk x3, #7019, lsl #32
	movk x3, #7027, lsl #48
	str x3, [x9, #1800]
	movz x3, #7039, lsl #0
	movk x3, #7043, lsl #16
	movk x3, #7057, lsl #32
	movk x3, #7069, lsl #48
	str x3, [x9, #1808]
	movz x3, #7079, lsl #0
	movk x3, #7103, lsl #16
	movk x3, #7109, lsl #32
	movk x3, #7121, lsl #48
	str x3, [x9, #1816]
	movz x3, #7127, lsl #0
	movk x3, #7129, lsl #16
	movk x3, #7151, lsl #32
	movk x3, #7159, lsl #48
	str x3, [x9, #1824]
	movz x3, #7177, lsl #0
	movk x3, #7187, lsl #16
	movk x3, #7193, lsl #32
	movk x3, #7207, lsl #48
	str x3, [x9, #1832]
	movz x3, #7211, lsl #0
	movk x3, #7213, lsl #16
	movk x3, #7219, lsl #32
	movk x3, #7229, lsl #48
	str x3, [x9, #1840]
	movz x3, #7237, lsl #0
	movk x3, #7243, lsl #16
	movk x3, #7247, lsl #32
	movk x3, #7253, lsl #48
	str x3, [x9, #1848]
	movz x3, #7283, lsl #0
	movk x3, #7297, lsl #16
	movk x3, #7307, lsl #32
	movk x3, #7309, lsl #48
	str x3, [x9, #1856]
	movz x3, #7321, lsl #0
	movk x3, #7331, lsl #16
	movk x3, #7333, lsl #32
	movk x3, #7349, lsl #48
	str x3, [x9, #1864]
	movz x3, #7351, lsl #0
	movk x3, #7369, lsl #16
	movk x3, #7393, lsl #32
	movk x3, #7411, lsl #48
	str x3, [x9, #1872]
	movz x3, #7417, lsl #0
	movk x3, #7433, lsl #16
	movk x3, #7451, lsl #32
	movk x3, #7457, lsl #48
	str x3, [x9, #1880]
	movz x3, #7459, lsl #0
	movk x3, #7477, lsl #16
	movk x3, #7481, lsl #32
	movk x3, #7487, lsl #48
	str x3, [x9, #1888]
	movz x3, #7489, lsl #0
	movk x3, #7499, lsl #16
	movk x3, #7507, lsl #32
	movk x3, #7517, lsl #48
	str x3, [x9, #1896]
	movz x3, #7523, lsl #0
	movk x3, #7529, lsl #16
	movk x3, #7537, lsl #32
	movk x3, #7541, lsl #48
	str x3, [x9, #1904]
	movz x3, #7547, lsl #0
	movk x3, #7549, lsl #16
	movk x3, #7559, lsl #32
	movk x3, #7561, lsl #48
	str x3, [x9, #1912]
	movz x3, #7573, lsl #0
	movk x3, #7577, lsl #16
	movk x3, #7583, lsl #32
	movk x3, #7589, lsl #48
	str x3, [x9, #1920]
	movz x3, #7591, lsl #0
	movk x3, #7603, lsl #16
	movk x3, #7607, lsl #32
	movk x3, #7621, lsl #48
	str x3, [x9, #1928]
	movz x3, #7639, lsl #0
	movk x3, #7643, lsl #16
	movk x3, #7649, lsl #32
	movk x3, #7669, lsl #48
	str x3, [x9, #1936]
	movz x3, #7673, lsl #0
	movk x3, #7681, lsl #16
	movk x3, #7687, lsl #32
	movk x3, #7691, lsl #48
	str x3, [x9, #1944]
	movz x3, #7699, lsl #0
	movk x3, #7703, lsl #16
	movk x3, #7717, lsl #32
	movk x3, #7723, lsl #48
	str x3, [x9, #1952]
	movz x3, #7727, lsl #0
	movk x3, #7741, lsl #16
	movk x3, #7753, lsl #32
	movk x3, #7757, lsl #48
	str x3, [x9, #1960]
	movz x3, #7759, lsl #0
	movk x3, #7789, lsl #16
	movk x3, #7793, lsl #32
	movk x3, #7817, lsl #48
	str x3, [x9, #1968]
	movz x3, #7823, lsl #0
	movk x3, #7829, lsl #16
	movk x3, #7841, lsl #32
	movk x3, #7853, lsl #48
	str x3, [x9, #1976]
	movz x3, #7867, lsl #0
	movk x3, #7873, lsl #16
	movk x3, #7877, lsl #32
	movk x3, #7879, lsl #48
	str x3, [x9, #1984]
	movz x3, #7883, lsl #0
	movk x3, #7901, lsl #16
	movk x3, #7907, lsl #32
	movk x3, #7919, lsl #48
	str x3, [x9, #1992]
	movz x3, #7927, lsl #0
	movk x3, #7933, lsl #16
	movk x3, #7937, lsl #32
	movk x3, #7949, lsl #48
	str x3, [x9, #2000]
	movz x3, #7951, lsl #0
	movk x3, #7963, lsl #16
	movk x3, #7993, lsl #32
	movk x3, #8009, lsl #48
	str x3, [x9, #2008]
	movz x3, #8011, lsl #0
	movk x3, #8017, lsl #16
	movk x3, #8039, lsl #32
	movk x3, #8053, lsl #48
	str x3, [x9, #2016]
	movz x3, #8059, lsl #0
	movk x3, #8069, lsl #16
	movk x3, #8081, lsl #32
	movk x3, #8087, lsl #48
	str x3, [x9, #2024]
	movz x3, #8089, lsl #0
	movk x3, #8093, lsl #16
	movk x3, #8101, lsl #32
	movk x3, #8111, lsl #48
	str x3, [x9, #2032]
	movz x3, #8117, lsl #0
	movk x3, #8123, lsl #16
	movk x3, #8147, lsl #32
	movk x3, #8161, lsl #48
	str x3, [x9, #2040]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	movz x10, #13, lsl #0
	movz x1, #0, lsl #0
	movz x7, #0, lsl #0
	sub x8, x7, #1
212:
	ldr x17, [x9, #0]
	add x9, x9, #8
	add x3, x17, #0
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
213:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 213b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #16
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
214:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 214b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #32
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
215:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 215b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #48
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
216:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 216b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	sub x10, x10, #1
	cbnz x10, 212b
	ldr x17, [x9, #0]
	add x3, x17, #0
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
217:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 217b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	ldr x5, [x0, #32]
	orr x5, x5, x1
	str x5, [x0, #32]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x17, x16, #0
	movz x7, #0, lsl #0
	sub x15, x7, #1
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
218:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 218b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x5, [x0, #32]
	ldr x3, [x16, #0]
	movz x4, #1, lsl #0
	and x3, x3, x4
	eor x3, x3, x4
	orr x5, x5, x3
	str x5, [x0, #32]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	movz x10, #13, lsl #0
	movz x1, #0, lsl #0
	movz x7, #0, lsl #0
	sub x8, x7, #1
219:
	ldr x17, [x9, #0]
	add x9, x9, #8
	add x3, x17, #0
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
220:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 220b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #16
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
221:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 221b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #32
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
222:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 222b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #48
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
223:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 223b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	sub x10, x10, #1
	cbnz x10, 219b
	ldr x17, [x9, #0]
	add x3, x17, #0
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
224:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 224b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	ldr x5, [x0, #32]
	orr x5, x5, x1
	str x5, [x0, #32]
	ldr x5, [x0, #32]
	cbz x5, 225f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 226f
225:
	ldr x3, [x0, #152]
	sub x3, x3, #1
	add x4, x3, #7
	lsr x4, x4, #3
	str x4, [x0, #144]
	add x6, x3, #63
	lsr x6, x6, #6
	lsl x6, x6, #6
	add x8, x3, #64
	sub x6, x8, x6
	movz x5, #64, lsl #0
	movz x9, #128, lsl #0
	movz x8, #2049, lsl #0
	subs x8, x3, x8
	csel x5, x9, x5, hs
	str x5, [x0, #0]
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
	add x3, x12, #2
	lsl x3, x3, #3
	add x4, x0, #256
	str x4, [x0, #64]
	add x4, x4, x3
	str x4, [x0, #72]
	add x4, x4, x3
	str x4, [x0, #80]
	add x4, x4, x3
	str x4, [x0, #88]
	add x4, x4, x3
	str x4, [x0, #96]
	add x4, x4, x3
	str x4, [x0, #104]
	add x4, x4, x3
	str x4, [x0, #112]
	add x4, x4, x3
	str x4, [x0, #120]
	add x4, x4, x3
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	movz x9, #0, lsl #0
227:
	add x9, x9, x9
	add x9, x9, #1
	sub x6, x6, #1
	cbnz x6, 227b
	str x9, [x0, #16]
	ldr x8, [x0, #64]
	ldr x3, [x8, #0]
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	str x15, [x0, #56]
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
228:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 228b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 229f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
231:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 231b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
232:
	lsr x3, x2, #63
	lsl x2, x2, #1
	orr x2, x2, x4
	subs x15, x2, x5
	adc x16, x7, x7
	orr x16, x16, x3
	tst x16, x16
	csel x2, x15, x2, ne
	add x10, x10, x10
	add x10, x10, x16
	sub x13, x13, #1
	cbnz x13, 232b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
233:
	ldr x8, [x0, #80]
	ldr x9, [x0, #64]
	ldr x11, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #8
	add x14, x9, x13
	ldr x5, [x14, #0]
	add x16, x11, x13
	ldr x2, [x16, #0]
	sub x16, x16, #8
	ldr x3, [x16, #0]
	sub x4, x5, x2
	ldr x17, [x6, #0]
	mul x13, x17, x2
	umulh x14, x17, x2
	adds x13, x13, x3
	adc x14, x14, x2
	add x14, x14, #1
	mul x15, x14, x5
	sub x15, x3, x15
	sub x16, x14, #1
	add x17, x15, x5
	subs x3, x13, x15
	csel x14, x16, x14, lo
	csel x15, x17, x15, lo
	subs x3, x15, x5
	adc x14, x14, x7
	movz x16, #0, lsl #0
	sub x16, x16, #1
	tst x4, x4
	csel x1, x16, x14, eq
	add x16, x8, #0
	add x14, x12, #2
234:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 234b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
235:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 235b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
236:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 236b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
237:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 237b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
238:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 238b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
239:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 239b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 233b
	b 230f
229:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 240f
242:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 242b
	b 241f
240:
241:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
243:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 243b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
244:
	ldr x5, [x0, #96]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
245:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 245b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
246:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 246b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
247:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 247b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 244b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
248:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 248b
230:
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
249:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 249b
	add x13, x12, #0
250:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
251:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 251b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
252:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 252b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 250b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
253:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 253b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
254:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 254b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
255:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 255b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
256:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 256b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x5, [x16, #0]
	movz x4, #1, lsl #0
	eor x5, x5, x4
	add x16, x16, #8
	sub x14, x12, #1
	movz x7, #0, lsl #0
	sub x8, x7, #1
257:
	ldr x3, [x16, #0]
	subs x6, x5, x4
	csel x6, x7, x8, hs
	and x3, x3, x6
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 257b
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	sub x6, x7, x5
	and x6, x6, x5
	lsl x9, x12, #3
	add x9, x10, x9
	str x6, [x9, #0]
	add x15, x8, #0
	add x17, x10, #0
	add x16, x0, #256
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
258:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 258b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #56797, lsl #0
	movk x4, #56797, lsl #16
	movk x4, #56797, lsl #32
	movk x4, #56797, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
259:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 259b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #39321, lsl #0
	movk x4, #39321, lsl #16
	movk x4, #39321, lsl #32
	movk x4, #39321, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
260:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 260b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #4369, lsl #0
	movk x4, #4369, lsl #16
	movk x4, #4369, lsl #32
	movk x4, #4369, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
261:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 261b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x3, #0, lsl #0
	str x3, [x0, #24]
262:
	ldr x3, [x0, #200]
	ldr x4, [x0, #216]
	sub x3, x3, x4
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 263f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
265:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 265b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #192]
	ldr x3, [x0, #216]
	add x1, x1, x3
	ldr x2, [x0, #144]
	add x3, x3, x2
	str x3, [x0, #216]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
266:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 267f
	b 268f
267:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
268:
	cbnz x2, 266b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x5, #0]
	and x3, x3, x4
	str x3, [x5, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	ldr x5, [x16, #0]
	lsr x5, x5, #1
	add x16, x16, #8
	sub x14, x12, #1
269:
	ldr x3, [x16, #0]
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 269b
	movz x7, #0, lsl #0
	sub x8, x7, #1
	movz x4, #1, lsl #0
	subs x3, x5, x4
	csel x9, x8, x7, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
	ldr x3, [x16, #0]
	orr x3, x3, x4
	ldr x4, [x17, #0]
	subs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x12, #1
270:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 270b
	csel x15, x7, x8, hs
	and x9, x9, x15
	cbz x9, 271f
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
273:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 273b
	add x13, x12, #0
274:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
275:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 275b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
276:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 276b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 274b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
277:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 277b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
278:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 278b
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	str x19, [x2, #0]
	str x30, [x2, #8]
	add x19, x0, #0
	ldr x1, [x0, #48]
	add x1, x1, #2
	movz x4, #28, lsl #0
	mul x1, x1, x4
	add x1, x1, #32
	bl {vg_miller_rabin_round}
	add w3, w0, #0
	add x0, x19, #0
	movz x4, #0, lsl #0
	sub x3, x4, x3
	str x3, [x0, #184]
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	ldr x30, [x2, #8]
	ldr x19, [x2, #0]
	ldr x3, [x0, #184]
	cbz x3, 279f
	ldr x3, [x0, #24]
	ldr x4, [x0, #0]
	add x3, x3, #1
	subs x5, x3, x4
	movz x6, #4, lsl #0
	movz x7, #1, lsl #0
	csel x5, x7, x6, hs
	str x3, [x0, #24]
	str x5, [x0, #248]
	b 280f
279:
	movz x3, #2, lsl #0
	str x3, [x0, #248]
280:
	b 272f
271:
	movz x3, #4, lsl #0
	str x3, [x0, #248]
272:
	b 264f
263:
	movz x3, #0, lsl #0
	str x3, [x0, #248]
264:
	ldr x3, [x0, #248]
	sub x3, x3, #4
	cbz x3, 262b
	ldr x3, [x0, #248]
	sub x3, x3, #1
	cbz x3, 281f
	ldr x3, [x0, #248]
	cbz x3, 283f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 284f
283:
	movz x3, #0, lsl #0
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #0, lsl #0
284:
	b 282f
281:
	ldr x3, [x0, #152]
	add x4, x3, #7
	lsr x4, x4, #3
	str x4, [x0, #144]
	add x6, x3, #63
	lsr x6, x6, #6
	lsl x6, x6, #6
	add x8, x3, #64
	sub x6, x8, x6
	movz x5, #64, lsl #0
	movz x9, #128, lsl #0
	movz x8, #2049, lsl #0
	subs x8, x3, x8
	csel x5, x9, x5, hs
	str x5, [x0, #0]
	ldr x3, [x0, #144]
	add x12, x3, #7
	lsr x12, x12, #3
	str x12, [x0, #48]
	add x3, x12, #2
	lsl x3, x3, #3
	add x4, x0, #256
	str x4, [x0, #64]
	add x4, x4, x3
	str x4, [x0, #72]
	add x4, x4, x3
	str x4, [x0, #80]
	add x4, x4, x3
	str x4, [x0, #88]
	add x4, x4, x3
	str x4, [x0, #96]
	add x4, x4, x3
	str x4, [x0, #104]
	add x4, x4, x3
	str x4, [x0, #112]
	add x4, x4, x3
	str x4, [x0, #120]
	add x4, x4, x3
	add x3, x12, #2
	lsl x3, x3, #3
	str x3, [x0, #224]
	movz x7, #0, lsl #0
	sub x4, x7, #1
	str x4, [x0, #176]
	movz x9, #0, lsl #0
285:
	add x9, x9, x9
	add x9, x9, #1
	sub x6, x6, #1
	cbnz x6, 285b
	str x9, [x0, #16]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
286:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 286b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #192]
	ldr x2, [x0, #144]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
287:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 288f
	b 289f
288:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
289:
	cbnz x2, 287b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x16, #0]
	ldr x6, [x5, #0]
	movz x9, #1, lsl #0
	orr x3, x3, x9
	and x6, x6, x4
	lsr x9, x4, #1
	add x9, x9, #1
	orr x6, x6, x9
	str x3, [x16, #0]
	str x6, [x5, #0]
	ldr x8, [x0, #64]
	ldr x3, [x8, #0]
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	str x15, [x0, #56]
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
290:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 290b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 291f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
293:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 293b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
294:
	lsr x3, x2, #63
	lsl x2, x2, #1
	orr x2, x2, x4
	subs x15, x2, x5
	adc x16, x7, x7
	orr x16, x16, x3
	tst x16, x16
	csel x2, x15, x2, ne
	add x10, x10, x10
	add x10, x10, x16
	sub x13, x13, #1
	cbnz x13, 294b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
295:
	ldr x8, [x0, #80]
	ldr x9, [x0, #64]
	ldr x11, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #8
	add x14, x9, x13
	ldr x5, [x14, #0]
	add x16, x11, x13
	ldr x2, [x16, #0]
	sub x16, x16, #8
	ldr x3, [x16, #0]
	sub x4, x5, x2
	ldr x17, [x6, #0]
	mul x13, x17, x2
	umulh x14, x17, x2
	adds x13, x13, x3
	adc x14, x14, x2
	add x14, x14, #1
	mul x15, x14, x5
	sub x15, x3, x15
	sub x16, x14, #1
	add x17, x15, x5
	subs x3, x13, x15
	csel x14, x16, x14, lo
	csel x15, x17, x15, lo
	subs x3, x15, x5
	adc x14, x14, x7
	movz x16, #0, lsl #0
	sub x16, x16, #1
	tst x4, x4
	csel x1, x16, x14, eq
	add x16, x8, #0
	add x14, x12, #2
296:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 296b
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
297:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 297b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
	ldr x3, [x16, #0]
	subs x3, x7, x3
	str x3, [x16, #0]
	add x16, x16, #8
298:
	ldr x4, [x17, #0]
	ldr x3, [x16, #0]
	sbcs x3, x4, x3
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 298b
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
299:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 299b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	lsl x13, x12, #3
	add x13, x8, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
2100:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2100b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x11, #0
	add x14, x12, #0
2101:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2101b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 295b
	b 292f
291:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 2102f
2104:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 2104b
	b 2103f
2102:
2103:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2105:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2105b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
2106:
	ldr x5, [x0, #96]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
2107:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2107b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2108:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2108b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2109:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2109b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2106b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
2110:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 2110b
292:
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2111:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2111b
	add x13, x12, #0
2112:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2113:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2113b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
2114:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2114b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2112b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2115:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2115b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2116:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2116b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
2117:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2117b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
2118:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 2118b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x5, [x16, #0]
	movz x4, #1, lsl #0
	eor x5, x5, x4
	add x16, x16, #8
	sub x14, x12, #1
	movz x7, #0, lsl #0
	sub x8, x7, #1
2119:
	ldr x3, [x16, #0]
	subs x6, x5, x4
	csel x6, x7, x8, hs
	and x3, x3, x6
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2119b
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	sub x6, x7, x5
	and x6, x6, x5
	lsl x9, x12, #3
	add x9, x10, x9
	str x6, [x9, #0]
	add x15, x8, #0
	add x17, x10, #0
	add x16, x0, #256
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2120:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2120b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #56797, lsl #0
	movk x4, #56797, lsl #16
	movk x4, #56797, lsl #32
	movk x4, #56797, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2121:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2121b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #39321, lsl #0
	movk x4, #39321, lsl #16
	movk x4, #39321, lsl #32
	movk x4, #39321, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2122:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2122b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #4369, lsl #0
	movk x4, #4369, lsl #16
	movk x4, #4369, lsl #32
	movk x4, #4369, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
2123:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 2123b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x3, #0, lsl #0
	str x3, [x0, #24]
2124:
	ldr x3, [x0, #200]
	ldr x4, [x0, #216]
	sub x3, x3, x4
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 2125f
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2127:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2127b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #192]
	ldr x3, [x0, #216]
	add x1, x1, x3
	ldr x2, [x0, #144]
	add x3, x3, x2
	str x3, [x0, #216]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
2128:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 2129f
	b 2130f
2129:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
2130:
	cbnz x2, 2128b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	lsl x5, x12, #3
	add x5, x16, x5
	sub x5, x5, #8
	ldr x4, [x0, #16]
	ldr x3, [x5, #0]
	and x3, x3, x4
	str x3, [x5, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	ldr x5, [x16, #0]
	lsr x5, x5, #1
	add x16, x16, #8
	sub x14, x12, #1
2131:
	ldr x3, [x16, #0]
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2131b
	movz x7, #0, lsl #0
	sub x8, x7, #1
	movz x4, #1, lsl #0
	subs x3, x5, x4
	csel x9, x8, x7, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
	ldr x3, [x16, #0]
	orr x3, x3, x4
	ldr x4, [x17, #0]
	subs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x12, #1
2132:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2132b
	csel x15, x7, x8, hs
	and x9, x9, x15
	cbz x9, 2133f
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
2135:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 2135b
	add x13, x12, #0
2136:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
2137:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2137b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
2138:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 2138b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 2136b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
2139:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 2139b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
2140:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 2140b
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	str x19, [x2, #0]
	str x30, [x2, #8]
	add x19, x0, #0
	ldr x1, [x0, #48]
	add x1, x1, #2
	movz x4, #28, lsl #0
	mul x1, x1, x4
	add x1, x1, #32
	bl {vg_miller_rabin_round}
	add w3, w0, #0
	add x0, x19, #0
	movz x4, #0, lsl #0
	sub x3, x4, x3
	str x3, [x0, #184]
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	ldr x30, [x2, #8]
	ldr x19, [x2, #0]
	ldr x3, [x0, #184]
	cbz x3, 2141f
	ldr x3, [x0, #24]
	ldr x4, [x0, #0]
	add x3, x3, #1
	subs x5, x3, x4
	movz x6, #4, lsl #0
	movz x7, #1, lsl #0
	csel x5, x7, x6, hs
	str x3, [x0, #24]
	str x5, [x0, #248]
	b 2142f
2141:
	movz x3, #2, lsl #0
	str x3, [x0, #248]
2142:
	b 2134f
2133:
	movz x3, #4, lsl #0
	str x3, [x0, #248]
2134:
	b 2126f
2125:
	movz x3, #0, lsl #0
	str x3, [x0, #248]
2126:
	ldr x3, [x0, #248]
	sub x3, x3, #4
	cbz x3, 2124b
	ldr x3, [x0, #248]
	cbz x3, 2143f
	sub x3, x3, #1
	cbz x3, 2145f
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #2, lsl #0
	b 2146f
2145:
	ldr x3, [x0, #216]
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #128]
	ldr x9, [x0, #144]
	add x1, x1, x9
	ldr x15, [x0, #176]
	movz x2, #0, lsl #0
	movz x6, #7, lsl #0
2147:
	and x5, x2, x6
	cbz x5, 2148f
	b 2149f
2148:
	add x5, x8, x2
	ldr x3, [x5, #0]
	and x3, x3, x15
2149:
	sub x1, x1, #1
	strb w3, [x1, #0]
	lsr x3, x3, #8
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 2147b
	movz x0, #1, lsl #0
2146:
	b 2144f
2143:
	movz x3, #0, lsl #0
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #0, lsl #0
2144:
282:
226:
211:
	b 22f
21:
	movz x3, #0, lsl #0
	ldr x2, [x0, #136]
	str x3, [x2, #0]
	movz x0, #0, lsl #0
22:
	ret
	.p2align 6
