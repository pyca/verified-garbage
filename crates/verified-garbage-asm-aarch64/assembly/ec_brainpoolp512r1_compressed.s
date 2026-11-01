// The functions of `src/ec_brainpoolp512r1_compressed.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp512r1_compress_public_key:
	add x4, x2, #0
	add x6, x1, #0
	add x3, x1, #1
	add x1, x3, #0
	add x2, x3, #0
	str x19, [x4, #0]
	str x20, [x4, #8]
	str x21, [x4, #16]
	str x22, [x4, #24]
	str x23, [x4, #32]
	str x24, [x4, #40]
	str x25, [x4, #48]
	str x30, [x4, #56]
	add x20, x0, #0
	add x0, x4, #0
	ldr x5, [x3, #56]
	rev x5, x5
	str x5, [x0, #2048]
	ldr x5, [x3, #48]
	rev x5, x5
	str x5, [x0, #2056]
	ldr x5, [x3, #40]
	rev x5, x5
	str x5, [x0, #2064]
	ldr x5, [x3, #32]
	rev x5, x5
	str x5, [x0, #2072]
	ldr x5, [x3, #24]
	rev x5, x5
	str x5, [x0, #2080]
	ldr x5, [x3, #16]
	rev x5, x5
	str x5, [x0, #2088]
	ldr x5, [x3, #8]
	rev x5, x5
	str x5, [x0, #2096]
	ldr x5, [x3, #0]
	rev x5, x5
	str x5, [x0, #2104]
	ldr x5, [x1, #56]
	rev x5, x5
	str x5, [x0, #2112]
	ldr x5, [x1, #48]
	rev x5, x5
	str x5, [x0, #2120]
	ldr x5, [x1, #40]
	rev x5, x5
	str x5, [x0, #2128]
	ldr x5, [x1, #32]
	rev x5, x5
	str x5, [x0, #2136]
	ldr x5, [x1, #24]
	rev x5, x5
	str x5, [x0, #2144]
	ldr x5, [x1, #16]
	rev x5, x5
	str x5, [x0, #2152]
	ldr x5, [x1, #8]
	rev x5, x5
	str x5, [x0, #2160]
	ldr x5, [x1, #0]
	rev x5, x5
	str x5, [x0, #2168]
	ldr x5, [x2, #56]
	rev x5, x5
	str x5, [x0, #2176]
	ldr x5, [x2, #48]
	rev x5, x5
	str x5, [x0, #2184]
	ldr x5, [x2, #40]
	rev x5, x5
	str x5, [x0, #2192]
	ldr x5, [x2, #32]
	rev x5, x5
	str x5, [x0, #2200]
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #2208]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #2216]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #2224]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #2232]
	movz x1, #18675, lsl #0
	movk x1, #22586, lsl #16
	movk x1, #24662, lsl #32
	movk x1, #10410, lsl #48
	str x1, [x0, #64]
	movz x1, #50821, lsl #0
	movk x1, #11650, lsl #16
	movk x1, #65327, lsl #32
	movk x1, #10369, lsl #48
	str x1, [x0, #72]
	movz x1, #32998, lsl #0
	movk x1, #59043, lsl #16
	movk x1, #41258, lsl #32
	movk x1, #44749, lsl #48
	str x1, [x0, #80]
	movz x1, #26690, lsl #0
	movk x1, #39878, lsl #16
	movk x1, #39680, lsl #32
	movk x1, #32077, lsl #48
	str x1, [x0, #88]
	movz x1, #2161, lsl #0
	movk x1, #28723, lsl #16
	movk x1, #40138, lsl #32
	movk x1, #54883, lsl #48
	str x1, [x0, #96]
	movz x1, #53774, lsl #0
	movk x1, #46025, lsl #16
	movk x1, #36275, lsl #32
	movk x1, #52016, lsl #48
	str x1, [x0, #104]
	movz x1, #64519, lsl #0
	movk x1, #13257, lsl #16
	movk x1, #59054, lsl #32
	movk x1, #16340, lsl #48
	str x1, [x0, #112]
	movz x1, #50315, lsl #0
	movk x1, #56297, lsl #16
	movk x1, #40376, lsl #32
	movk x1, #43741, lsl #48
	str x1, [x0, #120]
	movz x1, #105, lsl #0
	movk x1, #40105, lsl #16
	movk x1, #38530, lsl #32
	movk x1, #46471, lsl #48
	str x1, [x0, #128]
	movz x1, #56029, lsl #0
	movk x1, #2141, lsl #16
	movk x1, #54145, lsl #32
	movk x1, #7601, lsl #48
	str x1, [x0, #136]
	movz x1, #4167, lsl #0
	movk x1, #32684, lsl #16
	movk x1, #24857, lsl #32
	movk x1, #16774, lsl #48
	str x1, [x0, #144]
	movz x1, #9753, lsl #0
	movk x1, #19625, lsl #16
	movk x1, #23617, lsl #32
	movk x1, #21822, lsl #48
	str x1, [x0, #152]
	movz x1, #2160, lsl #0
	movk x1, #28723, lsl #16
	movk x1, #40138, lsl #32
	movk x1, #54883, lsl #48
	str x1, [x0, #160]
	movz x1, #53774, lsl #0
	movk x1, #46025, lsl #16
	movk x1, #36275, lsl #32
	movk x1, #52016, lsl #48
	str x1, [x0, #168]
	movz x1, #64519, lsl #0
	movk x1, #13257, lsl #16
	movk x1, #59054, lsl #32
	movk x1, #16340, lsl #48
	str x1, [x0, #176]
	movz x1, #50315, lsl #0
	movk x1, #56297, lsl #16
	movk x1, #40376, lsl #32
	movk x1, #43741, lsl #48
	str x1, [x0, #184]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #256]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #280]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #288]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #296]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #304]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #312]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #320]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #336]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #344]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #352]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #368]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #376]
	movz x1, #46861, lsl #0
	movk x1, #42949, lsl #16
	movk x1, #40873, lsl #32
	movk x1, #55125, lsl #48
	str x1, [x0, #384]
	movz x1, #14714, lsl #0
	movk x1, #53885, lsl #16
	movk x1, #208, lsl #32
	movk x1, #55166, lsl #48
	str x1, [x0, #392]
	movz x1, #32537, lsl #0
	movk x1, #6492, lsl #16
	movk x1, #24277, lsl #32
	movk x1, #20786, lsl #48
	str x1, [x0, #400]
	movz x1, #38845, lsl #0
	movk x1, #25657, lsl #16
	movk x1, #25855, lsl #32
	movk x1, #33458, lsl #48
	str x1, [x0, #408]
	movz x1, #63374, lsl #0
	movk x1, #36812, lsl #16
	movk x1, #25397, lsl #32
	movk x1, #10652, lsl #48
	str x1, [x0, #416]
	movz x1, #11761, lsl #0
	movk x1, #19510, lsl #16
	movk x1, #29260, lsl #32
	movk x1, #13519, lsl #48
	str x1, [x0, #424]
	movz x1, #1016, lsl #0
	movk x1, #52278, lsl #16
	movk x1, #6481, lsl #32
	movk x1, #49195, lsl #48
	str x1, [x0, #432]
	movz x1, #15220, lsl #0
	movk x1, #9238, lsl #16
	movk x1, #25159, lsl #32
	movk x1, #21794, lsl #48
	str x1, [x0, #440]
	movz x1, #50246, lsl #0
	movk x1, #59920, lsl #16
	movk x1, #35380, lsl #32
	movk x1, #55839, lsl #48
	str x1, [x0, #448]
	movz x1, #53891, lsl #0
	movk x1, #44967, lsl #16
	movk x1, #38269, lsl #32
	movk x1, #5348, lsl #48
	str x1, [x0, #456]
	movz x1, #48043, lsl #0
	movk x1, #18037, lsl #16
	movk x1, #19314, lsl #32
	movk x1, #16560, lsl #48
	str x1, [x0, #464]
	movz x1, #34815, lsl #0
	movk x1, #40558, lsl #16
	movk x1, #273, lsl #32
	movk x1, #53135, lsl #48
	str x1, [x0, #472]
	movz x1, #53703, lsl #0
	movk x1, #16256, lsl #16
	movk x1, #12488, lsl #32
	movk x1, #42476, lsl #48
	str x1, [x0, #480]
	movz x1, #34680, lsl #0
	movk x1, #62494, lsl #16
	movk x1, #3929, lsl #32
	movk x1, #6189, lsl #48
	str x1, [x0, #488]
	movz x1, #34060, lsl #0
	movk x1, #58064, lsl #16
	movk x1, #34042, lsl #32
	movk x1, #47163, lsl #48
	str x1, [x0, #496]
	movz x1, #10883, lsl #0
	movk x1, #8829, lsl #16
	movk x1, #61831, lsl #32
	movk x1, #24260, lsl #48
	str x1, [x0, #504]
	movz x1, #10804, lsl #0
	movk x1, #8425, lsl #16
	movk x1, #33686, lsl #32
	movk x1, #20606, lsl #48
	str x1, [x0, #512]
	movz x1, #23092, lsl #0
	movk x1, #58766, lsl #16
	movk x1, #25543, lsl #32
	movk x1, #155, lsl #48
	str x1, [x0, #520]
	movz x1, #9386, lsl #0
	movk x1, #11655, lsl #16
	movk x1, #42070, lsl #32
	movk x1, #57707, lsl #48
	str x1, [x0, #528]
	movz x1, #48642, lsl #0
	movk x1, #39031, lsl #16
	movk x1, #12520, lsl #32
	movk x1, #51006, lsl #48
	str x1, [x0, #536]
	movz x1, #9267, lsl #0
	movk x1, #65058, lsl #16
	movk x1, #3171, lsl #32
	movk x1, #38880, lsl #48
	str x1, [x0, #544]
	movz x1, #55325, lsl #0
	movk x1, #27927, lsl #16
	movk x1, #22444, lsl #32
	movk x1, #52186, lsl #48
	str x1, [x0, #552]
	movz x1, #43682, lsl #0
	movk x1, #2997, lsl #16
	movk x1, #4773, lsl #32
	movk x1, #25635, lsl #48
	str x1, [x0, #560]
	movz x1, #36519, lsl #0
	movk x1, #18206, lsl #16
	movk x1, #43956, lsl #32
	movk x1, #27210, lsl #48
	str x1, [x0, #568]
	movz x1, #55763, lsl #0
	movk x1, #20833, lsl #16
	movk x1, #38409, lsl #32
	movk x1, #50382, lsl #48
	str x1, [x0, #576]
	movz x1, #676, lsl #0
	movk x1, #10028, lsl #16
	movk x1, #19812, lsl #32
	movk x1, #26686, lsl #48
	str x1, [x0, #584]
	movz x1, #24207, lsl #0
	movk x1, #28149, lsl #16
	movk x1, #1044, lsl #32
	movk x1, #13483, lsl #48
	str x1, [x0, #592]
	movz x1, #8136, lsl #0
	movk x1, #5312, lsl #16
	movk x1, #21397, lsl #32
	movk x1, #34128, lsl #48
	str x1, [x0, #600]
	movz x1, #34615, lsl #0
	movk x1, #36956, lsl #16
	movk x1, #55151, lsl #32
	movk x1, #9267, lsl #48
	str x1, [x0, #608]
	movz x1, #15607, lsl #0
	movk x1, #62317, lsl #16
	movk x1, #59959, lsl #32
	movk x1, #45750, lsl #48
	str x1, [x0, #616]
	movz x1, #17779, lsl #0
	movk x1, #109, lsl #16
	movk x1, #46538, lsl #32
	movk x1, #34588, lsl #48
	str x1, [x0, #624]
	movz x1, #59777, lsl #0
	movk x1, #2452, lsl #16
	movk x1, #41292, lsl #32
	movk x1, #23083, lsl #48
	str x1, [x0, #632]
	movz x1, #10861, lsl #0
	movk x1, #9476, lsl #16
	movk x1, #26153, lsl #32
	movk x1, #12176, lsl #48
	str x1, [x0, #640]
	movz x1, #62245, lsl #0
	movk x1, #18242, lsl #16
	movk x1, #57199, lsl #32
	movk x1, #29976, lsl #48
	str x1, [x0, #648]
	movz x1, #38032, lsl #0
	movk x1, #19589, lsl #16
	movk x1, #21843, lsl #32
	movk x1, #49028, lsl #48
	str x1, [x0, #656]
	movz x1, #52286, lsl #0
	movk x1, #22926, lsl #16
	movk x1, #51061, lsl #32
	movk x1, #13838, lsl #48
	str x1, [x0, #664]
	movz x1, #12252, lsl #0
	movk x1, #36838, lsl #16
	movk x1, #2952, lsl #32
	movk x1, #31767, lsl #48
	str x1, [x0, #672]
	movz x1, #16268, lsl #0
	movk x1, #52637, lsl #16
	movk x1, #11127, lsl #32
	movk x1, #22621, lsl #48
	str x1, [x0, #680]
	movz x1, #16283, lsl #0
	movk x1, #34575, lsl #16
	movk x1, #55258, lsl #32
	movk x1, #39518, lsl #48
	str x1, [x0, #688]
	movz x1, #29313, lsl #0
	movk x1, #10955, lsl #16
	movk x1, #51665, lsl #32
	movk x1, #35920, lsl #48
	str x1, [x0, #696]
	movz x1, #5745, lsl #0
	movk x1, #52648, lsl #16
	movk x1, #26654, lsl #32
	movk x1, #53923, lsl #48
	str x1, [x0, #704]
	movz x1, #15837, lsl #0
	movk x1, #38184, lsl #16
	movk x1, #46936, lsl #32
	movk x1, #2182, lsl #48
	str x1, [x0, #712]
	movz x1, #25215, lsl #0
	movk x1, #13239, lsl #16
	movk x1, #19408, lsl #32
	movk x1, #16070, lsl #48
	str x1, [x0, #720]
	movz x1, #2024, lsl #0
	movk x1, #12034, lsl #16
	movk x1, #12487, lsl #32
	movk x1, #42738, lsl #48
	str x1, [x0, #728]
	movz x1, #3555, lsl #0
	movk x1, #15225, lsl #16
	movk x1, #52262, lsl #32
	movk x1, #55289, lsl #48
	str x1, [x0, #736]
	movz x1, #48095, lsl #0
	movk x1, #12054, lsl #16
	movk x1, #14242, lsl #32
	movk x1, #29244, lsl #48
	str x1, [x0, #744]
	movz x1, #11862, lsl #0
	movk x1, #6475, lsl #16
	movk x1, #6988, lsl #32
	movk x1, #38367, lsl #48
	str x1, [x0, #752]
	movz x1, #1968, lsl #0
	movk x1, #29060, lsl #16
	movk x1, #22634, lsl #32
	movk x1, #42900, lsl #48
	str x1, [x0, #760]
	movz x1, #65431, lsl #0
	movk x1, #25430, lsl #16
	movk x1, #27005, lsl #32
	movk x1, #19064, lsl #48
	str x1, [x0, #768]
	movz x1, #9506, lsl #0
	movk x1, #63394, lsl #16
	movk x1, #11390, lsl #32
	movk x1, #57934, lsl #48
	str x1, [x0, #776]
	movz x1, #61368, lsl #0
	movk x1, #32851, lsl #16
	movk x1, #40678, lsl #32
	movk x1, #48761, lsl #48
	str x1, [x0, #784]
	movz x1, #55782, lsl #0
	movk x1, #45910, lsl #16
	movk x1, #41918, lsl #32
	movk x1, #43713, lsl #48
	str x1, [x0, #792]
	movz x1, #63375, lsl #0
	movk x1, #36812, lsl #16
	movk x1, #25397, lsl #32
	movk x1, #10652, lsl #48
	str x1, [x0, #800]
	movz x1, #11761, lsl #0
	movk x1, #19510, lsl #16
	movk x1, #29260, lsl #32
	movk x1, #13519, lsl #48
	str x1, [x0, #808]
	movz x1, #1016, lsl #0
	movk x1, #52278, lsl #16
	movk x1, #6481, lsl #32
	movk x1, #49195, lsl #48
	str x1, [x0, #816]
	movz x1, #15220, lsl #0
	movk x1, #9238, lsl #16
	movk x1, #25159, lsl #32
	movk x1, #21794, lsl #48
	str x1, [x0, #824]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #960]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #968]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #976]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #984]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #992]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1000]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1008]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1016]
	movz x1, #46861, lsl #0
	movk x1, #42949, lsl #16
	movk x1, #40873, lsl #32
	movk x1, #55125, lsl #48
	str x1, [x0, #1024]
	movz x1, #14714, lsl #0
	movk x1, #53885, lsl #16
	movk x1, #208, lsl #32
	movk x1, #55166, lsl #48
	str x1, [x0, #1032]
	movz x1, #32537, lsl #0
	movk x1, #6492, lsl #16
	movk x1, #24277, lsl #32
	movk x1, #20786, lsl #48
	str x1, [x0, #1040]
	movz x1, #38845, lsl #0
	movk x1, #25657, lsl #16
	movk x1, #25855, lsl #32
	movk x1, #33458, lsl #48
	str x1, [x0, #1048]
	movz x1, #63374, lsl #0
	movk x1, #36812, lsl #16
	movk x1, #25397, lsl #32
	movk x1, #10652, lsl #48
	str x1, [x0, #1056]
	movz x1, #11761, lsl #0
	movk x1, #19510, lsl #16
	movk x1, #29260, lsl #32
	movk x1, #13519, lsl #48
	str x1, [x0, #1064]
	movz x1, #1016, lsl #0
	movk x1, #52278, lsl #16
	movk x1, #6481, lsl #32
	movk x1, #49195, lsl #48
	str x1, [x0, #1072]
	movz x1, #15220, lsl #0
	movk x1, #9238, lsl #16
	movk x1, #25159, lsl #32
	movk x1, #21794, lsl #48
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
	movk x1, #0, lsl #48
	str x1, [x0, #1144]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #2880]
	movz x1, #61957, lsl #0
	movk x1, #24920, lsl #16
	movk x1, #5194, lsl #32
	movk x1, #18861, lsl #48
	str x1, [x0, #2560]
	movz x1, #30981, lsl #0
	movk x1, #10005, lsl #16
	movk x1, #45360, lsl #32
	movk x1, #31039, lsl #48
	str x1, [x0, #2568]
	movz x1, #65491, lsl #0
	movk x1, #36954, lsl #16
	movk x1, #63932, lsl #32
	movk x1, #21431, lsl #48
	str x1, [x0, #2576]
	movz x1, #18981, lsl #0
	movk x1, #33617, lsl #16
	movk x1, #39543, lsl #32
	movk x1, #57537, lsl #48
	str x1, [x0, #2584]
	movz x1, #32855, lsl #0
	movk x1, #54665, lsl #16
	movk x1, #28632, lsl #32
	movk x1, #6472, lsl #48
	str x1, [x0, #2592]
	movz x1, #65411, lsl #0
	movk x1, #54315, lsl #16
	movk x1, #43615, lsl #32
	movk x1, #41325, lsl #48
	str x1, [x0, #2600]
	movz x1, #61132, lsl #0
	movk x1, #8278, lsl #16
	movk x1, #6464, lsl #32
	movk x1, #8238, lsl #48
	str x1, [x0, #2608]
	movz x1, #25680, lsl #0
	movk x1, #43519, lsl #16
	movk x1, #40197, lsl #32
	movk x1, #15436, lsl #48
	str x1, [x0, #2616]
	movz x1, #10804, lsl #0
	movk x1, #8425, lsl #16
	movk x1, #33686, lsl #32
	movk x1, #20606, lsl #48
	str x1, [x0, #2624]
	movz x1, #23092, lsl #0
	movk x1, #58766, lsl #16
	movk x1, #25543, lsl #32
	movk x1, #155, lsl #48
	str x1, [x0, #2632]
	movz x1, #9386, lsl #0
	movk x1, #11655, lsl #16
	movk x1, #42070, lsl #32
	movk x1, #57707, lsl #48
	str x1, [x0, #2640]
	movz x1, #48642, lsl #0
	movk x1, #39031, lsl #16
	movk x1, #12520, lsl #32
	movk x1, #51006, lsl #48
	str x1, [x0, #2648]
	movz x1, #9267, lsl #0
	movk x1, #65058, lsl #16
	movk x1, #3171, lsl #32
	movk x1, #38880, lsl #48
	str x1, [x0, #2656]
	movz x1, #55325, lsl #0
	movk x1, #27927, lsl #16
	movk x1, #22444, lsl #32
	movk x1, #52186, lsl #48
	str x1, [x0, #2664]
	movz x1, #43682, lsl #0
	movk x1, #2997, lsl #16
	movk x1, #4773, lsl #32
	movk x1, #25635, lsl #48
	str x1, [x0, #2672]
	movz x1, #36519, lsl #0
	movk x1, #18206, lsl #16
	movk x1, #43956, lsl #32
	movk x1, #27210, lsl #48
	str x1, [x0, #2680]
	add x2, x6, #65
	ldr x5, [x2, #56]
	rev x5, x5
	str x5, [x0, #2368]
	ldr x5, [x2, #48]
	rev x5, x5
	str x5, [x0, #2376]
	ldr x5, [x2, #40]
	rev x5, x5
	str x5, [x0, #2384]
	ldr x5, [x2, #32]
	rev x5, x5
	str x5, [x0, #2392]
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #2400]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #2408]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #2416]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #2424]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	movz x5, #4, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	mov v28.d[0], x30
	bl {vg_brainpoolp512r1_check_point}
	umov x30, v28.d[0]
	ldr x3, [x0, #2880]
	ldr x1, [x0, #2368]
	movz x2, #1, lsl #0
	and x1, x1, x2
	add x1, x1, #2
	and x1, x1, x3
	strb w1, [x20, #0]
	ldr x1, [x0, #2176]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #57
	str x1, [x17, #0]
	ldr x1, [x0, #2184]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #49
	str x1, [x17, #0]
	ldr x1, [x0, #2192]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #41
	str x1, [x17, #0]
	ldr x1, [x0, #2200]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #33
	str x1, [x17, #0]
	ldr x1, [x0, #2208]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #25
	str x1, [x17, #0]
	ldr x1, [x0, #2216]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #17
	str x1, [x17, #0]
	ldr x1, [x0, #2224]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #9
	str x1, [x17, #0]
	ldr x1, [x0, #2232]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #1
	str x1, [x17, #0]
	ldr x19, [x0, #0]
	ldr x20, [x0, #8]
	ldr x21, [x0, #16]
	ldr x22, [x0, #24]
	ldr x23, [x0, #32]
	ldr x24, [x0, #40]
	ldr x25, [x0, #48]
	ldr x30, [x0, #56]
	movz x1, #1, lsl #0
	and x0, x3, x1
	ret
	.p2align 6

vg_ec_brainpoolp512r1_decompress_public_key:
	add x4, x2, #0
	add x6, x1, #0
	add x3, x1, #1
	add x1, x3, #0
	add x2, x3, #0
	str x19, [x4, #0]
	str x20, [x4, #8]
	str x21, [x4, #16]
	str x22, [x4, #24]
	str x23, [x4, #32]
	str x24, [x4, #40]
	str x25, [x4, #48]
	str x30, [x4, #56]
	add x20, x0, #0
	add x0, x4, #0
	ldr x5, [x3, #56]
	rev x5, x5
	str x5, [x0, #2048]
	ldr x5, [x3, #48]
	rev x5, x5
	str x5, [x0, #2056]
	ldr x5, [x3, #40]
	rev x5, x5
	str x5, [x0, #2064]
	ldr x5, [x3, #32]
	rev x5, x5
	str x5, [x0, #2072]
	ldr x5, [x3, #24]
	rev x5, x5
	str x5, [x0, #2080]
	ldr x5, [x3, #16]
	rev x5, x5
	str x5, [x0, #2088]
	ldr x5, [x3, #8]
	rev x5, x5
	str x5, [x0, #2096]
	ldr x5, [x3, #0]
	rev x5, x5
	str x5, [x0, #2104]
	ldr x5, [x1, #56]
	rev x5, x5
	str x5, [x0, #2112]
	ldr x5, [x1, #48]
	rev x5, x5
	str x5, [x0, #2120]
	ldr x5, [x1, #40]
	rev x5, x5
	str x5, [x0, #2128]
	ldr x5, [x1, #32]
	rev x5, x5
	str x5, [x0, #2136]
	ldr x5, [x1, #24]
	rev x5, x5
	str x5, [x0, #2144]
	ldr x5, [x1, #16]
	rev x5, x5
	str x5, [x0, #2152]
	ldr x5, [x1, #8]
	rev x5, x5
	str x5, [x0, #2160]
	ldr x5, [x1, #0]
	rev x5, x5
	str x5, [x0, #2168]
	ldr x5, [x2, #56]
	rev x5, x5
	str x5, [x0, #2176]
	ldr x5, [x2, #48]
	rev x5, x5
	str x5, [x0, #2184]
	ldr x5, [x2, #40]
	rev x5, x5
	str x5, [x0, #2192]
	ldr x5, [x2, #32]
	rev x5, x5
	str x5, [x0, #2200]
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #2208]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #2216]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #2224]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #2232]
	movz x1, #18675, lsl #0
	movk x1, #22586, lsl #16
	movk x1, #24662, lsl #32
	movk x1, #10410, lsl #48
	str x1, [x0, #64]
	movz x1, #50821, lsl #0
	movk x1, #11650, lsl #16
	movk x1, #65327, lsl #32
	movk x1, #10369, lsl #48
	str x1, [x0, #72]
	movz x1, #32998, lsl #0
	movk x1, #59043, lsl #16
	movk x1, #41258, lsl #32
	movk x1, #44749, lsl #48
	str x1, [x0, #80]
	movz x1, #26690, lsl #0
	movk x1, #39878, lsl #16
	movk x1, #39680, lsl #32
	movk x1, #32077, lsl #48
	str x1, [x0, #88]
	movz x1, #2161, lsl #0
	movk x1, #28723, lsl #16
	movk x1, #40138, lsl #32
	movk x1, #54883, lsl #48
	str x1, [x0, #96]
	movz x1, #53774, lsl #0
	movk x1, #46025, lsl #16
	movk x1, #36275, lsl #32
	movk x1, #52016, lsl #48
	str x1, [x0, #104]
	movz x1, #64519, lsl #0
	movk x1, #13257, lsl #16
	movk x1, #59054, lsl #32
	movk x1, #16340, lsl #48
	str x1, [x0, #112]
	movz x1, #50315, lsl #0
	movk x1, #56297, lsl #16
	movk x1, #40376, lsl #32
	movk x1, #43741, lsl #48
	str x1, [x0, #120]
	movz x1, #105, lsl #0
	movk x1, #40105, lsl #16
	movk x1, #38530, lsl #32
	movk x1, #46471, lsl #48
	str x1, [x0, #128]
	movz x1, #56029, lsl #0
	movk x1, #2141, lsl #16
	movk x1, #54145, lsl #32
	movk x1, #7601, lsl #48
	str x1, [x0, #136]
	movz x1, #4167, lsl #0
	movk x1, #32684, lsl #16
	movk x1, #24857, lsl #32
	movk x1, #16774, lsl #48
	str x1, [x0, #144]
	movz x1, #9753, lsl #0
	movk x1, #19625, lsl #16
	movk x1, #23617, lsl #32
	movk x1, #21822, lsl #48
	str x1, [x0, #152]
	movz x1, #2160, lsl #0
	movk x1, #28723, lsl #16
	movk x1, #40138, lsl #32
	movk x1, #54883, lsl #48
	str x1, [x0, #160]
	movz x1, #53774, lsl #0
	movk x1, #46025, lsl #16
	movk x1, #36275, lsl #32
	movk x1, #52016, lsl #48
	str x1, [x0, #168]
	movz x1, #64519, lsl #0
	movk x1, #13257, lsl #16
	movk x1, #59054, lsl #32
	movk x1, #16340, lsl #48
	str x1, [x0, #176]
	movz x1, #50315, lsl #0
	movk x1, #56297, lsl #16
	movk x1, #40376, lsl #32
	movk x1, #43741, lsl #48
	str x1, [x0, #184]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #256]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #280]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #288]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #296]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #304]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #312]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #320]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #336]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #344]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #352]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #368]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #376]
	movz x1, #46861, lsl #0
	movk x1, #42949, lsl #16
	movk x1, #40873, lsl #32
	movk x1, #55125, lsl #48
	str x1, [x0, #384]
	movz x1, #14714, lsl #0
	movk x1, #53885, lsl #16
	movk x1, #208, lsl #32
	movk x1, #55166, lsl #48
	str x1, [x0, #392]
	movz x1, #32537, lsl #0
	movk x1, #6492, lsl #16
	movk x1, #24277, lsl #32
	movk x1, #20786, lsl #48
	str x1, [x0, #400]
	movz x1, #38845, lsl #0
	movk x1, #25657, lsl #16
	movk x1, #25855, lsl #32
	movk x1, #33458, lsl #48
	str x1, [x0, #408]
	movz x1, #63374, lsl #0
	movk x1, #36812, lsl #16
	movk x1, #25397, lsl #32
	movk x1, #10652, lsl #48
	str x1, [x0, #416]
	movz x1, #11761, lsl #0
	movk x1, #19510, lsl #16
	movk x1, #29260, lsl #32
	movk x1, #13519, lsl #48
	str x1, [x0, #424]
	movz x1, #1016, lsl #0
	movk x1, #52278, lsl #16
	movk x1, #6481, lsl #32
	movk x1, #49195, lsl #48
	str x1, [x0, #432]
	movz x1, #15220, lsl #0
	movk x1, #9238, lsl #16
	movk x1, #25159, lsl #32
	movk x1, #21794, lsl #48
	str x1, [x0, #440]
	movz x1, #50246, lsl #0
	movk x1, #59920, lsl #16
	movk x1, #35380, lsl #32
	movk x1, #55839, lsl #48
	str x1, [x0, #448]
	movz x1, #53891, lsl #0
	movk x1, #44967, lsl #16
	movk x1, #38269, lsl #32
	movk x1, #5348, lsl #48
	str x1, [x0, #456]
	movz x1, #48043, lsl #0
	movk x1, #18037, lsl #16
	movk x1, #19314, lsl #32
	movk x1, #16560, lsl #48
	str x1, [x0, #464]
	movz x1, #34815, lsl #0
	movk x1, #40558, lsl #16
	movk x1, #273, lsl #32
	movk x1, #53135, lsl #48
	str x1, [x0, #472]
	movz x1, #53703, lsl #0
	movk x1, #16256, lsl #16
	movk x1, #12488, lsl #32
	movk x1, #42476, lsl #48
	str x1, [x0, #480]
	movz x1, #34680, lsl #0
	movk x1, #62494, lsl #16
	movk x1, #3929, lsl #32
	movk x1, #6189, lsl #48
	str x1, [x0, #488]
	movz x1, #34060, lsl #0
	movk x1, #58064, lsl #16
	movk x1, #34042, lsl #32
	movk x1, #47163, lsl #48
	str x1, [x0, #496]
	movz x1, #10883, lsl #0
	movk x1, #8829, lsl #16
	movk x1, #61831, lsl #32
	movk x1, #24260, lsl #48
	str x1, [x0, #504]
	movz x1, #10804, lsl #0
	movk x1, #8425, lsl #16
	movk x1, #33686, lsl #32
	movk x1, #20606, lsl #48
	str x1, [x0, #512]
	movz x1, #23092, lsl #0
	movk x1, #58766, lsl #16
	movk x1, #25543, lsl #32
	movk x1, #155, lsl #48
	str x1, [x0, #520]
	movz x1, #9386, lsl #0
	movk x1, #11655, lsl #16
	movk x1, #42070, lsl #32
	movk x1, #57707, lsl #48
	str x1, [x0, #528]
	movz x1, #48642, lsl #0
	movk x1, #39031, lsl #16
	movk x1, #12520, lsl #32
	movk x1, #51006, lsl #48
	str x1, [x0, #536]
	movz x1, #9267, lsl #0
	movk x1, #65058, lsl #16
	movk x1, #3171, lsl #32
	movk x1, #38880, lsl #48
	str x1, [x0, #544]
	movz x1, #55325, lsl #0
	movk x1, #27927, lsl #16
	movk x1, #22444, lsl #32
	movk x1, #52186, lsl #48
	str x1, [x0, #552]
	movz x1, #43682, lsl #0
	movk x1, #2997, lsl #16
	movk x1, #4773, lsl #32
	movk x1, #25635, lsl #48
	str x1, [x0, #560]
	movz x1, #36519, lsl #0
	movk x1, #18206, lsl #16
	movk x1, #43956, lsl #32
	movk x1, #27210, lsl #48
	str x1, [x0, #568]
	movz x1, #55763, lsl #0
	movk x1, #20833, lsl #16
	movk x1, #38409, lsl #32
	movk x1, #50382, lsl #48
	str x1, [x0, #576]
	movz x1, #676, lsl #0
	movk x1, #10028, lsl #16
	movk x1, #19812, lsl #32
	movk x1, #26686, lsl #48
	str x1, [x0, #584]
	movz x1, #24207, lsl #0
	movk x1, #28149, lsl #16
	movk x1, #1044, lsl #32
	movk x1, #13483, lsl #48
	str x1, [x0, #592]
	movz x1, #8136, lsl #0
	movk x1, #5312, lsl #16
	movk x1, #21397, lsl #32
	movk x1, #34128, lsl #48
	str x1, [x0, #600]
	movz x1, #34615, lsl #0
	movk x1, #36956, lsl #16
	movk x1, #55151, lsl #32
	movk x1, #9267, lsl #48
	str x1, [x0, #608]
	movz x1, #15607, lsl #0
	movk x1, #62317, lsl #16
	movk x1, #59959, lsl #32
	movk x1, #45750, lsl #48
	str x1, [x0, #616]
	movz x1, #17779, lsl #0
	movk x1, #109, lsl #16
	movk x1, #46538, lsl #32
	movk x1, #34588, lsl #48
	str x1, [x0, #624]
	movz x1, #59777, lsl #0
	movk x1, #2452, lsl #16
	movk x1, #41292, lsl #32
	movk x1, #23083, lsl #48
	str x1, [x0, #632]
	movz x1, #10861, lsl #0
	movk x1, #9476, lsl #16
	movk x1, #26153, lsl #32
	movk x1, #12176, lsl #48
	str x1, [x0, #640]
	movz x1, #62245, lsl #0
	movk x1, #18242, lsl #16
	movk x1, #57199, lsl #32
	movk x1, #29976, lsl #48
	str x1, [x0, #648]
	movz x1, #38032, lsl #0
	movk x1, #19589, lsl #16
	movk x1, #21843, lsl #32
	movk x1, #49028, lsl #48
	str x1, [x0, #656]
	movz x1, #52286, lsl #0
	movk x1, #22926, lsl #16
	movk x1, #51061, lsl #32
	movk x1, #13838, lsl #48
	str x1, [x0, #664]
	movz x1, #12252, lsl #0
	movk x1, #36838, lsl #16
	movk x1, #2952, lsl #32
	movk x1, #31767, lsl #48
	str x1, [x0, #672]
	movz x1, #16268, lsl #0
	movk x1, #52637, lsl #16
	movk x1, #11127, lsl #32
	movk x1, #22621, lsl #48
	str x1, [x0, #680]
	movz x1, #16283, lsl #0
	movk x1, #34575, lsl #16
	movk x1, #55258, lsl #32
	movk x1, #39518, lsl #48
	str x1, [x0, #688]
	movz x1, #29313, lsl #0
	movk x1, #10955, lsl #16
	movk x1, #51665, lsl #32
	movk x1, #35920, lsl #48
	str x1, [x0, #696]
	movz x1, #5745, lsl #0
	movk x1, #52648, lsl #16
	movk x1, #26654, lsl #32
	movk x1, #53923, lsl #48
	str x1, [x0, #704]
	movz x1, #15837, lsl #0
	movk x1, #38184, lsl #16
	movk x1, #46936, lsl #32
	movk x1, #2182, lsl #48
	str x1, [x0, #712]
	movz x1, #25215, lsl #0
	movk x1, #13239, lsl #16
	movk x1, #19408, lsl #32
	movk x1, #16070, lsl #48
	str x1, [x0, #720]
	movz x1, #2024, lsl #0
	movk x1, #12034, lsl #16
	movk x1, #12487, lsl #32
	movk x1, #42738, lsl #48
	str x1, [x0, #728]
	movz x1, #3555, lsl #0
	movk x1, #15225, lsl #16
	movk x1, #52262, lsl #32
	movk x1, #55289, lsl #48
	str x1, [x0, #736]
	movz x1, #48095, lsl #0
	movk x1, #12054, lsl #16
	movk x1, #14242, lsl #32
	movk x1, #29244, lsl #48
	str x1, [x0, #744]
	movz x1, #11862, lsl #0
	movk x1, #6475, lsl #16
	movk x1, #6988, lsl #32
	movk x1, #38367, lsl #48
	str x1, [x0, #752]
	movz x1, #1968, lsl #0
	movk x1, #29060, lsl #16
	movk x1, #22634, lsl #32
	movk x1, #42900, lsl #48
	str x1, [x0, #760]
	movz x1, #65431, lsl #0
	movk x1, #25430, lsl #16
	movk x1, #27005, lsl #32
	movk x1, #19064, lsl #48
	str x1, [x0, #768]
	movz x1, #9506, lsl #0
	movk x1, #63394, lsl #16
	movk x1, #11390, lsl #32
	movk x1, #57934, lsl #48
	str x1, [x0, #776]
	movz x1, #61368, lsl #0
	movk x1, #32851, lsl #16
	movk x1, #40678, lsl #32
	movk x1, #48761, lsl #48
	str x1, [x0, #784]
	movz x1, #55782, lsl #0
	movk x1, #45910, lsl #16
	movk x1, #41918, lsl #32
	movk x1, #43713, lsl #48
	str x1, [x0, #792]
	movz x1, #63375, lsl #0
	movk x1, #36812, lsl #16
	movk x1, #25397, lsl #32
	movk x1, #10652, lsl #48
	str x1, [x0, #800]
	movz x1, #11761, lsl #0
	movk x1, #19510, lsl #16
	movk x1, #29260, lsl #32
	movk x1, #13519, lsl #48
	str x1, [x0, #808]
	movz x1, #1016, lsl #0
	movk x1, #52278, lsl #16
	movk x1, #6481, lsl #32
	movk x1, #49195, lsl #48
	str x1, [x0, #816]
	movz x1, #15220, lsl #0
	movk x1, #9238, lsl #16
	movk x1, #25159, lsl #32
	movk x1, #21794, lsl #48
	str x1, [x0, #824]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #960]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #968]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #976]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #984]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #992]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1000]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1008]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1016]
	movz x1, #46861, lsl #0
	movk x1, #42949, lsl #16
	movk x1, #40873, lsl #32
	movk x1, #55125, lsl #48
	str x1, [x0, #1024]
	movz x1, #14714, lsl #0
	movk x1, #53885, lsl #16
	movk x1, #208, lsl #32
	movk x1, #55166, lsl #48
	str x1, [x0, #1032]
	movz x1, #32537, lsl #0
	movk x1, #6492, lsl #16
	movk x1, #24277, lsl #32
	movk x1, #20786, lsl #48
	str x1, [x0, #1040]
	movz x1, #38845, lsl #0
	movk x1, #25657, lsl #16
	movk x1, #25855, lsl #32
	movk x1, #33458, lsl #48
	str x1, [x0, #1048]
	movz x1, #63374, lsl #0
	movk x1, #36812, lsl #16
	movk x1, #25397, lsl #32
	movk x1, #10652, lsl #48
	str x1, [x0, #1056]
	movz x1, #11761, lsl #0
	movk x1, #19510, lsl #16
	movk x1, #29260, lsl #32
	movk x1, #13519, lsl #48
	str x1, [x0, #1064]
	movz x1, #1016, lsl #0
	movk x1, #52278, lsl #16
	movk x1, #6481, lsl #32
	movk x1, #49195, lsl #48
	str x1, [x0, #1072]
	movz x1, #15220, lsl #0
	movk x1, #9238, lsl #16
	movk x1, #25159, lsl #32
	movk x1, #21794, lsl #48
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
	movk x1, #0, lsl #48
	str x1, [x0, #1144]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #2880]
	movz x1, #61957, lsl #0
	movk x1, #24920, lsl #16
	movk x1, #5194, lsl #32
	movk x1, #18861, lsl #48
	str x1, [x0, #2560]
	movz x1, #30981, lsl #0
	movk x1, #10005, lsl #16
	movk x1, #45360, lsl #32
	movk x1, #31039, lsl #48
	str x1, [x0, #2568]
	movz x1, #65491, lsl #0
	movk x1, #36954, lsl #16
	movk x1, #63932, lsl #32
	movk x1, #21431, lsl #48
	str x1, [x0, #2576]
	movz x1, #18981, lsl #0
	movk x1, #33617, lsl #16
	movk x1, #39543, lsl #32
	movk x1, #57537, lsl #48
	str x1, [x0, #2584]
	movz x1, #32855, lsl #0
	movk x1, #54665, lsl #16
	movk x1, #28632, lsl #32
	movk x1, #6472, lsl #48
	str x1, [x0, #2592]
	movz x1, #65411, lsl #0
	movk x1, #54315, lsl #16
	movk x1, #43615, lsl #32
	movk x1, #41325, lsl #48
	str x1, [x0, #2600]
	movz x1, #61132, lsl #0
	movk x1, #8278, lsl #16
	movk x1, #6464, lsl #32
	movk x1, #8238, lsl #48
	str x1, [x0, #2608]
	movz x1, #25680, lsl #0
	movk x1, #43519, lsl #16
	movk x1, #40197, lsl #32
	movk x1, #15436, lsl #48
	str x1, [x0, #2616]
	movz x1, #10804, lsl #0
	movk x1, #8425, lsl #16
	movk x1, #33686, lsl #32
	movk x1, #20606, lsl #48
	str x1, [x0, #2624]
	movz x1, #23092, lsl #0
	movk x1, #58766, lsl #16
	movk x1, #25543, lsl #32
	movk x1, #155, lsl #48
	str x1, [x0, #2632]
	movz x1, #9386, lsl #0
	movk x1, #11655, lsl #16
	movk x1, #42070, lsl #32
	movk x1, #57707, lsl #48
	str x1, [x0, #2640]
	movz x1, #48642, lsl #0
	movk x1, #39031, lsl #16
	movk x1, #12520, lsl #32
	movk x1, #51006, lsl #48
	str x1, [x0, #2648]
	movz x1, #9267, lsl #0
	movk x1, #65058, lsl #16
	movk x1, #3171, lsl #32
	movk x1, #38880, lsl #48
	str x1, [x0, #2656]
	movz x1, #55325, lsl #0
	movk x1, #27927, lsl #16
	movk x1, #22444, lsl #32
	movk x1, #52186, lsl #48
	str x1, [x0, #2664]
	movz x1, #43682, lsl #0
	movk x1, #2997, lsl #16
	movk x1, #4773, lsl #32
	movk x1, #25635, lsl #48
	str x1, [x0, #2672]
	movz x1, #36519, lsl #0
	movk x1, #18206, lsl #16
	movk x1, #43956, lsl #32
	movk x1, #27210, lsl #48
	str x1, [x0, #2680]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	str x1, [x0, #2112]
	movz x5, #1, lsl #0
	orr x1, x1, x5
	movz x5, #3, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2176]
	ldr x2, [x0, #64]
	subs x16, x1, x2
	ldr x1, [x0, #2184]
	ldr x2, [x0, #72]
	sbcs x16, x1, x2
	ldr x1, [x0, #2192]
	ldr x2, [x0, #80]
	sbcs x16, x1, x2
	ldr x1, [x0, #2200]
	ldr x2, [x0, #88]
	sbcs x16, x1, x2
	ldr x1, [x0, #2208]
	ldr x2, [x0, #96]
	sbcs x16, x1, x2
	ldr x1, [x0, #2216]
	ldr x2, [x0, #104]
	sbcs x16, x1, x2
	ldr x1, [x0, #2224]
	ldr x2, [x0, #112]
	sbcs x16, x1, x2
	ldr x1, [x0, #2232]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	mov v29.d[0], x30
	movz x1, #2240, lsl #0
	movz x2, #2176, lsl #0
	movz x3, #2560, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2688, lsl #0
	movz x2, #2240, lsl #0
	movz x3, #2240, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2752, lsl #0
	movz x2, #2688, lsl #0
	movz x3, #2240, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2688, lsl #0
	movz x2, #448, lsl #0
	movz x3, #2240, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2752]
	ldr x9, [x0, #2760]
	ldr x10, [x0, #2768]
	ldr x11, [x0, #2776]
	ldr x12, [x0, #2784]
	ldr x13, [x0, #2792]
	ldr x14, [x0, #2800]
	ldr x15, [x0, #2808]
	ldr x2, [x0, #2688]
	adds x8, x8, x2
	ldr x2, [x0, #2696]
	adcs x9, x9, x2
	ldr x2, [x0, #2704]
	adcs x10, x10, x2
	ldr x2, [x0, #2712]
	adcs x11, x11, x2
	ldr x2, [x0, #2720]
	adcs x12, x12, x2
	ldr x2, [x0, #2728]
	adcs x13, x13, x2
	ldr x2, [x0, #2736]
	adcs x14, x14, x2
	ldr x2, [x0, #2744]
	adcs x15, x15, x2
	adc x21, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	str x8, [x0, #2496]
	str x9, [x0, #2504]
	str x10, [x0, #2512]
	str x11, [x0, #2520]
	str x12, [x0, #2528]
	str x13, [x0, #2536]
	str x14, [x0, #2544]
	str x15, [x0, #2552]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2496]
	ldr x9, [x0, #2504]
	ldr x10, [x0, #2512]
	ldr x11, [x0, #2520]
	ldr x12, [x0, #2528]
	ldr x13, [x0, #2536]
	ldr x14, [x0, #2544]
	ldr x15, [x0, #2552]
	ldr x2, [x0, #2624]
	adds x8, x8, x2
	ldr x2, [x0, #2632]
	adcs x9, x9, x2
	ldr x2, [x0, #2640]
	adcs x10, x10, x2
	ldr x2, [x0, #2648]
	adcs x11, x11, x2
	ldr x2, [x0, #2656]
	adcs x12, x12, x2
	ldr x2, [x0, #2664]
	adcs x13, x13, x2
	ldr x2, [x0, #2672]
	adcs x14, x14, x2
	ldr x2, [x0, #2680]
	adcs x15, x15, x2
	adc x21, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr x2, [x0, #112]
	sbcs x17, x14, x2
	ldr x2, [x0, #120]
	sbcs x24, x15, x2
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	str x8, [x0, #2752]
	str x9, [x0, #2760]
	str x10, [x0, #2768]
	str x11, [x0, #2776]
	str x12, [x0, #2784]
	str x13, [x0, #2792]
	str x14, [x0, #2800]
	str x15, [x0, #2808]
	ldr x1, [x0, #2752]
	str x1, [x0, #960]
	ldr x1, [x0, #2760]
	str x1, [x0, #968]
	ldr x1, [x0, #2768]
	str x1, [x0, #976]
	ldr x1, [x0, #2776]
	str x1, [x0, #984]
	ldr x1, [x0, #2784]
	str x1, [x0, #992]
	ldr x1, [x0, #2792]
	str x1, [x0, #1000]
	ldr x1, [x0, #2800]
	str x1, [x0, #1008]
	ldr x1, [x0, #2808]
	str x1, [x0, #1016]
	mov v29.d[0], x30
	movz x1, #1472, lsl #0
	movz x2, #2752, lsl #0
	movz x3, #2752, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1024, lsl #0
	movz x2, #960, lsl #0
	movz x3, #1472, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1088, lsl #0
	movz x2, #1024, lsl #0
	movz x3, #1472, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1152, lsl #0
	movz x2, #1088, lsl #0
	movz x3, #1472, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1152, lsl #0
	movz x3, #1472, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1280, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1472, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1344, lsl #0
	movz x2, #1280, lsl #0
	movz x3, #1472, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1344, lsl #0
	movz x3, #1472, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1088]
	str x1, [x0, #1920]
	ldr x1, [x0, #1096]
	str x1, [x0, #1928]
	ldr x1, [x0, #1104]
	str x1, [x0, #1936]
	ldr x1, [x0, #1112]
	str x1, [x0, #1944]
	ldr x1, [x0, #1120]
	str x1, [x0, #1952]
	ldr x1, [x0, #1128]
	str x1, [x0, #1960]
	ldr x1, [x0, #1136]
	str x1, [x0, #1968]
	ldr x1, [x0, #1144]
	str x1, [x0, #1976]
	movz x19, #4, lsl #0
20:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 20b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
21:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 21b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
22:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 22b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
23:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 23b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
24:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 24b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
25:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 25b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #1, lsl #0
26:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 26b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
27:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 27b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
28:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 28b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
29:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 29b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
210:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 210b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
211:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 211b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
212:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 212b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
213:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 213b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
214:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 214b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
215:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 215b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
216:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 216b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
217:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 217b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
218:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 218b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
219:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 219b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #1, lsl #0
220:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 220b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
221:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 221b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
222:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 222b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
223:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 223b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
224:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 224b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
225:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 225b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #11, lsl #0
226:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 226b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
227:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 227b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
228:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 228b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
229:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 229b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
230:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 230b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
231:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 231b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
232:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 232b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
233:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 233b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
234:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 234b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
235:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 235b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
236:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 236b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
237:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 237b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
238:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 238b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #8, lsl #0
239:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 239b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
240:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 240b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
241:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 241b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
242:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 242b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
243:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 243b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
244:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 244b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
245:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 245b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
246:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 246b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
247:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 247b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #8, lsl #0
248:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 248b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
249:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 249b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
250:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 250b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
251:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 251b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
252:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 252b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
253:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 253b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
254:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 254b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
255:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 255b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
256:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 256b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
257:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 257b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #12, lsl #0
258:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 258b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
259:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 259b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
260:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 260b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
261:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 261b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
262:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 262b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
263:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 263b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
264:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 264b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
265:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 265b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
266:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 266b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
267:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 267b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
268:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 268b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #8, lsl #0
269:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 269b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
270:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 270b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
271:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 271b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
272:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 272b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
273:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 273b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
274:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 274b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #10, lsl #0
275:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 275b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
276:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 276b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
277:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 277b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
278:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 278b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #10, lsl #0
279:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 279b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
280:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 280b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
281:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 281b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
282:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 282b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
283:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 283b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
284:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 284b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #9, lsl #0
285:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 285b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
286:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 286b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
287:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 287b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
288:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 288b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
289:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 289b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
290:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 290b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
291:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 291b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #9, lsl #0
292:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 292b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
293:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 293b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
294:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 294b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #8, lsl #0
295:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 295b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
296:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 296b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
297:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 297b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
298:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 298b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
299:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 299b
	mov v29.d[0], x30
	movz x1, #1920, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2368, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #320, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #256]
	ldr x9, [x0, #264]
	ldr x10, [x0, #272]
	ldr x11, [x0, #280]
	ldr x12, [x0, #288]
	ldr x13, [x0, #296]
	ldr x14, [x0, #304]
	ldr x15, [x0, #312]
	ldr x2, [x0, #2368]
	subs x8, x8, x2
	ldr x2, [x0, #2376]
	sbcs x9, x9, x2
	ldr x2, [x0, #2384]
	sbcs x10, x10, x2
	ldr x2, [x0, #2392]
	sbcs x11, x11, x2
	ldr x2, [x0, #2400]
	sbcs x12, x12, x2
	ldr x2, [x0, #2408]
	sbcs x13, x13, x2
	ldr x2, [x0, #2416]
	sbcs x14, x14, x2
	ldr x2, [x0, #2424]
	sbcs x15, x15, x2
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
	str x8, [x0, #2432]
	str x9, [x0, #2440]
	str x10, [x0, #2448]
	str x11, [x0, #2456]
	str x12, [x0, #2464]
	str x13, [x0, #2472]
	str x14, [x0, #2480]
	str x15, [x0, #2488]
	ldr x1, [x0, #2368]
	ldr x2, [x0, #2112]
	eor x2, x2, x1
	movz x1, #1, lsl #0
	and x2, x2, x1
	movz x7, #0, lsl #0
	sub x3, x7, x2
	ldr x1, [x0, #2368]
	ldr x2, [x0, #2432]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2368]
	ldr x1, [x0, #2376]
	ldr x2, [x0, #2440]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2376]
	ldr x1, [x0, #2384]
	ldr x2, [x0, #2448]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2384]
	ldr x1, [x0, #2392]
	ldr x2, [x0, #2456]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2392]
	ldr x1, [x0, #2400]
	ldr x2, [x0, #2464]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2400]
	ldr x1, [x0, #2408]
	ldr x2, [x0, #2472]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2408]
	ldr x1, [x0, #2416]
	ldr x2, [x0, #2480]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2416]
	ldr x1, [x0, #2424]
	ldr x2, [x0, #2488]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2424]
	mov v29.d[0], x30
	movz x1, #2304, lsl #0
	movz x2, #2368, lsl #0
	movz x3, #2560, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2688, lsl #0
	movz x2, #2304, lsl #0
	movz x3, #2304, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2688]
	ldr x9, [x0, #2696]
	ldr x10, [x0, #2704]
	ldr x11, [x0, #2712]
	ldr x12, [x0, #2720]
	ldr x13, [x0, #2728]
	ldr x14, [x0, #2736]
	ldr x15, [x0, #2744]
	ldr x2, [x0, #2752]
	subs x8, x8, x2
	ldr x2, [x0, #2760]
	sbcs x9, x9, x2
	ldr x2, [x0, #2768]
	sbcs x10, x10, x2
	ldr x2, [x0, #2776]
	sbcs x11, x11, x2
	ldr x2, [x0, #2784]
	sbcs x12, x12, x2
	ldr x2, [x0, #2792]
	sbcs x13, x13, x2
	ldr x2, [x0, #2800]
	sbcs x14, x14, x2
	ldr x2, [x0, #2808]
	sbcs x15, x15, x2
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
	str x8, [x0, #2496]
	str x9, [x0, #2504]
	str x10, [x0, #2512]
	str x11, [x0, #2520]
	str x12, [x0, #2528]
	str x13, [x0, #2536]
	str x14, [x0, #2544]
	str x15, [x0, #2552]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2496]
	ldr x2, [x0, #2504]
	orr x1, x1, x2
	ldr x2, [x0, #2512]
	orr x1, x1, x2
	ldr x2, [x0, #2520]
	orr x1, x1, x2
	ldr x2, [x0, #2528]
	orr x1, x1, x2
	ldr x2, [x0, #2536]
	orr x1, x1, x2
	ldr x2, [x0, #2544]
	orr x1, x1, x2
	ldr x2, [x0, #2552]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	ldr x1, [x0, #2368]
	ldr x2, [x0, #2112]
	eor x2, x2, x1
	movz x1, #1, lsl #0
	and x2, x2, x1
	movz x7, #0, lsl #0
	sub x3, x7, x2
	movz x7, #0, lsl #0
	add x2, x3, #1
	sub x2, x7, x2
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	ldr x3, [x0, #2880]
	movz x1, #4, lsl #0
	and x1, x1, x3
	strb w1, [x20, #0]
	add x6, x20, #1
	ldr x1, [x0, #2176]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #56]
	ldr x1, [x0, #2184]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #48]
	ldr x1, [x0, #2192]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #40]
	ldr x1, [x0, #2200]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #32]
	ldr x1, [x0, #2208]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #24]
	ldr x1, [x0, #2216]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #16]
	ldr x1, [x0, #2224]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #8]
	ldr x1, [x0, #2232]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #0]
	ldr x1, [x0, #2368]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #120]
	ldr x1, [x0, #2376]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #112]
	ldr x1, [x0, #2384]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #104]
	ldr x1, [x0, #2392]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #96]
	ldr x1, [x0, #2400]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #88]
	ldr x1, [x0, #2408]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #80]
	ldr x1, [x0, #2416]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #72]
	ldr x1, [x0, #2424]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #64]
	ldr x19, [x0, #0]
	ldr x20, [x0, #8]
	ldr x21, [x0, #16]
	ldr x22, [x0, #24]
	ldr x23, [x0, #32]
	ldr x24, [x0, #40]
	ldr x25, [x0, #48]
	ldr x30, [x0, #56]
	movz x1, #1, lsl #0
	and x0, x3, x1
	ret
	.p2align 6
