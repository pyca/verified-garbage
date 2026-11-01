// The functions of `src/ecdh_brainpoolp512r1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_brainpoolp512r1:
	add x4, x3, #0
	add x6, x2, #0
	add x3, x1, #0
	add x2, x2, #1
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
	movz x19, #64, lsl #0
	movz x5, #1, lsl #0
20:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #2048]
	lsl x17, x19, #3
	add x17, x0, x17
	and x2, x1, x5
	strb w2, [x17, #2944]
	lsr x2, x1, #1
	and x2, x2, x5
	strb w2, [x17, #2945]
	lsr x2, x1, #2
	and x2, x2, x5
	strb w2, [x17, #2946]
	lsr x2, x1, #3
	and x2, x2, x5
	strb w2, [x17, #2947]
	lsr x2, x1, #4
	and x2, x2, x5
	strb w2, [x17, #2948]
	lsr x2, x1, #5
	and x2, x2, x5
	strb w2, [x17, #2949]
	lsr x2, x1, #6
	and x2, x2, x5
	strb w2, [x17, #2950]
	lsr x2, x1, #7
	and x2, x2, x5
	strb w2, [x17, #2951]
	cbnz x19, 20b
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
	movz x1, #13737, lsl #0
	movk x1, #2689, lsl #16
	movk x1, #10860, lsl #32
	movk x1, #51409, lsl #48
	str x1, [x0, #832]
	movz x1, #18455, lsl #0
	movk x1, #33576, lsl #16
	movk x1, #11304, lsl #32
	movk x1, #55632, lsl #48
	str x1, [x0, #840]
	movz x1, #60695, lsl #0
	movk x1, #41457, lsl #16
	movk x1, #19415, lsl #32
	movk x1, #62837, lsl #48
	str x1, [x0, #848]
	movz x1, #53701, lsl #0
	movk x1, #11680, lsl #16
	movk x1, #63417, lsl #32
	movk x1, #55404, lsl #48
	str x1, [x0, #856]
	movz x1, #25641, lsl #0
	movk x1, #35379, lsl #16
	movk x1, #34913, lsl #32
	movk x1, #61756, lsl #48
	str x1, [x0, #864]
	movz x1, #46665, lsl #0
	movk x1, #37757, lsl #16
	movk x1, #31057, lsl #32
	movk x1, #39006, lsl #48
	str x1, [x0, #872]
	movz x1, #992, lsl #0
	movk x1, #61271, lsl #16
	movk x1, #20800, lsl #32
	movk x1, #60564, lsl #48
	str x1, [x0, #880]
	movz x1, #59242, lsl #0
	movk x1, #63857, lsl #16
	movk x1, #25955, lsl #32
	movk x1, #37890, lsl #48
	str x1, [x0, #888]
	ldr x1, [x0, #2496]
	str x1, [x0, #960]
	ldr x1, [x0, #2504]
	str x1, [x0, #968]
	ldr x1, [x0, #2512]
	str x1, [x0, #976]
	ldr x1, [x0, #2520]
	str x1, [x0, #984]
	ldr x1, [x0, #2528]
	str x1, [x0, #992]
	ldr x1, [x0, #2536]
	str x1, [x0, #1000]
	ldr x1, [x0, #2544]
	str x1, [x0, #1008]
	ldr x1, [x0, #2552]
	str x1, [x0, #1016]
	ldr x1, [x0, #2816]
	str x1, [x0, #1024]
	ldr x1, [x0, #2824]
	str x1, [x0, #1032]
	ldr x1, [x0, #2832]
	str x1, [x0, #1040]
	ldr x1, [x0, #2840]
	str x1, [x0, #1048]
	ldr x1, [x0, #2848]
	str x1, [x0, #1056]
	ldr x1, [x0, #2856]
	str x1, [x0, #1064]
	ldr x1, [x0, #2864]
	str x1, [x0, #1072]
	ldr x1, [x0, #2872]
	str x1, [x0, #1080]
	movz x1, #13737, lsl #0
	movk x1, #2689, lsl #16
	movk x1, #10860, lsl #32
	movk x1, #51409, lsl #48
	str x1, [x0, #512]
	movz x1, #18455, lsl #0
	movk x1, #33576, lsl #16
	movk x1, #11304, lsl #32
	movk x1, #55632, lsl #48
	str x1, [x0, #520]
	movz x1, #60695, lsl #0
	movk x1, #41457, lsl #16
	movk x1, #19415, lsl #32
	movk x1, #62837, lsl #48
	str x1, [x0, #528]
	movz x1, #53701, lsl #0
	movk x1, #11680, lsl #16
	movk x1, #63417, lsl #32
	movk x1, #55404, lsl #48
	str x1, [x0, #536]
	movz x1, #25641, lsl #0
	movk x1, #35379, lsl #16
	movk x1, #34913, lsl #32
	movk x1, #61756, lsl #48
	str x1, [x0, #544]
	movz x1, #46665, lsl #0
	movk x1, #37757, lsl #16
	movk x1, #31057, lsl #32
	movk x1, #39006, lsl #48
	str x1, [x0, #552]
	movz x1, #992, lsl #0
	movk x1, #61271, lsl #16
	movk x1, #20800, lsl #32
	movk x1, #60564, lsl #48
	str x1, [x0, #560]
	movz x1, #59242, lsl #0
	movk x1, #63857, lsl #16
	movk x1, #25955, lsl #32
	movk x1, #37890, lsl #48
	str x1, [x0, #568]
	mov v29.d[0], x30
	bl {vg_brainpoolp512r1_mul}
	umov x30, v29.d[0]
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
	mov v29.d[0], x30
	bl {vg_brainpoolp512r1_inv_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2240, lsl #0
	movz x2, #960, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2304, lsl #0
	movz x2, #2240, lsl #0
	movz x3, #320, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2112]
	ldr x2, [x0, #128]
	subs x16, x1, x2
	ldr x1, [x0, #2120]
	ldr x2, [x0, #136]
	sbcs x16, x1, x2
	ldr x1, [x0, #2128]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #2136]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	ldr x1, [x0, #2144]
	ldr x2, [x0, #160]
	sbcs x16, x1, x2
	ldr x1, [x0, #2152]
	ldr x2, [x0, #168]
	sbcs x16, x1, x2
	ldr x1, [x0, #2160]
	ldr x2, [x0, #176]
	sbcs x16, x1, x2
	ldr x1, [x0, #2168]
	ldr x2, [x0, #184]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #2112]
	ldr x2, [x0, #2120]
	orr x1, x1, x2
	ldr x2, [x0, #2128]
	orr x1, x1, x2
	ldr x2, [x0, #2136]
	orr x1, x1, x2
	ldr x2, [x0, #2144]
	orr x1, x1, x2
	ldr x2, [x0, #2152]
	orr x1, x1, x2
	ldr x2, [x0, #2160]
	orr x1, x1, x2
	ldr x2, [x0, #2168]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1088]
	ldr x2, [x0, #1096]
	orr x1, x1, x2
	ldr x2, [x0, #1104]
	orr x1, x1, x2
	ldr x2, [x0, #1112]
	orr x1, x1, x2
	ldr x2, [x0, #1120]
	orr x1, x1, x2
	ldr x2, [x0, #1128]
	orr x1, x1, x2
	ldr x2, [x0, #1136]
	orr x1, x1, x2
	ldr x2, [x0, #1144]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	ldr x3, [x0, #2880]
	ldr x1, [x0, #2304]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #56]
	ldr x1, [x0, #2312]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #48]
	ldr x1, [x0, #2320]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #40]
	ldr x1, [x0, #2328]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #32]
	ldr x1, [x0, #2336]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #24]
	ldr x1, [x0, #2344]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #16]
	ldr x1, [x0, #2352]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #8]
	ldr x1, [x0, #2360]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #0]
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
