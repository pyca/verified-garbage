// The functions of `src/ecdsa_brainpoolp512r1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_sign:
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
	ldr x1, [x0, #576]
	str x1, [x0, #960]
	ldr x1, [x0, #584]
	str x1, [x0, #968]
	ldr x1, [x0, #592]
	str x1, [x0, #976]
	ldr x1, [x0, #600]
	str x1, [x0, #984]
	ldr x1, [x0, #608]
	str x1, [x0, #992]
	ldr x1, [x0, #616]
	str x1, [x0, #1000]
	ldr x1, [x0, #624]
	str x1, [x0, #1008]
	ldr x1, [x0, #632]
	str x1, [x0, #1016]
	ldr x1, [x0, #640]
	str x1, [x0, #1024]
	ldr x1, [x0, #648]
	str x1, [x0, #1032]
	ldr x1, [x0, #656]
	str x1, [x0, #1040]
	ldr x1, [x0, #664]
	str x1, [x0, #1048]
	ldr x1, [x0, #672]
	str x1, [x0, #1056]
	ldr x1, [x0, #680]
	str x1, [x0, #1064]
	ldr x1, [x0, #688]
	str x1, [x0, #1072]
	ldr x1, [x0, #696]
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
	ldr x8, [x0, #2304]
	ldr x9, [x0, #2312]
	ldr x10, [x0, #2320]
	ldr x11, [x0, #2328]
	ldr x12, [x0, #2336]
	ldr x13, [x0, #2344]
	ldr x14, [x0, #2352]
	ldr x15, [x0, #2360]
	ldr x2, [x0, #256]
	adds x8, x8, x2
	ldr x2, [x0, #264]
	adcs x9, x9, x2
	ldr x2, [x0, #272]
	adcs x10, x10, x2
	ldr x2, [x0, #280]
	adcs x11, x11, x2
	ldr x2, [x0, #288]
	adcs x12, x12, x2
	ldr x2, [x0, #296]
	adcs x13, x13, x2
	ldr x2, [x0, #304]
	adcs x14, x14, x2
	ldr x2, [x0, #312]
	adcs x15, x15, x2
	adc x21, x7, x7
	ldr x2, [x0, #128]
	subs x1, x8, x2
	ldr x2, [x0, #136]
	sbcs x3, x9, x2
	ldr x2, [x0, #144]
	sbcs x4, x10, x2
	ldr x2, [x0, #152]
	sbcs x5, x11, x2
	ldr x2, [x0, #160]
	sbcs x6, x12, x2
	ldr x2, [x0, #168]
	sbcs x16, x13, x2
	ldr x2, [x0, #176]
	sbcs x17, x14, x2
	ldr x2, [x0, #184]
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
	str x8, [x0, #2368]
	str x9, [x0, #2376]
	str x10, [x0, #2384]
	str x11, [x0, #2392]
	str x12, [x0, #2400]
	str x13, [x0, #2408]
	str x14, [x0, #2416]
	str x15, [x0, #2424]
	mov v29.d[0], x30
	movz x1, #2432, lsl #0
	movz x2, #2048, lsl #0
	movz x3, #704, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
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
	ldr x1, [x0, #2048]
	ldr x2, [x0, #128]
	subs x16, x1, x2
	ldr x1, [x0, #2056]
	ldr x2, [x0, #136]
	sbcs x16, x1, x2
	ldr x1, [x0, #2064]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #2072]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	ldr x1, [x0, #2080]
	ldr x2, [x0, #160]
	sbcs x16, x1, x2
	ldr x1, [x0, #2088]
	ldr x2, [x0, #168]
	sbcs x16, x1, x2
	ldr x1, [x0, #2096]
	ldr x2, [x0, #176]
	sbcs x16, x1, x2
	ldr x1, [x0, #2104]
	ldr x2, [x0, #184]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #2048]
	ldr x2, [x0, #2056]
	orr x1, x1, x2
	ldr x2, [x0, #2064]
	orr x1, x1, x2
	ldr x2, [x0, #2072]
	orr x1, x1, x2
	ldr x2, [x0, #2080]
	orr x1, x1, x2
	ldr x2, [x0, #2088]
	orr x1, x1, x2
	ldr x2, [x0, #2096]
	orr x1, x1, x2
	ldr x2, [x0, #2104]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2368]
	ldr x2, [x0, #2376]
	orr x1, x1, x2
	ldr x2, [x0, #2384]
	orr x1, x1, x2
	ldr x2, [x0, #2392]
	orr x1, x1, x2
	ldr x2, [x0, #2400]
	orr x1, x1, x2
	ldr x2, [x0, #2408]
	orr x1, x1, x2
	ldr x2, [x0, #2416]
	orr x1, x1, x2
	ldr x2, [x0, #2424]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	mov v29.d[0], x30
	bl {vg_brainpoolp512r1_inv_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2496, lsl #0
	movz x2, #2368, lsl #0
	movz x3, #704, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2560, lsl #0
	movz x2, #2112, lsl #0
	movz x3, #704, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2624, lsl #0
	movz x2, #2176, lsl #0
	movz x3, #704, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2688, lsl #0
	movz x2, #2496, lsl #0
	movz x3, #2560, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
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
	ldr x2, [x0, #128]
	subs x1, x8, x2
	ldr x2, [x0, #136]
	sbcs x3, x9, x2
	ldr x2, [x0, #144]
	sbcs x4, x10, x2
	ldr x2, [x0, #152]
	sbcs x5, x11, x2
	ldr x2, [x0, #160]
	sbcs x6, x12, x2
	ldr x2, [x0, #168]
	sbcs x16, x13, x2
	ldr x2, [x0, #176]
	sbcs x17, x14, x2
	ldr x2, [x0, #184]
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
	str x8, [x0, #2688]
	str x9, [x0, #2696]
	str x10, [x0, #2704]
	str x11, [x0, #2712]
	str x12, [x0, #2720]
	str x13, [x0, #2728]
	str x14, [x0, #2736]
	str x15, [x0, #2744]
	mov v29.d[0], x30
	movz x1, #2752, lsl #0
	movz x2, #1920, lsl #0
	movz x3, #2688, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2816, lsl #0
	movz x2, #2752, lsl #0
	movz x3, #320, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2816]
	ldr x2, [x0, #2824]
	orr x1, x1, x2
	ldr x2, [x0, #2832]
	orr x1, x1, x2
	ldr x2, [x0, #2840]
	orr x1, x1, x2
	ldr x2, [x0, #2848]
	orr x1, x1, x2
	ldr x2, [x0, #2856]
	orr x1, x1, x2
	ldr x2, [x0, #2864]
	orr x1, x1, x2
	ldr x2, [x0, #2872]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	ldr x3, [x0, #2880]
	ldr x1, [x0, #2368]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #56]
	ldr x1, [x0, #2376]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #48]
	ldr x1, [x0, #2384]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #40]
	ldr x1, [x0, #2392]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #32]
	ldr x1, [x0, #2400]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #24]
	ldr x1, [x0, #2408]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #16]
	ldr x1, [x0, #2416]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #8]
	ldr x1, [x0, #2424]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #0]
	ldr x1, [x0, #2816]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #120]
	ldr x1, [x0, #2824]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #112]
	ldr x1, [x0, #2832]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #104]
	ldr x1, [x0, #2840]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #96]
	ldr x1, [x0, #2848]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #88]
	ldr x1, [x0, #2856]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #80]
	ldr x1, [x0, #2864]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #72]
	ldr x1, [x0, #2872]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #64]
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

vg_ecdsa_brainpoolp512r1_verify:
	add x4, x3, #0
	add x6, x0, #0
	add x3, x2, #0
	add x8, x2, #64
	add x2, x0, #1
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
	ldr x5, [x8, #56]
	rev x5, x5
	str x5, [x0, #1984]
	ldr x5, [x8, #48]
	rev x5, x5
	str x5, [x0, #1992]
	ldr x5, [x8, #40]
	rev x5, x5
	str x5, [x0, #2000]
	ldr x5, [x8, #32]
	rev x5, x5
	str x5, [x0, #2008]
	ldr x5, [x8, #24]
	rev x5, x5
	str x5, [x0, #2016]
	ldr x5, [x8, #16]
	rev x5, x5
	str x5, [x0, #2024]
	ldr x5, [x8, #8]
	rev x5, x5
	str x5, [x0, #2032]
	ldr x5, [x8, #0]
	rev x5, x5
	str x5, [x0, #2040]
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
	movz x7, #0, lsl #0
	ldr x1, [x0, #2048]
	ldr x2, [x0, #128]
	subs x16, x1, x2
	ldr x1, [x0, #2056]
	ldr x2, [x0, #136]
	sbcs x16, x1, x2
	ldr x1, [x0, #2064]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #2072]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	ldr x1, [x0, #2080]
	ldr x2, [x0, #160]
	sbcs x16, x1, x2
	ldr x1, [x0, #2088]
	ldr x2, [x0, #168]
	sbcs x16, x1, x2
	ldr x1, [x0, #2096]
	ldr x2, [x0, #176]
	sbcs x16, x1, x2
	ldr x1, [x0, #2104]
	ldr x2, [x0, #184]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #2048]
	ldr x2, [x0, #2056]
	orr x1, x1, x2
	ldr x2, [x0, #2064]
	orr x1, x1, x2
	ldr x2, [x0, #2072]
	orr x1, x1, x2
	ldr x2, [x0, #2080]
	orr x1, x1, x2
	ldr x2, [x0, #2088]
	orr x1, x1, x2
	ldr x2, [x0, #2096]
	orr x1, x1, x2
	ldr x2, [x0, #2104]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1984]
	ldr x2, [x0, #128]
	subs x16, x1, x2
	ldr x1, [x0, #1992]
	ldr x2, [x0, #136]
	sbcs x16, x1, x2
	ldr x1, [x0, #2000]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #2008]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	ldr x1, [x0, #2016]
	ldr x2, [x0, #160]
	sbcs x16, x1, x2
	ldr x1, [x0, #2024]
	ldr x2, [x0, #168]
	sbcs x16, x1, x2
	ldr x1, [x0, #2032]
	ldr x2, [x0, #176]
	sbcs x16, x1, x2
	ldr x1, [x0, #2040]
	ldr x2, [x0, #184]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1984]
	ldr x2, [x0, #1992]
	orr x1, x1, x2
	ldr x2, [x0, #2000]
	orr x1, x1, x2
	ldr x2, [x0, #2008]
	orr x1, x1, x2
	ldr x2, [x0, #2016]
	orr x1, x1, x2
	ldr x2, [x0, #2024]
	orr x1, x1, x2
	ldr x2, [x0, #2032]
	orr x1, x1, x2
	ldr x2, [x0, #2040]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #2880]
	and x1, x1, x2
	str x1, [x0, #2880]
	mov v29.d[0], x30
	movz x1, #2432, lsl #0
	movz x2, #1984, lsl #0
	movz x3, #704, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	bl {vg_brainpoolp512r1_inv_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2624, lsl #0
	movz x2, #2112, lsl #0
	movz x3, #704, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2560, lsl #0
	movz x2, #2048, lsl #0
	movz x3, #704, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2688, lsl #0
	movz x2, #2624, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2752, lsl #0
	movz x2, #2560, lsl #0
	movz x3, #1920, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2240, lsl #0
	movz x2, #2688, lsl #0
	movz x3, #320, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2304, lsl #0
	movz x2, #2752, lsl #0
	movz x3, #320, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_n}
	umov x30, v29.d[0]
	movz x19, #64, lsl #0
	movz x5, #1, lsl #0
21:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #2240]
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
	cbnz x19, 21b
	movz x19, #64, lsl #0
	movz x5, #1, lsl #0
22:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #2304]
	lsl x17, x19, #3
	add x17, x0, x17
	and x2, x1, x5
	strb w2, [x17, #3456]
	lsr x2, x1, #1
	and x2, x2, x5
	strb w2, [x17, #3457]
	lsr x2, x1, #2
	and x2, x2, x5
	strb w2, [x17, #3458]
	lsr x2, x1, #3
	and x2, x2, x5
	strb w2, [x17, #3459]
	lsr x2, x1, #4
	and x2, x2, x5
	strb w2, [x17, #3460]
	lsr x2, x1, #5
	and x2, x2, x5
	strb w2, [x17, #3461]
	lsr x2, x1, #6
	and x2, x2, x5
	strb w2, [x17, #3462]
	lsr x2, x1, #7
	and x2, x2, x5
	strb w2, [x17, #3463]
	cbnz x19, 22b
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
	movz x19, #15, lsl #0
23:
	sub x19, x19, #1
	movz x5, #3, lsl #0
	and x2, x19, x5
	eor x2, x2, x5
	cbz x2, 24f
	movz x2, #14, lsl #0
	sub x2, x2, x19
	cbz x2, 26f
	sub x2, x2, #1
	movz x17, #192, lsl #0
	mul x2, x2, x17
	movz x16, #5280, lsl #0
	add x16, x0, x16
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #960]
	ldr x4, [x16, #8]
	str x4, [x0, #968]
	ldr x4, [x16, #16]
	str x4, [x0, #976]
	ldr x4, [x16, #24]
	str x4, [x0, #984]
	ldr x4, [x16, #32]
	str x4, [x0, #992]
	ldr x4, [x16, #40]
	str x4, [x0, #1000]
	ldr x4, [x16, #48]
	str x4, [x0, #1008]
	ldr x4, [x16, #56]
	str x4, [x0, #1016]
	ldr x4, [x16, #64]
	str x4, [x0, #1024]
	ldr x4, [x16, #72]
	str x4, [x0, #1032]
	ldr x4, [x16, #80]
	str x4, [x0, #1040]
	ldr x4, [x16, #88]
	str x4, [x0, #1048]
	ldr x4, [x16, #96]
	str x4, [x0, #1056]
	ldr x4, [x16, #104]
	str x4, [x0, #1064]
	ldr x4, [x16, #112]
	str x4, [x0, #1072]
	ldr x4, [x16, #120]
	str x4, [x0, #1080]
	ldr x4, [x16, #128]
	str x4, [x0, #1088]
	ldr x4, [x16, #136]
	str x4, [x0, #1096]
	ldr x4, [x16, #144]
	str x4, [x0, #1104]
	ldr x4, [x16, #152]
	str x4, [x0, #1112]
	ldr x4, [x16, #160]
	str x4, [x0, #1120]
	ldr x4, [x16, #168]
	str x4, [x0, #1128]
	ldr x4, [x16, #176]
	str x4, [x0, #1136]
	ldr x4, [x16, #184]
	str x4, [x0, #1144]
	b 27f
26:
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
27:
	ldr x1, [x0, #576]
	str x1, [x0, #2688]
	ldr x1, [x0, #584]
	str x1, [x0, #2696]
	ldr x1, [x0, #592]
	str x1, [x0, #2704]
	ldr x1, [x0, #600]
	str x1, [x0, #2712]
	ldr x1, [x0, #608]
	str x1, [x0, #2720]
	ldr x1, [x0, #616]
	str x1, [x0, #2728]
	ldr x1, [x0, #624]
	str x1, [x0, #2736]
	ldr x1, [x0, #632]
	str x1, [x0, #2744]
	ldr x1, [x0, #640]
	str x1, [x0, #2752]
	ldr x1, [x0, #648]
	str x1, [x0, #2760]
	ldr x1, [x0, #656]
	str x1, [x0, #2768]
	ldr x1, [x0, #664]
	str x1, [x0, #2776]
	ldr x1, [x0, #672]
	str x1, [x0, #2784]
	ldr x1, [x0, #680]
	str x1, [x0, #2792]
	ldr x1, [x0, #688]
	str x1, [x0, #2800]
	ldr x1, [x0, #696]
	str x1, [x0, #2808]
	ldr x1, [x0, #384]
	str x1, [x0, #2432]
	ldr x1, [x0, #392]
	str x1, [x0, #2440]
	ldr x1, [x0, #400]
	str x1, [x0, #2448]
	ldr x1, [x0, #408]
	str x1, [x0, #2456]
	ldr x1, [x0, #416]
	str x1, [x0, #2464]
	ldr x1, [x0, #424]
	str x1, [x0, #2472]
	ldr x1, [x0, #432]
	str x1, [x0, #2480]
	ldr x1, [x0, #440]
	str x1, [x0, #2488]
	b 25f
24:
	movz x2, #11, lsl #0
	sub x2, x2, x19
	cbz x2, 28f
	sub x2, x2, #1
	movz x17, #192, lsl #0
	mul x2, x2, x17
	movz x16, #5280, lsl #0
	add x16, x0, x16
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #960]
	ldr x4, [x16, #8]
	str x4, [x0, #968]
	ldr x4, [x16, #16]
	str x4, [x0, #976]
	ldr x4, [x16, #24]
	str x4, [x0, #984]
	ldr x4, [x16, #32]
	str x4, [x0, #992]
	ldr x4, [x16, #40]
	str x4, [x0, #1000]
	ldr x4, [x16, #48]
	str x4, [x0, #1008]
	ldr x4, [x16, #56]
	str x4, [x0, #1016]
	ldr x4, [x16, #64]
	str x4, [x0, #1024]
	ldr x4, [x16, #72]
	str x4, [x0, #1032]
	ldr x4, [x16, #80]
	str x4, [x0, #1040]
	ldr x4, [x16, #88]
	str x4, [x0, #1048]
	ldr x4, [x16, #96]
	str x4, [x0, #1056]
	ldr x4, [x16, #104]
	str x4, [x0, #1064]
	ldr x4, [x16, #112]
	str x4, [x0, #1072]
	ldr x4, [x16, #120]
	str x4, [x0, #1080]
	ldr x4, [x16, #128]
	str x4, [x0, #1088]
	ldr x4, [x16, #136]
	str x4, [x0, #1096]
	ldr x4, [x16, #144]
	str x4, [x0, #1104]
	ldr x4, [x16, #152]
	str x4, [x0, #1112]
	ldr x4, [x16, #160]
	str x4, [x0, #1120]
	ldr x4, [x16, #168]
	str x4, [x0, #1128]
	ldr x4, [x16, #176]
	str x4, [x0, #1136]
	ldr x4, [x16, #184]
	str x4, [x0, #1144]
	b 29f
28:
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
29:
	ldr x1, [x0, #2496]
	str x1, [x0, #2688]
	ldr x1, [x0, #2504]
	str x1, [x0, #2696]
	ldr x1, [x0, #2512]
	str x1, [x0, #2704]
	ldr x1, [x0, #2520]
	str x1, [x0, #2712]
	ldr x1, [x0, #2528]
	str x1, [x0, #2720]
	ldr x1, [x0, #2536]
	str x1, [x0, #2728]
	ldr x1, [x0, #2544]
	str x1, [x0, #2736]
	ldr x1, [x0, #2552]
	str x1, [x0, #2744]
	ldr x1, [x0, #2816]
	str x1, [x0, #2752]
	ldr x1, [x0, #2824]
	str x1, [x0, #2760]
	ldr x1, [x0, #2832]
	str x1, [x0, #2768]
	ldr x1, [x0, #2840]
	str x1, [x0, #2776]
	ldr x1, [x0, #2848]
	str x1, [x0, #2784]
	ldr x1, [x0, #2856]
	str x1, [x0, #2792]
	ldr x1, [x0, #2864]
	str x1, [x0, #2800]
	ldr x1, [x0, #2872]
	str x1, [x0, #2808]
	ldr x1, [x0, #384]
	str x1, [x0, #2432]
	ldr x1, [x0, #392]
	str x1, [x0, #2440]
	ldr x1, [x0, #400]
	str x1, [x0, #2448]
	ldr x1, [x0, #408]
	str x1, [x0, #2456]
	ldr x1, [x0, #416]
	str x1, [x0, #2464]
	ldr x1, [x0, #424]
	str x1, [x0, #2472]
	ldr x1, [x0, #432]
	str x1, [x0, #2480]
	ldr x1, [x0, #440]
	str x1, [x0, #2488]
25:
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #2688, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1600, lsl #0
	movz x2, #2752, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #2432, lsl #0
	movz x3, #1088, lsl #0
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
	adds x8, x8, x2
	ldr x2, [x0, #2760]
	adcs x9, x9, x2
	ldr x2, [x0, #2768]
	adcs x10, x10, x2
	ldr x2, [x0, #2776]
	adcs x11, x11, x2
	ldr x2, [x0, #2784]
	adcs x12, x12, x2
	ldr x2, [x0, #2792]
	adcs x13, x13, x2
	ldr x2, [x0, #2800]
	adcs x14, x14, x2
	ldr x2, [x0, #2808]
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
	str x8, [x0, #1728]
	str x9, [x0, #1736]
	str x10, [x0, #1744]
	str x11, [x0, #1752]
	str x12, [x0, #1760]
	str x13, [x0, #1768]
	str x14, [x0, #1776]
	str x15, [x0, #1784]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #1024]
	adds x8, x8, x2
	ldr x2, [x0, #1032]
	adcs x9, x9, x2
	ldr x2, [x0, #1040]
	adcs x10, x10, x2
	ldr x2, [x0, #1048]
	adcs x11, x11, x2
	ldr x2, [x0, #1056]
	adcs x12, x12, x2
	ldr x2, [x0, #1064]
	adcs x13, x13, x2
	ldr x2, [x0, #1072]
	adcs x14, x14, x2
	ldr x2, [x0, #1080]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	mov v29.d[0], x30
	movz x1, #1728, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1600]
	adds x8, x8, x2
	ldr x2, [x0, #1608]
	adcs x9, x9, x2
	ldr x2, [x0, #1616]
	adcs x10, x10, x2
	ldr x2, [x0, #1624]
	adcs x11, x11, x2
	ldr x2, [x0, #1632]
	adcs x12, x12, x2
	ldr x2, [x0, #1640]
	adcs x13, x13, x2
	ldr x2, [x0, #1648]
	adcs x14, x14, x2
	ldr x2, [x0, #1656]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1728]
	ldr x9, [x0, #1736]
	ldr x10, [x0, #1744]
	ldr x11, [x0, #1752]
	ldr x12, [x0, #1760]
	ldr x13, [x0, #1768]
	ldr x14, [x0, #1776]
	ldr x15, [x0, #1784]
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
	str x8, [x0, #1728]
	str x9, [x0, #1736]
	str x10, [x0, #1744]
	str x11, [x0, #1752]
	str x12, [x0, #1760]
	str x13, [x0, #1768]
	str x14, [x0, #1776]
	str x15, [x0, #1784]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2688]
	ldr x9, [x0, #2696]
	ldr x10, [x0, #2704]
	ldr x11, [x0, #2712]
	ldr x12, [x0, #2720]
	ldr x13, [x0, #2728]
	ldr x14, [x0, #2736]
	ldr x15, [x0, #2744]
	ldr x2, [x0, #2432]
	adds x8, x8, x2
	ldr x2, [x0, #2440]
	adcs x9, x9, x2
	ldr x2, [x0, #2448]
	adcs x10, x10, x2
	ldr x2, [x0, #2456]
	adcs x11, x11, x2
	ldr x2, [x0, #2464]
	adcs x12, x12, x2
	ldr x2, [x0, #2472]
	adcs x13, x13, x2
	ldr x2, [x0, #2480]
	adcs x14, x14, x2
	ldr x2, [x0, #2488]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #1088]
	adds x8, x8, x2
	ldr x2, [x0, #1096]
	adcs x9, x9, x2
	ldr x2, [x0, #1104]
	adcs x10, x10, x2
	ldr x2, [x0, #1112]
	adcs x11, x11, x2
	ldr x2, [x0, #1120]
	adcs x12, x12, x2
	ldr x2, [x0, #1128]
	adcs x13, x13, x2
	ldr x2, [x0, #1136]
	adcs x14, x14, x2
	ldr x2, [x0, #1144]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1856, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x2, [x0, #1856]
	subs x8, x8, x2
	ldr x2, [x0, #1864]
	sbcs x9, x9, x2
	ldr x2, [x0, #1872]
	sbcs x10, x10, x2
	ldr x2, [x0, #1880]
	sbcs x11, x11, x2
	ldr x2, [x0, #1888]
	sbcs x12, x12, x2
	ldr x2, [x0, #1896]
	sbcs x13, x13, x2
	ldr x2, [x0, #1904]
	sbcs x14, x14, x2
	ldr x2, [x0, #1912]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2752]
	ldr x9, [x0, #2760]
	ldr x10, [x0, #2768]
	ldr x11, [x0, #2776]
	ldr x12, [x0, #2784]
	ldr x13, [x0, #2792]
	ldr x14, [x0, #2800]
	ldr x15, [x0, #2808]
	ldr x2, [x0, #2432]
	adds x8, x8, x2
	ldr x2, [x0, #2440]
	adcs x9, x9, x2
	ldr x2, [x0, #2448]
	adcs x10, x10, x2
	ldr x2, [x0, #2456]
	adcs x11, x11, x2
	ldr x2, [x0, #2464]
	adcs x12, x12, x2
	ldr x2, [x0, #2472]
	adcs x13, x13, x2
	ldr x2, [x0, #2480]
	adcs x14, x14, x2
	ldr x2, [x0, #2488]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x14, [x0, #1072]
	ldr x15, [x0, #1080]
	ldr x2, [x0, #1088]
	adds x8, x8, x2
	ldr x2, [x0, #1096]
	adcs x9, x9, x2
	ldr x2, [x0, #1104]
	adcs x10, x10, x2
	ldr x2, [x0, #1112]
	adcs x11, x11, x2
	ldr x2, [x0, #1120]
	adcs x12, x12, x2
	ldr x2, [x0, #1128]
	adcs x13, x13, x2
	ldr x2, [x0, #1136]
	adcs x14, x14, x2
	ldr x2, [x0, #1144]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1856, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1856]
	ldr x9, [x0, #1864]
	ldr x10, [x0, #1872]
	ldr x11, [x0, #1880]
	ldr x12, [x0, #1888]
	ldr x13, [x0, #1896]
	ldr x14, [x0, #1904]
	ldr x15, [x0, #1912]
	ldr x2, [x0, #1152]
	subs x8, x8, x2
	ldr x2, [x0, #1160]
	sbcs x9, x9, x2
	ldr x2, [x0, #1168]
	sbcs x10, x10, x2
	ldr x2, [x0, #1176]
	sbcs x11, x11, x2
	ldr x2, [x0, #1184]
	sbcs x12, x12, x2
	ldr x2, [x0, #1192]
	sbcs x13, x13, x2
	ldr x2, [x0, #1200]
	sbcs x14, x14, x2
	ldr x2, [x0, #1208]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	mov v29.d[0], x30
	movz x1, #1280, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1152, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1152]
	ldr x9, [x0, #1160]
	ldr x10, [x0, #1168]
	ldr x11, [x0, #1176]
	ldr x12, [x0, #1184]
	ldr x13, [x0, #1192]
	ldr x14, [x0, #1200]
	ldr x15, [x0, #1208]
	ldr x2, [x0, #1280]
	adds x8, x8, x2
	ldr x2, [x0, #1288]
	adcs x9, x9, x2
	ldr x2, [x0, #1296]
	adcs x10, x10, x2
	ldr x2, [x0, #1304]
	adcs x11, x11, x2
	ldr x2, [x0, #1312]
	adcs x12, x12, x2
	ldr x2, [x0, #1320]
	adcs x13, x13, x2
	ldr x2, [x0, #1328]
	adcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1280]
	subs x8, x8, x2
	ldr x2, [x0, #1288]
	sbcs x9, x9, x2
	ldr x2, [x0, #1296]
	sbcs x10, x10, x2
	ldr x2, [x0, #1304]
	sbcs x11, x11, x2
	ldr x2, [x0, #1312]
	sbcs x12, x12, x2
	ldr x2, [x0, #1320]
	sbcs x13, x13, x2
	ldr x2, [x0, #1328]
	sbcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1280]
	adds x8, x8, x2
	ldr x2, [x0, #1288]
	adcs x9, x9, x2
	ldr x2, [x0, #1296]
	adcs x10, x10, x2
	ldr x2, [x0, #1304]
	adcs x11, x11, x2
	ldr x2, [x0, #1312]
	adcs x12, x12, x2
	ldr x2, [x0, #1320]
	adcs x13, x13, x2
	ldr x2, [x0, #1328]
	adcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1152, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1664]
	subs x8, x8, x2
	ldr x2, [x0, #1672]
	sbcs x9, x9, x2
	ldr x2, [x0, #1680]
	sbcs x10, x10, x2
	ldr x2, [x0, #1688]
	sbcs x11, x11, x2
	ldr x2, [x0, #1696]
	sbcs x12, x12, x2
	ldr x2, [x0, #1704]
	sbcs x13, x13, x2
	ldr x2, [x0, #1712]
	sbcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1664]
	str x9, [x0, #1672]
	str x10, [x0, #1680]
	str x11, [x0, #1688]
	str x12, [x0, #1696]
	str x13, [x0, #1704]
	str x14, [x0, #1712]
	str x15, [x0, #1720]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1600, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x14, [x0, #1264]
	ldr x15, [x0, #1272]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x14, [x0, #1264]
	str x15, [x0, #1272]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1152, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1152]
	ldr x9, [x0, #1160]
	ldr x10, [x0, #1168]
	ldr x11, [x0, #1176]
	ldr x12, [x0, #1184]
	ldr x13, [x0, #1192]
	ldr x14, [x0, #1200]
	ldr x15, [x0, #1208]
	ldr x2, [x0, #1536]
	subs x8, x8, x2
	ldr x2, [x0, #1544]
	sbcs x9, x9, x2
	ldr x2, [x0, #1552]
	sbcs x10, x10, x2
	ldr x2, [x0, #1560]
	sbcs x11, x11, x2
	ldr x2, [x0, #1568]
	sbcs x12, x12, x2
	ldr x2, [x0, #1576]
	sbcs x13, x13, x2
	ldr x2, [x0, #1584]
	sbcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1600, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1280, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1280]
	ldr x9, [x0, #1288]
	ldr x10, [x0, #1296]
	ldr x11, [x0, #1304]
	ldr x12, [x0, #1312]
	ldr x13, [x0, #1320]
	ldr x14, [x0, #1328]
	ldr x15, [x0, #1336]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	ldr x1, [x0, #1152]
	str x1, [x0, #960]
	ldr x1, [x0, #1160]
	str x1, [x0, #968]
	ldr x1, [x0, #1168]
	str x1, [x0, #976]
	ldr x1, [x0, #1176]
	str x1, [x0, #984]
	ldr x1, [x0, #1184]
	str x1, [x0, #992]
	ldr x1, [x0, #1192]
	str x1, [x0, #1000]
	ldr x1, [x0, #1200]
	str x1, [x0, #1008]
	ldr x1, [x0, #1208]
	str x1, [x0, #1016]
	ldr x1, [x0, #1216]
	str x1, [x0, #1024]
	ldr x1, [x0, #1224]
	str x1, [x0, #1032]
	ldr x1, [x0, #1232]
	str x1, [x0, #1040]
	ldr x1, [x0, #1240]
	str x1, [x0, #1048]
	ldr x1, [x0, #1248]
	str x1, [x0, #1056]
	ldr x1, [x0, #1256]
	str x1, [x0, #1064]
	ldr x1, [x0, #1264]
	str x1, [x0, #1072]
	ldr x1, [x0, #1272]
	str x1, [x0, #1080]
	ldr x1, [x0, #1280]
	str x1, [x0, #1088]
	ldr x1, [x0, #1288]
	str x1, [x0, #1096]
	ldr x1, [x0, #1296]
	str x1, [x0, #1104]
	ldr x1, [x0, #1304]
	str x1, [x0, #1112]
	ldr x1, [x0, #1312]
	str x1, [x0, #1120]
	ldr x1, [x0, #1320]
	str x1, [x0, #1128]
	ldr x1, [x0, #1328]
	str x1, [x0, #1136]
	ldr x1, [x0, #1336]
	str x1, [x0, #1144]
	movz x2, #15, lsl #0
	sub x2, x2, x19
	sub x2, x2, #1
	movz x17, #192, lsl #0
	mul x2, x2, x17
	movz x16, #5280, lsl #0
	add x16, x0, x16
	add x16, x16, x2
	ldr x4, [x0, #960]
	str x4, [x16, #0]
	ldr x4, [x0, #968]
	str x4, [x16, #8]
	ldr x4, [x0, #976]
	str x4, [x16, #16]
	ldr x4, [x0, #984]
	str x4, [x16, #24]
	ldr x4, [x0, #992]
	str x4, [x16, #32]
	ldr x4, [x0, #1000]
	str x4, [x16, #40]
	ldr x4, [x0, #1008]
	str x4, [x16, #48]
	ldr x4, [x0, #1016]
	str x4, [x16, #56]
	ldr x4, [x0, #1024]
	str x4, [x16, #64]
	ldr x4, [x0, #1032]
	str x4, [x16, #72]
	ldr x4, [x0, #1040]
	str x4, [x16, #80]
	ldr x4, [x0, #1048]
	str x4, [x16, #88]
	ldr x4, [x0, #1056]
	str x4, [x16, #96]
	ldr x4, [x0, #1064]
	str x4, [x16, #104]
	ldr x4, [x0, #1072]
	str x4, [x16, #112]
	ldr x4, [x0, #1080]
	str x4, [x16, #120]
	ldr x4, [x0, #1088]
	str x4, [x16, #128]
	ldr x4, [x0, #1096]
	str x4, [x16, #136]
	ldr x4, [x0, #1104]
	str x4, [x16, #144]
	ldr x4, [x0, #1112]
	str x4, [x16, #152]
	ldr x4, [x0, #1120]
	str x4, [x16, #160]
	ldr x4, [x0, #1128]
	str x4, [x16, #168]
	ldr x4, [x0, #1136]
	str x4, [x16, #176]
	ldr x4, [x0, #1144]
	str x4, [x16, #184]
	cbnz x19, 23b
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
	movz x19, #256, lsl #0
210:
	sub x19, x19, #1
	ldr x1, [x0, #960]
	str x1, [x0, #2688]
	ldr x1, [x0, #968]
	str x1, [x0, #2696]
	ldr x1, [x0, #976]
	str x1, [x0, #2704]
	ldr x1, [x0, #984]
	str x1, [x0, #2712]
	ldr x1, [x0, #992]
	str x1, [x0, #2720]
	ldr x1, [x0, #1000]
	str x1, [x0, #2728]
	ldr x1, [x0, #1008]
	str x1, [x0, #2736]
	ldr x1, [x0, #1016]
	str x1, [x0, #2744]
	ldr x1, [x0, #1024]
	str x1, [x0, #2752]
	ldr x1, [x0, #1032]
	str x1, [x0, #2760]
	ldr x1, [x0, #1040]
	str x1, [x0, #2768]
	ldr x1, [x0, #1048]
	str x1, [x0, #2776]
	ldr x1, [x0, #1056]
	str x1, [x0, #2784]
	ldr x1, [x0, #1064]
	str x1, [x0, #2792]
	ldr x1, [x0, #1072]
	str x1, [x0, #2800]
	ldr x1, [x0, #1080]
	str x1, [x0, #2808]
	ldr x1, [x0, #1088]
	str x1, [x0, #2432]
	ldr x1, [x0, #1096]
	str x1, [x0, #2440]
	ldr x1, [x0, #1104]
	str x1, [x0, #2448]
	ldr x1, [x0, #1112]
	str x1, [x0, #2456]
	ldr x1, [x0, #1120]
	str x1, [x0, #2464]
	ldr x1, [x0, #1128]
	str x1, [x0, #2472]
	ldr x1, [x0, #1136]
	str x1, [x0, #2480]
	ldr x1, [x0, #1144]
	str x1, [x0, #2488]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #2688, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1600, lsl #0
	movz x2, #2752, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #2432, lsl #0
	movz x3, #1088, lsl #0
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
	adds x8, x8, x2
	ldr x2, [x0, #2760]
	adcs x9, x9, x2
	ldr x2, [x0, #2768]
	adcs x10, x10, x2
	ldr x2, [x0, #2776]
	adcs x11, x11, x2
	ldr x2, [x0, #2784]
	adcs x12, x12, x2
	ldr x2, [x0, #2792]
	adcs x13, x13, x2
	ldr x2, [x0, #2800]
	adcs x14, x14, x2
	ldr x2, [x0, #2808]
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
	str x8, [x0, #1728]
	str x9, [x0, #1736]
	str x10, [x0, #1744]
	str x11, [x0, #1752]
	str x12, [x0, #1760]
	str x13, [x0, #1768]
	str x14, [x0, #1776]
	str x15, [x0, #1784]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #1024]
	adds x8, x8, x2
	ldr x2, [x0, #1032]
	adcs x9, x9, x2
	ldr x2, [x0, #1040]
	adcs x10, x10, x2
	ldr x2, [x0, #1048]
	adcs x11, x11, x2
	ldr x2, [x0, #1056]
	adcs x12, x12, x2
	ldr x2, [x0, #1064]
	adcs x13, x13, x2
	ldr x2, [x0, #1072]
	adcs x14, x14, x2
	ldr x2, [x0, #1080]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	mov v29.d[0], x30
	movz x1, #1728, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1600]
	adds x8, x8, x2
	ldr x2, [x0, #1608]
	adcs x9, x9, x2
	ldr x2, [x0, #1616]
	adcs x10, x10, x2
	ldr x2, [x0, #1624]
	adcs x11, x11, x2
	ldr x2, [x0, #1632]
	adcs x12, x12, x2
	ldr x2, [x0, #1640]
	adcs x13, x13, x2
	ldr x2, [x0, #1648]
	adcs x14, x14, x2
	ldr x2, [x0, #1656]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1728]
	ldr x9, [x0, #1736]
	ldr x10, [x0, #1744]
	ldr x11, [x0, #1752]
	ldr x12, [x0, #1760]
	ldr x13, [x0, #1768]
	ldr x14, [x0, #1776]
	ldr x15, [x0, #1784]
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
	str x8, [x0, #1728]
	str x9, [x0, #1736]
	str x10, [x0, #1744]
	str x11, [x0, #1752]
	str x12, [x0, #1760]
	str x13, [x0, #1768]
	str x14, [x0, #1776]
	str x15, [x0, #1784]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2688]
	ldr x9, [x0, #2696]
	ldr x10, [x0, #2704]
	ldr x11, [x0, #2712]
	ldr x12, [x0, #2720]
	ldr x13, [x0, #2728]
	ldr x14, [x0, #2736]
	ldr x15, [x0, #2744]
	ldr x2, [x0, #2432]
	adds x8, x8, x2
	ldr x2, [x0, #2440]
	adcs x9, x9, x2
	ldr x2, [x0, #2448]
	adcs x10, x10, x2
	ldr x2, [x0, #2456]
	adcs x11, x11, x2
	ldr x2, [x0, #2464]
	adcs x12, x12, x2
	ldr x2, [x0, #2472]
	adcs x13, x13, x2
	ldr x2, [x0, #2480]
	adcs x14, x14, x2
	ldr x2, [x0, #2488]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #1088]
	adds x8, x8, x2
	ldr x2, [x0, #1096]
	adcs x9, x9, x2
	ldr x2, [x0, #1104]
	adcs x10, x10, x2
	ldr x2, [x0, #1112]
	adcs x11, x11, x2
	ldr x2, [x0, #1120]
	adcs x12, x12, x2
	ldr x2, [x0, #1128]
	adcs x13, x13, x2
	ldr x2, [x0, #1136]
	adcs x14, x14, x2
	ldr x2, [x0, #1144]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1856, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x2, [x0, #1856]
	subs x8, x8, x2
	ldr x2, [x0, #1864]
	sbcs x9, x9, x2
	ldr x2, [x0, #1872]
	sbcs x10, x10, x2
	ldr x2, [x0, #1880]
	sbcs x11, x11, x2
	ldr x2, [x0, #1888]
	sbcs x12, x12, x2
	ldr x2, [x0, #1896]
	sbcs x13, x13, x2
	ldr x2, [x0, #1904]
	sbcs x14, x14, x2
	ldr x2, [x0, #1912]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2752]
	ldr x9, [x0, #2760]
	ldr x10, [x0, #2768]
	ldr x11, [x0, #2776]
	ldr x12, [x0, #2784]
	ldr x13, [x0, #2792]
	ldr x14, [x0, #2800]
	ldr x15, [x0, #2808]
	ldr x2, [x0, #2432]
	adds x8, x8, x2
	ldr x2, [x0, #2440]
	adcs x9, x9, x2
	ldr x2, [x0, #2448]
	adcs x10, x10, x2
	ldr x2, [x0, #2456]
	adcs x11, x11, x2
	ldr x2, [x0, #2464]
	adcs x12, x12, x2
	ldr x2, [x0, #2472]
	adcs x13, x13, x2
	ldr x2, [x0, #2480]
	adcs x14, x14, x2
	ldr x2, [x0, #2488]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x14, [x0, #1072]
	ldr x15, [x0, #1080]
	ldr x2, [x0, #1088]
	adds x8, x8, x2
	ldr x2, [x0, #1096]
	adcs x9, x9, x2
	ldr x2, [x0, #1104]
	adcs x10, x10, x2
	ldr x2, [x0, #1112]
	adcs x11, x11, x2
	ldr x2, [x0, #1120]
	adcs x12, x12, x2
	ldr x2, [x0, #1128]
	adcs x13, x13, x2
	ldr x2, [x0, #1136]
	adcs x14, x14, x2
	ldr x2, [x0, #1144]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1856, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1856]
	ldr x9, [x0, #1864]
	ldr x10, [x0, #1872]
	ldr x11, [x0, #1880]
	ldr x12, [x0, #1888]
	ldr x13, [x0, #1896]
	ldr x14, [x0, #1904]
	ldr x15, [x0, #1912]
	ldr x2, [x0, #1152]
	subs x8, x8, x2
	ldr x2, [x0, #1160]
	sbcs x9, x9, x2
	ldr x2, [x0, #1168]
	sbcs x10, x10, x2
	ldr x2, [x0, #1176]
	sbcs x11, x11, x2
	ldr x2, [x0, #1184]
	sbcs x12, x12, x2
	ldr x2, [x0, #1192]
	sbcs x13, x13, x2
	ldr x2, [x0, #1200]
	sbcs x14, x14, x2
	ldr x2, [x0, #1208]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	mov v29.d[0], x30
	movz x1, #1280, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1152, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1152]
	ldr x9, [x0, #1160]
	ldr x10, [x0, #1168]
	ldr x11, [x0, #1176]
	ldr x12, [x0, #1184]
	ldr x13, [x0, #1192]
	ldr x14, [x0, #1200]
	ldr x15, [x0, #1208]
	ldr x2, [x0, #1280]
	adds x8, x8, x2
	ldr x2, [x0, #1288]
	adcs x9, x9, x2
	ldr x2, [x0, #1296]
	adcs x10, x10, x2
	ldr x2, [x0, #1304]
	adcs x11, x11, x2
	ldr x2, [x0, #1312]
	adcs x12, x12, x2
	ldr x2, [x0, #1320]
	adcs x13, x13, x2
	ldr x2, [x0, #1328]
	adcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1280]
	subs x8, x8, x2
	ldr x2, [x0, #1288]
	sbcs x9, x9, x2
	ldr x2, [x0, #1296]
	sbcs x10, x10, x2
	ldr x2, [x0, #1304]
	sbcs x11, x11, x2
	ldr x2, [x0, #1312]
	sbcs x12, x12, x2
	ldr x2, [x0, #1320]
	sbcs x13, x13, x2
	ldr x2, [x0, #1328]
	sbcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1280]
	adds x8, x8, x2
	ldr x2, [x0, #1288]
	adcs x9, x9, x2
	ldr x2, [x0, #1296]
	adcs x10, x10, x2
	ldr x2, [x0, #1304]
	adcs x11, x11, x2
	ldr x2, [x0, #1312]
	adcs x12, x12, x2
	ldr x2, [x0, #1320]
	adcs x13, x13, x2
	ldr x2, [x0, #1328]
	adcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1152, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1664]
	subs x8, x8, x2
	ldr x2, [x0, #1672]
	sbcs x9, x9, x2
	ldr x2, [x0, #1680]
	sbcs x10, x10, x2
	ldr x2, [x0, #1688]
	sbcs x11, x11, x2
	ldr x2, [x0, #1696]
	sbcs x12, x12, x2
	ldr x2, [x0, #1704]
	sbcs x13, x13, x2
	ldr x2, [x0, #1712]
	sbcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1664]
	str x9, [x0, #1672]
	str x10, [x0, #1680]
	str x11, [x0, #1688]
	str x12, [x0, #1696]
	str x13, [x0, #1704]
	str x14, [x0, #1712]
	str x15, [x0, #1720]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1600, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x14, [x0, #1264]
	ldr x15, [x0, #1272]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x14, [x0, #1264]
	str x15, [x0, #1272]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1152, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1152]
	ldr x9, [x0, #1160]
	ldr x10, [x0, #1168]
	ldr x11, [x0, #1176]
	ldr x12, [x0, #1184]
	ldr x13, [x0, #1192]
	ldr x14, [x0, #1200]
	ldr x15, [x0, #1208]
	ldr x2, [x0, #1536]
	subs x8, x8, x2
	ldr x2, [x0, #1544]
	sbcs x9, x9, x2
	ldr x2, [x0, #1552]
	sbcs x10, x10, x2
	ldr x2, [x0, #1560]
	sbcs x11, x11, x2
	ldr x2, [x0, #1568]
	sbcs x12, x12, x2
	ldr x2, [x0, #1576]
	sbcs x13, x13, x2
	ldr x2, [x0, #1584]
	sbcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1600, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1280, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1280]
	ldr x9, [x0, #1288]
	ldr x10, [x0, #1296]
	ldr x11, [x0, #1304]
	ldr x12, [x0, #1312]
	ldr x13, [x0, #1320]
	ldr x14, [x0, #1328]
	ldr x15, [x0, #1336]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	ldr x1, [x0, #1152]
	str x1, [x0, #960]
	ldr x1, [x0, #1160]
	str x1, [x0, #968]
	ldr x1, [x0, #1168]
	str x1, [x0, #976]
	ldr x1, [x0, #1176]
	str x1, [x0, #984]
	ldr x1, [x0, #1184]
	str x1, [x0, #992]
	ldr x1, [x0, #1192]
	str x1, [x0, #1000]
	ldr x1, [x0, #1200]
	str x1, [x0, #1008]
	ldr x1, [x0, #1208]
	str x1, [x0, #1016]
	ldr x1, [x0, #1216]
	str x1, [x0, #1024]
	ldr x1, [x0, #1224]
	str x1, [x0, #1032]
	ldr x1, [x0, #1232]
	str x1, [x0, #1040]
	ldr x1, [x0, #1240]
	str x1, [x0, #1048]
	ldr x1, [x0, #1248]
	str x1, [x0, #1056]
	ldr x1, [x0, #1256]
	str x1, [x0, #1064]
	ldr x1, [x0, #1264]
	str x1, [x0, #1072]
	ldr x1, [x0, #1272]
	str x1, [x0, #1080]
	ldr x1, [x0, #1280]
	str x1, [x0, #1088]
	ldr x1, [x0, #1288]
	str x1, [x0, #1096]
	ldr x1, [x0, #1296]
	str x1, [x0, #1104]
	ldr x1, [x0, #1304]
	str x1, [x0, #1112]
	ldr x1, [x0, #1312]
	str x1, [x0, #1120]
	ldr x1, [x0, #1320]
	str x1, [x0, #1128]
	ldr x1, [x0, #1328]
	str x1, [x0, #1136]
	ldr x1, [x0, #1336]
	str x1, [x0, #1144]
	ldr x1, [x0, #960]
	str x1, [x0, #2688]
	ldr x1, [x0, #968]
	str x1, [x0, #2696]
	ldr x1, [x0, #976]
	str x1, [x0, #2704]
	ldr x1, [x0, #984]
	str x1, [x0, #2712]
	ldr x1, [x0, #992]
	str x1, [x0, #2720]
	ldr x1, [x0, #1000]
	str x1, [x0, #2728]
	ldr x1, [x0, #1008]
	str x1, [x0, #2736]
	ldr x1, [x0, #1016]
	str x1, [x0, #2744]
	ldr x1, [x0, #1024]
	str x1, [x0, #2752]
	ldr x1, [x0, #1032]
	str x1, [x0, #2760]
	ldr x1, [x0, #1040]
	str x1, [x0, #2768]
	ldr x1, [x0, #1048]
	str x1, [x0, #2776]
	ldr x1, [x0, #1056]
	str x1, [x0, #2784]
	ldr x1, [x0, #1064]
	str x1, [x0, #2792]
	ldr x1, [x0, #1072]
	str x1, [x0, #2800]
	ldr x1, [x0, #1080]
	str x1, [x0, #2808]
	ldr x1, [x0, #1088]
	str x1, [x0, #2432]
	ldr x1, [x0, #1096]
	str x1, [x0, #2440]
	ldr x1, [x0, #1104]
	str x1, [x0, #2448]
	ldr x1, [x0, #1112]
	str x1, [x0, #2456]
	ldr x1, [x0, #1120]
	str x1, [x0, #2464]
	ldr x1, [x0, #1128]
	str x1, [x0, #2472]
	ldr x1, [x0, #1136]
	str x1, [x0, #2480]
	ldr x1, [x0, #1144]
	str x1, [x0, #2488]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #2688, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1600, lsl #0
	movz x2, #2752, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #2432, lsl #0
	movz x3, #1088, lsl #0
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
	adds x8, x8, x2
	ldr x2, [x0, #2760]
	adcs x9, x9, x2
	ldr x2, [x0, #2768]
	adcs x10, x10, x2
	ldr x2, [x0, #2776]
	adcs x11, x11, x2
	ldr x2, [x0, #2784]
	adcs x12, x12, x2
	ldr x2, [x0, #2792]
	adcs x13, x13, x2
	ldr x2, [x0, #2800]
	adcs x14, x14, x2
	ldr x2, [x0, #2808]
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
	str x8, [x0, #1728]
	str x9, [x0, #1736]
	str x10, [x0, #1744]
	str x11, [x0, #1752]
	str x12, [x0, #1760]
	str x13, [x0, #1768]
	str x14, [x0, #1776]
	str x15, [x0, #1784]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #1024]
	adds x8, x8, x2
	ldr x2, [x0, #1032]
	adcs x9, x9, x2
	ldr x2, [x0, #1040]
	adcs x10, x10, x2
	ldr x2, [x0, #1048]
	adcs x11, x11, x2
	ldr x2, [x0, #1056]
	adcs x12, x12, x2
	ldr x2, [x0, #1064]
	adcs x13, x13, x2
	ldr x2, [x0, #1072]
	adcs x14, x14, x2
	ldr x2, [x0, #1080]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	mov v29.d[0], x30
	movz x1, #1728, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1600]
	adds x8, x8, x2
	ldr x2, [x0, #1608]
	adcs x9, x9, x2
	ldr x2, [x0, #1616]
	adcs x10, x10, x2
	ldr x2, [x0, #1624]
	adcs x11, x11, x2
	ldr x2, [x0, #1632]
	adcs x12, x12, x2
	ldr x2, [x0, #1640]
	adcs x13, x13, x2
	ldr x2, [x0, #1648]
	adcs x14, x14, x2
	ldr x2, [x0, #1656]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1728]
	ldr x9, [x0, #1736]
	ldr x10, [x0, #1744]
	ldr x11, [x0, #1752]
	ldr x12, [x0, #1760]
	ldr x13, [x0, #1768]
	ldr x14, [x0, #1776]
	ldr x15, [x0, #1784]
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
	str x8, [x0, #1728]
	str x9, [x0, #1736]
	str x10, [x0, #1744]
	str x11, [x0, #1752]
	str x12, [x0, #1760]
	str x13, [x0, #1768]
	str x14, [x0, #1776]
	str x15, [x0, #1784]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2688]
	ldr x9, [x0, #2696]
	ldr x10, [x0, #2704]
	ldr x11, [x0, #2712]
	ldr x12, [x0, #2720]
	ldr x13, [x0, #2728]
	ldr x14, [x0, #2736]
	ldr x15, [x0, #2744]
	ldr x2, [x0, #2432]
	adds x8, x8, x2
	ldr x2, [x0, #2440]
	adcs x9, x9, x2
	ldr x2, [x0, #2448]
	adcs x10, x10, x2
	ldr x2, [x0, #2456]
	adcs x11, x11, x2
	ldr x2, [x0, #2464]
	adcs x12, x12, x2
	ldr x2, [x0, #2472]
	adcs x13, x13, x2
	ldr x2, [x0, #2480]
	adcs x14, x14, x2
	ldr x2, [x0, #2488]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #1088]
	adds x8, x8, x2
	ldr x2, [x0, #1096]
	adcs x9, x9, x2
	ldr x2, [x0, #1104]
	adcs x10, x10, x2
	ldr x2, [x0, #1112]
	adcs x11, x11, x2
	ldr x2, [x0, #1120]
	adcs x12, x12, x2
	ldr x2, [x0, #1128]
	adcs x13, x13, x2
	ldr x2, [x0, #1136]
	adcs x14, x14, x2
	ldr x2, [x0, #1144]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1856, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x2, [x0, #1856]
	subs x8, x8, x2
	ldr x2, [x0, #1864]
	sbcs x9, x9, x2
	ldr x2, [x0, #1872]
	sbcs x10, x10, x2
	ldr x2, [x0, #1880]
	sbcs x11, x11, x2
	ldr x2, [x0, #1888]
	sbcs x12, x12, x2
	ldr x2, [x0, #1896]
	sbcs x13, x13, x2
	ldr x2, [x0, #1904]
	sbcs x14, x14, x2
	ldr x2, [x0, #1912]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2752]
	ldr x9, [x0, #2760]
	ldr x10, [x0, #2768]
	ldr x11, [x0, #2776]
	ldr x12, [x0, #2784]
	ldr x13, [x0, #2792]
	ldr x14, [x0, #2800]
	ldr x15, [x0, #2808]
	ldr x2, [x0, #2432]
	adds x8, x8, x2
	ldr x2, [x0, #2440]
	adcs x9, x9, x2
	ldr x2, [x0, #2448]
	adcs x10, x10, x2
	ldr x2, [x0, #2456]
	adcs x11, x11, x2
	ldr x2, [x0, #2464]
	adcs x12, x12, x2
	ldr x2, [x0, #2472]
	adcs x13, x13, x2
	ldr x2, [x0, #2480]
	adcs x14, x14, x2
	ldr x2, [x0, #2488]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x14, [x0, #1072]
	ldr x15, [x0, #1080]
	ldr x2, [x0, #1088]
	adds x8, x8, x2
	ldr x2, [x0, #1096]
	adcs x9, x9, x2
	ldr x2, [x0, #1104]
	adcs x10, x10, x2
	ldr x2, [x0, #1112]
	adcs x11, x11, x2
	ldr x2, [x0, #1120]
	adcs x12, x12, x2
	ldr x2, [x0, #1128]
	adcs x13, x13, x2
	ldr x2, [x0, #1136]
	adcs x14, x14, x2
	ldr x2, [x0, #1144]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1856, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1856]
	ldr x9, [x0, #1864]
	ldr x10, [x0, #1872]
	ldr x11, [x0, #1880]
	ldr x12, [x0, #1888]
	ldr x13, [x0, #1896]
	ldr x14, [x0, #1904]
	ldr x15, [x0, #1912]
	ldr x2, [x0, #1152]
	subs x8, x8, x2
	ldr x2, [x0, #1160]
	sbcs x9, x9, x2
	ldr x2, [x0, #1168]
	sbcs x10, x10, x2
	ldr x2, [x0, #1176]
	sbcs x11, x11, x2
	ldr x2, [x0, #1184]
	sbcs x12, x12, x2
	ldr x2, [x0, #1192]
	sbcs x13, x13, x2
	ldr x2, [x0, #1200]
	sbcs x14, x14, x2
	ldr x2, [x0, #1208]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	mov v29.d[0], x30
	movz x1, #1280, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1152, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1152]
	ldr x9, [x0, #1160]
	ldr x10, [x0, #1168]
	ldr x11, [x0, #1176]
	ldr x12, [x0, #1184]
	ldr x13, [x0, #1192]
	ldr x14, [x0, #1200]
	ldr x15, [x0, #1208]
	ldr x2, [x0, #1280]
	adds x8, x8, x2
	ldr x2, [x0, #1288]
	adcs x9, x9, x2
	ldr x2, [x0, #1296]
	adcs x10, x10, x2
	ldr x2, [x0, #1304]
	adcs x11, x11, x2
	ldr x2, [x0, #1312]
	adcs x12, x12, x2
	ldr x2, [x0, #1320]
	adcs x13, x13, x2
	ldr x2, [x0, #1328]
	adcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1280]
	subs x8, x8, x2
	ldr x2, [x0, #1288]
	sbcs x9, x9, x2
	ldr x2, [x0, #1296]
	sbcs x10, x10, x2
	ldr x2, [x0, #1304]
	sbcs x11, x11, x2
	ldr x2, [x0, #1312]
	sbcs x12, x12, x2
	ldr x2, [x0, #1320]
	sbcs x13, x13, x2
	ldr x2, [x0, #1328]
	sbcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1280]
	adds x8, x8, x2
	ldr x2, [x0, #1288]
	adcs x9, x9, x2
	ldr x2, [x0, #1296]
	adcs x10, x10, x2
	ldr x2, [x0, #1304]
	adcs x11, x11, x2
	ldr x2, [x0, #1312]
	adcs x12, x12, x2
	ldr x2, [x0, #1320]
	adcs x13, x13, x2
	ldr x2, [x0, #1328]
	adcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1152, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1664]
	subs x8, x8, x2
	ldr x2, [x0, #1672]
	sbcs x9, x9, x2
	ldr x2, [x0, #1680]
	sbcs x10, x10, x2
	ldr x2, [x0, #1688]
	sbcs x11, x11, x2
	ldr x2, [x0, #1696]
	sbcs x12, x12, x2
	ldr x2, [x0, #1704]
	sbcs x13, x13, x2
	ldr x2, [x0, #1712]
	sbcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1664]
	str x9, [x0, #1672]
	str x10, [x0, #1680]
	str x11, [x0, #1688]
	str x12, [x0, #1696]
	str x13, [x0, #1704]
	str x14, [x0, #1712]
	str x15, [x0, #1720]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1600, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x14, [x0, #1264]
	ldr x15, [x0, #1272]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x14, [x0, #1264]
	str x15, [x0, #1272]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1152, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1152]
	ldr x9, [x0, #1160]
	ldr x10, [x0, #1168]
	ldr x11, [x0, #1176]
	ldr x12, [x0, #1184]
	ldr x13, [x0, #1192]
	ldr x14, [x0, #1200]
	ldr x15, [x0, #1208]
	ldr x2, [x0, #1536]
	subs x8, x8, x2
	ldr x2, [x0, #1544]
	sbcs x9, x9, x2
	ldr x2, [x0, #1552]
	sbcs x10, x10, x2
	ldr x2, [x0, #1560]
	sbcs x11, x11, x2
	ldr x2, [x0, #1568]
	sbcs x12, x12, x2
	ldr x2, [x0, #1576]
	sbcs x13, x13, x2
	ldr x2, [x0, #1584]
	sbcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1600, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1280, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1280]
	ldr x9, [x0, #1288]
	ldr x10, [x0, #1296]
	ldr x11, [x0, #1304]
	ldr x12, [x0, #1312]
	ldr x13, [x0, #1320]
	ldr x14, [x0, #1328]
	ldr x15, [x0, #1336]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	ldr x1, [x0, #1152]
	str x1, [x0, #960]
	ldr x1, [x0, #1160]
	str x1, [x0, #968]
	ldr x1, [x0, #1168]
	str x1, [x0, #976]
	ldr x1, [x0, #1176]
	str x1, [x0, #984]
	ldr x1, [x0, #1184]
	str x1, [x0, #992]
	ldr x1, [x0, #1192]
	str x1, [x0, #1000]
	ldr x1, [x0, #1200]
	str x1, [x0, #1008]
	ldr x1, [x0, #1208]
	str x1, [x0, #1016]
	ldr x1, [x0, #1216]
	str x1, [x0, #1024]
	ldr x1, [x0, #1224]
	str x1, [x0, #1032]
	ldr x1, [x0, #1232]
	str x1, [x0, #1040]
	ldr x1, [x0, #1240]
	str x1, [x0, #1048]
	ldr x1, [x0, #1248]
	str x1, [x0, #1056]
	ldr x1, [x0, #1256]
	str x1, [x0, #1064]
	ldr x1, [x0, #1264]
	str x1, [x0, #1072]
	ldr x1, [x0, #1272]
	str x1, [x0, #1080]
	ldr x1, [x0, #1280]
	str x1, [x0, #1088]
	ldr x1, [x0, #1288]
	str x1, [x0, #1096]
	ldr x1, [x0, #1296]
	str x1, [x0, #1104]
	ldr x1, [x0, #1304]
	str x1, [x0, #1112]
	ldr x1, [x0, #1312]
	str x1, [x0, #1120]
	ldr x1, [x0, #1320]
	str x1, [x0, #1128]
	ldr x1, [x0, #1328]
	str x1, [x0, #1136]
	ldr x1, [x0, #1336]
	str x1, [x0, #1144]
	lsl x16, x19, #1
	add x16, x0, x16
	movz x2, #0, lsl #0
	add x2, x2, x2
	ldrb w4, [x16, #2945]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2944]
	add x2, x2, x4
	add x6, x2, #0
	movz x2, #0, lsl #0
	add x2, x2, x2
	ldrb w4, [x16, #3457]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #3456]
	add x2, x2, x4
	lsl x2, x2, #2
	add x2, x2, x6
	cbz x2, 211f
	sub x2, x2, #1
	movz x17, #192, lsl #0
	mul x2, x2, x17
	movz x16, #5280, lsl #0
	add x16, x0, x16
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #2688]
	ldr x4, [x16, #8]
	str x4, [x0, #2696]
	ldr x4, [x16, #16]
	str x4, [x0, #2704]
	ldr x4, [x16, #24]
	str x4, [x0, #2712]
	ldr x4, [x16, #32]
	str x4, [x0, #2720]
	ldr x4, [x16, #40]
	str x4, [x0, #2728]
	ldr x4, [x16, #48]
	str x4, [x0, #2736]
	ldr x4, [x16, #56]
	str x4, [x0, #2744]
	ldr x4, [x16, #64]
	str x4, [x0, #2752]
	ldr x4, [x16, #72]
	str x4, [x0, #2760]
	ldr x4, [x16, #80]
	str x4, [x0, #2768]
	ldr x4, [x16, #88]
	str x4, [x0, #2776]
	ldr x4, [x16, #96]
	str x4, [x0, #2784]
	ldr x4, [x16, #104]
	str x4, [x0, #2792]
	ldr x4, [x16, #112]
	str x4, [x0, #2800]
	ldr x4, [x16, #120]
	str x4, [x0, #2808]
	ldr x4, [x16, #128]
	str x4, [x0, #2432]
	ldr x4, [x16, #136]
	str x4, [x0, #2440]
	ldr x4, [x16, #144]
	str x4, [x0, #2448]
	ldr x4, [x16, #152]
	str x4, [x0, #2456]
	ldr x4, [x16, #160]
	str x4, [x0, #2464]
	ldr x4, [x16, #168]
	str x4, [x0, #2472]
	ldr x4, [x16, #176]
	str x4, [x0, #2480]
	ldr x4, [x16, #184]
	str x4, [x0, #2488]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #2688, lsl #0
	movz x3, #960, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1600, lsl #0
	movz x2, #2752, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #2432, lsl #0
	movz x3, #1088, lsl #0
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
	adds x8, x8, x2
	ldr x2, [x0, #2760]
	adcs x9, x9, x2
	ldr x2, [x0, #2768]
	adcs x10, x10, x2
	ldr x2, [x0, #2776]
	adcs x11, x11, x2
	ldr x2, [x0, #2784]
	adcs x12, x12, x2
	ldr x2, [x0, #2792]
	adcs x13, x13, x2
	ldr x2, [x0, #2800]
	adcs x14, x14, x2
	ldr x2, [x0, #2808]
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
	str x8, [x0, #1728]
	str x9, [x0, #1736]
	str x10, [x0, #1744]
	str x11, [x0, #1752]
	str x12, [x0, #1760]
	str x13, [x0, #1768]
	str x14, [x0, #1776]
	str x15, [x0, #1784]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #1024]
	adds x8, x8, x2
	ldr x2, [x0, #1032]
	adcs x9, x9, x2
	ldr x2, [x0, #1040]
	adcs x10, x10, x2
	ldr x2, [x0, #1048]
	adcs x11, x11, x2
	ldr x2, [x0, #1056]
	adcs x12, x12, x2
	ldr x2, [x0, #1064]
	adcs x13, x13, x2
	ldr x2, [x0, #1072]
	adcs x14, x14, x2
	ldr x2, [x0, #1080]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	mov v29.d[0], x30
	movz x1, #1728, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1600]
	adds x8, x8, x2
	ldr x2, [x0, #1608]
	adcs x9, x9, x2
	ldr x2, [x0, #1616]
	adcs x10, x10, x2
	ldr x2, [x0, #1624]
	adcs x11, x11, x2
	ldr x2, [x0, #1632]
	adcs x12, x12, x2
	ldr x2, [x0, #1640]
	adcs x13, x13, x2
	ldr x2, [x0, #1648]
	adcs x14, x14, x2
	ldr x2, [x0, #1656]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1728]
	ldr x9, [x0, #1736]
	ldr x10, [x0, #1744]
	ldr x11, [x0, #1752]
	ldr x12, [x0, #1760]
	ldr x13, [x0, #1768]
	ldr x14, [x0, #1776]
	ldr x15, [x0, #1784]
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
	str x8, [x0, #1728]
	str x9, [x0, #1736]
	str x10, [x0, #1744]
	str x11, [x0, #1752]
	str x12, [x0, #1760]
	str x13, [x0, #1768]
	str x14, [x0, #1776]
	str x15, [x0, #1784]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2688]
	ldr x9, [x0, #2696]
	ldr x10, [x0, #2704]
	ldr x11, [x0, #2712]
	ldr x12, [x0, #2720]
	ldr x13, [x0, #2728]
	ldr x14, [x0, #2736]
	ldr x15, [x0, #2744]
	ldr x2, [x0, #2432]
	adds x8, x8, x2
	ldr x2, [x0, #2440]
	adcs x9, x9, x2
	ldr x2, [x0, #2448]
	adcs x10, x10, x2
	ldr x2, [x0, #2456]
	adcs x11, x11, x2
	ldr x2, [x0, #2464]
	adcs x12, x12, x2
	ldr x2, [x0, #2472]
	adcs x13, x13, x2
	ldr x2, [x0, #2480]
	adcs x14, x14, x2
	ldr x2, [x0, #2488]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #1088]
	adds x8, x8, x2
	ldr x2, [x0, #1096]
	adcs x9, x9, x2
	ldr x2, [x0, #1104]
	adcs x10, x10, x2
	ldr x2, [x0, #1112]
	adcs x11, x11, x2
	ldr x2, [x0, #1120]
	adcs x12, x12, x2
	ldr x2, [x0, #1128]
	adcs x13, x13, x2
	ldr x2, [x0, #1136]
	adcs x14, x14, x2
	ldr x2, [x0, #1144]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1856, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x2, [x0, #1856]
	subs x8, x8, x2
	ldr x2, [x0, #1864]
	sbcs x9, x9, x2
	ldr x2, [x0, #1872]
	sbcs x10, x10, x2
	ldr x2, [x0, #1880]
	sbcs x11, x11, x2
	ldr x2, [x0, #1888]
	sbcs x12, x12, x2
	ldr x2, [x0, #1896]
	sbcs x13, x13, x2
	ldr x2, [x0, #1904]
	sbcs x14, x14, x2
	ldr x2, [x0, #1912]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2752]
	ldr x9, [x0, #2760]
	ldr x10, [x0, #2768]
	ldr x11, [x0, #2776]
	ldr x12, [x0, #2784]
	ldr x13, [x0, #2792]
	ldr x14, [x0, #2800]
	ldr x15, [x0, #2808]
	ldr x2, [x0, #2432]
	adds x8, x8, x2
	ldr x2, [x0, #2440]
	adcs x9, x9, x2
	ldr x2, [x0, #2448]
	adcs x10, x10, x2
	ldr x2, [x0, #2456]
	adcs x11, x11, x2
	ldr x2, [x0, #2464]
	adcs x12, x12, x2
	ldr x2, [x0, #2472]
	adcs x13, x13, x2
	ldr x2, [x0, #2480]
	adcs x14, x14, x2
	ldr x2, [x0, #2488]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x14, [x0, #1072]
	ldr x15, [x0, #1080]
	ldr x2, [x0, #1088]
	adds x8, x8, x2
	ldr x2, [x0, #1096]
	adcs x9, x9, x2
	ldr x2, [x0, #1104]
	adcs x10, x10, x2
	ldr x2, [x0, #1112]
	adcs x11, x11, x2
	ldr x2, [x0, #1120]
	adcs x12, x12, x2
	ldr x2, [x0, #1128]
	adcs x13, x13, x2
	ldr x2, [x0, #1136]
	adcs x14, x14, x2
	ldr x2, [x0, #1144]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1856, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1856]
	ldr x9, [x0, #1864]
	ldr x10, [x0, #1872]
	ldr x11, [x0, #1880]
	ldr x12, [x0, #1888]
	ldr x13, [x0, #1896]
	ldr x14, [x0, #1904]
	ldr x15, [x0, #1912]
	ldr x2, [x0, #1152]
	subs x8, x8, x2
	ldr x2, [x0, #1160]
	sbcs x9, x9, x2
	ldr x2, [x0, #1168]
	sbcs x10, x10, x2
	ldr x2, [x0, #1176]
	sbcs x11, x11, x2
	ldr x2, [x0, #1184]
	sbcs x12, x12, x2
	ldr x2, [x0, #1192]
	sbcs x13, x13, x2
	ldr x2, [x0, #1200]
	sbcs x14, x14, x2
	ldr x2, [x0, #1208]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	mov v29.d[0], x30
	movz x1, #1280, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1152, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1152]
	ldr x9, [x0, #1160]
	ldr x10, [x0, #1168]
	ldr x11, [x0, #1176]
	ldr x12, [x0, #1184]
	ldr x13, [x0, #1192]
	ldr x14, [x0, #1200]
	ldr x15, [x0, #1208]
	ldr x2, [x0, #1280]
	adds x8, x8, x2
	ldr x2, [x0, #1288]
	adcs x9, x9, x2
	ldr x2, [x0, #1296]
	adcs x10, x10, x2
	ldr x2, [x0, #1304]
	adcs x11, x11, x2
	ldr x2, [x0, #1312]
	adcs x12, x12, x2
	ldr x2, [x0, #1320]
	adcs x13, x13, x2
	ldr x2, [x0, #1328]
	adcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1280]
	subs x8, x8, x2
	ldr x2, [x0, #1288]
	sbcs x9, x9, x2
	ldr x2, [x0, #1296]
	sbcs x10, x10, x2
	ldr x2, [x0, #1304]
	sbcs x11, x11, x2
	ldr x2, [x0, #1312]
	sbcs x12, x12, x2
	ldr x2, [x0, #1320]
	sbcs x13, x13, x2
	ldr x2, [x0, #1328]
	sbcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1280]
	adds x8, x8, x2
	ldr x2, [x0, #1288]
	adcs x9, x9, x2
	ldr x2, [x0, #1296]
	adcs x10, x10, x2
	ldr x2, [x0, #1304]
	adcs x11, x11, x2
	ldr x2, [x0, #1312]
	adcs x12, x12, x2
	ldr x2, [x0, #1320]
	adcs x13, x13, x2
	ldr x2, [x0, #1328]
	adcs x14, x14, x2
	ldr x2, [x0, #1336]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1152, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1600]
	ldr x9, [x0, #1608]
	ldr x10, [x0, #1616]
	ldr x11, [x0, #1624]
	ldr x12, [x0, #1632]
	ldr x13, [x0, #1640]
	ldr x14, [x0, #1648]
	ldr x15, [x0, #1656]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1600]
	str x9, [x0, #1608]
	str x10, [x0, #1616]
	str x11, [x0, #1624]
	str x12, [x0, #1632]
	str x13, [x0, #1640]
	str x14, [x0, #1648]
	str x15, [x0, #1656]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1536]
	ldr x9, [x0, #1544]
	ldr x10, [x0, #1552]
	ldr x11, [x0, #1560]
	ldr x12, [x0, #1568]
	ldr x13, [x0, #1576]
	ldr x14, [x0, #1584]
	ldr x15, [x0, #1592]
	ldr x2, [x0, #1664]
	subs x8, x8, x2
	ldr x2, [x0, #1672]
	sbcs x9, x9, x2
	ldr x2, [x0, #1680]
	sbcs x10, x10, x2
	ldr x2, [x0, #1688]
	sbcs x11, x11, x2
	ldr x2, [x0, #1696]
	sbcs x12, x12, x2
	ldr x2, [x0, #1704]
	sbcs x13, x13, x2
	ldr x2, [x0, #1712]
	sbcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1664]
	str x9, [x0, #1672]
	str x10, [x0, #1680]
	str x11, [x0, #1688]
	str x12, [x0, #1696]
	str x13, [x0, #1704]
	str x14, [x0, #1712]
	str x15, [x0, #1720]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #448, lsl #0
	movz x3, #1664, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1792]
	ldr x9, [x0, #1800]
	ldr x10, [x0, #1808]
	ldr x11, [x0, #1816]
	ldr x12, [x0, #1824]
	ldr x13, [x0, #1832]
	ldr x14, [x0, #1840]
	ldr x15, [x0, #1848]
	ldr x2, [x0, #1664]
	adds x8, x8, x2
	ldr x2, [x0, #1672]
	adcs x9, x9, x2
	ldr x2, [x0, #1680]
	adcs x10, x10, x2
	ldr x2, [x0, #1688]
	adcs x11, x11, x2
	ldr x2, [x0, #1696]
	adcs x12, x12, x2
	ldr x2, [x0, #1704]
	adcs x13, x13, x2
	ldr x2, [x0, #1712]
	adcs x14, x14, x2
	ldr x2, [x0, #1720]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1600, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x14, [x0, #1264]
	ldr x15, [x0, #1272]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x14, [x0, #1264]
	str x15, [x0, #1272]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1792, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1152, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1152, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1152]
	ldr x9, [x0, #1160]
	ldr x10, [x0, #1168]
	ldr x11, [x0, #1176]
	ldr x12, [x0, #1184]
	ldr x13, [x0, #1192]
	ldr x14, [x0, #1200]
	ldr x15, [x0, #1208]
	ldr x2, [x0, #1536]
	subs x8, x8, x2
	ldr x2, [x0, #1544]
	sbcs x9, x9, x2
	ldr x2, [x0, #1552]
	sbcs x10, x10, x2
	ldr x2, [x0, #1560]
	sbcs x11, x11, x2
	ldr x2, [x0, #1568]
	sbcs x12, x12, x2
	ldr x2, [x0, #1576]
	sbcs x13, x13, x2
	ldr x2, [x0, #1584]
	sbcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x14, [x0, #1200]
	str x15, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #1600, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1280, lsl #0
	movz x2, #1856, lsl #0
	movz x3, #1280, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1280]
	ldr x9, [x0, #1288]
	ldr x10, [x0, #1296]
	ldr x11, [x0, #1304]
	ldr x12, [x0, #1312]
	ldr x13, [x0, #1320]
	ldr x14, [x0, #1328]
	ldr x15, [x0, #1336]
	ldr x2, [x0, #1536]
	adds x8, x8, x2
	ldr x2, [x0, #1544]
	adcs x9, x9, x2
	ldr x2, [x0, #1552]
	adcs x10, x10, x2
	ldr x2, [x0, #1560]
	adcs x11, x11, x2
	ldr x2, [x0, #1568]
	adcs x12, x12, x2
	ldr x2, [x0, #1576]
	adcs x13, x13, x2
	ldr x2, [x0, #1584]
	adcs x14, x14, x2
	ldr x2, [x0, #1592]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x14, [x0, #1328]
	str x15, [x0, #1336]
	ldr x1, [x0, #1152]
	str x1, [x0, #960]
	ldr x1, [x0, #1160]
	str x1, [x0, #968]
	ldr x1, [x0, #1168]
	str x1, [x0, #976]
	ldr x1, [x0, #1176]
	str x1, [x0, #984]
	ldr x1, [x0, #1184]
	str x1, [x0, #992]
	ldr x1, [x0, #1192]
	str x1, [x0, #1000]
	ldr x1, [x0, #1200]
	str x1, [x0, #1008]
	ldr x1, [x0, #1208]
	str x1, [x0, #1016]
	ldr x1, [x0, #1216]
	str x1, [x0, #1024]
	ldr x1, [x0, #1224]
	str x1, [x0, #1032]
	ldr x1, [x0, #1232]
	str x1, [x0, #1040]
	ldr x1, [x0, #1240]
	str x1, [x0, #1048]
	ldr x1, [x0, #1248]
	str x1, [x0, #1056]
	ldr x1, [x0, #1256]
	str x1, [x0, #1064]
	ldr x1, [x0, #1264]
	str x1, [x0, #1072]
	ldr x1, [x0, #1272]
	str x1, [x0, #1080]
	ldr x1, [x0, #1280]
	str x1, [x0, #1088]
	ldr x1, [x0, #1288]
	str x1, [x0, #1096]
	ldr x1, [x0, #1296]
	str x1, [x0, #1104]
	ldr x1, [x0, #1304]
	str x1, [x0, #1112]
	ldr x1, [x0, #1312]
	str x1, [x0, #1120]
	ldr x1, [x0, #1320]
	str x1, [x0, #1128]
	ldr x1, [x0, #1328]
	str x1, [x0, #1136]
	ldr x1, [x0, #1336]
	str x1, [x0, #1144]
	b 212f
211:
212:
	cbnz x19, 210b
	movz x1, #61957, lsl #0
	movk x1, #24920, lsl #16
	movk x1, #5194, lsl #32
	movk x1, #18861, lsl #48
	str x1, [x0, #2240]
	movz x1, #30981, lsl #0
	movk x1, #10005, lsl #16
	movk x1, #45360, lsl #32
	movk x1, #31039, lsl #48
	str x1, [x0, #2248]
	movz x1, #65491, lsl #0
	movk x1, #36954, lsl #16
	movk x1, #63932, lsl #32
	movk x1, #21431, lsl #48
	str x1, [x0, #2256]
	movz x1, #18981, lsl #0
	movk x1, #33617, lsl #16
	movk x1, #39543, lsl #32
	movk x1, #57537, lsl #48
	str x1, [x0, #2264]
	movz x1, #32855, lsl #0
	movk x1, #54665, lsl #16
	movk x1, #28632, lsl #32
	movk x1, #6472, lsl #48
	str x1, [x0, #2272]
	movz x1, #65411, lsl #0
	movk x1, #54315, lsl #16
	movk x1, #43615, lsl #32
	movk x1, #41325, lsl #48
	str x1, [x0, #2280]
	movz x1, #61132, lsl #0
	movk x1, #8278, lsl #16
	movk x1, #6464, lsl #32
	movk x1, #8238, lsl #48
	str x1, [x0, #2288]
	movz x1, #25680, lsl #0
	movk x1, #43519, lsl #16
	movk x1, #40197, lsl #32
	movk x1, #15436, lsl #48
	str x1, [x0, #2296]
	movz x1, #62639, lsl #0
	movk x1, #64950, lsl #16
	movk x1, #62038, lsl #32
	movk x1, #4217, lsl #48
	str x1, [x0, #1920]
	movz x1, #10078, lsl #0
	movk x1, #309, lsl #16
	movk x1, #5639, lsl #32
	movk x1, #14762, lsl #48
	str x1, [x0, #1928]
	movz x1, #13975, lsl #0
	movk x1, #18464, lsl #16
	movk x1, #29953, lsl #32
	movk x1, #25132, lsl #48
	str x1, [x0, #1936]
	movz x1, #51679, lsl #0
	movk x1, #2763, lsl #16
	movk x1, #3521, lsl #32
	movk x1, #1339, lsl #48
	str x1, [x0, #1944]
	movz x1, #149, lsl #0
	movk x1, #40686, lsl #16
	movk x1, #56209, lsl #32
	movk x1, #4137, lsl #48
	str x1, [x0, #1952]
	movz x1, #37823, lsl #0
	movk x1, #45330, lsl #16
	movk x1, #8272, lsl #32
	movk x1, #34508, lsl #48
	str x1, [x0, #1960]
	movz x1, #61418, lsl #0
	movk x1, #39041, lsl #16
	movk x1, #56717, lsl #32
	movk x1, #57305, lsl #48
	str x1, [x0, #1968]
	movz x1, #37959, lsl #0
	movk x1, #16179, lsl #16
	movk x1, #62573, lsl #32
	movk x1, #38422, lsl #48
	str x1, [x0, #1976]
	movz x1, #18570, lsl #0
	movk x1, #48017, lsl #16
	movk x1, #51667, lsl #32
	movk x1, #29474, lsl #48
	str x1, [x0, #128]
	movz x1, #60327, lsl #0
	movk x1, #9508, lsl #16
	movk x1, #11182, lsl #32
	movk x1, #2768, lsl #48
	str x1, [x0, #136]
	movz x1, #28831, lsl #0
	movk x1, #26359, lsl #16
	movk x1, #16401, lsl #32
	movk x1, #27975, lsl #48
	str x1, [x0, #144]
	movz x1, #16937, lsl #0
	movk x1, #20253, lsl #16
	movk x1, #16063, lsl #32
	movk x1, #10255, lsl #48
	str x1, [x0, #152]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #160]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #168]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #176]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #184]
	mov v29.d[0], x30
	movz x1, #2240, lsl #0
	movz x2, #2048, lsl #0
	movz x3, #2240, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2304, lsl #0
	movz x2, #2240, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #2304]
	subs x8, x8, x2
	ldr x2, [x0, #2312]
	sbcs x9, x9, x2
	ldr x2, [x0, #2320]
	sbcs x10, x10, x2
	ldr x2, [x0, #2328]
	sbcs x11, x11, x2
	ldr x2, [x0, #2336]
	sbcs x12, x12, x2
	ldr x2, [x0, #2344]
	sbcs x13, x13, x2
	ldr x2, [x0, #2352]
	sbcs x14, x14, x2
	ldr x2, [x0, #2360]
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
	str x8, [x0, #2624]
	str x9, [x0, #2632]
	str x10, [x0, #2640]
	str x11, [x0, #2648]
	str x12, [x0, #2656]
	str x13, [x0, #2664]
	str x14, [x0, #2672]
	str x15, [x0, #2680]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2240]
	ldr x9, [x0, #2248]
	ldr x10, [x0, #2256]
	ldr x11, [x0, #2264]
	ldr x12, [x0, #2272]
	ldr x13, [x0, #2280]
	ldr x14, [x0, #2288]
	ldr x15, [x0, #2296]
	ldr x2, [x0, #1920]
	adds x8, x8, x2
	ldr x2, [x0, #1928]
	adcs x9, x9, x2
	ldr x2, [x0, #1936]
	adcs x10, x10, x2
	ldr x2, [x0, #1944]
	adcs x11, x11, x2
	ldr x2, [x0, #1952]
	adcs x12, x12, x2
	ldr x2, [x0, #1960]
	adcs x13, x13, x2
	ldr x2, [x0, #1968]
	adcs x14, x14, x2
	ldr x2, [x0, #1976]
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
	str x8, [x0, #2240]
	str x9, [x0, #2248]
	str x10, [x0, #2256]
	str x11, [x0, #2264]
	str x12, [x0, #2272]
	str x13, [x0, #2280]
	str x14, [x0, #2288]
	str x15, [x0, #2296]
	mov v29.d[0], x30
	movz x1, #2304, lsl #0
	movz x2, #2240, lsl #0
	movz x3, #1088, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #960]
	ldr x9, [x0, #968]
	ldr x10, [x0, #976]
	ldr x11, [x0, #984]
	ldr x12, [x0, #992]
	ldr x13, [x0, #1000]
	ldr x14, [x0, #1008]
	ldr x15, [x0, #1016]
	ldr x2, [x0, #2304]
	subs x8, x8, x2
	ldr x2, [x0, #2312]
	sbcs x9, x9, x2
	ldr x2, [x0, #2320]
	sbcs x10, x10, x2
	ldr x2, [x0, #2328]
	sbcs x11, x11, x2
	ldr x2, [x0, #2336]
	sbcs x12, x12, x2
	ldr x2, [x0, #2344]
	sbcs x13, x13, x2
	ldr x2, [x0, #2352]
	sbcs x14, x14, x2
	ldr x2, [x0, #2360]
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
	ldr x1, [x0, #2624]
	ldr x2, [x0, #2632]
	orr x1, x1, x2
	ldr x2, [x0, #2640]
	orr x1, x1, x2
	ldr x2, [x0, #2648]
	orr x1, x1, x2
	ldr x2, [x0, #2656]
	orr x1, x1, x2
	ldr x2, [x0, #2664]
	orr x1, x1, x2
	ldr x2, [x0, #2672]
	orr x1, x1, x2
	ldr x2, [x0, #2680]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #2048]
	ldr x2, [x0, #128]
	subs x16, x1, x2
	ldr x1, [x0, #2056]
	ldr x2, [x0, #136]
	sbcs x16, x1, x2
	ldr x1, [x0, #2064]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #2072]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	ldr x1, [x0, #2080]
	ldr x2, [x0, #160]
	sbcs x16, x1, x2
	ldr x1, [x0, #2088]
	ldr x2, [x0, #168]
	sbcs x16, x1, x2
	ldr x1, [x0, #2096]
	ldr x2, [x0, #176]
	sbcs x16, x1, x2
	ldr x1, [x0, #2104]
	ldr x2, [x0, #184]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x6, x2, #0
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
	and x2, x2, x6
	orr x2, x2, x4
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
