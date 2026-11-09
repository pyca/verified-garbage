// The functions of `src/internal/vg_ecdsa_brainpoolp512r1_sign_k.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_sign_k:
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
	movz x1, #24749, lsl #0
	movk x1, #723, lsl #16
	movk x1, #26908, lsl #32
	movk x1, #10122, lsl #48
	str x1, [x0, #960]
	movz x1, #47708, lsl #0
	movk x1, #45466, lsl #16
	movk x1, #63333, lsl #32
	movk x1, #63573, lsl #48
	str x1, [x0, #968]
	movz x1, #32431, lsl #0
	movk x1, #48622, lsl #16
	movk x1, #22524, lsl #32
	movk x1, #9804, lsl #48
	str x1, [x0, #976]
	movz x1, #20273, lsl #0
	movk x1, #25470, lsl #16
	movk x1, #4032, lsl #32
	movk x1, #61332, lsl #48
	str x1, [x0, #984]
	movz x1, #60103, lsl #0
	movk x1, #63233, lsl #16
	movk x1, #61066, lsl #32
	movk x1, #21414, lsl #48
	str x1, [x0, #992]
	movz x1, #51386, lsl #0
	movk x1, #23664, lsl #16
	movk x1, #27876, lsl #32
	movk x1, #57284, lsl #48
	str x1, [x0, #1000]
	movz x1, #33648, lsl #0
	movk x1, #2097, lsl #16
	movk x1, #9370, lsl #32
	movk x1, #31331, lsl #48
	str x1, [x0, #1008]
	movz x1, #24707, lsl #0
	movk x1, #65179, lsl #16
	movk x1, #14231, lsl #32
	movk x1, #23585, lsl #48
	str x1, [x0, #1016]
	movz x1, #31196, lsl #0
	movk x1, #7036, lsl #16
	movk x1, #10383, lsl #32
	movk x1, #7774, lsl #48
	str x1, [x0, #1024]
	movz x1, #55885, lsl #0
	movk x1, #63897, lsl #16
	movk x1, #40253, lsl #32
	movk x1, #22852, lsl #48
	str x1, [x0, #1032]
	movz x1, #588, lsl #0
	movk x1, #34562, lsl #16
	movk x1, #54870, lsl #32
	movk x1, #9380, lsl #48
	str x1, [x0, #1040]
	movz x1, #51918, lsl #0
	movk x1, #52001, lsl #16
	movk x1, #485, lsl #32
	movk x1, #36590, lsl #48
	str x1, [x0, #1048]
	movz x1, #53737, lsl #0
	movk x1, #11387, lsl #16
	movk x1, #7322, lsl #32
	movk x1, #58850, lsl #48
	str x1, [x0, #1056]
	movz x1, #35845, lsl #0
	movk x1, #45032, lsl #16
	movk x1, #61749, lsl #32
	movk x1, #26060, lsl #48
	str x1, [x0, #1064]
	movz x1, #39269, lsl #0
	movk x1, #44846, lsl #16
	movk x1, #49447, lsl #32
	movk x1, #30292, lsl #48
	str x1, [x0, #1072]
	movz x1, #10673, lsl #0
	movk x1, #24172, lsl #16
	movk x1, #40998, lsl #32
	movk x1, #21547, lsl #48
	str x1, [x0, #1080]
	movz x1, #46861, lsl #0
	movk x1, #42949, lsl #16
	movk x1, #40873, lsl #32
	movk x1, #55125, lsl #48
	str x1, [x0, #1088]
	movz x1, #14714, lsl #0
	movk x1, #53885, lsl #16
	movk x1, #208, lsl #32
	movk x1, #55166, lsl #48
	str x1, [x0, #1096]
	movz x1, #32537, lsl #0
	movk x1, #6492, lsl #16
	movk x1, #24277, lsl #32
	movk x1, #20786, lsl #48
	str x1, [x0, #1104]
	movz x1, #38845, lsl #0
	movk x1, #25657, lsl #16
	movk x1, #25855, lsl #32
	movk x1, #33458, lsl #48
	str x1, [x0, #1112]
	movz x1, #63374, lsl #0
	movk x1, #36812, lsl #16
	movk x1, #25397, lsl #32
	movk x1, #10652, lsl #48
	str x1, [x0, #1120]
	movz x1, #11761, lsl #0
	movk x1, #19510, lsl #16
	movk x1, #29260, lsl #32
	movk x1, #13519, lsl #48
	str x1, [x0, #1128]
	movz x1, #1016, lsl #0
	movk x1, #52278, lsl #16
	movk x1, #6481, lsl #32
	movk x1, #49195, lsl #48
	str x1, [x0, #1136]
	movz x1, #15220, lsl #0
	movk x1, #9238, lsl #16
	movk x1, #25159, lsl #32
	movk x1, #21794, lsl #48
	str x1, [x0, #1144]
	movz x7, #0, lsl #0
	str x7, [x0, #3456]
	movz x19, #74, lsl #0
21:
	sub x19, x19, #1
	movz x16, #7, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	movz x2, #0, lsl #0
	add x2, x2, x2
	ldrb w4, [x16, #2950]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2949]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2948]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2947]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2946]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2945]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2944]
	add x2, x2, x4
	sub x3, x2, #64
	lsr x4, x3, #63
	movz x9, #0, lsl #0
	sub x4, x9, x4
	eor x2, x3, x4
	sub x2, x2, x4
	movz x7, #0, lsl #0
	adrp x16, {VG_BRAINPOOLP512R1_COMB7}
	add x16, x16, {VG_BRAINPOOLP512R1_COMB7}
	movz x17, #8192, lsl #0
	mul x17, x19, x17
	add x16, x16, x17
	movz x5, #1, lsl #0
	movz x1, #0, lsl #0
	dup v19.2d, x2
	dup v28.2d, x5
	add v18.2d, v28.2d, v28.2d
	movi v17.2d, #0
	sub v17.2d, v17.2d, v28.2d
	movi v30.2d, #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #0]
	ldr q21, [x16, #16]
	ldr q22, [x16, #32]
	ldr q23, [x16, #48]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #128]
	ldr q25, [x16, #144]
	ldr q26, [x16, #160]
	ldr q27, [x16, #176]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #256]
	ldr q21, [x16, #272]
	ldr q22, [x16, #288]
	ldr q23, [x16, #304]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #384]
	ldr q25, [x16, #400]
	ldr q26, [x16, #416]
	ldr q27, [x16, #432]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #512]
	ldr q21, [x16, #528]
	ldr q22, [x16, #544]
	ldr q23, [x16, #560]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #640]
	ldr q25, [x16, #656]
	ldr q26, [x16, #672]
	ldr q27, [x16, #688]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #768]
	ldr q21, [x16, #784]
	ldr q22, [x16, #800]
	ldr q23, [x16, #816]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #896]
	ldr q25, [x16, #912]
	ldr q26, [x16, #928]
	ldr q27, [x16, #944]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1024]
	ldr q21, [x16, #1040]
	ldr q22, [x16, #1056]
	ldr q23, [x16, #1072]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1152]
	ldr q25, [x16, #1168]
	ldr q26, [x16, #1184]
	ldr q27, [x16, #1200]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1280]
	ldr q21, [x16, #1296]
	ldr q22, [x16, #1312]
	ldr q23, [x16, #1328]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1408]
	ldr q25, [x16, #1424]
	ldr q26, [x16, #1440]
	ldr q27, [x16, #1456]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1536]
	ldr q21, [x16, #1552]
	ldr q22, [x16, #1568]
	ldr q23, [x16, #1584]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1664]
	ldr q25, [x16, #1680]
	ldr q26, [x16, #1696]
	ldr q27, [x16, #1712]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1792]
	ldr q21, [x16, #1808]
	ldr q22, [x16, #1824]
	ldr q23, [x16, #1840]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1920]
	ldr q25, [x16, #1936]
	ldr q26, [x16, #1952]
	ldr q27, [x16, #1968]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2048]
	ldr q21, [x16, #2064]
	ldr q22, [x16, #2080]
	ldr q23, [x16, #2096]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2176]
	ldr q25, [x16, #2192]
	ldr q26, [x16, #2208]
	ldr q27, [x16, #2224]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2304]
	ldr q21, [x16, #2320]
	ldr q22, [x16, #2336]
	ldr q23, [x16, #2352]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2432]
	ldr q25, [x16, #2448]
	ldr q26, [x16, #2464]
	ldr q27, [x16, #2480]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2560]
	ldr q21, [x16, #2576]
	ldr q22, [x16, #2592]
	ldr q23, [x16, #2608]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2688]
	ldr q25, [x16, #2704]
	ldr q26, [x16, #2720]
	ldr q27, [x16, #2736]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2816]
	ldr q21, [x16, #2832]
	ldr q22, [x16, #2848]
	ldr q23, [x16, #2864]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2944]
	ldr q25, [x16, #2960]
	ldr q26, [x16, #2976]
	ldr q27, [x16, #2992]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3072]
	ldr q21, [x16, #3088]
	ldr q22, [x16, #3104]
	ldr q23, [x16, #3120]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3200]
	ldr q25, [x16, #3216]
	ldr q26, [x16, #3232]
	ldr q27, [x16, #3248]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3328]
	ldr q21, [x16, #3344]
	ldr q22, [x16, #3360]
	ldr q23, [x16, #3376]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3456]
	ldr q25, [x16, #3472]
	ldr q26, [x16, #3488]
	ldr q27, [x16, #3504]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3584]
	ldr q21, [x16, #3600]
	ldr q22, [x16, #3616]
	ldr q23, [x16, #3632]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3712]
	ldr q25, [x16, #3728]
	ldr q26, [x16, #3744]
	ldr q27, [x16, #3760]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3840]
	ldr q21, [x16, #3856]
	ldr q22, [x16, #3872]
	ldr q23, [x16, #3888]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3968]
	ldr q25, [x16, #3984]
	ldr q26, [x16, #4000]
	ldr q27, [x16, #4016]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4096]
	ldr q21, [x16, #4112]
	ldr q22, [x16, #4128]
	ldr q23, [x16, #4144]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4224]
	ldr q25, [x16, #4240]
	ldr q26, [x16, #4256]
	ldr q27, [x16, #4272]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4352]
	ldr q21, [x16, #4368]
	ldr q22, [x16, #4384]
	ldr q23, [x16, #4400]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4480]
	ldr q25, [x16, #4496]
	ldr q26, [x16, #4512]
	ldr q27, [x16, #4528]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4608]
	ldr q21, [x16, #4624]
	ldr q22, [x16, #4640]
	ldr q23, [x16, #4656]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4736]
	ldr q25, [x16, #4752]
	ldr q26, [x16, #4768]
	ldr q27, [x16, #4784]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4864]
	ldr q21, [x16, #4880]
	ldr q22, [x16, #4896]
	ldr q23, [x16, #4912]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4992]
	ldr q25, [x16, #5008]
	ldr q26, [x16, #5024]
	ldr q27, [x16, #5040]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5120]
	ldr q21, [x16, #5136]
	ldr q22, [x16, #5152]
	ldr q23, [x16, #5168]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5248]
	ldr q25, [x16, #5264]
	ldr q26, [x16, #5280]
	ldr q27, [x16, #5296]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5376]
	ldr q21, [x16, #5392]
	ldr q22, [x16, #5408]
	ldr q23, [x16, #5424]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5504]
	ldr q25, [x16, #5520]
	ldr q26, [x16, #5536]
	ldr q27, [x16, #5552]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5632]
	ldr q21, [x16, #5648]
	ldr q22, [x16, #5664]
	ldr q23, [x16, #5680]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5760]
	ldr q25, [x16, #5776]
	ldr q26, [x16, #5792]
	ldr q27, [x16, #5808]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5888]
	ldr q21, [x16, #5904]
	ldr q22, [x16, #5920]
	ldr q23, [x16, #5936]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6016]
	ldr q25, [x16, #6032]
	ldr q26, [x16, #6048]
	ldr q27, [x16, #6064]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #6144]
	ldr q21, [x16, #6160]
	ldr q22, [x16, #6176]
	ldr q23, [x16, #6192]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6272]
	ldr q25, [x16, #6288]
	ldr q26, [x16, #6304]
	ldr q27, [x16, #6320]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #6400]
	ldr q21, [x16, #6416]
	ldr q22, [x16, #6432]
	ldr q23, [x16, #6448]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6528]
	ldr q25, [x16, #6544]
	ldr q26, [x16, #6560]
	ldr q27, [x16, #6576]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #6656]
	ldr q21, [x16, #6672]
	ldr q22, [x16, #6688]
	ldr q23, [x16, #6704]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6784]
	ldr q25, [x16, #6800]
	ldr q26, [x16, #6816]
	ldr q27, [x16, #6832]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #6912]
	ldr q21, [x16, #6928]
	ldr q22, [x16, #6944]
	ldr q23, [x16, #6960]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #7040]
	ldr q25, [x16, #7056]
	ldr q26, [x16, #7072]
	ldr q27, [x16, #7088]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #7168]
	ldr q21, [x16, #7184]
	ldr q22, [x16, #7200]
	ldr q23, [x16, #7216]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #7296]
	ldr q25, [x16, #7312]
	ldr q26, [x16, #7328]
	ldr q27, [x16, #7344]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #7424]
	ldr q21, [x16, #7440]
	ldr q22, [x16, #7456]
	ldr q23, [x16, #7472]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #7552]
	ldr q25, [x16, #7568]
	ldr q26, [x16, #7584]
	ldr q27, [x16, #7600]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #7680]
	ldr q21, [x16, #7696]
	ldr q22, [x16, #7712]
	ldr q23, [x16, #7728]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #7808]
	ldr q25, [x16, #7824]
	ldr q26, [x16, #7840]
	ldr q27, [x16, #7856]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #7936]
	ldr q21, [x16, #7952]
	ldr q22, [x16, #7968]
	ldr q23, [x16, #7984]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #8064]
	ldr q25, [x16, #8080]
	ldr q26, [x16, #8096]
	ldr q27, [x16, #8112]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	orr v0.16b, v0.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	orr v2.16b, v2.16b, v6.16b
	orr v3.16b, v3.16b, v7.16b
	str q0, [x0, #1344]
	str q1, [x0, #1360]
	str q2, [x0, #1376]
	str q3, [x0, #1392]
	movi v17.2d, #0
	sub v17.2d, v17.2d, v28.2d
	movi v30.2d, #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #64]
	ldr q21, [x16, #80]
	ldr q22, [x16, #96]
	ldr q23, [x16, #112]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #192]
	ldr q25, [x16, #208]
	ldr q26, [x16, #224]
	ldr q27, [x16, #240]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #320]
	ldr q21, [x16, #336]
	ldr q22, [x16, #352]
	ldr q23, [x16, #368]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #448]
	ldr q25, [x16, #464]
	ldr q26, [x16, #480]
	ldr q27, [x16, #496]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #576]
	ldr q21, [x16, #592]
	ldr q22, [x16, #608]
	ldr q23, [x16, #624]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #704]
	ldr q25, [x16, #720]
	ldr q26, [x16, #736]
	ldr q27, [x16, #752]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #832]
	ldr q21, [x16, #848]
	ldr q22, [x16, #864]
	ldr q23, [x16, #880]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #960]
	ldr q25, [x16, #976]
	ldr q26, [x16, #992]
	ldr q27, [x16, #1008]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1088]
	ldr q21, [x16, #1104]
	ldr q22, [x16, #1120]
	ldr q23, [x16, #1136]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1216]
	ldr q25, [x16, #1232]
	ldr q26, [x16, #1248]
	ldr q27, [x16, #1264]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1344]
	ldr q21, [x16, #1360]
	ldr q22, [x16, #1376]
	ldr q23, [x16, #1392]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1472]
	ldr q25, [x16, #1488]
	ldr q26, [x16, #1504]
	ldr q27, [x16, #1520]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1600]
	ldr q21, [x16, #1616]
	ldr q22, [x16, #1632]
	ldr q23, [x16, #1648]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1728]
	ldr q25, [x16, #1744]
	ldr q26, [x16, #1760]
	ldr q27, [x16, #1776]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1856]
	ldr q21, [x16, #1872]
	ldr q22, [x16, #1888]
	ldr q23, [x16, #1904]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1984]
	ldr q25, [x16, #2000]
	ldr q26, [x16, #2016]
	ldr q27, [x16, #2032]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2112]
	ldr q21, [x16, #2128]
	ldr q22, [x16, #2144]
	ldr q23, [x16, #2160]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2240]
	ldr q25, [x16, #2256]
	ldr q26, [x16, #2272]
	ldr q27, [x16, #2288]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2368]
	ldr q21, [x16, #2384]
	ldr q22, [x16, #2400]
	ldr q23, [x16, #2416]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2496]
	ldr q25, [x16, #2512]
	ldr q26, [x16, #2528]
	ldr q27, [x16, #2544]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2624]
	ldr q21, [x16, #2640]
	ldr q22, [x16, #2656]
	ldr q23, [x16, #2672]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2752]
	ldr q25, [x16, #2768]
	ldr q26, [x16, #2784]
	ldr q27, [x16, #2800]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2880]
	ldr q21, [x16, #2896]
	ldr q22, [x16, #2912]
	ldr q23, [x16, #2928]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3008]
	ldr q25, [x16, #3024]
	ldr q26, [x16, #3040]
	ldr q27, [x16, #3056]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3136]
	ldr q21, [x16, #3152]
	ldr q22, [x16, #3168]
	ldr q23, [x16, #3184]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3264]
	ldr q25, [x16, #3280]
	ldr q26, [x16, #3296]
	ldr q27, [x16, #3312]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3392]
	ldr q21, [x16, #3408]
	ldr q22, [x16, #3424]
	ldr q23, [x16, #3440]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3520]
	ldr q25, [x16, #3536]
	ldr q26, [x16, #3552]
	ldr q27, [x16, #3568]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3648]
	ldr q21, [x16, #3664]
	ldr q22, [x16, #3680]
	ldr q23, [x16, #3696]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3776]
	ldr q25, [x16, #3792]
	ldr q26, [x16, #3808]
	ldr q27, [x16, #3824]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3904]
	ldr q21, [x16, #3920]
	ldr q22, [x16, #3936]
	ldr q23, [x16, #3952]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4032]
	ldr q25, [x16, #4048]
	ldr q26, [x16, #4064]
	ldr q27, [x16, #4080]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4160]
	ldr q21, [x16, #4176]
	ldr q22, [x16, #4192]
	ldr q23, [x16, #4208]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4288]
	ldr q25, [x16, #4304]
	ldr q26, [x16, #4320]
	ldr q27, [x16, #4336]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4416]
	ldr q21, [x16, #4432]
	ldr q22, [x16, #4448]
	ldr q23, [x16, #4464]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4544]
	ldr q25, [x16, #4560]
	ldr q26, [x16, #4576]
	ldr q27, [x16, #4592]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4672]
	ldr q21, [x16, #4688]
	ldr q22, [x16, #4704]
	ldr q23, [x16, #4720]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4800]
	ldr q25, [x16, #4816]
	ldr q26, [x16, #4832]
	ldr q27, [x16, #4848]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4928]
	ldr q21, [x16, #4944]
	ldr q22, [x16, #4960]
	ldr q23, [x16, #4976]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5056]
	ldr q25, [x16, #5072]
	ldr q26, [x16, #5088]
	ldr q27, [x16, #5104]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5184]
	ldr q21, [x16, #5200]
	ldr q22, [x16, #5216]
	ldr q23, [x16, #5232]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5312]
	ldr q25, [x16, #5328]
	ldr q26, [x16, #5344]
	ldr q27, [x16, #5360]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5440]
	ldr q21, [x16, #5456]
	ldr q22, [x16, #5472]
	ldr q23, [x16, #5488]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5568]
	ldr q25, [x16, #5584]
	ldr q26, [x16, #5600]
	ldr q27, [x16, #5616]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5696]
	ldr q21, [x16, #5712]
	ldr q22, [x16, #5728]
	ldr q23, [x16, #5744]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5824]
	ldr q25, [x16, #5840]
	ldr q26, [x16, #5856]
	ldr q27, [x16, #5872]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5952]
	ldr q21, [x16, #5968]
	ldr q22, [x16, #5984]
	ldr q23, [x16, #6000]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6080]
	ldr q25, [x16, #6096]
	ldr q26, [x16, #6112]
	ldr q27, [x16, #6128]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #6208]
	ldr q21, [x16, #6224]
	ldr q22, [x16, #6240]
	ldr q23, [x16, #6256]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6336]
	ldr q25, [x16, #6352]
	ldr q26, [x16, #6368]
	ldr q27, [x16, #6384]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #6464]
	ldr q21, [x16, #6480]
	ldr q22, [x16, #6496]
	ldr q23, [x16, #6512]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6592]
	ldr q25, [x16, #6608]
	ldr q26, [x16, #6624]
	ldr q27, [x16, #6640]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #6720]
	ldr q21, [x16, #6736]
	ldr q22, [x16, #6752]
	ldr q23, [x16, #6768]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6848]
	ldr q25, [x16, #6864]
	ldr q26, [x16, #6880]
	ldr q27, [x16, #6896]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #6976]
	ldr q21, [x16, #6992]
	ldr q22, [x16, #7008]
	ldr q23, [x16, #7024]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #7104]
	ldr q25, [x16, #7120]
	ldr q26, [x16, #7136]
	ldr q27, [x16, #7152]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #7232]
	ldr q21, [x16, #7248]
	ldr q22, [x16, #7264]
	ldr q23, [x16, #7280]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #7360]
	ldr q25, [x16, #7376]
	ldr q26, [x16, #7392]
	ldr q27, [x16, #7408]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #7488]
	ldr q21, [x16, #7504]
	ldr q22, [x16, #7520]
	ldr q23, [x16, #7536]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #7616]
	ldr q25, [x16, #7632]
	ldr q26, [x16, #7648]
	ldr q27, [x16, #7664]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #7744]
	ldr q21, [x16, #7760]
	ldr q22, [x16, #7776]
	ldr q23, [x16, #7792]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #7872]
	ldr q25, [x16, #7888]
	ldr q26, [x16, #7904]
	ldr q27, [x16, #7920]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #8000]
	ldr q21, [x16, #8016]
	ldr q22, [x16, #8032]
	ldr q23, [x16, #8048]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #8128]
	ldr q25, [x16, #8144]
	ldr q26, [x16, #8160]
	ldr q27, [x16, #8176]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	orr v0.16b, v0.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	orr v2.16b, v2.16b, v6.16b
	orr v3.16b, v3.16b, v7.16b
	movi v16.2d, #0
	cmeq v16.2d, v16.2d, v19.2d
	movz x6, #46861, lsl #0
	movk x6, #42949, lsl #16
	movk x6, #40873, lsl #32
	movk x6, #55125, lsl #48
	mov v20.d[0], x6
	movz x6, #14714, lsl #0
	movk x6, #53885, lsl #16
	movk x6, #208, lsl #32
	movk x6, #55166, lsl #48
	mov v20.d[1], x6
	bit v0.16b, v20.16b, v16.16b
	movz x6, #32537, lsl #0
	movk x6, #6492, lsl #16
	movk x6, #24277, lsl #32
	movk x6, #20786, lsl #48
	mov v20.d[0], x6
	movz x6, #38845, lsl #0
	movk x6, #25657, lsl #16
	movk x6, #25855, lsl #32
	movk x6, #33458, lsl #48
	mov v20.d[1], x6
	bit v1.16b, v20.16b, v16.16b
	movz x6, #63374, lsl #0
	movk x6, #36812, lsl #16
	movk x6, #25397, lsl #32
	movk x6, #10652, lsl #48
	mov v20.d[0], x6
	movz x6, #11761, lsl #0
	movk x6, #19510, lsl #16
	movk x6, #29260, lsl #32
	movk x6, #13519, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	movz x6, #1016, lsl #0
	movk x6, #52278, lsl #16
	movk x6, #6481, lsl #32
	movk x6, #49195, lsl #48
	mov v20.d[0], x6
	movz x6, #15220, lsl #0
	movk x6, #9238, lsl #16
	movk x6, #25159, lsl #32
	movk x6, #21794, lsl #48
	mov v20.d[1], x6
	bit v3.16b, v20.16b, v16.16b
	str q0, [x0, #1408]
	str q1, [x0, #1424]
	str q2, [x0, #1440]
	str q3, [x0, #1456]
	subs x4, x2, x5
	movz x6, #46861, lsl #0
	movk x6, #42949, lsl #16
	movk x6, #40873, lsl #32
	movk x6, #55125, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1472]
	movz x6, #14714, lsl #0
	movk x6, #53885, lsl #16
	movk x6, #208, lsl #32
	movk x6, #55166, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1480]
	movz x6, #32537, lsl #0
	movk x6, #6492, lsl #16
	movk x6, #24277, lsl #32
	movk x6, #20786, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1488]
	movz x6, #38845, lsl #0
	movk x6, #25657, lsl #16
	movk x6, #25855, lsl #32
	movk x6, #33458, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1496]
	movz x6, #63374, lsl #0
	movk x6, #36812, lsl #16
	movk x6, #25397, lsl #32
	movk x6, #10652, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1504]
	movz x6, #11761, lsl #0
	movk x6, #19510, lsl #16
	movk x6, #29260, lsl #32
	movk x6, #13519, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1512]
	movz x6, #1016, lsl #0
	movk x6, #52278, lsl #16
	movk x6, #6481, lsl #32
	movk x6, #49195, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1520]
	movz x6, #15220, lsl #0
	movk x6, #9238, lsl #16
	movk x6, #25159, lsl #32
	movk x6, #21794, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1528]
	movz x7, #0, lsl #0
	ldr x8, [x0, #256]
	ldr x9, [x0, #264]
	ldr x10, [x0, #272]
	ldr x11, [x0, #280]
	ldr x12, [x0, #288]
	ldr x13, [x0, #296]
	ldr x14, [x0, #304]
	ldr x15, [x0, #312]
	ldr x2, [x0, #1408]
	subs x8, x8, x2
	ldr x2, [x0, #1416]
	sbcs x9, x9, x2
	ldr x2, [x0, #1424]
	sbcs x10, x10, x2
	ldr x2, [x0, #1432]
	sbcs x11, x11, x2
	ldr x2, [x0, #1440]
	sbcs x12, x12, x2
	ldr x2, [x0, #1448]
	sbcs x13, x13, x2
	ldr x2, [x0, #1456]
	sbcs x14, x14, x2
	ldr x2, [x0, #1464]
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
	str x8, [x0, #1984]
	str x9, [x0, #1992]
	str x10, [x0, #2000]
	str x11, [x0, #2008]
	str x12, [x0, #2016]
	str x13, [x0, #2024]
	str x14, [x0, #2032]
	str x15, [x0, #2040]
	movz x16, #7, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	ldrb w3, [x16, #2950]
	sub x3, x3, #1
	ldr x1, [x0, #1408]
	ldr x2, [x0, #1984]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1408]
	ldr x1, [x0, #1416]
	ldr x2, [x0, #1992]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1416]
	ldr x1, [x0, #1424]
	ldr x2, [x0, #2000]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1424]
	ldr x1, [x0, #1432]
	ldr x2, [x0, #2008]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1432]
	ldr x1, [x0, #1440]
	ldr x2, [x0, #2016]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1440]
	ldr x1, [x0, #1448]
	ldr x2, [x0, #2024]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1448]
	ldr x1, [x0, #1456]
	ldr x2, [x0, #2032]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1456]
	ldr x1, [x0, #1464]
	ldr x2, [x0, #2040]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1464]
	movz x1, #13737, lsl #0
	movk x1, #2689, lsl #16
	movk x1, #10860, lsl #32
	movk x1, #51409, lsl #48
	str x1, [x0, #1984]
	movz x1, #18455, lsl #0
	movk x1, #33576, lsl #16
	movk x1, #11304, lsl #32
	movk x1, #55632, lsl #48
	str x1, [x0, #1992]
	movz x1, #60695, lsl #0
	movk x1, #41457, lsl #16
	movk x1, #19415, lsl #32
	movk x1, #62837, lsl #48
	str x1, [x0, #2000]
	movz x1, #53701, lsl #0
	movk x1, #11680, lsl #16
	movk x1, #63417, lsl #32
	movk x1, #55404, lsl #48
	str x1, [x0, #2008]
	movz x1, #25641, lsl #0
	movk x1, #35379, lsl #16
	movk x1, #34913, lsl #32
	movk x1, #61756, lsl #48
	str x1, [x0, #2016]
	movz x1, #46665, lsl #0
	movk x1, #37757, lsl #16
	movk x1, #31057, lsl #32
	movk x1, #39006, lsl #48
	str x1, [x0, #2024]
	movz x1, #992, lsl #0
	movk x1, #61271, lsl #16
	movk x1, #20800, lsl #32
	movk x1, #60564, lsl #48
	str x1, [x0, #2032]
	movz x1, #59242, lsl #0
	movk x1, #63857, lsl #16
	movk x1, #25955, lsl #32
	movk x1, #37890, lsl #48
	str x1, [x0, #2040]
	mov v29.d[0], x30
	movz x1, #1536, lsl #0
	movz x2, #960, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1600, lsl #0
	movz x2, #1024, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp512r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1664, lsl #0
	movz x2, #1088, lsl #0
	movz x3, #1472, lsl #0
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
	str x8, [x0, #1728]
	str x9, [x0, #1736]
	str x10, [x0, #1744]
	str x11, [x0, #1752]
	str x12, [x0, #1760]
	str x13, [x0, #1768]
	str x14, [x0, #1776]
	str x15, [x0, #1784]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1344]
	ldr x9, [x0, #1352]
	ldr x10, [x0, #1360]
	ldr x11, [x0, #1368]
	ldr x12, [x0, #1376]
	ldr x13, [x0, #1384]
	ldr x14, [x0, #1392]
	ldr x15, [x0, #1400]
	ldr x2, [x0, #1408]
	adds x8, x8, x2
	ldr x2, [x0, #1416]
	adcs x9, x9, x2
	ldr x2, [x0, #1424]
	adcs x10, x10, x2
	ldr x2, [x0, #1432]
	adcs x11, x11, x2
	ldr x2, [x0, #1440]
	adcs x12, x12, x2
	ldr x2, [x0, #1448]
	adcs x13, x13, x2
	ldr x2, [x0, #1456]
	adcs x14, x14, x2
	ldr x2, [x0, #1464]
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
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	str x14, [x0, #1840]
	str x15, [x0, #1848]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1344]
	ldr x9, [x0, #1352]
	ldr x10, [x0, #1360]
	ldr x11, [x0, #1368]
	ldr x12, [x0, #1376]
	ldr x13, [x0, #1384]
	ldr x14, [x0, #1392]
	ldr x15, [x0, #1400]
	ldr x2, [x0, #1472]
	adds x8, x8, x2
	ldr x2, [x0, #1480]
	adcs x9, x9, x2
	ldr x2, [x0, #1488]
	adcs x10, x10, x2
	ldr x2, [x0, #1496]
	adcs x11, x11, x2
	ldr x2, [x0, #1504]
	adcs x12, x12, x2
	ldr x2, [x0, #1512]
	adcs x13, x13, x2
	ldr x2, [x0, #1520]
	adcs x14, x14, x2
	ldr x2, [x0, #1528]
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
	str x8, [x0, #1856]
	str x9, [x0, #1864]
	str x10, [x0, #1872]
	str x11, [x0, #1880]
	str x12, [x0, #1888]
	str x13, [x0, #1896]
	str x14, [x0, #1904]
	str x15, [x0, #1912]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1408]
	ldr x9, [x0, #1416]
	ldr x10, [x0, #1424]
	ldr x11, [x0, #1432]
	ldr x12, [x0, #1440]
	ldr x13, [x0, #1448]
	ldr x14, [x0, #1456]
	ldr x15, [x0, #1464]
	ldr x2, [x0, #1472]
	adds x8, x8, x2
	ldr x2, [x0, #1480]
	adcs x9, x9, x2
	ldr x2, [x0, #1488]
	adcs x10, x10, x2
	ldr x2, [x0, #1496]
	adcs x11, x11, x2
	ldr x2, [x0, #1504]
	adcs x12, x12, x2
	ldr x2, [x0, #1512]
	adcs x13, x13, x2
	ldr x2, [x0, #1520]
	adcs x14, x14, x2
	ldr x2, [x0, #1528]
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
	movz x2, #1984, lsl #0
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
	movz x2, #1984, lsl #0
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
	cbnz x19, 21b
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
