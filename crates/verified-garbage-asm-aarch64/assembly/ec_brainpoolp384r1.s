// The functions of `src/ec_brainpoolp384r1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp384r1_public_key:
	add x4, x2, #0
	add x3, x1, #0
	add x2, x1, #0
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
	ldr x5, [x3, #40]
	rev x5, x5
	str x5, [x0, #1552]
	ldr x5, [x3, #32]
	rev x5, x5
	str x5, [x0, #1560]
	ldr x5, [x3, #24]
	rev x5, x5
	str x5, [x0, #1568]
	ldr x5, [x3, #16]
	rev x5, x5
	str x5, [x0, #1576]
	ldr x5, [x3, #8]
	rev x5, x5
	str x5, [x0, #1584]
	ldr x5, [x3, #0]
	rev x5, x5
	str x5, [x0, #1592]
	ldr x5, [x1, #40]
	rev x5, x5
	str x5, [x0, #1600]
	ldr x5, [x1, #32]
	rev x5, x5
	str x5, [x0, #1608]
	ldr x5, [x1, #24]
	rev x5, x5
	str x5, [x0, #1616]
	ldr x5, [x1, #16]
	rev x5, x5
	str x5, [x0, #1624]
	ldr x5, [x1, #8]
	rev x5, x5
	str x5, [x0, #1632]
	ldr x5, [x1, #0]
	rev x5, x5
	str x5, [x0, #1640]
	ldr x5, [x2, #40]
	rev x5, x5
	str x5, [x0, #1648]
	ldr x5, [x2, #32]
	rev x5, x5
	str x5, [x0, #1656]
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #1664]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1672]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1680]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1688]
	movz x1, #60499, lsl #0
	movk x1, #12551, lsl #16
	movk x1, #19, lsl #32
	movk x1, #34631, lsl #48
	str x1, [x0, #64]
	movz x1, #6769, lsl #0
	movk x1, #36893, lsl #16
	movk x1, #42793, lsl #32
	movk x1, #44243, lsl #48
	str x1, [x0, #72]
	movz x1, #4387, lsl #0
	movk x1, #32695, lsl #16
	movk x1, #55833, lsl #32
	movk x1, #4785, lsl #48
	str x1, [x0, #80]
	movz x1, #22196, lsl #0
	movk x1, #60756, lsl #16
	movk x1, #28937, lsl #32
	movk x1, #5423, lsl #48
	str x1, [x0, #88]
	movz x1, #16863, lsl #0
	movk x1, #20710, lsl #16
	movk x1, #28542, lsl #32
	movk x1, #3933, lsl #48
	str x1, [x0, #96]
	movz x1, #27944, lsl #0
	movk x1, #41784, lsl #16
	movk x1, #7810, lsl #32
	movk x1, #36025, lsl #48
	str x1, [x0, #104]
	movz x1, #25957, lsl #0
	movk x1, #59652, lsl #16
	movk x1, #12802, lsl #32
	movk x1, #15240, lsl #48
	str x1, [x0, #112]
	movz x1, #49936, lsl #0
	movk x1, #27519, lsl #16
	movk x1, #46767, lsl #32
	movk x1, #53050, lsl #48
	str x1, [x0, #120]
	movz x1, #9639, lsl #0
	movk x1, #44036, lsl #16
	movk x1, #28268, lsl #32
	movk x1, #7958, lsl #48
	str x1, [x0, #128]
	movz x1, #22195, lsl #0
	movk x1, #60756, lsl #16
	movk x1, #28937, lsl #32
	movk x1, #5423, lsl #48
	str x1, [x0, #136]
	movz x1, #16863, lsl #0
	movk x1, #20710, lsl #16
	movk x1, #28542, lsl #32
	movk x1, #3933, lsl #48
	str x1, [x0, #144]
	movz x1, #27944, lsl #0
	movk x1, #41784, lsl #16
	movk x1, #7810, lsl #32
	movk x1, #36025, lsl #48
	str x1, [x0, #152]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #208]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #216]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #224]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #248]
	movz x1, #1, lsl #0
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
	movz x1, #5037, lsl #0
	movk x1, #52984, lsl #16
	movk x1, #65516, lsl #32
	movk x1, #30904, lsl #48
	str x1, [x0, #304]
	movz x1, #58766, lsl #0
	movk x1, #28642, lsl #16
	movk x1, #22742, lsl #32
	movk x1, #21292, lsl #48
	str x1, [x0, #312]
	movz x1, #61148, lsl #0
	movk x1, #32840, lsl #16
	movk x1, #9702, lsl #32
	movk x1, #60750, lsl #48
	str x1, [x0, #320]
	movz x1, #43339, lsl #0
	movk x1, #4779, lsl #16
	movk x1, #36598, lsl #32
	movk x1, #60112, lsl #48
	str x1, [x0, #328]
	movz x1, #48672, lsl #0
	movk x1, #44825, lsl #16
	movk x1, #36993, lsl #32
	movk x1, #61602, lsl #48
	str x1, [x0, #336]
	movz x1, #37591, lsl #0
	movk x1, #23751, lsl #16
	movk x1, #57725, lsl #32
	movk x1, #29510, lsl #48
	str x1, [x0, #344]
	movz x1, #15513, lsl #0
	movk x1, #18028, lsl #16
	movk x1, #47253, lsl #32
	movk x1, #56102, lsl #48
	str x1, [x0, #352]
	movz x1, #45179, lsl #0
	movk x1, #61783, lsl #16
	movk x1, #62462, lsl #32
	movk x1, #30167, lsl #48
	str x1, [x0, #360]
	movz x1, #3508, lsl #0
	movk x1, #55281, lsl #16
	movk x1, #29113, lsl #32
	movk x1, #37735, lsl #48
	str x1, [x0, #368]
	movz x1, #37748, lsl #0
	movk x1, #13650, lsl #16
	movk x1, #59877, lsl #32
	movk x1, #59391, lsl #48
	str x1, [x0, #376]
	movz x1, #3168, lsl #0
	movk x1, #17072, lsl #16
	movk x1, #36831, lsl #32
	movk x1, #16394, lsl #48
	str x1, [x0, #384]
	movz x1, #49361, lsl #0
	movk x1, #41704, lsl #16
	movk x1, #32801, lsl #32
	movk x1, #31795, lsl #48
	str x1, [x0, #392]
	movz x1, #57709, lsl #0
	movk x1, #200, lsl #16
	movk x1, #65002, lsl #32
	movk x1, #7941, lsl #48
	str x1, [x0, #400]
	movz x1, #4067, lsl #0
	movk x1, #8282, lsl #16
	movk x1, #63432, lsl #32
	movk x1, #13870, lsl #48
	str x1, [x0, #408]
	movz x1, #28378, lsl #0
	movk x1, #63265, lsl #16
	movk x1, #22211, lsl #32
	movk x1, #52660, lsl #48
	str x1, [x0, #416]
	movz x1, #65240, lsl #0
	movk x1, #65143, lsl #16
	movk x1, #14375, lsl #32
	movk x1, #5953, lsl #48
	str x1, [x0, #424]
	movz x1, #9565, lsl #0
	movk x1, #53709, lsl #16
	movk x1, #22145, lsl #32
	movk x1, #11059, lsl #48
	str x1, [x0, #432]
	movz x1, #34474, lsl #0
	movk x1, #59462, lsl #16
	movk x1, #52986, lsl #32
	movk x1, #17725, lsl #48
	str x1, [x0, #440]
	movz x1, #64449, lsl #0
	movk x1, #54328, lsl #16
	movk x1, #57067, lsl #32
	movk x1, #41353, lsl #48
	str x1, [x0, #448]
	movz x1, #34495, lsl #0
	movk x1, #54696, lsl #16
	movk x1, #33000, lsl #32
	movk x1, #26364, lsl #48
	str x1, [x0, #456]
	movz x1, #12067, lsl #0
	movk x1, #40224, lsl #16
	movk x1, #30953, lsl #32
	movk x1, #38083, lsl #48
	str x1, [x0, #464]
	movz x1, #8548, lsl #0
	movk x1, #63836, lsl #16
	movk x1, #9806, lsl #32
	movk x1, #1675, lsl #48
	str x1, [x0, #472]
	movz x1, #153, lsl #0
	movk x1, #47821, lsl #16
	movk x1, #3535, lsl #32
	movk x1, #40157, lsl #48
	str x1, [x0, #480]
	movz x1, #16321, lsl #0
	movk x1, #35061, lsl #16
	movk x1, #30003, lsl #32
	movk x1, #34048, lsl #48
	str x1, [x0, #488]
	movz x1, #16549, lsl #0
	movk x1, #3553, lsl #16
	movk x1, #45873, lsl #32
	movk x1, #59192, lsl #48
	str x1, [x0, #496]
	movz x1, #28501, lsl #0
	movk x1, #51097, lsl #16
	movk x1, #53830, lsl #32
	movk x1, #62944, lsl #48
	str x1, [x0, #504]
	movz x1, #14332, lsl #0
	movk x1, #36615, lsl #16
	movk x1, #2467, lsl #32
	movk x1, #63619, lsl #48
	str x1, [x0, #512]
	movz x1, #37399, lsl #0
	movk x1, #54641, lsl #16
	movk x1, #44244, lsl #32
	movk x1, #41344, lsl #48
	str x1, [x0, #520]
	movz x1, #56758, lsl #0
	movk x1, #20257, lsl #16
	movk x1, #9574, lsl #32
	movk x1, #50710, lsl #48
	str x1, [x0, #528]
	movz x1, #26805, lsl #0
	movk x1, #17801, lsl #16
	movk x1, #41058, lsl #32
	movk x1, #11508, lsl #48
	str x1, [x0, #536]
	movz x1, #7310, lsl #0
	movk x1, #56951, lsl #16
	movk x1, #54178, lsl #32
	movk x1, #44110, lsl #48
	str x1, [x0, #544]
	movz x1, #27502, lsl #0
	movk x1, #12075, lsl #16
	movk x1, #20000, lsl #32
	movk x1, #14118, lsl #48
	str x1, [x0, #552]
	movz x1, #26762, lsl #0
	movk x1, #38914, lsl #16
	movk x1, #32315, lsl #32
	movk x1, #10898, lsl #48
	str x1, [x0, #560]
	movz x1, #18687, lsl #0
	movk x1, #21207, lsl #16
	movk x1, #29899, lsl #32
	movk x1, #22346, lsl #48
	str x1, [x0, #568]
	movz x1, #24539, lsl #0
	movk x1, #25878, lsl #16
	movk x1, #28105, lsl #32
	movk x1, #36744, lsl #48
	str x1, [x0, #576]
	movz x1, #38850, lsl #0
	movk x1, #24910, lsl #16
	movk x1, #37914, lsl #32
	movk x1, #3304, lsl #48
	str x1, [x0, #584]
	movz x1, #39579, lsl #0
	movk x1, #5883, lsl #16
	movk x1, #52733, lsl #32
	movk x1, #50295, lsl #48
	str x1, [x0, #592]
	movz x1, #15599, lsl #0
	movk x1, #38016, lsl #16
	movk x1, #18768, lsl #32
	movk x1, #12485, lsl #48
	str x1, [x0, #600]
	movz x1, #55896, lsl #0
	movk x1, #21499, lsl #16
	movk x1, #37267, lsl #32
	movk x1, #57577, lsl #48
	str x1, [x0, #608]
	movz x1, #43340, lsl #0
	movk x1, #4779, lsl #16
	movk x1, #36598, lsl #32
	movk x1, #60112, lsl #48
	str x1, [x0, #616]
	movz x1, #48672, lsl #0
	movk x1, #44825, lsl #16
	movk x1, #36993, lsl #32
	movk x1, #61602, lsl #48
	str x1, [x0, #624]
	movz x1, #37591, lsl #0
	movk x1, #23751, lsl #16
	movk x1, #57725, lsl #32
	movk x1, #29510, lsl #48
	str x1, [x0, #632]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #736]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #744]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #752]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #760]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #768]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #776]
	movz x1, #5037, lsl #0
	movk x1, #52984, lsl #16
	movk x1, #65516, lsl #32
	movk x1, #30904, lsl #48
	str x1, [x0, #784]
	movz x1, #58766, lsl #0
	movk x1, #28642, lsl #16
	movk x1, #22742, lsl #32
	movk x1, #21292, lsl #48
	str x1, [x0, #792]
	movz x1, #61148, lsl #0
	movk x1, #32840, lsl #16
	movk x1, #9702, lsl #32
	movk x1, #60750, lsl #48
	str x1, [x0, #800]
	movz x1, #43339, lsl #0
	movk x1, #4779, lsl #16
	movk x1, #36598, lsl #32
	movk x1, #60112, lsl #48
	str x1, [x0, #808]
	movz x1, #48672, lsl #0
	movk x1, #44825, lsl #16
	movk x1, #36993, lsl #32
	movk x1, #61602, lsl #48
	str x1, [x0, #816]
	movz x1, #37591, lsl #0
	movk x1, #23751, lsl #16
	movk x1, #57725, lsl #32
	movk x1, #29510, lsl #48
	str x1, [x0, #824]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #832]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #840]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #848]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #856]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #864]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #872]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #2176]
	movz x19, #48, lsl #0
	movz x5, #1, lsl #0
20:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #1552]
	lsl x17, x19, #3
	add x17, x0, x17
	and x2, x1, x5
	strb w2, [x17, #2224]
	lsr x2, x1, #1
	and x2, x2, x5
	strb w2, [x17, #2225]
	lsr x2, x1, #2
	and x2, x2, x5
	strb w2, [x17, #2226]
	lsr x2, x1, #3
	and x2, x2, x5
	strb w2, [x17, #2227]
	lsr x2, x1, #4
	and x2, x2, x5
	strb w2, [x17, #2228]
	lsr x2, x1, #5
	and x2, x2, x5
	strb w2, [x17, #2229]
	lsr x2, x1, #6
	and x2, x2, x5
	strb w2, [x17, #2230]
	lsr x2, x1, #7
	and x2, x2, x5
	strb w2, [x17, #2231]
	cbnz x19, 20b
	ldr x1, [x0, #448]
	str x1, [x0, #736]
	ldr x1, [x0, #456]
	str x1, [x0, #744]
	ldr x1, [x0, #464]
	str x1, [x0, #752]
	ldr x1, [x0, #472]
	str x1, [x0, #760]
	ldr x1, [x0, #480]
	str x1, [x0, #768]
	ldr x1, [x0, #488]
	str x1, [x0, #776]
	ldr x1, [x0, #496]
	str x1, [x0, #784]
	ldr x1, [x0, #504]
	str x1, [x0, #792]
	ldr x1, [x0, #512]
	str x1, [x0, #800]
	ldr x1, [x0, #520]
	str x1, [x0, #808]
	ldr x1, [x0, #528]
	str x1, [x0, #816]
	ldr x1, [x0, #536]
	str x1, [x0, #824]
	movz x1, #47092, lsl #0
	movk x1, #53586, lsl #16
	movk x1, #63914, lsl #32
	movk x1, #54730, lsl #48
	str x1, [x0, #400]
	movz x1, #5431, lsl #0
	movk x1, #53489, lsl #16
	movk x1, #16430, lsl #32
	movk x1, #62905, lsl #48
	str x1, [x0, #408]
	movz x1, #15210, lsl #0
	movk x1, #26029, lsl #16
	movk x1, #10802, lsl #32
	movk x1, #22123, lsl #48
	str x1, [x0, #416]
	movz x1, #42454, lsl #0
	movk x1, #3603, lsl #16
	movk x1, #14190, lsl #32
	movk x1, #12436, lsl #48
	str x1, [x0, #424]
	movz x1, #11832, lsl #0
	movk x1, #9345, lsl #16
	movk x1, #37895, lsl #32
	movk x1, #29244, lsl #48
	str x1, [x0, #432]
	movz x1, #9942, lsl #0
	movk x1, #5531, lsl #16
	movk x1, #20078, lsl #32
	movk x1, #17152, lsl #48
	str x1, [x0, #440]
	mov v29.d[0], x30
	bl {vg_brainpoolp384r1_mul}
	umov x30, v29.d[0]
	movz x1, #57709, lsl #0
	movk x1, #200, lsl #16
	movk x1, #65002, lsl #32
	movk x1, #7941, lsl #48
	str x1, [x0, #400]
	movz x1, #4067, lsl #0
	movk x1, #8282, lsl #16
	movk x1, #63432, lsl #32
	movk x1, #13870, lsl #48
	str x1, [x0, #408]
	movz x1, #28378, lsl #0
	movk x1, #63265, lsl #16
	movk x1, #22211, lsl #32
	movk x1, #52660, lsl #48
	str x1, [x0, #416]
	movz x1, #65240, lsl #0
	movk x1, #65143, lsl #16
	movk x1, #14375, lsl #32
	movk x1, #5953, lsl #48
	str x1, [x0, #424]
	movz x1, #9565, lsl #0
	movk x1, #53709, lsl #16
	movk x1, #22145, lsl #32
	movk x1, #11059, lsl #48
	str x1, [x0, #432]
	movz x1, #34474, lsl #0
	movk x1, #59462, lsl #16
	movk x1, #52986, lsl #32
	movk x1, #17725, lsl #48
	str x1, [x0, #440]
	mov v29.d[0], x30
	bl {vg_brainpoolp384r1_inv_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1696, lsl #0
	movz x2, #736, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1744, lsl #0
	movz x2, #1696, lsl #0
	movz x3, #256, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1888, lsl #0
	movz x2, #784, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2128, lsl #0
	movz x2, #1888, lsl #0
	movz x3, #256, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1600]
	ldr x2, [x0, #112]
	subs x16, x1, x2
	ldr x1, [x0, #1608]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	ldr x1, [x0, #1616]
	ldr x2, [x0, #128]
	sbcs x16, x1, x2
	ldr x1, [x0, #1624]
	ldr x2, [x0, #136]
	sbcs x16, x1, x2
	ldr x1, [x0, #1632]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #1640]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1600]
	ldr x2, [x0, #1608]
	orr x1, x1, x2
	ldr x2, [x0, #1616]
	orr x1, x1, x2
	ldr x2, [x0, #1624]
	orr x1, x1, x2
	ldr x2, [x0, #1632]
	orr x1, x1, x2
	ldr x2, [x0, #1640]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	movz x7, #0, lsl #0
	ldr x1, [x0, #832]
	ldr x2, [x0, #840]
	orr x1, x1, x2
	ldr x2, [x0, #848]
	orr x1, x1, x2
	ldr x2, [x0, #856]
	orr x1, x1, x2
	ldr x2, [x0, #864]
	orr x1, x1, x2
	ldr x2, [x0, #872]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	ldr x3, [x0, #2176]
	movz x1, #4, lsl #0
	and x1, x1, x3
	strb w1, [x20, #0]
	add x6, x20, #1
	ldr x1, [x0, #1744]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #40]
	ldr x1, [x0, #1752]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #32]
	ldr x1, [x0, #1760]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #24]
	ldr x1, [x0, #1768]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #16]
	ldr x1, [x0, #1776]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #8]
	ldr x1, [x0, #1784]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #0]
	ldr x1, [x0, #2128]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #88]
	ldr x1, [x0, #2136]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #80]
	ldr x1, [x0, #2144]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #72]
	ldr x1, [x0, #2152]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #64]
	ldr x1, [x0, #2160]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #56]
	ldr x1, [x0, #2168]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #48]
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
