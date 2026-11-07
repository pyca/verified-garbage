// The functions of `src/internal/vg_ecdsa_brainpoolp384r1_sign_k.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp384r1_sign_k:
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
	movz x1, #36060, lsl #0
	movk x1, #21440, lsl #16
	movk x1, #40760, lsl #32
	movk x1, #3778, lsl #48
	str x1, [x0, #736]
	movz x1, #13069, lsl #0
	movk x1, #35174, lsl #16
	movk x1, #16408, lsl #32
	movk x1, #58041, lsl #48
	str x1, [x0, #744]
	movz x1, #30462, lsl #0
	movk x1, #34760, lsl #16
	movk x1, #48997, lsl #32
	movk x1, #17306, lsl #48
	str x1, [x0, #752]
	movz x1, #6930, lsl #0
	movk x1, #12769, lsl #16
	movk x1, #64236, lsl #32
	movk x1, #18915, lsl #48
	str x1, [x0, #760]
	movz x1, #35606, lsl #0
	movk x1, #20565, lsl #16
	movk x1, #21984, lsl #32
	movk x1, #32226, lsl #48
	str x1, [x0, #768]
	movz x1, #49212, lsl #0
	movk x1, #63449, lsl #16
	movk x1, #25243, lsl #32
	movk x1, #34482, lsl #48
	str x1, [x0, #776]
	movz x1, #3404, lsl #0
	movk x1, #5816, lsl #16
	movk x1, #26316, lsl #32
	movk x1, #51565, lsl #48
	str x1, [x0, #784]
	movz x1, #21388, lsl #0
	movk x1, #19549, lsl #16
	movk x1, #2388, lsl #32
	movk x1, #9661, lsl #48
	str x1, [x0, #792]
	movz x1, #56402, lsl #0
	movk x1, #57212, lsl #16
	movk x1, #63360, lsl #32
	movk x1, #9167, lsl #48
	str x1, [x0, #800]
	movz x1, #33047, lsl #0
	movk x1, #58193, lsl #16
	movk x1, #46342, lsl #32
	movk x1, #21534, lsl #48
	str x1, [x0, #808]
	movz x1, #39385, lsl #0
	movk x1, #15543, lsl #16
	movk x1, #2378, lsl #32
	movk x1, #24391, lsl #48
	str x1, [x0, #816]
	movz x1, #36661, lsl #0
	movk x1, #57022, lsl #16
	movk x1, #31396, lsl #32
	movk x1, #7146, lsl #48
	str x1, [x0, #824]
	movz x1, #5037, lsl #0
	movk x1, #52984, lsl #16
	movk x1, #65516, lsl #32
	movk x1, #30904, lsl #48
	str x1, [x0, #832]
	movz x1, #58766, lsl #0
	movk x1, #28642, lsl #16
	movk x1, #22742, lsl #32
	movk x1, #21292, lsl #48
	str x1, [x0, #840]
	movz x1, #61148, lsl #0
	movk x1, #32840, lsl #16
	movk x1, #9702, lsl #32
	movk x1, #60750, lsl #48
	str x1, [x0, #848]
	movz x1, #43339, lsl #0
	movk x1, #4779, lsl #16
	movk x1, #36598, lsl #32
	movk x1, #60112, lsl #48
	str x1, [x0, #856]
	movz x1, #48672, lsl #0
	movk x1, #44825, lsl #16
	movk x1, #36993, lsl #32
	movk x1, #61602, lsl #48
	str x1, [x0, #864]
	movz x1, #37591, lsl #0
	movk x1, #23751, lsl #16
	movk x1, #57725, lsl #32
	movk x1, #29510, lsl #48
	str x1, [x0, #872]
	movz x7, #0, lsl #0
	str x7, [x0, #2608]
	movz x19, #55, lsl #0
21:
	sub x19, x19, #1
	movz x16, #7, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	movz x2, #0, lsl #0
	add x2, x2, x2
	ldrb w4, [x16, #2230]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2229]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2228]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2227]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2226]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2225]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #2224]
	add x2, x2, x4
	sub x3, x2, #64
	lsr x4, x3, #63
	movz x9, #0, lsl #0
	sub x4, x9, x4
	eor x2, x3, x4
	sub x2, x2, x4
	movz x7, #0, lsl #0
	adrp x16, {VG_BRAINPOOLP384R1_COMB7}
	add x16, x16, {VG_BRAINPOOLP384R1_COMB7}
	movz x17, #6144, lsl #0
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
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #0]
	ldr q21, [x16, #16]
	ldr q22, [x16, #32]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #96]
	ldr q25, [x16, #112]
	ldr q26, [x16, #128]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #192]
	ldr q21, [x16, #208]
	ldr q22, [x16, #224]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #288]
	ldr q25, [x16, #304]
	ldr q26, [x16, #320]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #384]
	ldr q21, [x16, #400]
	ldr q22, [x16, #416]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #480]
	ldr q25, [x16, #496]
	ldr q26, [x16, #512]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #576]
	ldr q21, [x16, #592]
	ldr q22, [x16, #608]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #672]
	ldr q25, [x16, #688]
	ldr q26, [x16, #704]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #768]
	ldr q21, [x16, #784]
	ldr q22, [x16, #800]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #864]
	ldr q25, [x16, #880]
	ldr q26, [x16, #896]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #960]
	ldr q21, [x16, #976]
	ldr q22, [x16, #992]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1056]
	ldr q25, [x16, #1072]
	ldr q26, [x16, #1088]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1152]
	ldr q21, [x16, #1168]
	ldr q22, [x16, #1184]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1248]
	ldr q25, [x16, #1264]
	ldr q26, [x16, #1280]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1344]
	ldr q21, [x16, #1360]
	ldr q22, [x16, #1376]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1440]
	ldr q25, [x16, #1456]
	ldr q26, [x16, #1472]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1536]
	ldr q21, [x16, #1552]
	ldr q22, [x16, #1568]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1632]
	ldr q25, [x16, #1648]
	ldr q26, [x16, #1664]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1728]
	ldr q21, [x16, #1744]
	ldr q22, [x16, #1760]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1824]
	ldr q25, [x16, #1840]
	ldr q26, [x16, #1856]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1920]
	ldr q21, [x16, #1936]
	ldr q22, [x16, #1952]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2016]
	ldr q25, [x16, #2032]
	ldr q26, [x16, #2048]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2112]
	ldr q21, [x16, #2128]
	ldr q22, [x16, #2144]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2208]
	ldr q25, [x16, #2224]
	ldr q26, [x16, #2240]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2304]
	ldr q21, [x16, #2320]
	ldr q22, [x16, #2336]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2400]
	ldr q25, [x16, #2416]
	ldr q26, [x16, #2432]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2496]
	ldr q21, [x16, #2512]
	ldr q22, [x16, #2528]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2592]
	ldr q25, [x16, #2608]
	ldr q26, [x16, #2624]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2688]
	ldr q21, [x16, #2704]
	ldr q22, [x16, #2720]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2784]
	ldr q25, [x16, #2800]
	ldr q26, [x16, #2816]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2880]
	ldr q21, [x16, #2896]
	ldr q22, [x16, #2912]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2976]
	ldr q25, [x16, #2992]
	ldr q26, [x16, #3008]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3072]
	ldr q21, [x16, #3088]
	ldr q22, [x16, #3104]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3168]
	ldr q25, [x16, #3184]
	ldr q26, [x16, #3200]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3264]
	ldr q21, [x16, #3280]
	ldr q22, [x16, #3296]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3360]
	ldr q25, [x16, #3376]
	ldr q26, [x16, #3392]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3456]
	ldr q21, [x16, #3472]
	ldr q22, [x16, #3488]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3552]
	ldr q25, [x16, #3568]
	ldr q26, [x16, #3584]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3648]
	ldr q21, [x16, #3664]
	ldr q22, [x16, #3680]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3744]
	ldr q25, [x16, #3760]
	ldr q26, [x16, #3776]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3840]
	ldr q21, [x16, #3856]
	ldr q22, [x16, #3872]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3936]
	ldr q25, [x16, #3952]
	ldr q26, [x16, #3968]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4032]
	ldr q21, [x16, #4048]
	ldr q22, [x16, #4064]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4128]
	ldr q25, [x16, #4144]
	ldr q26, [x16, #4160]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4224]
	ldr q21, [x16, #4240]
	ldr q22, [x16, #4256]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4320]
	ldr q25, [x16, #4336]
	ldr q26, [x16, #4352]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4416]
	ldr q21, [x16, #4432]
	ldr q22, [x16, #4448]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4512]
	ldr q25, [x16, #4528]
	ldr q26, [x16, #4544]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4608]
	ldr q21, [x16, #4624]
	ldr q22, [x16, #4640]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4704]
	ldr q25, [x16, #4720]
	ldr q26, [x16, #4736]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4800]
	ldr q21, [x16, #4816]
	ldr q22, [x16, #4832]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4896]
	ldr q25, [x16, #4912]
	ldr q26, [x16, #4928]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4992]
	ldr q21, [x16, #5008]
	ldr q22, [x16, #5024]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5088]
	ldr q25, [x16, #5104]
	ldr q26, [x16, #5120]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5184]
	ldr q21, [x16, #5200]
	ldr q22, [x16, #5216]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5280]
	ldr q25, [x16, #5296]
	ldr q26, [x16, #5312]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5376]
	ldr q21, [x16, #5392]
	ldr q22, [x16, #5408]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5472]
	ldr q25, [x16, #5488]
	ldr q26, [x16, #5504]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5568]
	ldr q21, [x16, #5584]
	ldr q22, [x16, #5600]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5664]
	ldr q25, [x16, #5680]
	ldr q26, [x16, #5696]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5760]
	ldr q21, [x16, #5776]
	ldr q22, [x16, #5792]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5856]
	ldr q25, [x16, #5872]
	ldr q26, [x16, #5888]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5952]
	ldr q21, [x16, #5968]
	ldr q22, [x16, #5984]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6048]
	ldr q25, [x16, #6064]
	ldr q26, [x16, #6080]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	orr v0.16b, v0.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	orr v2.16b, v2.16b, v6.16b
	str q0, [x0, #1024]
	str q1, [x0, #1040]
	str q2, [x0, #1056]
	movi v17.2d, #0
	sub v17.2d, v17.2d, v28.2d
	movi v30.2d, #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #48]
	ldr q21, [x16, #64]
	ldr q22, [x16, #80]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #144]
	ldr q25, [x16, #160]
	ldr q26, [x16, #176]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #240]
	ldr q21, [x16, #256]
	ldr q22, [x16, #272]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #336]
	ldr q25, [x16, #352]
	ldr q26, [x16, #368]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #432]
	ldr q21, [x16, #448]
	ldr q22, [x16, #464]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #528]
	ldr q25, [x16, #544]
	ldr q26, [x16, #560]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #624]
	ldr q21, [x16, #640]
	ldr q22, [x16, #656]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #720]
	ldr q25, [x16, #736]
	ldr q26, [x16, #752]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #816]
	ldr q21, [x16, #832]
	ldr q22, [x16, #848]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #912]
	ldr q25, [x16, #928]
	ldr q26, [x16, #944]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1008]
	ldr q21, [x16, #1024]
	ldr q22, [x16, #1040]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1104]
	ldr q25, [x16, #1120]
	ldr q26, [x16, #1136]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1200]
	ldr q21, [x16, #1216]
	ldr q22, [x16, #1232]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1296]
	ldr q25, [x16, #1312]
	ldr q26, [x16, #1328]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1392]
	ldr q21, [x16, #1408]
	ldr q22, [x16, #1424]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1488]
	ldr q25, [x16, #1504]
	ldr q26, [x16, #1520]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1584]
	ldr q21, [x16, #1600]
	ldr q22, [x16, #1616]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1680]
	ldr q25, [x16, #1696]
	ldr q26, [x16, #1712]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1776]
	ldr q21, [x16, #1792]
	ldr q22, [x16, #1808]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1872]
	ldr q25, [x16, #1888]
	ldr q26, [x16, #1904]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1968]
	ldr q21, [x16, #1984]
	ldr q22, [x16, #2000]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2064]
	ldr q25, [x16, #2080]
	ldr q26, [x16, #2096]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2160]
	ldr q21, [x16, #2176]
	ldr q22, [x16, #2192]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2256]
	ldr q25, [x16, #2272]
	ldr q26, [x16, #2288]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2352]
	ldr q21, [x16, #2368]
	ldr q22, [x16, #2384]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2448]
	ldr q25, [x16, #2464]
	ldr q26, [x16, #2480]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2544]
	ldr q21, [x16, #2560]
	ldr q22, [x16, #2576]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2640]
	ldr q25, [x16, #2656]
	ldr q26, [x16, #2672]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2736]
	ldr q21, [x16, #2752]
	ldr q22, [x16, #2768]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2832]
	ldr q25, [x16, #2848]
	ldr q26, [x16, #2864]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2928]
	ldr q21, [x16, #2944]
	ldr q22, [x16, #2960]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3024]
	ldr q25, [x16, #3040]
	ldr q26, [x16, #3056]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3120]
	ldr q21, [x16, #3136]
	ldr q22, [x16, #3152]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3216]
	ldr q25, [x16, #3232]
	ldr q26, [x16, #3248]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3312]
	ldr q21, [x16, #3328]
	ldr q22, [x16, #3344]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3408]
	ldr q25, [x16, #3424]
	ldr q26, [x16, #3440]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3504]
	ldr q21, [x16, #3520]
	ldr q22, [x16, #3536]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3600]
	ldr q25, [x16, #3616]
	ldr q26, [x16, #3632]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3696]
	ldr q21, [x16, #3712]
	ldr q22, [x16, #3728]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3792]
	ldr q25, [x16, #3808]
	ldr q26, [x16, #3824]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3888]
	ldr q21, [x16, #3904]
	ldr q22, [x16, #3920]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3984]
	ldr q25, [x16, #4000]
	ldr q26, [x16, #4016]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4080]
	ldr q21, [x16, #4096]
	ldr q22, [x16, #4112]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4176]
	ldr q25, [x16, #4192]
	ldr q26, [x16, #4208]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4272]
	ldr q21, [x16, #4288]
	ldr q22, [x16, #4304]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4368]
	ldr q25, [x16, #4384]
	ldr q26, [x16, #4400]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4464]
	ldr q21, [x16, #4480]
	ldr q22, [x16, #4496]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4560]
	ldr q25, [x16, #4576]
	ldr q26, [x16, #4592]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4656]
	ldr q21, [x16, #4672]
	ldr q22, [x16, #4688]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4752]
	ldr q25, [x16, #4768]
	ldr q26, [x16, #4784]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #4848]
	ldr q21, [x16, #4864]
	ldr q22, [x16, #4880]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4944]
	ldr q25, [x16, #4960]
	ldr q26, [x16, #4976]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5040]
	ldr q21, [x16, #5056]
	ldr q22, [x16, #5072]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5136]
	ldr q25, [x16, #5152]
	ldr q26, [x16, #5168]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5232]
	ldr q21, [x16, #5248]
	ldr q22, [x16, #5264]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5328]
	ldr q25, [x16, #5344]
	ldr q26, [x16, #5360]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5424]
	ldr q21, [x16, #5440]
	ldr q22, [x16, #5456]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5520]
	ldr q25, [x16, #5536]
	ldr q26, [x16, #5552]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5616]
	ldr q21, [x16, #5632]
	ldr q22, [x16, #5648]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5712]
	ldr q25, [x16, #5728]
	ldr q26, [x16, #5744]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #5808]
	ldr q21, [x16, #5824]
	ldr q22, [x16, #5840]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #5904]
	ldr q25, [x16, #5920]
	ldr q26, [x16, #5936]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #6000]
	ldr q21, [x16, #6016]
	ldr q22, [x16, #6032]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #6096]
	ldr q25, [x16, #6112]
	ldr q26, [x16, #6128]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	orr v0.16b, v0.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	orr v2.16b, v2.16b, v6.16b
	movi v16.2d, #0
	cmeq v16.2d, v16.2d, v19.2d
	movz x6, #5037, lsl #0
	movk x6, #52984, lsl #16
	movk x6, #65516, lsl #32
	movk x6, #30904, lsl #48
	mov v20.d[0], x6
	movz x6, #58766, lsl #0
	movk x6, #28642, lsl #16
	movk x6, #22742, lsl #32
	movk x6, #21292, lsl #48
	mov v20.d[1], x6
	bit v0.16b, v20.16b, v16.16b
	movz x6, #61148, lsl #0
	movk x6, #32840, lsl #16
	movk x6, #9702, lsl #32
	movk x6, #60750, lsl #48
	mov v20.d[0], x6
	movz x6, #43339, lsl #0
	movk x6, #4779, lsl #16
	movk x6, #36598, lsl #32
	movk x6, #60112, lsl #48
	mov v20.d[1], x6
	bit v1.16b, v20.16b, v16.16b
	movz x6, #48672, lsl #0
	movk x6, #44825, lsl #16
	movk x6, #36993, lsl #32
	movk x6, #61602, lsl #48
	mov v20.d[0], x6
	movz x6, #37591, lsl #0
	movk x6, #23751, lsl #16
	movk x6, #57725, lsl #32
	movk x6, #29510, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	str q0, [x0, #1072]
	str q1, [x0, #1088]
	str q2, [x0, #1104]
	subs x4, x2, x5
	movz x6, #5037, lsl #0
	movk x6, #52984, lsl #16
	movk x6, #65516, lsl #32
	movk x6, #30904, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1120]
	movz x6, #58766, lsl #0
	movk x6, #28642, lsl #16
	movk x6, #22742, lsl #32
	movk x6, #21292, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1128]
	movz x6, #61148, lsl #0
	movk x6, #32840, lsl #16
	movk x6, #9702, lsl #32
	movk x6, #60750, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1136]
	movz x6, #43339, lsl #0
	movk x6, #4779, lsl #16
	movk x6, #36598, lsl #32
	movk x6, #60112, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1144]
	movz x6, #48672, lsl #0
	movk x6, #44825, lsl #16
	movk x6, #36993, lsl #32
	movk x6, #61602, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1152]
	movz x6, #37591, lsl #0
	movk x6, #23751, lsl #16
	movk x6, #57725, lsl #32
	movk x6, #29510, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1160]
	movz x7, #0, lsl #0
	ldr x8, [x0, #208]
	ldr x9, [x0, #216]
	ldr x10, [x0, #224]
	ldr x11, [x0, #232]
	ldr x12, [x0, #240]
	ldr x13, [x0, #248]
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
	str x8, [x0, #1504]
	str x9, [x0, #1512]
	str x10, [x0, #1520]
	str x11, [x0, #1528]
	str x12, [x0, #1536]
	str x13, [x0, #1544]
	movz x16, #7, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	ldrb w3, [x16, #2230]
	sub x3, x3, #1
	ldr x1, [x0, #1072]
	ldr x2, [x0, #1504]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1072]
	ldr x1, [x0, #1080]
	ldr x2, [x0, #1512]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1080]
	ldr x1, [x0, #1088]
	ldr x2, [x0, #1520]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1088]
	ldr x1, [x0, #1096]
	ldr x2, [x0, #1528]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1096]
	ldr x1, [x0, #1104]
	ldr x2, [x0, #1536]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1104]
	ldr x1, [x0, #1112]
	ldr x2, [x0, #1544]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1112]
	movz x1, #47092, lsl #0
	movk x1, #53586, lsl #16
	movk x1, #63914, lsl #32
	movk x1, #54730, lsl #48
	str x1, [x0, #1504]
	movz x1, #5431, lsl #0
	movk x1, #53489, lsl #16
	movk x1, #16430, lsl #32
	movk x1, #62905, lsl #48
	str x1, [x0, #1512]
	movz x1, #15210, lsl #0
	movk x1, #26029, lsl #16
	movk x1, #10802, lsl #32
	movk x1, #22123, lsl #48
	str x1, [x0, #1520]
	movz x1, #42454, lsl #0
	movk x1, #3603, lsl #16
	movk x1, #14190, lsl #32
	movk x1, #12436, lsl #48
	str x1, [x0, #1528]
	movz x1, #11832, lsl #0
	movk x1, #9345, lsl #16
	movk x1, #37895, lsl #32
	movk x1, #29244, lsl #48
	str x1, [x0, #1536]
	movz x1, #9942, lsl #0
	movk x1, #5531, lsl #16
	movk x1, #20078, lsl #32
	movk x1, #17152, lsl #48
	str x1, [x0, #1544]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #736, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #784, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #784]
	adds x8, x8, x2
	ldr x2, [x0, #792]
	adcs x9, x9, x2
	ldr x2, [x0, #800]
	adcs x10, x10, x2
	ldr x2, [x0, #808]
	adcs x11, x11, x2
	ldr x2, [x0, #816]
	adcs x12, x12, x2
	ldr x2, [x0, #824]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x2, [x0, #1072]
	adds x8, x8, x2
	ldr x2, [x0, #1080]
	adcs x9, x9, x2
	ldr x2, [x0, #1088]
	adcs x10, x10, x2
	ldr x2, [x0, #1096]
	adcs x11, x11, x2
	ldr x2, [x0, #1104]
	adcs x12, x12, x2
	ldr x2, [x0, #1112]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1168]
	ldr x9, [x0, #1176]
	ldr x10, [x0, #1184]
	ldr x11, [x0, #1192]
	ldr x12, [x0, #1200]
	ldr x13, [x0, #1208]
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
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
	ldr x2, [x0, #1360]
	subs x8, x8, x2
	ldr x2, [x0, #1368]
	sbcs x9, x9, x2
	ldr x2, [x0, #1376]
	sbcs x10, x10, x2
	ldr x2, [x0, #1384]
	sbcs x11, x11, x2
	ldr x2, [x0, #1392]
	sbcs x12, x12, x2
	ldr x2, [x0, #1400]
	sbcs x13, x13, x2
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
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #832]
	adds x8, x8, x2
	ldr x2, [x0, #840]
	adcs x9, x9, x2
	ldr x2, [x0, #848]
	adcs x10, x10, x2
	ldr x2, [x0, #856]
	adcs x11, x11, x2
	ldr x2, [x0, #864]
	adcs x12, x12, x2
	ldr x2, [x0, #872]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x2, [x0, #1120]
	adds x8, x8, x2
	ldr x2, [x0, #1128]
	adcs x9, x9, x2
	ldr x2, [x0, #1136]
	adcs x10, x10, x2
	ldr x2, [x0, #1144]
	adcs x11, x11, x2
	ldr x2, [x0, #1152]
	adcs x12, x12, x2
	ldr x2, [x0, #1160]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1168]
	ldr x9, [x0, #1176]
	ldr x10, [x0, #1184]
	ldr x11, [x0, #1192]
	ldr x12, [x0, #1200]
	ldr x13, [x0, #1208]
	ldr x2, [x0, #1264]
	adds x8, x8, x2
	ldr x2, [x0, #1272]
	adcs x9, x9, x2
	ldr x2, [x0, #1280]
	adcs x10, x10, x2
	ldr x2, [x0, #1288]
	adcs x11, x11, x2
	ldr x2, [x0, #1296]
	adcs x12, x12, x2
	ldr x2, [x0, #1304]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1360]
	ldr x9, [x0, #1368]
	ldr x10, [x0, #1376]
	ldr x11, [x0, #1384]
	ldr x12, [x0, #1392]
	ldr x13, [x0, #1400]
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
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x8, [x0, #784]
	ldr x9, [x0, #792]
	ldr x10, [x0, #800]
	ldr x11, [x0, #808]
	ldr x12, [x0, #816]
	ldr x13, [x0, #824]
	ldr x2, [x0, #832]
	adds x8, x8, x2
	ldr x2, [x0, #840]
	adcs x9, x9, x2
	ldr x2, [x0, #848]
	adcs x10, x10, x2
	ldr x2, [x0, #856]
	adcs x11, x11, x2
	ldr x2, [x0, #864]
	adcs x12, x12, x2
	ldr x2, [x0, #872]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x2, [x0, #1120]
	adds x8, x8, x2
	ldr x2, [x0, #1128]
	adcs x9, x9, x2
	ldr x2, [x0, #1136]
	adcs x10, x10, x2
	ldr x2, [x0, #1144]
	adcs x11, x11, x2
	ldr x2, [x0, #1152]
	adcs x12, x12, x2
	ldr x2, [x0, #1160]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x2, [x0, #1264]
	adds x8, x8, x2
	ldr x2, [x0, #1272]
	adcs x9, x9, x2
	ldr x2, [x0, #1280]
	adcs x10, x10, x2
	ldr x2, [x0, #1288]
	adcs x11, x11, x2
	ldr x2, [x0, #1296]
	adcs x12, x12, x2
	ldr x2, [x0, #1304]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1408]
	ldr x9, [x0, #1416]
	ldr x10, [x0, #1424]
	ldr x11, [x0, #1432]
	ldr x12, [x0, #1440]
	ldr x13, [x0, #1448]
	ldr x2, [x0, #880]
	subs x8, x8, x2
	ldr x2, [x0, #888]
	sbcs x9, x9, x2
	ldr x2, [x0, #896]
	sbcs x10, x10, x2
	ldr x2, [x0, #904]
	sbcs x11, x11, x2
	ldr x2, [x0, #912]
	sbcs x12, x12, x2
	ldr x2, [x0, #920]
	sbcs x13, x13, x2
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
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	mov v29.d[0], x30
	movz x1, #976, lsl #0
	movz x2, #352, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #880, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
	ldr x2, [x0, #976]
	adds x8, x8, x2
	ldr x2, [x0, #984]
	adcs x9, x9, x2
	ldr x2, [x0, #992]
	adcs x10, x10, x2
	ldr x2, [x0, #1000]
	adcs x11, x11, x2
	ldr x2, [x0, #1008]
	adcs x12, x12, x2
	ldr x2, [x0, #1016]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #976]
	str x9, [x0, #984]
	str x10, [x0, #992]
	str x11, [x0, #1000]
	str x12, [x0, #1008]
	str x13, [x0, #1016]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x2, [x0, #976]
	subs x8, x8, x2
	ldr x2, [x0, #984]
	sbcs x9, x9, x2
	ldr x2, [x0, #992]
	sbcs x10, x10, x2
	ldr x2, [x0, #1000]
	sbcs x11, x11, x2
	ldr x2, [x0, #1008]
	sbcs x12, x12, x2
	ldr x2, [x0, #1016]
	sbcs x13, x13, x2
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x2, [x0, #976]
	adds x8, x8, x2
	ldr x2, [x0, #984]
	adcs x9, x9, x2
	ldr x2, [x0, #992]
	adcs x10, x10, x2
	ldr x2, [x0, #1000]
	adcs x11, x11, x2
	ldr x2, [x0, #1008]
	adcs x12, x12, x2
	ldr x2, [x0, #1016]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #976]
	str x9, [x0, #984]
	str x10, [x0, #992]
	str x11, [x0, #1000]
	str x12, [x0, #1008]
	str x13, [x0, #1016]
	mov v29.d[0], x30
	movz x1, #928, lsl #0
	movz x2, #880, lsl #0
	movz x3, #976, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1168]
	ldr x9, [x0, #1176]
	ldr x10, [x0, #1184]
	ldr x11, [x0, #1192]
	ldr x12, [x0, #1200]
	ldr x13, [x0, #1208]
	ldr x2, [x0, #1168]
	adds x8, x8, x2
	ldr x2, [x0, #1176]
	adcs x9, x9, x2
	ldr x2, [x0, #1184]
	adcs x10, x10, x2
	ldr x2, [x0, #1192]
	adcs x11, x11, x2
	ldr x2, [x0, #1200]
	adcs x12, x12, x2
	ldr x2, [x0, #1208]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x2, [x0, #1168]
	adds x8, x8, x2
	ldr x2, [x0, #1176]
	adcs x9, x9, x2
	ldr x2, [x0, #1184]
	adcs x10, x10, x2
	ldr x2, [x0, #1192]
	adcs x11, x11, x2
	ldr x2, [x0, #1200]
	adcs x12, x12, x2
	ldr x2, [x0, #1208]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #352, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x2, [x0, #1264]
	adds x8, x8, x2
	ldr x2, [x0, #1272]
	adcs x9, x9, x2
	ldr x2, [x0, #1280]
	adcs x10, x10, x2
	ldr x2, [x0, #1288]
	adcs x11, x11, x2
	ldr x2, [x0, #1296]
	adcs x12, x12, x2
	ldr x2, [x0, #1304]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1168]
	ldr x9, [x0, #1176]
	ldr x10, [x0, #1184]
	ldr x11, [x0, #1192]
	ldr x12, [x0, #1200]
	ldr x13, [x0, #1208]
	ldr x2, [x0, #1264]
	subs x8, x8, x2
	ldr x2, [x0, #1272]
	sbcs x9, x9, x2
	ldr x2, [x0, #1280]
	sbcs x10, x10, x2
	ldr x2, [x0, #1288]
	sbcs x11, x11, x2
	ldr x2, [x0, #1296]
	sbcs x12, x12, x2
	ldr x2, [x0, #1304]
	sbcs x13, x13, x2
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
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	str x11, [x0, #1288]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #352, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1360]
	ldr x9, [x0, #1368]
	ldr x10, [x0, #1376]
	ldr x11, [x0, #1384]
	ldr x12, [x0, #1392]
	ldr x13, [x0, #1400]
	ldr x2, [x0, #1264]
	adds x8, x8, x2
	ldr x2, [x0, #1272]
	adcs x9, x9, x2
	ldr x2, [x0, #1280]
	adcs x10, x10, x2
	ldr x2, [x0, #1288]
	adcs x11, x11, x2
	ldr x2, [x0, #1296]
	adcs x12, x12, x2
	ldr x2, [x0, #1304]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #928]
	ldr x9, [x0, #936]
	ldr x10, [x0, #944]
	ldr x11, [x0, #952]
	ldr x12, [x0, #960]
	ldr x13, [x0, #968]
	ldr x2, [x0, #1168]
	adds x8, x8, x2
	ldr x2, [x0, #1176]
	adcs x9, x9, x2
	ldr x2, [x0, #1184]
	adcs x10, x10, x2
	ldr x2, [x0, #1192]
	adcs x11, x11, x2
	ldr x2, [x0, #1200]
	adcs x12, x12, x2
	ldr x2, [x0, #1208]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #880, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
	ldr x2, [x0, #1168]
	subs x8, x8, x2
	ldr x2, [x0, #1176]
	sbcs x9, x9, x2
	ldr x2, [x0, #1184]
	sbcs x10, x10, x2
	ldr x2, [x0, #1192]
	sbcs x11, x11, x2
	ldr x2, [x0, #1200]
	sbcs x12, x12, x2
	ldr x2, [x0, #1208]
	sbcs x13, x13, x2
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #976, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #976, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #976]
	ldr x9, [x0, #984]
	ldr x10, [x0, #992]
	ldr x11, [x0, #1000]
	ldr x12, [x0, #1008]
	ldr x13, [x0, #1016]
	ldr x2, [x0, #1168]
	adds x8, x8, x2
	ldr x2, [x0, #1176]
	adcs x9, x9, x2
	ldr x2, [x0, #1184]
	adcs x10, x10, x2
	ldr x2, [x0, #1192]
	adcs x11, x11, x2
	ldr x2, [x0, #1200]
	adcs x12, x12, x2
	ldr x2, [x0, #1208]
	adcs x13, x13, x2
	adc x14, x7, x7
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
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #976]
	str x9, [x0, #984]
	str x10, [x0, #992]
	str x11, [x0, #1000]
	str x12, [x0, #1008]
	str x13, [x0, #1016]
	ldr x1, [x0, #880]
	str x1, [x0, #736]
	ldr x1, [x0, #888]
	str x1, [x0, #744]
	ldr x1, [x0, #896]
	str x1, [x0, #752]
	ldr x1, [x0, #904]
	str x1, [x0, #760]
	ldr x1, [x0, #912]
	str x1, [x0, #768]
	ldr x1, [x0, #920]
	str x1, [x0, #776]
	ldr x1, [x0, #928]
	str x1, [x0, #784]
	ldr x1, [x0, #936]
	str x1, [x0, #792]
	ldr x1, [x0, #944]
	str x1, [x0, #800]
	ldr x1, [x0, #952]
	str x1, [x0, #808]
	ldr x1, [x0, #960]
	str x1, [x0, #816]
	ldr x1, [x0, #968]
	str x1, [x0, #824]
	ldr x1, [x0, #976]
	str x1, [x0, #832]
	ldr x1, [x0, #984]
	str x1, [x0, #840]
	ldr x1, [x0, #992]
	str x1, [x0, #848]
	ldr x1, [x0, #1000]
	str x1, [x0, #856]
	ldr x1, [x0, #1008]
	str x1, [x0, #864]
	ldr x1, [x0, #1016]
	str x1, [x0, #872]
	cbnz x19, 21b
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
	movz x7, #0, lsl #0
	ldr x8, [x0, #1744]
	ldr x9, [x0, #1752]
	ldr x10, [x0, #1760]
	ldr x11, [x0, #1768]
	ldr x12, [x0, #1776]
	ldr x13, [x0, #1784]
	ldr x2, [x0, #208]
	adds x8, x8, x2
	ldr x2, [x0, #216]
	adcs x9, x9, x2
	ldr x2, [x0, #224]
	adcs x10, x10, x2
	ldr x2, [x0, #232]
	adcs x11, x11, x2
	ldr x2, [x0, #240]
	adcs x12, x12, x2
	ldr x2, [x0, #248]
	adcs x13, x13, x2
	adc x14, x7, x7
	ldr x2, [x0, #112]
	subs x1, x8, x2
	ldr x2, [x0, #120]
	sbcs x3, x9, x2
	ldr x2, [x0, #128]
	sbcs x4, x10, x2
	ldr x2, [x0, #136]
	sbcs x5, x11, x2
	ldr x2, [x0, #144]
	sbcs x6, x12, x2
	ldr x2, [x0, #152]
	sbcs x16, x13, x2
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1792]
	str x9, [x0, #1800]
	str x10, [x0, #1808]
	str x11, [x0, #1816]
	str x12, [x0, #1824]
	str x13, [x0, #1832]
	mov v29.d[0], x30
	movz x1, #1840, lsl #0
	movz x2, #1552, lsl #0
	movz x3, #544, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
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
	ldr x1, [x0, #1552]
	ldr x2, [x0, #112]
	subs x16, x1, x2
	ldr x1, [x0, #1560]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	ldr x1, [x0, #1568]
	ldr x2, [x0, #128]
	sbcs x16, x1, x2
	ldr x1, [x0, #1576]
	ldr x2, [x0, #136]
	sbcs x16, x1, x2
	ldr x1, [x0, #1584]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #1592]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1552]
	ldr x2, [x0, #1560]
	orr x1, x1, x2
	ldr x2, [x0, #1568]
	orr x1, x1, x2
	ldr x2, [x0, #1576]
	orr x1, x1, x2
	ldr x2, [x0, #1584]
	orr x1, x1, x2
	ldr x2, [x0, #1592]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1792]
	ldr x2, [x0, #1800]
	orr x1, x1, x2
	ldr x2, [x0, #1808]
	orr x1, x1, x2
	ldr x2, [x0, #1816]
	orr x1, x1, x2
	ldr x2, [x0, #1824]
	orr x1, x1, x2
	ldr x2, [x0, #1832]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	mov v29.d[0], x30
	bl {vg_brainpoolp384r1_inv_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1888, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #544, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1600, lsl #0
	movz x3, #544, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1984, lsl #0
	movz x2, #1648, lsl #0
	movz x3, #544, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2032, lsl #0
	movz x2, #1888, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2032]
	ldr x9, [x0, #2040]
	ldr x10, [x0, #2048]
	ldr x11, [x0, #2056]
	ldr x12, [x0, #2064]
	ldr x13, [x0, #2072]
	ldr x2, [x0, #1984]
	adds x8, x8, x2
	ldr x2, [x0, #1992]
	adcs x9, x9, x2
	ldr x2, [x0, #2000]
	adcs x10, x10, x2
	ldr x2, [x0, #2008]
	adcs x11, x11, x2
	ldr x2, [x0, #2016]
	adcs x12, x12, x2
	ldr x2, [x0, #2024]
	adcs x13, x13, x2
	adc x14, x7, x7
	ldr x2, [x0, #112]
	subs x1, x8, x2
	ldr x2, [x0, #120]
	sbcs x3, x9, x2
	ldr x2, [x0, #128]
	sbcs x4, x10, x2
	ldr x2, [x0, #136]
	sbcs x5, x11, x2
	ldr x2, [x0, #144]
	sbcs x6, x12, x2
	ldr x2, [x0, #152]
	sbcs x16, x13, x2
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #2032]
	str x9, [x0, #2040]
	str x10, [x0, #2048]
	str x11, [x0, #2056]
	str x12, [x0, #2064]
	str x13, [x0, #2072]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #2032, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2128, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #256, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2128]
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
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	ldr x3, [x0, #2176]
	ldr x1, [x0, #1792]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #40]
	ldr x1, [x0, #1800]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #32]
	ldr x1, [x0, #1808]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #24]
	ldr x1, [x0, #1816]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #16]
	ldr x1, [x0, #1824]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #8]
	ldr x1, [x0, #1832]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #0]
	ldr x1, [x0, #2128]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #88]
	ldr x1, [x0, #2136]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #80]
	ldr x1, [x0, #2144]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #72]
	ldr x1, [x0, #2152]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #64]
	ldr x1, [x0, #2160]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #56]
	ldr x1, [x0, #2168]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #48]
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
