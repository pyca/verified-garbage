// The functions of `src/ecdsa_brainpoolp384r1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp384r1_verify:
	add x4, x3, #0
	add x6, x0, #0
	add x3, x2, #0
	add x8, x2, #48
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
	ldr x5, [x8, #40]
	rev x5, x5
	str x5, [x0, #1504]
	ldr x5, [x8, #32]
	rev x5, x5
	str x5, [x0, #1512]
	ldr x5, [x8, #24]
	rev x5, x5
	str x5, [x0, #1520]
	ldr x5, [x8, #16]
	rev x5, x5
	str x5, [x0, #1528]
	ldr x5, [x8, #8]
	rev x5, x5
	str x5, [x0, #1536]
	ldr x5, [x8, #0]
	rev x5, x5
	str x5, [x0, #1544]
	movz x1, #19422, lsl #0
	movk x1, #16566, lsl #16
	movk x1, #61439, lsl #32
	movk x1, #2172, lsl #48
	str x1, [x0, #1936]
	movz x1, #55653, lsl #0
	movk x1, #15743, lsl #16
	movk x1, #33588, lsl #32
	movk x1, #21330, lsl #48
	str x1, [x0, #1944]
	movz x1, #2201, lsl #0
	movk x1, #51604, lsl #16
	movk x1, #63900, lsl #32
	movk x1, #36392, lsl #48
	str x1, [x0, #1952]
	movz x1, #54703, lsl #0
	movk x1, #39192, lsl #16
	movk x1, #401, lsl #32
	movk x1, #25108, lsl #48
	str x1, [x0, #1960]
	movz x1, #1324, lsl #0
	movk x1, #42366, lsl #16
	movk x1, #61243, lsl #32
	movk x1, #54726, lsl #48
	str x1, [x0, #1968]
	movz x1, #63554, lsl #0
	movk x1, #6029, lsl #16
	movk x1, #26755, lsl #32
	movk x1, #14015, lsl #48
	str x1, [x0, #1976]
	movz x1, #57709, lsl #0
	movk x1, #200, lsl #16
	movk x1, #65002, lsl #32
	movk x1, #7941, lsl #48
	str x1, [x0, #1984]
	movz x1, #4067, lsl #0
	movk x1, #8282, lsl #16
	movk x1, #63432, lsl #32
	movk x1, #13870, lsl #48
	str x1, [x0, #1992]
	movz x1, #28378, lsl #0
	movk x1, #63265, lsl #16
	movk x1, #22211, lsl #32
	movk x1, #52660, lsl #48
	str x1, [x0, #2000]
	movz x1, #65240, lsl #0
	movk x1, #65143, lsl #16
	movk x1, #14375, lsl #32
	movk x1, #5953, lsl #48
	str x1, [x0, #2008]
	movz x1, #9565, lsl #0
	movk x1, #53709, lsl #16
	movk x1, #22145, lsl #32
	movk x1, #11059, lsl #48
	str x1, [x0, #2016]
	movz x1, #34474, lsl #0
	movk x1, #59462, lsl #16
	movk x1, #52986, lsl #32
	movk x1, #17725, lsl #48
	str x1, [x0, #2024]
	add x2, x6, #49
	ldr x5, [x2, #40]
	rev x5, x5
	str x5, [x0, #1792]
	ldr x5, [x2, #32]
	rev x5, x5
	str x5, [x0, #1800]
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #1808]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1816]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1824]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1832]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	movz x5, #4, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	mov v28.d[0], x30
	bl {vg_brainpoolp384r1_check_point}
	umov x30, v28.d[0]
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
	ldr x1, [x0, #1504]
	ldr x2, [x0, #112]
	subs x16, x1, x2
	ldr x1, [x0, #1512]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	ldr x1, [x0, #1520]
	ldr x2, [x0, #128]
	sbcs x16, x1, x2
	ldr x1, [x0, #1528]
	ldr x2, [x0, #136]
	sbcs x16, x1, x2
	ldr x1, [x0, #1536]
	ldr x2, [x0, #144]
	sbcs x16, x1, x2
	ldr x1, [x0, #1544]
	ldr x2, [x0, #152]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1504]
	ldr x2, [x0, #1512]
	orr x1, x1, x2
	ldr x2, [x0, #1520]
	orr x1, x1, x2
	ldr x2, [x0, #1528]
	orr x1, x1, x2
	ldr x2, [x0, #1536]
	orr x1, x1, x2
	ldr x2, [x0, #1544]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	mov v29.d[0], x30
	movz x1, #1840, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #544, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	bl {vg_brainpoolp384r1_inv_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1984, lsl #0
	movz x2, #1600, lsl #0
	movz x3, #544, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1552, lsl #0
	movz x3, #544, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2032, lsl #0
	movz x2, #1984, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1696, lsl #0
	movz x2, #2032, lsl #0
	movz x3, #256, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1744, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #256, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_n}
	umov x30, v29.d[0]
	movz x19, #48, lsl #0
	movz x5, #1, lsl #0
21:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #1696]
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
	movz x19, #48, lsl #0
	movz x5, #1, lsl #0
22:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #1744]
	lsl x17, x19, #3
	add x17, x0, x17
	and x2, x1, x5
	strb w2, [x17, #3328]
	lsr x2, x1, #1
	and x2, x2, x5
	strb w2, [x17, #3329]
	lsr x2, x1, #2
	and x2, x2, x5
	strb w2, [x17, #3330]
	lsr x2, x1, #3
	and x2, x2, x5
	strb w2, [x17, #3331]
	lsr x2, x1, #4
	and x2, x2, x5
	strb w2, [x17, #3332]
	lsr x2, x1, #5
	and x2, x2, x5
	strb w2, [x17, #3333]
	lsr x2, x1, #6
	and x2, x2, x5
	strb w2, [x17, #3334]
	lsr x2, x1, #7
	and x2, x2, x5
	strb w2, [x17, #3335]
	cbnz x19, 22b
	movz x1, #47092, lsl #0
	movk x1, #53586, lsl #16
	movk x1, #63914, lsl #32
	movk x1, #54730, lsl #48
	str x1, [x0, #640]
	movz x1, #5431, lsl #0
	movk x1, #53489, lsl #16
	movk x1, #16430, lsl #32
	movk x1, #62905, lsl #48
	str x1, [x0, #648]
	movz x1, #15210, lsl #0
	movk x1, #26029, lsl #16
	movk x1, #10802, lsl #32
	movk x1, #22123, lsl #48
	str x1, [x0, #656]
	movz x1, #42454, lsl #0
	movk x1, #3603, lsl #16
	movk x1, #14190, lsl #32
	movk x1, #12436, lsl #48
	str x1, [x0, #664]
	movz x1, #11832, lsl #0
	movk x1, #9345, lsl #16
	movk x1, #37895, lsl #32
	movk x1, #29244, lsl #48
	str x1, [x0, #672]
	movz x1, #9942, lsl #0
	movk x1, #5531, lsl #16
	movk x1, #20078, lsl #32
	movk x1, #17152, lsl #48
	str x1, [x0, #680]
	movz x19, #1, lsl #0
23:
	sub x2, x19, #15
	cbz x2, 24f
	sub x2, x19, #14
	cbz x2, 26f
	sub x2, x19, #13
	cbz x2, 28f
	sub x2, x19, #12
	cbz x2, 210f
	sub x2, x19, #11
	cbz x2, 212f
	sub x2, x19, #10
	cbz x2, 214f
	sub x2, x19, #9
	cbz x2, 216f
	sub x2, x19, #8
	cbz x2, 218f
	sub x2, x19, #7
	cbz x2, 220f
	sub x2, x19, #6
	cbz x2, 222f
	sub x2, x19, #5
	cbz x2, 224f
	sub x2, x19, #4
	cbz x2, 226f
	sub x2, x19, #3
	cbz x2, 228f
	sub x2, x19, #2
	cbz x2, 230f
	sub x2, x19, #1
	cbz x2, 232f
	b 233f
232:
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
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
233:
	b 231f
230:
	ldr x1, [x0, #5280]
	str x1, [x0, #736]
	ldr x1, [x0, #5288]
	str x1, [x0, #744]
	ldr x1, [x0, #5296]
	str x1, [x0, #752]
	ldr x1, [x0, #5304]
	str x1, [x0, #760]
	ldr x1, [x0, #5312]
	str x1, [x0, #768]
	ldr x1, [x0, #5320]
	str x1, [x0, #776]
	ldr x1, [x0, #5328]
	str x1, [x0, #784]
	ldr x1, [x0, #5336]
	str x1, [x0, #792]
	ldr x1, [x0, #5344]
	str x1, [x0, #800]
	ldr x1, [x0, #5352]
	str x1, [x0, #808]
	ldr x1, [x0, #5360]
	str x1, [x0, #816]
	ldr x1, [x0, #5368]
	str x1, [x0, #824]
	ldr x1, [x0, #5376]
	str x1, [x0, #832]
	ldr x1, [x0, #5384]
	str x1, [x0, #840]
	ldr x1, [x0, #5392]
	str x1, [x0, #848]
	ldr x1, [x0, #5400]
	str x1, [x0, #856]
	ldr x1, [x0, #5408]
	str x1, [x0, #864]
	ldr x1, [x0, #5416]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
231:
	b 229f
228:
	ldr x1, [x0, #5424]
	str x1, [x0, #736]
	ldr x1, [x0, #5432]
	str x1, [x0, #744]
	ldr x1, [x0, #5440]
	str x1, [x0, #752]
	ldr x1, [x0, #5448]
	str x1, [x0, #760]
	ldr x1, [x0, #5456]
	str x1, [x0, #768]
	ldr x1, [x0, #5464]
	str x1, [x0, #776]
	ldr x1, [x0, #5472]
	str x1, [x0, #784]
	ldr x1, [x0, #5480]
	str x1, [x0, #792]
	ldr x1, [x0, #5488]
	str x1, [x0, #800]
	ldr x1, [x0, #5496]
	str x1, [x0, #808]
	ldr x1, [x0, #5504]
	str x1, [x0, #816]
	ldr x1, [x0, #5512]
	str x1, [x0, #824]
	ldr x1, [x0, #5520]
	str x1, [x0, #832]
	ldr x1, [x0, #5528]
	str x1, [x0, #840]
	ldr x1, [x0, #5536]
	str x1, [x0, #848]
	ldr x1, [x0, #5544]
	str x1, [x0, #856]
	ldr x1, [x0, #5552]
	str x1, [x0, #864]
	ldr x1, [x0, #5560]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
229:
	b 227f
226:
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
	ldr x1, [x0, #1888]
	str x1, [x0, #2032]
	ldr x1, [x0, #1896]
	str x1, [x0, #2040]
	ldr x1, [x0, #1904]
	str x1, [x0, #2048]
	ldr x1, [x0, #1912]
	str x1, [x0, #2056]
	ldr x1, [x0, #1920]
	str x1, [x0, #2064]
	ldr x1, [x0, #1928]
	str x1, [x0, #2072]
	ldr x1, [x0, #2128]
	str x1, [x0, #2080]
	ldr x1, [x0, #2136]
	str x1, [x0, #2088]
	ldr x1, [x0, #2144]
	str x1, [x0, #2096]
	ldr x1, [x0, #2152]
	str x1, [x0, #2104]
	ldr x1, [x0, #2160]
	str x1, [x0, #2112]
	ldr x1, [x0, #2168]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
227:
	b 225f
224:
	ldr x1, [x0, #5712]
	str x1, [x0, #736]
	ldr x1, [x0, #5720]
	str x1, [x0, #744]
	ldr x1, [x0, #5728]
	str x1, [x0, #752]
	ldr x1, [x0, #5736]
	str x1, [x0, #760]
	ldr x1, [x0, #5744]
	str x1, [x0, #768]
	ldr x1, [x0, #5752]
	str x1, [x0, #776]
	ldr x1, [x0, #5760]
	str x1, [x0, #784]
	ldr x1, [x0, #5768]
	str x1, [x0, #792]
	ldr x1, [x0, #5776]
	str x1, [x0, #800]
	ldr x1, [x0, #5784]
	str x1, [x0, #808]
	ldr x1, [x0, #5792]
	str x1, [x0, #816]
	ldr x1, [x0, #5800]
	str x1, [x0, #824]
	ldr x1, [x0, #5808]
	str x1, [x0, #832]
	ldr x1, [x0, #5816]
	str x1, [x0, #840]
	ldr x1, [x0, #5824]
	str x1, [x0, #848]
	ldr x1, [x0, #5832]
	str x1, [x0, #856]
	ldr x1, [x0, #5840]
	str x1, [x0, #864]
	ldr x1, [x0, #5848]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
225:
	b 223f
222:
	ldr x1, [x0, #5856]
	str x1, [x0, #736]
	ldr x1, [x0, #5864]
	str x1, [x0, #744]
	ldr x1, [x0, #5872]
	str x1, [x0, #752]
	ldr x1, [x0, #5880]
	str x1, [x0, #760]
	ldr x1, [x0, #5888]
	str x1, [x0, #768]
	ldr x1, [x0, #5896]
	str x1, [x0, #776]
	ldr x1, [x0, #5904]
	str x1, [x0, #784]
	ldr x1, [x0, #5912]
	str x1, [x0, #792]
	ldr x1, [x0, #5920]
	str x1, [x0, #800]
	ldr x1, [x0, #5928]
	str x1, [x0, #808]
	ldr x1, [x0, #5936]
	str x1, [x0, #816]
	ldr x1, [x0, #5944]
	str x1, [x0, #824]
	ldr x1, [x0, #5952]
	str x1, [x0, #832]
	ldr x1, [x0, #5960]
	str x1, [x0, #840]
	ldr x1, [x0, #5968]
	str x1, [x0, #848]
	ldr x1, [x0, #5976]
	str x1, [x0, #856]
	ldr x1, [x0, #5984]
	str x1, [x0, #864]
	ldr x1, [x0, #5992]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
223:
	b 221f
220:
	ldr x1, [x0, #6000]
	str x1, [x0, #736]
	ldr x1, [x0, #6008]
	str x1, [x0, #744]
	ldr x1, [x0, #6016]
	str x1, [x0, #752]
	ldr x1, [x0, #6024]
	str x1, [x0, #760]
	ldr x1, [x0, #6032]
	str x1, [x0, #768]
	ldr x1, [x0, #6040]
	str x1, [x0, #776]
	ldr x1, [x0, #6048]
	str x1, [x0, #784]
	ldr x1, [x0, #6056]
	str x1, [x0, #792]
	ldr x1, [x0, #6064]
	str x1, [x0, #800]
	ldr x1, [x0, #6072]
	str x1, [x0, #808]
	ldr x1, [x0, #6080]
	str x1, [x0, #816]
	ldr x1, [x0, #6088]
	str x1, [x0, #824]
	ldr x1, [x0, #6096]
	str x1, [x0, #832]
	ldr x1, [x0, #6104]
	str x1, [x0, #840]
	ldr x1, [x0, #6112]
	str x1, [x0, #848]
	ldr x1, [x0, #6120]
	str x1, [x0, #856]
	ldr x1, [x0, #6128]
	str x1, [x0, #864]
	ldr x1, [x0, #6136]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
221:
	b 219f
218:
	ldr x1, [x0, #5712]
	str x1, [x0, #736]
	ldr x1, [x0, #5720]
	str x1, [x0, #744]
	ldr x1, [x0, #5728]
	str x1, [x0, #752]
	ldr x1, [x0, #5736]
	str x1, [x0, #760]
	ldr x1, [x0, #5744]
	str x1, [x0, #768]
	ldr x1, [x0, #5752]
	str x1, [x0, #776]
	ldr x1, [x0, #5760]
	str x1, [x0, #784]
	ldr x1, [x0, #5768]
	str x1, [x0, #792]
	ldr x1, [x0, #5776]
	str x1, [x0, #800]
	ldr x1, [x0, #5784]
	str x1, [x0, #808]
	ldr x1, [x0, #5792]
	str x1, [x0, #816]
	ldr x1, [x0, #5800]
	str x1, [x0, #824]
	ldr x1, [x0, #5808]
	str x1, [x0, #832]
	ldr x1, [x0, #5816]
	str x1, [x0, #840]
	ldr x1, [x0, #5824]
	str x1, [x0, #848]
	ldr x1, [x0, #5832]
	str x1, [x0, #856]
	ldr x1, [x0, #5840]
	str x1, [x0, #864]
	ldr x1, [x0, #5848]
	str x1, [x0, #872]
	ldr x1, [x0, #1888]
	str x1, [x0, #2032]
	ldr x1, [x0, #1896]
	str x1, [x0, #2040]
	ldr x1, [x0, #1904]
	str x1, [x0, #2048]
	ldr x1, [x0, #1912]
	str x1, [x0, #2056]
	ldr x1, [x0, #1920]
	str x1, [x0, #2064]
	ldr x1, [x0, #1928]
	str x1, [x0, #2072]
	ldr x1, [x0, #2128]
	str x1, [x0, #2080]
	ldr x1, [x0, #2136]
	str x1, [x0, #2088]
	ldr x1, [x0, #2144]
	str x1, [x0, #2096]
	ldr x1, [x0, #2152]
	str x1, [x0, #2104]
	ldr x1, [x0, #2160]
	str x1, [x0, #2112]
	ldr x1, [x0, #2168]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
219:
	b 217f
216:
	ldr x1, [x0, #6288]
	str x1, [x0, #736]
	ldr x1, [x0, #6296]
	str x1, [x0, #744]
	ldr x1, [x0, #6304]
	str x1, [x0, #752]
	ldr x1, [x0, #6312]
	str x1, [x0, #760]
	ldr x1, [x0, #6320]
	str x1, [x0, #768]
	ldr x1, [x0, #6328]
	str x1, [x0, #776]
	ldr x1, [x0, #6336]
	str x1, [x0, #784]
	ldr x1, [x0, #6344]
	str x1, [x0, #792]
	ldr x1, [x0, #6352]
	str x1, [x0, #800]
	ldr x1, [x0, #6360]
	str x1, [x0, #808]
	ldr x1, [x0, #6368]
	str x1, [x0, #816]
	ldr x1, [x0, #6376]
	str x1, [x0, #824]
	ldr x1, [x0, #6384]
	str x1, [x0, #832]
	ldr x1, [x0, #6392]
	str x1, [x0, #840]
	ldr x1, [x0, #6400]
	str x1, [x0, #848]
	ldr x1, [x0, #6408]
	str x1, [x0, #856]
	ldr x1, [x0, #6416]
	str x1, [x0, #864]
	ldr x1, [x0, #6424]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
217:
	b 215f
214:
	ldr x1, [x0, #6432]
	str x1, [x0, #736]
	ldr x1, [x0, #6440]
	str x1, [x0, #744]
	ldr x1, [x0, #6448]
	str x1, [x0, #752]
	ldr x1, [x0, #6456]
	str x1, [x0, #760]
	ldr x1, [x0, #6464]
	str x1, [x0, #768]
	ldr x1, [x0, #6472]
	str x1, [x0, #776]
	ldr x1, [x0, #6480]
	str x1, [x0, #784]
	ldr x1, [x0, #6488]
	str x1, [x0, #792]
	ldr x1, [x0, #6496]
	str x1, [x0, #800]
	ldr x1, [x0, #6504]
	str x1, [x0, #808]
	ldr x1, [x0, #6512]
	str x1, [x0, #816]
	ldr x1, [x0, #6520]
	str x1, [x0, #824]
	ldr x1, [x0, #6528]
	str x1, [x0, #832]
	ldr x1, [x0, #6536]
	str x1, [x0, #840]
	ldr x1, [x0, #6544]
	str x1, [x0, #848]
	ldr x1, [x0, #6552]
	str x1, [x0, #856]
	ldr x1, [x0, #6560]
	str x1, [x0, #864]
	ldr x1, [x0, #6568]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
215:
	b 213f
212:
	ldr x1, [x0, #6576]
	str x1, [x0, #736]
	ldr x1, [x0, #6584]
	str x1, [x0, #744]
	ldr x1, [x0, #6592]
	str x1, [x0, #752]
	ldr x1, [x0, #6600]
	str x1, [x0, #760]
	ldr x1, [x0, #6608]
	str x1, [x0, #768]
	ldr x1, [x0, #6616]
	str x1, [x0, #776]
	ldr x1, [x0, #6624]
	str x1, [x0, #784]
	ldr x1, [x0, #6632]
	str x1, [x0, #792]
	ldr x1, [x0, #6640]
	str x1, [x0, #800]
	ldr x1, [x0, #6648]
	str x1, [x0, #808]
	ldr x1, [x0, #6656]
	str x1, [x0, #816]
	ldr x1, [x0, #6664]
	str x1, [x0, #824]
	ldr x1, [x0, #6672]
	str x1, [x0, #832]
	ldr x1, [x0, #6680]
	str x1, [x0, #840]
	ldr x1, [x0, #6688]
	str x1, [x0, #848]
	ldr x1, [x0, #6696]
	str x1, [x0, #856]
	ldr x1, [x0, #6704]
	str x1, [x0, #864]
	ldr x1, [x0, #6712]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
213:
	b 211f
210:
	ldr x1, [x0, #6288]
	str x1, [x0, #736]
	ldr x1, [x0, #6296]
	str x1, [x0, #744]
	ldr x1, [x0, #6304]
	str x1, [x0, #752]
	ldr x1, [x0, #6312]
	str x1, [x0, #760]
	ldr x1, [x0, #6320]
	str x1, [x0, #768]
	ldr x1, [x0, #6328]
	str x1, [x0, #776]
	ldr x1, [x0, #6336]
	str x1, [x0, #784]
	ldr x1, [x0, #6344]
	str x1, [x0, #792]
	ldr x1, [x0, #6352]
	str x1, [x0, #800]
	ldr x1, [x0, #6360]
	str x1, [x0, #808]
	ldr x1, [x0, #6368]
	str x1, [x0, #816]
	ldr x1, [x0, #6376]
	str x1, [x0, #824]
	ldr x1, [x0, #6384]
	str x1, [x0, #832]
	ldr x1, [x0, #6392]
	str x1, [x0, #840]
	ldr x1, [x0, #6400]
	str x1, [x0, #848]
	ldr x1, [x0, #6408]
	str x1, [x0, #856]
	ldr x1, [x0, #6416]
	str x1, [x0, #864]
	ldr x1, [x0, #6424]
	str x1, [x0, #872]
	ldr x1, [x0, #1888]
	str x1, [x0, #2032]
	ldr x1, [x0, #1896]
	str x1, [x0, #2040]
	ldr x1, [x0, #1904]
	str x1, [x0, #2048]
	ldr x1, [x0, #1912]
	str x1, [x0, #2056]
	ldr x1, [x0, #1920]
	str x1, [x0, #2064]
	ldr x1, [x0, #1928]
	str x1, [x0, #2072]
	ldr x1, [x0, #2128]
	str x1, [x0, #2080]
	ldr x1, [x0, #2136]
	str x1, [x0, #2088]
	ldr x1, [x0, #2144]
	str x1, [x0, #2096]
	ldr x1, [x0, #2152]
	str x1, [x0, #2104]
	ldr x1, [x0, #2160]
	str x1, [x0, #2112]
	ldr x1, [x0, #2168]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
211:
	b 29f
28:
	ldr x1, [x0, #6864]
	str x1, [x0, #736]
	ldr x1, [x0, #6872]
	str x1, [x0, #744]
	ldr x1, [x0, #6880]
	str x1, [x0, #752]
	ldr x1, [x0, #6888]
	str x1, [x0, #760]
	ldr x1, [x0, #6896]
	str x1, [x0, #768]
	ldr x1, [x0, #6904]
	str x1, [x0, #776]
	ldr x1, [x0, #6912]
	str x1, [x0, #784]
	ldr x1, [x0, #6920]
	str x1, [x0, #792]
	ldr x1, [x0, #6928]
	str x1, [x0, #800]
	ldr x1, [x0, #6936]
	str x1, [x0, #808]
	ldr x1, [x0, #6944]
	str x1, [x0, #816]
	ldr x1, [x0, #6952]
	str x1, [x0, #824]
	ldr x1, [x0, #6960]
	str x1, [x0, #832]
	ldr x1, [x0, #6968]
	str x1, [x0, #840]
	ldr x1, [x0, #6976]
	str x1, [x0, #848]
	ldr x1, [x0, #6984]
	str x1, [x0, #856]
	ldr x1, [x0, #6992]
	str x1, [x0, #864]
	ldr x1, [x0, #7000]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
29:
	b 27f
26:
	ldr x1, [x0, #7008]
	str x1, [x0, #736]
	ldr x1, [x0, #7016]
	str x1, [x0, #744]
	ldr x1, [x0, #7024]
	str x1, [x0, #752]
	ldr x1, [x0, #7032]
	str x1, [x0, #760]
	ldr x1, [x0, #7040]
	str x1, [x0, #768]
	ldr x1, [x0, #7048]
	str x1, [x0, #776]
	ldr x1, [x0, #7056]
	str x1, [x0, #784]
	ldr x1, [x0, #7064]
	str x1, [x0, #792]
	ldr x1, [x0, #7072]
	str x1, [x0, #800]
	ldr x1, [x0, #7080]
	str x1, [x0, #808]
	ldr x1, [x0, #7088]
	str x1, [x0, #816]
	ldr x1, [x0, #7096]
	str x1, [x0, #824]
	ldr x1, [x0, #7104]
	str x1, [x0, #832]
	ldr x1, [x0, #7112]
	str x1, [x0, #840]
	ldr x1, [x0, #7120]
	str x1, [x0, #848]
	ldr x1, [x0, #7128]
	str x1, [x0, #856]
	ldr x1, [x0, #7136]
	str x1, [x0, #864]
	ldr x1, [x0, #7144]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
27:
	b 25f
24:
	ldr x1, [x0, #7152]
	str x1, [x0, #736]
	ldr x1, [x0, #7160]
	str x1, [x0, #744]
	ldr x1, [x0, #7168]
	str x1, [x0, #752]
	ldr x1, [x0, #7176]
	str x1, [x0, #760]
	ldr x1, [x0, #7184]
	str x1, [x0, #768]
	ldr x1, [x0, #7192]
	str x1, [x0, #776]
	ldr x1, [x0, #7200]
	str x1, [x0, #784]
	ldr x1, [x0, #7208]
	str x1, [x0, #792]
	ldr x1, [x0, #7216]
	str x1, [x0, #800]
	ldr x1, [x0, #7224]
	str x1, [x0, #808]
	ldr x1, [x0, #7232]
	str x1, [x0, #816]
	ldr x1, [x0, #7240]
	str x1, [x0, #824]
	ldr x1, [x0, #7248]
	str x1, [x0, #832]
	ldr x1, [x0, #7256]
	str x1, [x0, #840]
	ldr x1, [x0, #7264]
	str x1, [x0, #848]
	ldr x1, [x0, #7272]
	str x1, [x0, #856]
	ldr x1, [x0, #7280]
	str x1, [x0, #864]
	ldr x1, [x0, #7288]
	str x1, [x0, #872]
	ldr x1, [x0, #448]
	str x1, [x0, #2032]
	ldr x1, [x0, #456]
	str x1, [x0, #2040]
	ldr x1, [x0, #464]
	str x1, [x0, #2048]
	ldr x1, [x0, #472]
	str x1, [x0, #2056]
	ldr x1, [x0, #480]
	str x1, [x0, #2064]
	ldr x1, [x0, #488]
	str x1, [x0, #2072]
	ldr x1, [x0, #496]
	str x1, [x0, #2080]
	ldr x1, [x0, #504]
	str x1, [x0, #2088]
	ldr x1, [x0, #512]
	str x1, [x0, #2096]
	ldr x1, [x0, #520]
	str x1, [x0, #2104]
	ldr x1, [x0, #528]
	str x1, [x0, #2112]
	ldr x1, [x0, #536]
	str x1, [x0, #2120]
	ldr x1, [x0, #304]
	str x1, [x0, #1840]
	ldr x1, [x0, #312]
	str x1, [x0, #1848]
	ldr x1, [x0, #320]
	str x1, [x0, #1856]
	ldr x1, [x0, #328]
	str x1, [x0, #1864]
	ldr x1, [x0, #336]
	str x1, [x0, #1872]
	ldr x1, [x0, #344]
	str x1, [x0, #1880]
25:
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #2032, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #1840, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2032]
	ldr x9, [x0, #2040]
	ldr x10, [x0, #2048]
	ldr x11, [x0, #2056]
	ldr x12, [x0, #2064]
	ldr x13, [x0, #2072]
	ldr x2, [x0, #2080]
	adds x8, x8, x2
	ldr x2, [x0, #2088]
	adcs x9, x9, x2
	ldr x2, [x0, #2096]
	adcs x10, x10, x2
	ldr x2, [x0, #2104]
	adcs x11, x11, x2
	ldr x2, [x0, #2112]
	adcs x12, x12, x2
	ldr x2, [x0, #2120]
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
	ldr x8, [x0, #2032]
	ldr x9, [x0, #2040]
	ldr x10, [x0, #2048]
	ldr x11, [x0, #2056]
	ldr x12, [x0, #2064]
	ldr x13, [x0, #2072]
	ldr x2, [x0, #1840]
	adds x8, x8, x2
	ldr x2, [x0, #1848]
	adcs x9, x9, x2
	ldr x2, [x0, #1856]
	adcs x10, x10, x2
	ldr x2, [x0, #1864]
	adcs x11, x11, x2
	ldr x2, [x0, #1872]
	adcs x12, x12, x2
	ldr x2, [x0, #1880]
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
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x2, [x0, #1840]
	adds x8, x8, x2
	ldr x2, [x0, #1848]
	adcs x9, x9, x2
	ldr x2, [x0, #1856]
	adcs x10, x10, x2
	ldr x2, [x0, #1864]
	adcs x11, x11, x2
	ldr x2, [x0, #1872]
	adcs x12, x12, x2
	ldr x2, [x0, #1880]
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
	movz x2, #640, lsl #0
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
	movz x2, #640, lsl #0
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
	sub x2, x19, #15
	cbz x2, 234f
	sub x2, x19, #14
	cbz x2, 236f
	sub x2, x19, #13
	cbz x2, 238f
	sub x2, x19, #12
	cbz x2, 240f
	sub x2, x19, #11
	cbz x2, 242f
	sub x2, x19, #10
	cbz x2, 244f
	sub x2, x19, #9
	cbz x2, 246f
	sub x2, x19, #8
	cbz x2, 248f
	sub x2, x19, #7
	cbz x2, 250f
	sub x2, x19, #6
	cbz x2, 252f
	sub x2, x19, #5
	cbz x2, 254f
	sub x2, x19, #4
	cbz x2, 256f
	sub x2, x19, #3
	cbz x2, 258f
	sub x2, x19, #2
	cbz x2, 260f
	sub x2, x19, #1
	cbz x2, 262f
	b 263f
262:
	ldr x1, [x0, #736]
	str x1, [x0, #5280]
	ldr x1, [x0, #744]
	str x1, [x0, #5288]
	ldr x1, [x0, #752]
	str x1, [x0, #5296]
	ldr x1, [x0, #760]
	str x1, [x0, #5304]
	ldr x1, [x0, #768]
	str x1, [x0, #5312]
	ldr x1, [x0, #776]
	str x1, [x0, #5320]
	ldr x1, [x0, #784]
	str x1, [x0, #5328]
	ldr x1, [x0, #792]
	str x1, [x0, #5336]
	ldr x1, [x0, #800]
	str x1, [x0, #5344]
	ldr x1, [x0, #808]
	str x1, [x0, #5352]
	ldr x1, [x0, #816]
	str x1, [x0, #5360]
	ldr x1, [x0, #824]
	str x1, [x0, #5368]
	ldr x1, [x0, #832]
	str x1, [x0, #5376]
	ldr x1, [x0, #840]
	str x1, [x0, #5384]
	ldr x1, [x0, #848]
	str x1, [x0, #5392]
	ldr x1, [x0, #856]
	str x1, [x0, #5400]
	ldr x1, [x0, #864]
	str x1, [x0, #5408]
	ldr x1, [x0, #872]
	str x1, [x0, #5416]
263:
	b 261f
260:
	ldr x1, [x0, #736]
	str x1, [x0, #5424]
	ldr x1, [x0, #744]
	str x1, [x0, #5432]
	ldr x1, [x0, #752]
	str x1, [x0, #5440]
	ldr x1, [x0, #760]
	str x1, [x0, #5448]
	ldr x1, [x0, #768]
	str x1, [x0, #5456]
	ldr x1, [x0, #776]
	str x1, [x0, #5464]
	ldr x1, [x0, #784]
	str x1, [x0, #5472]
	ldr x1, [x0, #792]
	str x1, [x0, #5480]
	ldr x1, [x0, #800]
	str x1, [x0, #5488]
	ldr x1, [x0, #808]
	str x1, [x0, #5496]
	ldr x1, [x0, #816]
	str x1, [x0, #5504]
	ldr x1, [x0, #824]
	str x1, [x0, #5512]
	ldr x1, [x0, #832]
	str x1, [x0, #5520]
	ldr x1, [x0, #840]
	str x1, [x0, #5528]
	ldr x1, [x0, #848]
	str x1, [x0, #5536]
	ldr x1, [x0, #856]
	str x1, [x0, #5544]
	ldr x1, [x0, #864]
	str x1, [x0, #5552]
	ldr x1, [x0, #872]
	str x1, [x0, #5560]
261:
	b 259f
258:
	ldr x1, [x0, #736]
	str x1, [x0, #5568]
	ldr x1, [x0, #744]
	str x1, [x0, #5576]
	ldr x1, [x0, #752]
	str x1, [x0, #5584]
	ldr x1, [x0, #760]
	str x1, [x0, #5592]
	ldr x1, [x0, #768]
	str x1, [x0, #5600]
	ldr x1, [x0, #776]
	str x1, [x0, #5608]
	ldr x1, [x0, #784]
	str x1, [x0, #5616]
	ldr x1, [x0, #792]
	str x1, [x0, #5624]
	ldr x1, [x0, #800]
	str x1, [x0, #5632]
	ldr x1, [x0, #808]
	str x1, [x0, #5640]
	ldr x1, [x0, #816]
	str x1, [x0, #5648]
	ldr x1, [x0, #824]
	str x1, [x0, #5656]
	ldr x1, [x0, #832]
	str x1, [x0, #5664]
	ldr x1, [x0, #840]
	str x1, [x0, #5672]
	ldr x1, [x0, #848]
	str x1, [x0, #5680]
	ldr x1, [x0, #856]
	str x1, [x0, #5688]
	ldr x1, [x0, #864]
	str x1, [x0, #5696]
	ldr x1, [x0, #872]
	str x1, [x0, #5704]
259:
	b 257f
256:
	ldr x1, [x0, #736]
	str x1, [x0, #5712]
	ldr x1, [x0, #744]
	str x1, [x0, #5720]
	ldr x1, [x0, #752]
	str x1, [x0, #5728]
	ldr x1, [x0, #760]
	str x1, [x0, #5736]
	ldr x1, [x0, #768]
	str x1, [x0, #5744]
	ldr x1, [x0, #776]
	str x1, [x0, #5752]
	ldr x1, [x0, #784]
	str x1, [x0, #5760]
	ldr x1, [x0, #792]
	str x1, [x0, #5768]
	ldr x1, [x0, #800]
	str x1, [x0, #5776]
	ldr x1, [x0, #808]
	str x1, [x0, #5784]
	ldr x1, [x0, #816]
	str x1, [x0, #5792]
	ldr x1, [x0, #824]
	str x1, [x0, #5800]
	ldr x1, [x0, #832]
	str x1, [x0, #5808]
	ldr x1, [x0, #840]
	str x1, [x0, #5816]
	ldr x1, [x0, #848]
	str x1, [x0, #5824]
	ldr x1, [x0, #856]
	str x1, [x0, #5832]
	ldr x1, [x0, #864]
	str x1, [x0, #5840]
	ldr x1, [x0, #872]
	str x1, [x0, #5848]
257:
	b 255f
254:
	ldr x1, [x0, #736]
	str x1, [x0, #5856]
	ldr x1, [x0, #744]
	str x1, [x0, #5864]
	ldr x1, [x0, #752]
	str x1, [x0, #5872]
	ldr x1, [x0, #760]
	str x1, [x0, #5880]
	ldr x1, [x0, #768]
	str x1, [x0, #5888]
	ldr x1, [x0, #776]
	str x1, [x0, #5896]
	ldr x1, [x0, #784]
	str x1, [x0, #5904]
	ldr x1, [x0, #792]
	str x1, [x0, #5912]
	ldr x1, [x0, #800]
	str x1, [x0, #5920]
	ldr x1, [x0, #808]
	str x1, [x0, #5928]
	ldr x1, [x0, #816]
	str x1, [x0, #5936]
	ldr x1, [x0, #824]
	str x1, [x0, #5944]
	ldr x1, [x0, #832]
	str x1, [x0, #5952]
	ldr x1, [x0, #840]
	str x1, [x0, #5960]
	ldr x1, [x0, #848]
	str x1, [x0, #5968]
	ldr x1, [x0, #856]
	str x1, [x0, #5976]
	ldr x1, [x0, #864]
	str x1, [x0, #5984]
	ldr x1, [x0, #872]
	str x1, [x0, #5992]
255:
	b 253f
252:
	ldr x1, [x0, #736]
	str x1, [x0, #6000]
	ldr x1, [x0, #744]
	str x1, [x0, #6008]
	ldr x1, [x0, #752]
	str x1, [x0, #6016]
	ldr x1, [x0, #760]
	str x1, [x0, #6024]
	ldr x1, [x0, #768]
	str x1, [x0, #6032]
	ldr x1, [x0, #776]
	str x1, [x0, #6040]
	ldr x1, [x0, #784]
	str x1, [x0, #6048]
	ldr x1, [x0, #792]
	str x1, [x0, #6056]
	ldr x1, [x0, #800]
	str x1, [x0, #6064]
	ldr x1, [x0, #808]
	str x1, [x0, #6072]
	ldr x1, [x0, #816]
	str x1, [x0, #6080]
	ldr x1, [x0, #824]
	str x1, [x0, #6088]
	ldr x1, [x0, #832]
	str x1, [x0, #6096]
	ldr x1, [x0, #840]
	str x1, [x0, #6104]
	ldr x1, [x0, #848]
	str x1, [x0, #6112]
	ldr x1, [x0, #856]
	str x1, [x0, #6120]
	ldr x1, [x0, #864]
	str x1, [x0, #6128]
	ldr x1, [x0, #872]
	str x1, [x0, #6136]
253:
	b 251f
250:
	ldr x1, [x0, #736]
	str x1, [x0, #6144]
	ldr x1, [x0, #744]
	str x1, [x0, #6152]
	ldr x1, [x0, #752]
	str x1, [x0, #6160]
	ldr x1, [x0, #760]
	str x1, [x0, #6168]
	ldr x1, [x0, #768]
	str x1, [x0, #6176]
	ldr x1, [x0, #776]
	str x1, [x0, #6184]
	ldr x1, [x0, #784]
	str x1, [x0, #6192]
	ldr x1, [x0, #792]
	str x1, [x0, #6200]
	ldr x1, [x0, #800]
	str x1, [x0, #6208]
	ldr x1, [x0, #808]
	str x1, [x0, #6216]
	ldr x1, [x0, #816]
	str x1, [x0, #6224]
	ldr x1, [x0, #824]
	str x1, [x0, #6232]
	ldr x1, [x0, #832]
	str x1, [x0, #6240]
	ldr x1, [x0, #840]
	str x1, [x0, #6248]
	ldr x1, [x0, #848]
	str x1, [x0, #6256]
	ldr x1, [x0, #856]
	str x1, [x0, #6264]
	ldr x1, [x0, #864]
	str x1, [x0, #6272]
	ldr x1, [x0, #872]
	str x1, [x0, #6280]
251:
	b 249f
248:
	ldr x1, [x0, #736]
	str x1, [x0, #6288]
	ldr x1, [x0, #744]
	str x1, [x0, #6296]
	ldr x1, [x0, #752]
	str x1, [x0, #6304]
	ldr x1, [x0, #760]
	str x1, [x0, #6312]
	ldr x1, [x0, #768]
	str x1, [x0, #6320]
	ldr x1, [x0, #776]
	str x1, [x0, #6328]
	ldr x1, [x0, #784]
	str x1, [x0, #6336]
	ldr x1, [x0, #792]
	str x1, [x0, #6344]
	ldr x1, [x0, #800]
	str x1, [x0, #6352]
	ldr x1, [x0, #808]
	str x1, [x0, #6360]
	ldr x1, [x0, #816]
	str x1, [x0, #6368]
	ldr x1, [x0, #824]
	str x1, [x0, #6376]
	ldr x1, [x0, #832]
	str x1, [x0, #6384]
	ldr x1, [x0, #840]
	str x1, [x0, #6392]
	ldr x1, [x0, #848]
	str x1, [x0, #6400]
	ldr x1, [x0, #856]
	str x1, [x0, #6408]
	ldr x1, [x0, #864]
	str x1, [x0, #6416]
	ldr x1, [x0, #872]
	str x1, [x0, #6424]
249:
	b 247f
246:
	ldr x1, [x0, #736]
	str x1, [x0, #6432]
	ldr x1, [x0, #744]
	str x1, [x0, #6440]
	ldr x1, [x0, #752]
	str x1, [x0, #6448]
	ldr x1, [x0, #760]
	str x1, [x0, #6456]
	ldr x1, [x0, #768]
	str x1, [x0, #6464]
	ldr x1, [x0, #776]
	str x1, [x0, #6472]
	ldr x1, [x0, #784]
	str x1, [x0, #6480]
	ldr x1, [x0, #792]
	str x1, [x0, #6488]
	ldr x1, [x0, #800]
	str x1, [x0, #6496]
	ldr x1, [x0, #808]
	str x1, [x0, #6504]
	ldr x1, [x0, #816]
	str x1, [x0, #6512]
	ldr x1, [x0, #824]
	str x1, [x0, #6520]
	ldr x1, [x0, #832]
	str x1, [x0, #6528]
	ldr x1, [x0, #840]
	str x1, [x0, #6536]
	ldr x1, [x0, #848]
	str x1, [x0, #6544]
	ldr x1, [x0, #856]
	str x1, [x0, #6552]
	ldr x1, [x0, #864]
	str x1, [x0, #6560]
	ldr x1, [x0, #872]
	str x1, [x0, #6568]
247:
	b 245f
244:
	ldr x1, [x0, #736]
	str x1, [x0, #6576]
	ldr x1, [x0, #744]
	str x1, [x0, #6584]
	ldr x1, [x0, #752]
	str x1, [x0, #6592]
	ldr x1, [x0, #760]
	str x1, [x0, #6600]
	ldr x1, [x0, #768]
	str x1, [x0, #6608]
	ldr x1, [x0, #776]
	str x1, [x0, #6616]
	ldr x1, [x0, #784]
	str x1, [x0, #6624]
	ldr x1, [x0, #792]
	str x1, [x0, #6632]
	ldr x1, [x0, #800]
	str x1, [x0, #6640]
	ldr x1, [x0, #808]
	str x1, [x0, #6648]
	ldr x1, [x0, #816]
	str x1, [x0, #6656]
	ldr x1, [x0, #824]
	str x1, [x0, #6664]
	ldr x1, [x0, #832]
	str x1, [x0, #6672]
	ldr x1, [x0, #840]
	str x1, [x0, #6680]
	ldr x1, [x0, #848]
	str x1, [x0, #6688]
	ldr x1, [x0, #856]
	str x1, [x0, #6696]
	ldr x1, [x0, #864]
	str x1, [x0, #6704]
	ldr x1, [x0, #872]
	str x1, [x0, #6712]
245:
	b 243f
242:
	ldr x1, [x0, #736]
	str x1, [x0, #6720]
	ldr x1, [x0, #744]
	str x1, [x0, #6728]
	ldr x1, [x0, #752]
	str x1, [x0, #6736]
	ldr x1, [x0, #760]
	str x1, [x0, #6744]
	ldr x1, [x0, #768]
	str x1, [x0, #6752]
	ldr x1, [x0, #776]
	str x1, [x0, #6760]
	ldr x1, [x0, #784]
	str x1, [x0, #6768]
	ldr x1, [x0, #792]
	str x1, [x0, #6776]
	ldr x1, [x0, #800]
	str x1, [x0, #6784]
	ldr x1, [x0, #808]
	str x1, [x0, #6792]
	ldr x1, [x0, #816]
	str x1, [x0, #6800]
	ldr x1, [x0, #824]
	str x1, [x0, #6808]
	ldr x1, [x0, #832]
	str x1, [x0, #6816]
	ldr x1, [x0, #840]
	str x1, [x0, #6824]
	ldr x1, [x0, #848]
	str x1, [x0, #6832]
	ldr x1, [x0, #856]
	str x1, [x0, #6840]
	ldr x1, [x0, #864]
	str x1, [x0, #6848]
	ldr x1, [x0, #872]
	str x1, [x0, #6856]
243:
	b 241f
240:
	ldr x1, [x0, #736]
	str x1, [x0, #6864]
	ldr x1, [x0, #744]
	str x1, [x0, #6872]
	ldr x1, [x0, #752]
	str x1, [x0, #6880]
	ldr x1, [x0, #760]
	str x1, [x0, #6888]
	ldr x1, [x0, #768]
	str x1, [x0, #6896]
	ldr x1, [x0, #776]
	str x1, [x0, #6904]
	ldr x1, [x0, #784]
	str x1, [x0, #6912]
	ldr x1, [x0, #792]
	str x1, [x0, #6920]
	ldr x1, [x0, #800]
	str x1, [x0, #6928]
	ldr x1, [x0, #808]
	str x1, [x0, #6936]
	ldr x1, [x0, #816]
	str x1, [x0, #6944]
	ldr x1, [x0, #824]
	str x1, [x0, #6952]
	ldr x1, [x0, #832]
	str x1, [x0, #6960]
	ldr x1, [x0, #840]
	str x1, [x0, #6968]
	ldr x1, [x0, #848]
	str x1, [x0, #6976]
	ldr x1, [x0, #856]
	str x1, [x0, #6984]
	ldr x1, [x0, #864]
	str x1, [x0, #6992]
	ldr x1, [x0, #872]
	str x1, [x0, #7000]
241:
	b 239f
238:
	ldr x1, [x0, #736]
	str x1, [x0, #7008]
	ldr x1, [x0, #744]
	str x1, [x0, #7016]
	ldr x1, [x0, #752]
	str x1, [x0, #7024]
	ldr x1, [x0, #760]
	str x1, [x0, #7032]
	ldr x1, [x0, #768]
	str x1, [x0, #7040]
	ldr x1, [x0, #776]
	str x1, [x0, #7048]
	ldr x1, [x0, #784]
	str x1, [x0, #7056]
	ldr x1, [x0, #792]
	str x1, [x0, #7064]
	ldr x1, [x0, #800]
	str x1, [x0, #7072]
	ldr x1, [x0, #808]
	str x1, [x0, #7080]
	ldr x1, [x0, #816]
	str x1, [x0, #7088]
	ldr x1, [x0, #824]
	str x1, [x0, #7096]
	ldr x1, [x0, #832]
	str x1, [x0, #7104]
	ldr x1, [x0, #840]
	str x1, [x0, #7112]
	ldr x1, [x0, #848]
	str x1, [x0, #7120]
	ldr x1, [x0, #856]
	str x1, [x0, #7128]
	ldr x1, [x0, #864]
	str x1, [x0, #7136]
	ldr x1, [x0, #872]
	str x1, [x0, #7144]
239:
	b 237f
236:
	ldr x1, [x0, #736]
	str x1, [x0, #7152]
	ldr x1, [x0, #744]
	str x1, [x0, #7160]
	ldr x1, [x0, #752]
	str x1, [x0, #7168]
	ldr x1, [x0, #760]
	str x1, [x0, #7176]
	ldr x1, [x0, #768]
	str x1, [x0, #7184]
	ldr x1, [x0, #776]
	str x1, [x0, #7192]
	ldr x1, [x0, #784]
	str x1, [x0, #7200]
	ldr x1, [x0, #792]
	str x1, [x0, #7208]
	ldr x1, [x0, #800]
	str x1, [x0, #7216]
	ldr x1, [x0, #808]
	str x1, [x0, #7224]
	ldr x1, [x0, #816]
	str x1, [x0, #7232]
	ldr x1, [x0, #824]
	str x1, [x0, #7240]
	ldr x1, [x0, #832]
	str x1, [x0, #7248]
	ldr x1, [x0, #840]
	str x1, [x0, #7256]
	ldr x1, [x0, #848]
	str x1, [x0, #7264]
	ldr x1, [x0, #856]
	str x1, [x0, #7272]
	ldr x1, [x0, #864]
	str x1, [x0, #7280]
	ldr x1, [x0, #872]
	str x1, [x0, #7288]
237:
	b 235f
234:
	ldr x1, [x0, #736]
	str x1, [x0, #7296]
	ldr x1, [x0, #744]
	str x1, [x0, #7304]
	ldr x1, [x0, #752]
	str x1, [x0, #7312]
	ldr x1, [x0, #760]
	str x1, [x0, #7320]
	ldr x1, [x0, #768]
	str x1, [x0, #7328]
	ldr x1, [x0, #776]
	str x1, [x0, #7336]
	ldr x1, [x0, #784]
	str x1, [x0, #7344]
	ldr x1, [x0, #792]
	str x1, [x0, #7352]
	ldr x1, [x0, #800]
	str x1, [x0, #7360]
	ldr x1, [x0, #808]
	str x1, [x0, #7368]
	ldr x1, [x0, #816]
	str x1, [x0, #7376]
	ldr x1, [x0, #824]
	str x1, [x0, #7384]
	ldr x1, [x0, #832]
	str x1, [x0, #7392]
	ldr x1, [x0, #840]
	str x1, [x0, #7400]
	ldr x1, [x0, #848]
	str x1, [x0, #7408]
	ldr x1, [x0, #856]
	str x1, [x0, #7416]
	ldr x1, [x0, #864]
	str x1, [x0, #7424]
	ldr x1, [x0, #872]
	str x1, [x0, #7432]
235:
	add x19, x19, #1
	sub x6, x19, #16
	cbnz x6, 23b
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
	movz x19, #192, lsl #0
264:
	sub x19, x19, #1
	ldr x1, [x0, #736]
	str x1, [x0, #2032]
	ldr x1, [x0, #744]
	str x1, [x0, #2040]
	ldr x1, [x0, #752]
	str x1, [x0, #2048]
	ldr x1, [x0, #760]
	str x1, [x0, #2056]
	ldr x1, [x0, #768]
	str x1, [x0, #2064]
	ldr x1, [x0, #776]
	str x1, [x0, #2072]
	ldr x1, [x0, #784]
	str x1, [x0, #2080]
	ldr x1, [x0, #792]
	str x1, [x0, #2088]
	ldr x1, [x0, #800]
	str x1, [x0, #2096]
	ldr x1, [x0, #808]
	str x1, [x0, #2104]
	ldr x1, [x0, #816]
	str x1, [x0, #2112]
	ldr x1, [x0, #824]
	str x1, [x0, #2120]
	ldr x1, [x0, #832]
	str x1, [x0, #1840]
	ldr x1, [x0, #840]
	str x1, [x0, #1848]
	ldr x1, [x0, #848]
	str x1, [x0, #1856]
	ldr x1, [x0, #856]
	str x1, [x0, #1864]
	ldr x1, [x0, #864]
	str x1, [x0, #1872]
	ldr x1, [x0, #872]
	str x1, [x0, #1880]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #2032, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #1840, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2032]
	ldr x9, [x0, #2040]
	ldr x10, [x0, #2048]
	ldr x11, [x0, #2056]
	ldr x12, [x0, #2064]
	ldr x13, [x0, #2072]
	ldr x2, [x0, #2080]
	adds x8, x8, x2
	ldr x2, [x0, #2088]
	adcs x9, x9, x2
	ldr x2, [x0, #2096]
	adcs x10, x10, x2
	ldr x2, [x0, #2104]
	adcs x11, x11, x2
	ldr x2, [x0, #2112]
	adcs x12, x12, x2
	ldr x2, [x0, #2120]
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
	ldr x8, [x0, #2032]
	ldr x9, [x0, #2040]
	ldr x10, [x0, #2048]
	ldr x11, [x0, #2056]
	ldr x12, [x0, #2064]
	ldr x13, [x0, #2072]
	ldr x2, [x0, #1840]
	adds x8, x8, x2
	ldr x2, [x0, #1848]
	adcs x9, x9, x2
	ldr x2, [x0, #1856]
	adcs x10, x10, x2
	ldr x2, [x0, #1864]
	adcs x11, x11, x2
	ldr x2, [x0, #1872]
	adcs x12, x12, x2
	ldr x2, [x0, #1880]
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
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x2, [x0, #1840]
	adds x8, x8, x2
	ldr x2, [x0, #1848]
	adcs x9, x9, x2
	ldr x2, [x0, #1856]
	adcs x10, x10, x2
	ldr x2, [x0, #1864]
	adcs x11, x11, x2
	ldr x2, [x0, #1872]
	adcs x12, x12, x2
	ldr x2, [x0, #1880]
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
	movz x2, #640, lsl #0
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
	movz x2, #640, lsl #0
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
	ldr x1, [x0, #736]
	str x1, [x0, #2032]
	ldr x1, [x0, #744]
	str x1, [x0, #2040]
	ldr x1, [x0, #752]
	str x1, [x0, #2048]
	ldr x1, [x0, #760]
	str x1, [x0, #2056]
	ldr x1, [x0, #768]
	str x1, [x0, #2064]
	ldr x1, [x0, #776]
	str x1, [x0, #2072]
	ldr x1, [x0, #784]
	str x1, [x0, #2080]
	ldr x1, [x0, #792]
	str x1, [x0, #2088]
	ldr x1, [x0, #800]
	str x1, [x0, #2096]
	ldr x1, [x0, #808]
	str x1, [x0, #2104]
	ldr x1, [x0, #816]
	str x1, [x0, #2112]
	ldr x1, [x0, #824]
	str x1, [x0, #2120]
	ldr x1, [x0, #832]
	str x1, [x0, #1840]
	ldr x1, [x0, #840]
	str x1, [x0, #1848]
	ldr x1, [x0, #848]
	str x1, [x0, #1856]
	ldr x1, [x0, #856]
	str x1, [x0, #1864]
	ldr x1, [x0, #864]
	str x1, [x0, #1872]
	ldr x1, [x0, #872]
	str x1, [x0, #1880]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #2032, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #1840, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2032]
	ldr x9, [x0, #2040]
	ldr x10, [x0, #2048]
	ldr x11, [x0, #2056]
	ldr x12, [x0, #2064]
	ldr x13, [x0, #2072]
	ldr x2, [x0, #2080]
	adds x8, x8, x2
	ldr x2, [x0, #2088]
	adcs x9, x9, x2
	ldr x2, [x0, #2096]
	adcs x10, x10, x2
	ldr x2, [x0, #2104]
	adcs x11, x11, x2
	ldr x2, [x0, #2112]
	adcs x12, x12, x2
	ldr x2, [x0, #2120]
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
	ldr x8, [x0, #2032]
	ldr x9, [x0, #2040]
	ldr x10, [x0, #2048]
	ldr x11, [x0, #2056]
	ldr x12, [x0, #2064]
	ldr x13, [x0, #2072]
	ldr x2, [x0, #1840]
	adds x8, x8, x2
	ldr x2, [x0, #1848]
	adcs x9, x9, x2
	ldr x2, [x0, #1856]
	adcs x10, x10, x2
	ldr x2, [x0, #1864]
	adcs x11, x11, x2
	ldr x2, [x0, #1872]
	adcs x12, x12, x2
	ldr x2, [x0, #1880]
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
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x2, [x0, #1840]
	adds x8, x8, x2
	ldr x2, [x0, #1848]
	adcs x9, x9, x2
	ldr x2, [x0, #1856]
	adcs x10, x10, x2
	ldr x2, [x0, #1864]
	adcs x11, x11, x2
	ldr x2, [x0, #1872]
	adcs x12, x12, x2
	ldr x2, [x0, #1880]
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
	movz x2, #640, lsl #0
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
	movz x2, #640, lsl #0
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
	ldrb w4, [x16, #3329]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #3328]
	add x2, x2, x4
	lsl x2, x2, #2
	add x2, x2, x6
	cbz x2, 265f
	sub x2, x2, #1
	movz x17, #144, lsl #0
	mul x2, x2, x17
	movz x16, #5280, lsl #0
	add x16, x0, x16
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #2032]
	ldr x4, [x16, #8]
	str x4, [x0, #2040]
	ldr x4, [x16, #16]
	str x4, [x0, #2048]
	ldr x4, [x16, #24]
	str x4, [x0, #2056]
	ldr x4, [x16, #32]
	str x4, [x0, #2064]
	ldr x4, [x16, #40]
	str x4, [x0, #2072]
	ldr x4, [x16, #48]
	str x4, [x0, #2080]
	ldr x4, [x16, #56]
	str x4, [x0, #2088]
	ldr x4, [x16, #64]
	str x4, [x0, #2096]
	ldr x4, [x16, #72]
	str x4, [x0, #2104]
	ldr x4, [x16, #80]
	str x4, [x0, #2112]
	ldr x4, [x16, #88]
	str x4, [x0, #2120]
	ldr x4, [x16, #96]
	str x4, [x0, #1840]
	ldr x4, [x16, #104]
	str x4, [x0, #1848]
	ldr x4, [x16, #112]
	str x4, [x0, #1856]
	ldr x4, [x16, #120]
	str x4, [x0, #1864]
	ldr x4, [x16, #128]
	str x4, [x0, #1872]
	ldr x4, [x16, #136]
	str x4, [x0, #1880]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #2032, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #1840, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2032]
	ldr x9, [x0, #2040]
	ldr x10, [x0, #2048]
	ldr x11, [x0, #2056]
	ldr x12, [x0, #2064]
	ldr x13, [x0, #2072]
	ldr x2, [x0, #2080]
	adds x8, x8, x2
	ldr x2, [x0, #2088]
	adcs x9, x9, x2
	ldr x2, [x0, #2096]
	adcs x10, x10, x2
	ldr x2, [x0, #2104]
	adcs x11, x11, x2
	ldr x2, [x0, #2112]
	adcs x12, x12, x2
	ldr x2, [x0, #2120]
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
	ldr x8, [x0, #2032]
	ldr x9, [x0, #2040]
	ldr x10, [x0, #2048]
	ldr x11, [x0, #2056]
	ldr x12, [x0, #2064]
	ldr x13, [x0, #2072]
	ldr x2, [x0, #1840]
	adds x8, x8, x2
	ldr x2, [x0, #1848]
	adcs x9, x9, x2
	ldr x2, [x0, #1856]
	adcs x10, x10, x2
	ldr x2, [x0, #1864]
	adcs x11, x11, x2
	ldr x2, [x0, #1872]
	adcs x12, x12, x2
	ldr x2, [x0, #1880]
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
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x2, [x0, #1840]
	adds x8, x8, x2
	ldr x2, [x0, #1848]
	adcs x9, x9, x2
	ldr x2, [x0, #1856]
	adcs x10, x10, x2
	ldr x2, [x0, #1864]
	adcs x11, x11, x2
	ldr x2, [x0, #1872]
	adcs x12, x12, x2
	ldr x2, [x0, #1880]
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
	movz x2, #640, lsl #0
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
	movz x2, #640, lsl #0
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
	b 266f
265:
266:
	cbnz x19, 264b
	movz x1, #19422, lsl #0
	movk x1, #16566, lsl #16
	movk x1, #61439, lsl #32
	movk x1, #2172, lsl #48
	str x1, [x0, #1696]
	movz x1, #55653, lsl #0
	movk x1, #15743, lsl #16
	movk x1, #33588, lsl #32
	movk x1, #21330, lsl #48
	str x1, [x0, #1704]
	movz x1, #2201, lsl #0
	movk x1, #51604, lsl #16
	movk x1, #63900, lsl #32
	movk x1, #36392, lsl #48
	str x1, [x0, #1712]
	movz x1, #54703, lsl #0
	movk x1, #39192, lsl #16
	movk x1, #401, lsl #32
	movk x1, #25108, lsl #48
	str x1, [x0, #1720]
	movz x1, #1324, lsl #0
	movk x1, #42366, lsl #16
	movk x1, #61243, lsl #32
	movk x1, #54726, lsl #48
	str x1, [x0, #1728]
	movz x1, #63554, lsl #0
	movk x1, #6029, lsl #16
	movk x1, #26755, lsl #32
	movk x1, #14015, lsl #48
	str x1, [x0, #1736]
	movz x1, #24013, lsl #0
	movk x1, #63625, lsl #16
	movk x1, #15212, lsl #32
	movk x1, #39656, lsl #48
	str x1, [x0, #1456]
	movz x1, #37974, lsl #0
	movk x1, #35847, lsl #16
	movk x1, #19952, lsl #32
	movk x1, #29206, lsl #48
	str x1, [x0, #1464]
	movz x1, #8219, lsl #0
	movk x1, #5655, lsl #16
	movk x1, #11819, lsl #32
	movk x1, #24686, lsl #48
	str x1, [x0, #1472]
	movz x1, #48726, lsl #0
	movk x1, #25130, lsl #16
	movk x1, #8872, lsl #32
	movk x1, #11829, lsl #48
	str x1, [x0, #1480]
	movz x1, #15464, lsl #0
	movk x1, #26762, lsl #16
	movk x1, #48735, lsl #32
	movk x1, #65080, lsl #48
	str x1, [x0, #1488]
	movz x1, #63912, lsl #0
	movk x1, #47670, lsl #16
	movk x1, #43579, lsl #32
	movk x1, #20304, lsl #48
	str x1, [x0, #1496]
	movz x1, #34542, lsl #0
	movk x1, #18435, lsl #16
	movk x1, #52752, lsl #32
	movk x1, #19390, lsl #48
	str x1, [x0, #112]
	movz x1, #22369, lsl #0
	movk x1, #9373, lsl #16
	movk x1, #61562, lsl #32
	movk x1, #56728, lsl #48
	str x1, [x0, #120]
	movz x1, #60283, lsl #0
	movk x1, #54194, lsl #16
	movk x1, #27564, lsl #32
	movk x1, #62363, lsl #48
	str x1, [x0, #128]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #136]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #144]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #152]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1696]
	ldr x5, [x0, #1704]
	ldr x16, [x0, #1712]
	ldr x17, [x0, #1720]
	movz x6, #51237, lsl #0
	movk x6, #60062, lsl #16
	movk x6, #43372, lsl #32
	movk x6, #39534, lsl #48
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	ldr x1, [x0, #1552]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x0, #1728]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #1736]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #1736]
	umulh x2, x1, x3
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #1728]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x1, x8, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	adcs x15, x15, x7
	ldr x1, [x0, #1560]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #1728]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #1736]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #1736]
	umulh x2, x1, x3
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #1728]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x15, x15, x7
	mul x1, x9, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x8, x8, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x15, x15, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1568]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #1728]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #1736]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #1736]
	umulh x2, x1, x3
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #1728]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x15, x15, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1576]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #1728]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #1736]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #1736]
	umulh x2, x1, x3
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #1728]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x1, [x0, #1584]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x0, #1728]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #1736]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #1736]
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #1728]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	mul x1, x12, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x1, [x0, #1592]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #1728]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #1736]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #1736]
	umulh x2, x1, x3
	adcs x11, x11, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	ldr x3, [x0, #1728]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	mul x1, x13, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x14, x14, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	ldr x2, [x0, #64]
	subs x1, x14, x2
	ldr x2, [x0, #72]
	sbcs x3, x15, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	ldr x2, [x0, #96]
	sbcs x6, x10, x2
	ldr x2, [x0, #104]
	sbcs x16, x11, x2
	sbcs x2, x12, x7
	csel x14, x1, x14, hs
	csel x15, x3, x15, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	csel x11, x16, x11, hs
	str x14, [x0, #1696]
	str x15, [x0, #1704]
	str x8, [x0, #1712]
	str x9, [x0, #1720]
	str x10, [x0, #1728]
	str x11, [x0, #1736]
	mov v29.d[0], x30
	movz x1, #1744, lsl #0
	movz x2, #1696, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #1744]
	subs x8, x8, x2
	ldr x2, [x0, #1752]
	sbcs x9, x9, x2
	ldr x2, [x0, #1760]
	sbcs x10, x10, x2
	ldr x2, [x0, #1768]
	sbcs x11, x11, x2
	ldr x2, [x0, #1776]
	sbcs x12, x12, x2
	ldr x2, [x0, #1784]
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
	str x8, [x0, #1984]
	str x9, [x0, #1992]
	str x10, [x0, #2000]
	str x11, [x0, #2008]
	str x12, [x0, #2016]
	str x13, [x0, #2024]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1696]
	ldr x9, [x0, #1704]
	ldr x10, [x0, #1712]
	ldr x11, [x0, #1720]
	ldr x12, [x0, #1728]
	ldr x13, [x0, #1736]
	ldr x2, [x0, #1456]
	adds x8, x8, x2
	ldr x2, [x0, #1464]
	adcs x9, x9, x2
	ldr x2, [x0, #1472]
	adcs x10, x10, x2
	ldr x2, [x0, #1480]
	adcs x11, x11, x2
	ldr x2, [x0, #1488]
	adcs x12, x12, x2
	ldr x2, [x0, #1496]
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
	str x8, [x0, #1696]
	str x9, [x0, #1704]
	str x10, [x0, #1712]
	str x11, [x0, #1720]
	str x12, [x0, #1728]
	str x13, [x0, #1736]
	mov v29.d[0], x30
	movz x1, #1744, lsl #0
	movz x2, #1696, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #1744]
	subs x8, x8, x2
	ldr x2, [x0, #1752]
	sbcs x9, x9, x2
	ldr x2, [x0, #1760]
	sbcs x10, x10, x2
	ldr x2, [x0, #1768]
	sbcs x11, x11, x2
	ldr x2, [x0, #1776]
	sbcs x12, x12, x2
	ldr x2, [x0, #1784]
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
	str x8, [x0, #1888]
	str x9, [x0, #1896]
	str x10, [x0, #1904]
	str x11, [x0, #1912]
	str x12, [x0, #1920]
	str x13, [x0, #1928]
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
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	add x4, x2, #0
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
	add x6, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1888]
	ldr x2, [x0, #1896]
	orr x1, x1, x2
	ldr x2, [x0, #1904]
	orr x1, x1, x2
	ldr x2, [x0, #1912]
	orr x1, x1, x2
	ldr x2, [x0, #1920]
	orr x1, x1, x2
	ldr x2, [x0, #1928]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	and x2, x2, x6
	orr x2, x2, x4
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
