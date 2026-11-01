// The functions of `src/ec_brainpoolp384r1_compressed.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp384r1_compress_public_key:
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
	ldr x3, [x0, #2176]
	ldr x1, [x0, #1792]
	movz x2, #1, lsl #0
	and x1, x1, x2
	add x1, x1, #2
	and x1, x1, x3
	strb w1, [x20, #0]
	ldr x1, [x0, #1648]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #41
	str x1, [x17, #0]
	ldr x1, [x0, #1656]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #33
	str x1, [x17, #0]
	ldr x1, [x0, #1664]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #25
	str x1, [x17, #0]
	ldr x1, [x0, #1672]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #17
	str x1, [x17, #0]
	ldr x1, [x0, #1680]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #9
	str x1, [x17, #0]
	ldr x1, [x0, #1688]
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

vg_ec_brainpoolp384r1_decompress_public_key:
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
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	str x1, [x0, #1600]
	movz x5, #1, lsl #0
	orr x1, x1, x5
	movz x5, #3, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1648]
	ldr x2, [x0, #64]
	subs x16, x1, x2
	ldr x1, [x0, #1656]
	ldr x2, [x0, #72]
	sbcs x16, x1, x2
	ldr x1, [x0, #1664]
	ldr x2, [x0, #80]
	sbcs x16, x1, x2
	ldr x1, [x0, #1672]
	ldr x2, [x0, #88]
	sbcs x16, x1, x2
	ldr x1, [x0, #1680]
	ldr x2, [x0, #96]
	sbcs x16, x1, x2
	ldr x1, [x0, #1688]
	ldr x2, [x0, #104]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	mov v29.d[0], x30
	movz x1, #1696, lsl #0
	movz x2, #1648, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2032, lsl #0
	movz x2, #1696, lsl #0
	movz x3, #1696, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #2032, lsl #0
	movz x3, #1696, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2032, lsl #0
	movz x2, #352, lsl #0
	movz x3, #1696, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2080]
	ldr x9, [x0, #2088]
	ldr x10, [x0, #2096]
	ldr x11, [x0, #2104]
	ldr x12, [x0, #2112]
	ldr x13, [x0, #2120]
	ldr x2, [x0, #2032]
	adds x8, x8, x2
	ldr x2, [x0, #2040]
	adcs x9, x9, x2
	ldr x2, [x0, #2048]
	adcs x10, x10, x2
	ldr x2, [x0, #2056]
	adcs x11, x11, x2
	ldr x2, [x0, #2064]
	adcs x12, x12, x2
	ldr x2, [x0, #2072]
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
	str x8, [x0, #1888]
	str x9, [x0, #1896]
	str x10, [x0, #1904]
	str x11, [x0, #1912]
	str x12, [x0, #1920]
	str x13, [x0, #1928]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1888]
	ldr x9, [x0, #1896]
	ldr x10, [x0, #1904]
	ldr x11, [x0, #1912]
	ldr x12, [x0, #1920]
	ldr x13, [x0, #1928]
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
	str x8, [x0, #2080]
	str x9, [x0, #2088]
	str x10, [x0, #2096]
	str x11, [x0, #2104]
	str x12, [x0, #2112]
	str x13, [x0, #2120]
	ldr x1, [x0, #2080]
	str x1, [x0, #736]
	ldr x1, [x0, #2088]
	str x1, [x0, #744]
	ldr x1, [x0, #2096]
	str x1, [x0, #752]
	ldr x1, [x0, #2104]
	str x1, [x0, #760]
	ldr x1, [x0, #2112]
	str x1, [x0, #768]
	ldr x1, [x0, #2120]
	str x1, [x0, #776]
	mov v29.d[0], x30
	movz x1, #1120, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #2080, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #784, lsl #0
	movz x2, #736, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #832, lsl #0
	movz x2, #784, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #880, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #928, lsl #0
	movz x2, #880, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #976, lsl #0
	movz x2, #928, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1024, lsl #0
	movz x2, #976, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #1024, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #736]
	str x1, [x0, #1456]
	ldr x1, [x0, #744]
	str x1, [x0, #1464]
	ldr x1, [x0, #752]
	str x1, [x0, #1472]
	ldr x1, [x0, #760]
	str x1, [x0, #1480]
	ldr x1, [x0, #768]
	str x1, [x0, #1488]
	ldr x1, [x0, #776]
	str x1, [x0, #1496]
	movz x19, #5, lsl #0
20:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 20b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
21:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 21b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #976, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
22:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 22b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #928, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
23:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 23b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
24:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 24b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #8, lsl #0
25:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 25b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
26:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 26b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
27:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 27b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
28:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 28b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #8, lsl #0
29:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 29b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
210:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 210b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
211:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 211b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #11, lsl #0
212:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 212b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
213:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 213b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #976, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
214:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 214b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
215:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 215b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
216:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 216b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
217:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 217b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
218:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 218b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
219:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 219b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
220:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 220b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
221:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 221b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
222:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 222b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #8, lsl #0
223:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 223b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
224:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 224b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #1, lsl #0
225:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 225b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
226:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 226b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
227:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 227b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #928, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
228:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 228b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
229:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 229b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
230:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 230b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #8, lsl #0
231:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 231b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #928, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
232:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 232b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
233:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 233b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
234:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 234b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
235:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 235b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
236:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 236b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
237:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 237b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
238:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 238b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #9, lsl #0
239:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 239b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #928, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
240:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 240b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #976, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
241:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 241b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
242:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 242b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
243:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 243b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
244:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 244b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #976, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
245:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 245b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
246:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 246b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
247:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 247b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #976, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #1, lsl #0
248:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 248b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
249:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 249b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
250:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 250b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #928, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
251:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 251b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
252:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 252b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #976, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
253:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 253b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
254:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 254b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
255:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 255b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #928, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
256:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 256b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
257:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 257b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
258:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 258b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #3, lsl #0
259:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 259b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #10, lsl #0
260:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 260b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
261:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 261b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
262:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 262b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
263:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 263b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #5, lsl #0
264:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 264b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #784, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #7, lsl #0
265:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 265b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
266:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 266b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
267:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 267b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #880, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #15, lsl #0
268:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 268b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #928, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
269:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 269b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #928, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #1, lsl #0
270:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 270b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
271:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 271b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #9, lsl #0
272:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 272b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1072, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #4, lsl #0
273:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 273b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1024, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #1, lsl #0
274:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 274b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #6, lsl #0
275:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 275b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #832, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x19, #2, lsl #0
276:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 276b
	mov v29.d[0], x30
	movz x1, #1456, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #736, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1792, lsl #0
	movz x2, #1456, lsl #0
	movz x3, #256, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #208]
	ldr x9, [x0, #216]
	ldr x10, [x0, #224]
	ldr x11, [x0, #232]
	ldr x12, [x0, #240]
	ldr x13, [x0, #248]
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
	str x8, [x0, #1840]
	str x9, [x0, #1848]
	str x10, [x0, #1856]
	str x11, [x0, #1864]
	str x12, [x0, #1872]
	str x13, [x0, #1880]
	ldr x1, [x0, #1792]
	ldr x2, [x0, #1600]
	eor x2, x2, x1
	movz x1, #1, lsl #0
	and x2, x2, x1
	movz x7, #0, lsl #0
	sub x3, x7, x2
	ldr x1, [x0, #1792]
	ldr x2, [x0, #1840]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1792]
	ldr x1, [x0, #1800]
	ldr x2, [x0, #1848]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1800]
	ldr x1, [x0, #1808]
	ldr x2, [x0, #1856]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1808]
	ldr x1, [x0, #1816]
	ldr x2, [x0, #1864]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1816]
	ldr x1, [x0, #1824]
	ldr x2, [x0, #1872]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1824]
	ldr x1, [x0, #1832]
	ldr x2, [x0, #1880]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1832]
	mov v29.d[0], x30
	movz x1, #1744, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_brainpoolp384r1_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2032, lsl #0
	movz x2, #1744, lsl #0
	movz x3, #1744, lsl #0
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
	subs x8, x8, x2
	ldr x2, [x0, #2088]
	sbcs x9, x9, x2
	ldr x2, [x0, #2096]
	sbcs x10, x10, x2
	ldr x2, [x0, #2104]
	sbcs x11, x11, x2
	ldr x2, [x0, #2112]
	sbcs x12, x12, x2
	ldr x2, [x0, #2120]
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
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	ldr x1, [x0, #1792]
	ldr x2, [x0, #1600]
	eor x2, x2, x1
	movz x1, #1, lsl #0
	and x2, x2, x1
	movz x7, #0, lsl #0
	sub x3, x7, x2
	movz x7, #0, lsl #0
	add x2, x3, #1
	sub x2, x7, x2
	ldr x1, [x0, #2176]
	and x1, x1, x2
	str x1, [x0, #2176]
	ldr x3, [x0, #2176]
	movz x1, #4, lsl #0
	and x1, x1, x3
	strb w1, [x20, #0]
	add x6, x20, #1
	ldr x1, [x0, #1648]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #40]
	ldr x1, [x0, #1656]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #32]
	ldr x1, [x0, #1664]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #24]
	ldr x1, [x0, #1672]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #16]
	ldr x1, [x0, #1680]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #8]
	ldr x1, [x0, #1688]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #0]
	ldr x1, [x0, #1792]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #88]
	ldr x1, [x0, #1800]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #80]
	ldr x1, [x0, #1808]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #72]
	ldr x1, [x0, #1816]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #64]
	ldr x1, [x0, #1824]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #56]
	ldr x1, [x0, #1832]
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
