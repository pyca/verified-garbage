// The functions of `src/ec_p521_compressed.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p521_compress_public_key:
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
	add x17, x3, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2296]
	add x17, x3, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2304]
	add x17, x3, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2312]
	add x17, x3, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2320]
	add x17, x3, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2328]
	add x17, x3, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2336]
	add x17, x3, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2344]
	add x17, x3, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2352]
	ldr x5, [x3, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2360]
	add x17, x1, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2368]
	add x17, x1, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2376]
	add x17, x1, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2384]
	add x17, x1, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2392]
	add x17, x1, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2400]
	add x17, x1, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2408]
	add x17, x1, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2416]
	add x17, x1, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2424]
	ldr x5, [x1, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2432]
	add x17, x2, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2440]
	add x17, x2, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2448]
	add x17, x2, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2456]
	add x17, x2, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2464]
	add x17, x2, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2472]
	add x17, x2, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2480]
	add x17, x2, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2488]
	add x17, x2, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2496]
	ldr x5, [x2, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2504]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #64]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #72]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #80]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #88]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #96]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #104]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #112]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #120]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #128]
	movz x1, #25609, lsl #0
	movk x1, #37176, lsl #16
	movk x1, #46878, lsl #32
	movk x1, #47983, lsl #48
	str x1, [x0, #136]
	movz x1, #18350, lsl #0
	movk x1, #35228, lsl #16
	movk x1, #51640, lsl #32
	movk x1, #15285, lsl #48
	str x1, [x0, #144]
	movz x1, #42448, lsl #0
	movk x1, #63241, lsl #16
	movk x1, #328, lsl #32
	movk x1, #32716, lsl #48
	str x1, [x0, #152]
	movz x1, #38507, lsl #0
	movk x1, #48943, lsl #16
	movk x1, #34691, lsl #32
	movk x1, #20870, lsl #48
	str x1, [x0, #160]
	movz x1, #65530, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #168]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #176]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #184]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #192]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #200]
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
	movz x1, #0, lsl #0
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
	movz x1, #1, lsl #0
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
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #384]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #392]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #400]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #416]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #424]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #432]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #440]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #448]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #456]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #464]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #472]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #480]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #488]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65151, lsl #48
	str x1, [x0, #496]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #504]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #512]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #520]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #528]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #536]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #544]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #552]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #560]
	movz x1, #25479, lsl #0
	movk x1, #44632, lsl #16
	movk x1, #25935, lsl #32
	movk x1, #32788, lsl #48
	str x1, [x0, #568]
	movz x1, #43039, lsl #0
	movk x1, #59957, lsl #16
	movk x1, #41615, lsl #32
	movk x1, #30967, lsl #48
	str x1, [x0, #576]
	movz x1, #38426, lsl #0
	movk x1, #50206, lsl #16
	movk x1, #47599, lsl #32
	movk x1, #33690, lsl #48
	str x1, [x0, #584]
	movz x1, #55519, lsl #0
	movk x1, #24221, lsl #16
	movk x1, #10592, lsl #32
	movk x1, #48523, lsl #48
	str x1, [x0, #592]
	movz x1, #16201, lsl #0
	movk x1, #43254, lsl #16
	movk x1, #3228, lsl #32
	movk x1, #61611, lsl #48
	str x1, [x0, #600]
	movz x1, #30852, lsl #0
	movk x1, #51399, lsl #16
	movk x1, #23108, lsl #32
	movk x1, #63964, lsl #48
	str x1, [x0, #608]
	movz x1, #55690, lsl #0
	movk x1, #11724, lsl #16
	movk x1, #27961, lsl #32
	movk x1, #30545, lsl #48
	str x1, [x0, #616]
	movz x1, #17056, lsl #0
	movk x1, #53339, lsl #16
	movk x1, #19728, lsl #32
	movk x1, #4041, lsl #48
	str x1, [x0, #624]
	movz x1, #77, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #632]
	movz x1, #49409, lsl #0
	movk x1, #33197, lsl #16
	movk x1, #41315, lsl #32
	movk x1, #45873, lsl #48
	str x1, [x0, #640]
	movz x1, #29406, lsl #0
	movk x1, #6369, lsl #16
	movk x1, #48959, lsl #32
	movk x1, #19964, lsl #48
	str x1, [x0, #648]
	movz x1, #46369, lsl #0
	movk x1, #57538, lsl #16
	movk x1, #42073, lsl #32
	movk x1, #28441, lsl #48
	str x1, [x0, #656]
	movz x1, #32724, lsl #0
	movk x1, #37841, lsl #16
	movk x1, #3808, lsl #32
	movk x1, #38015, lsl #48
	str x1, [x0, #664]
	movz x1, #62380, lsl #0
	movk x1, #15351, lsl #16
	movk x1, #42415, lsl #32
	movk x1, #56656, lsl #48
	str x1, [x0, #672]
	movz x1, #42654, lsl #0
	movk x1, #45109, lsl #16
	movk x1, #5207, lsl #32
	movk x1, #37116, lsl #48
	str x1, [x0, #680]
	movz x1, #40922, lsl #0
	movk x1, #40066, lsl #16
	movk x1, #12864, lsl #32
	movk x1, #8526, lsl #48
	str x1, [x0, #688]
	movz x1, #51930, lsl #0
	movk x1, #45841, lsl #16
	movk x1, #8037, lsl #32
	movk x1, #59087, lsl #48
	str x1, [x0, #696]
	movz x1, #116, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #704]
	movz x1, #9870, lsl #0
	movk x1, #23198, lsl #16
	movk x1, #3658, lsl #32
	movk x1, #10310, lsl #48
	str x1, [x0, #712]
	movz x1, #59571, lsl #0
	movk x1, #15183, lsl #16
	movk x1, #24394, lsl #32
	movk x1, #8260, lsl #48
	str x1, [x0, #720]
	movz x1, #14689, lsl #0
	movk x1, #17233, lsl #16
	movk x1, #40504, lsl #32
	movk x1, #45210, lsl #48
	str x1, [x0, #728]
	movz x1, #54915, lsl #0
	movk x1, #32927, lsl #16
	movk x1, #43100, lsl #32
	movk x1, #8290, lsl #48
	str x1, [x0, #736]
	movz x1, #31251, lsl #0
	movk x1, #19631, lsl #16
	movk x1, #63289, lsl #32
	movk x1, #5707, lsl #48
	str x1, [x0, #744]
	movz x1, #40755, lsl #0
	movk x1, #35731, lsl #16
	movk x1, #55262, lsl #32
	movk x1, #13323, lsl #48
	str x1, [x0, #752]
	movz x1, #52642, lsl #0
	movk x1, #9387, lsl #16
	movk x1, #31394, lsl #32
	movk x1, #60620, lsl #48
	str x1, [x0, #760]
	movz x1, #16013, lsl #0
	movk x1, #55830, lsl #16
	movk x1, #17711, lsl #32
	movk x1, #558, lsl #48
	str x1, [x0, #768]
	movz x1, #480, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #776]
	movz x1, #56580, lsl #0
	movk x1, #53013, lsl #16
	movk x1, #53325, lsl #32
	movk x1, #4988, lsl #48
	str x1, [x0, #784]
	movz x1, #32419, lsl #0
	movk x1, #58708, lsl #16
	movk x1, #47836, lsl #32
	movk x1, #63239, lsl #48
	str x1, [x0, #792]
	movz x1, #29695, lsl #0
	movk x1, #31045, lsl #16
	movk x1, #36152, lsl #32
	movk x1, #4775, lsl #48
	str x1, [x0, #800]
	movz x1, #24070, lsl #0
	movk x1, #22519, lsl #16
	movk x1, #7925, lsl #32
	movk x1, #54130, lsl #48
	str x1, [x0, #808]
	movz x1, #51163, lsl #0
	movk x1, #11849, lsl #16
	movk x1, #9176, lsl #32
	movk x1, #56686, lsl #48
	str x1, [x0, #816]
	movz x1, #28222, lsl #0
	movk x1, #46965, lsl #16
	movk x1, #53570, lsl #32
	movk x1, #53235, lsl #48
	str x1, [x0, #824]
	movz x1, #26556, lsl #0
	movk x1, #43237, lsl #16
	movk x1, #28001, lsl #32
	movk x1, #23500, lsl #48
	str x1, [x0, #832]
	movz x1, #3397, lsl #0
	movk x1, #18733, lsl #16
	movk x1, #977, lsl #32
	movk x1, #11662, lsl #48
	str x1, [x0, #840]
	movz x1, #61, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #848]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #64384, lsl #48
	str x1, [x0, #856]
	movz x1, #25549, lsl #0
	movk x1, #28855, lsl #16
	movk x1, #18468, lsl #32
	movk x1, #10402, lsl #48
	str x1, [x0, #864]
	movz x1, #12764, lsl #0
	movk x1, #9147, lsl #16
	movk x1, #9499, lsl #32
	movk x1, #6114, lsl #48
	str x1, [x0, #872]
	movz x1, #31533, lsl #0
	movk x1, #23428, lsl #16
	movk x1, #6655, lsl #32
	movk x1, #51776, lsl #48
	str x1, [x0, #880]
	movz x1, #26676, lsl #0
	movk x1, #15904, lsl #16
	movk x1, #15548, lsl #32
	movk x1, #727, lsl #48
	str x1, [x0, #888]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #896]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #904]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #912]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #920]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1072]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	movk x1, #128, lsl #48
	str x1, [x0, #1144]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1152]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1160]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1168]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1176]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1184]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1192]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1200]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1208]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1216]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1224]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1248]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1256]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1280]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #3232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2872]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #16384, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2880]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2888]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2896]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2904]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2912]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2920]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2928]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2936]
	movz x1, #25479, lsl #0
	movk x1, #44632, lsl #16
	movk x1, #25935, lsl #32
	movk x1, #32788, lsl #48
	str x1, [x0, #2944]
	movz x1, #43039, lsl #0
	movk x1, #59957, lsl #16
	movk x1, #41615, lsl #32
	movk x1, #30967, lsl #48
	str x1, [x0, #2952]
	movz x1, #38426, lsl #0
	movk x1, #50206, lsl #16
	movk x1, #47599, lsl #32
	movk x1, #33690, lsl #48
	str x1, [x0, #2960]
	movz x1, #55519, lsl #0
	movk x1, #24221, lsl #16
	movk x1, #10592, lsl #32
	movk x1, #48523, lsl #48
	str x1, [x0, #2968]
	movz x1, #16201, lsl #0
	movk x1, #43254, lsl #16
	movk x1, #3228, lsl #32
	movk x1, #61611, lsl #48
	str x1, [x0, #2976]
	movz x1, #30852, lsl #0
	movk x1, #51399, lsl #16
	movk x1, #23108, lsl #32
	movk x1, #63964, lsl #48
	str x1, [x0, #2984]
	movz x1, #55690, lsl #0
	movk x1, #11724, lsl #16
	movk x1, #27961, lsl #32
	movk x1, #30545, lsl #48
	str x1, [x0, #2992]
	movz x1, #17056, lsl #0
	movk x1, #53339, lsl #16
	movk x1, #19728, lsl #32
	movk x1, #4041, lsl #48
	str x1, [x0, #3000]
	movz x1, #77, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #3008]
	add x2, x6, #67
	add x17, x2, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2656]
	add x17, x2, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2664]
	add x17, x2, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2672]
	add x17, x2, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2680]
	add x17, x2, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2688]
	add x17, x2, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2696]
	add x17, x2, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2704]
	add x17, x2, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2712]
	ldr x5, [x2, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2720]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	movz x5, #4, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	mov v28.d[0], x30
	bl {vg_p521_check_point}
	umov x30, v28.d[0]
	ldr x3, [x0, #3232]
	ldr x1, [x0, #2656]
	movz x2, #1, lsl #0
	and x1, x1, x2
	add x1, x1, #2
	and x1, x1, x3
	strb w1, [x20, #0]
	ldr x1, [x0, #2440]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #59
	str x1, [x17, #0]
	ldr x1, [x0, #2448]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #51
	str x1, [x17, #0]
	ldr x1, [x0, #2456]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #43
	str x1, [x17, #0]
	ldr x1, [x0, #2464]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #35
	str x1, [x17, #0]
	ldr x1, [x0, #2472]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #27
	str x1, [x17, #0]
	ldr x1, [x0, #2480]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #19
	str x1, [x17, #0]
	ldr x1, [x0, #2488]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #11
	str x1, [x17, #0]
	ldr x1, [x0, #2496]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #3
	str x1, [x17, #0]
	ldr x1, [x0, #2504]
	and x1, x1, x3
	lsr x2, x1, #8
	strb w2, [x20, #1]
	strb w1, [x20, #2]
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

vg_ec_p521_decompress_public_key:
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
	add x17, x3, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2296]
	add x17, x3, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2304]
	add x17, x3, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2312]
	add x17, x3, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2320]
	add x17, x3, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2328]
	add x17, x3, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2336]
	add x17, x3, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2344]
	add x17, x3, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2352]
	ldr x5, [x3, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2360]
	add x17, x1, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2368]
	add x17, x1, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2376]
	add x17, x1, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2384]
	add x17, x1, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2392]
	add x17, x1, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2400]
	add x17, x1, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2408]
	add x17, x1, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2416]
	add x17, x1, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2424]
	ldr x5, [x1, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2432]
	add x17, x2, #58
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2440]
	add x17, x2, #50
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2448]
	add x17, x2, #42
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2456]
	add x17, x2, #34
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2464]
	add x17, x2, #26
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2472]
	add x17, x2, #18
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2480]
	add x17, x2, #10
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2488]
	add x17, x2, #2
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #2496]
	ldr x5, [x2, #0]
	rev x5, x5
	lsr x5, x5, #48
	str x5, [x0, #2504]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #64]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #72]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #80]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #88]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #96]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #104]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #112]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #120]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #128]
	movz x1, #25609, lsl #0
	movk x1, #37176, lsl #16
	movk x1, #46878, lsl #32
	movk x1, #47983, lsl #48
	str x1, [x0, #136]
	movz x1, #18350, lsl #0
	movk x1, #35228, lsl #16
	movk x1, #51640, lsl #32
	movk x1, #15285, lsl #48
	str x1, [x0, #144]
	movz x1, #42448, lsl #0
	movk x1, #63241, lsl #16
	movk x1, #328, lsl #32
	movk x1, #32716, lsl #48
	str x1, [x0, #152]
	movz x1, #38507, lsl #0
	movk x1, #48943, lsl #16
	movk x1, #34691, lsl #32
	movk x1, #20870, lsl #48
	str x1, [x0, #160]
	movz x1, #65530, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #168]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #176]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #184]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #192]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #200]
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
	movz x1, #0, lsl #0
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
	movz x1, #1, lsl #0
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
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #384]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #392]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #400]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #416]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #128, lsl #48
	str x1, [x0, #424]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #432]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #440]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #448]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #456]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #464]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #472]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #480]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #488]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65151, lsl #48
	str x1, [x0, #496]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #504]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #512]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #520]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #528]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #536]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #544]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #552]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #560]
	movz x1, #25479, lsl #0
	movk x1, #44632, lsl #16
	movk x1, #25935, lsl #32
	movk x1, #32788, lsl #48
	str x1, [x0, #568]
	movz x1, #43039, lsl #0
	movk x1, #59957, lsl #16
	movk x1, #41615, lsl #32
	movk x1, #30967, lsl #48
	str x1, [x0, #576]
	movz x1, #38426, lsl #0
	movk x1, #50206, lsl #16
	movk x1, #47599, lsl #32
	movk x1, #33690, lsl #48
	str x1, [x0, #584]
	movz x1, #55519, lsl #0
	movk x1, #24221, lsl #16
	movk x1, #10592, lsl #32
	movk x1, #48523, lsl #48
	str x1, [x0, #592]
	movz x1, #16201, lsl #0
	movk x1, #43254, lsl #16
	movk x1, #3228, lsl #32
	movk x1, #61611, lsl #48
	str x1, [x0, #600]
	movz x1, #30852, lsl #0
	movk x1, #51399, lsl #16
	movk x1, #23108, lsl #32
	movk x1, #63964, lsl #48
	str x1, [x0, #608]
	movz x1, #55690, lsl #0
	movk x1, #11724, lsl #16
	movk x1, #27961, lsl #32
	movk x1, #30545, lsl #48
	str x1, [x0, #616]
	movz x1, #17056, lsl #0
	movk x1, #53339, lsl #16
	movk x1, #19728, lsl #32
	movk x1, #4041, lsl #48
	str x1, [x0, #624]
	movz x1, #77, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #632]
	movz x1, #49409, lsl #0
	movk x1, #33197, lsl #16
	movk x1, #41315, lsl #32
	movk x1, #45873, lsl #48
	str x1, [x0, #640]
	movz x1, #29406, lsl #0
	movk x1, #6369, lsl #16
	movk x1, #48959, lsl #32
	movk x1, #19964, lsl #48
	str x1, [x0, #648]
	movz x1, #46369, lsl #0
	movk x1, #57538, lsl #16
	movk x1, #42073, lsl #32
	movk x1, #28441, lsl #48
	str x1, [x0, #656]
	movz x1, #32724, lsl #0
	movk x1, #37841, lsl #16
	movk x1, #3808, lsl #32
	movk x1, #38015, lsl #48
	str x1, [x0, #664]
	movz x1, #62380, lsl #0
	movk x1, #15351, lsl #16
	movk x1, #42415, lsl #32
	movk x1, #56656, lsl #48
	str x1, [x0, #672]
	movz x1, #42654, lsl #0
	movk x1, #45109, lsl #16
	movk x1, #5207, lsl #32
	movk x1, #37116, lsl #48
	str x1, [x0, #680]
	movz x1, #40922, lsl #0
	movk x1, #40066, lsl #16
	movk x1, #12864, lsl #32
	movk x1, #8526, lsl #48
	str x1, [x0, #688]
	movz x1, #51930, lsl #0
	movk x1, #45841, lsl #16
	movk x1, #8037, lsl #32
	movk x1, #59087, lsl #48
	str x1, [x0, #696]
	movz x1, #116, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #704]
	movz x1, #9870, lsl #0
	movk x1, #23198, lsl #16
	movk x1, #3658, lsl #32
	movk x1, #10310, lsl #48
	str x1, [x0, #712]
	movz x1, #59571, lsl #0
	movk x1, #15183, lsl #16
	movk x1, #24394, lsl #32
	movk x1, #8260, lsl #48
	str x1, [x0, #720]
	movz x1, #14689, lsl #0
	movk x1, #17233, lsl #16
	movk x1, #40504, lsl #32
	movk x1, #45210, lsl #48
	str x1, [x0, #728]
	movz x1, #54915, lsl #0
	movk x1, #32927, lsl #16
	movk x1, #43100, lsl #32
	movk x1, #8290, lsl #48
	str x1, [x0, #736]
	movz x1, #31251, lsl #0
	movk x1, #19631, lsl #16
	movk x1, #63289, lsl #32
	movk x1, #5707, lsl #48
	str x1, [x0, #744]
	movz x1, #40755, lsl #0
	movk x1, #35731, lsl #16
	movk x1, #55262, lsl #32
	movk x1, #13323, lsl #48
	str x1, [x0, #752]
	movz x1, #52642, lsl #0
	movk x1, #9387, lsl #16
	movk x1, #31394, lsl #32
	movk x1, #60620, lsl #48
	str x1, [x0, #760]
	movz x1, #16013, lsl #0
	movk x1, #55830, lsl #16
	movk x1, #17711, lsl #32
	movk x1, #558, lsl #48
	str x1, [x0, #768]
	movz x1, #480, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #776]
	movz x1, #56580, lsl #0
	movk x1, #53013, lsl #16
	movk x1, #53325, lsl #32
	movk x1, #4988, lsl #48
	str x1, [x0, #784]
	movz x1, #32419, lsl #0
	movk x1, #58708, lsl #16
	movk x1, #47836, lsl #32
	movk x1, #63239, lsl #48
	str x1, [x0, #792]
	movz x1, #29695, lsl #0
	movk x1, #31045, lsl #16
	movk x1, #36152, lsl #32
	movk x1, #4775, lsl #48
	str x1, [x0, #800]
	movz x1, #24070, lsl #0
	movk x1, #22519, lsl #16
	movk x1, #7925, lsl #32
	movk x1, #54130, lsl #48
	str x1, [x0, #808]
	movz x1, #51163, lsl #0
	movk x1, #11849, lsl #16
	movk x1, #9176, lsl #32
	movk x1, #56686, lsl #48
	str x1, [x0, #816]
	movz x1, #28222, lsl #0
	movk x1, #46965, lsl #16
	movk x1, #53570, lsl #32
	movk x1, #53235, lsl #48
	str x1, [x0, #824]
	movz x1, #26556, lsl #0
	movk x1, #43237, lsl #16
	movk x1, #28001, lsl #32
	movk x1, #23500, lsl #48
	str x1, [x0, #832]
	movz x1, #3397, lsl #0
	movk x1, #18733, lsl #16
	movk x1, #977, lsl #32
	movk x1, #11662, lsl #48
	str x1, [x0, #840]
	movz x1, #61, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #848]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #64384, lsl #48
	str x1, [x0, #856]
	movz x1, #25549, lsl #0
	movk x1, #28855, lsl #16
	movk x1, #18468, lsl #32
	movk x1, #10402, lsl #48
	str x1, [x0, #864]
	movz x1, #12764, lsl #0
	movk x1, #9147, lsl #16
	movk x1, #9499, lsl #32
	movk x1, #6114, lsl #48
	str x1, [x0, #872]
	movz x1, #31533, lsl #0
	movk x1, #23428, lsl #16
	movk x1, #6655, lsl #32
	movk x1, #51776, lsl #48
	str x1, [x0, #880]
	movz x1, #26676, lsl #0
	movk x1, #15904, lsl #16
	movk x1, #15548, lsl #32
	movk x1, #727, lsl #48
	str x1, [x0, #888]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #896]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #904]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #912]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #920]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1072]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	movk x1, #128, lsl #48
	str x1, [x0, #1144]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1152]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1160]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1168]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1176]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1184]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1192]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1200]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1208]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1216]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1224]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1248]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1256]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1280]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #3232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2872]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #16384, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2880]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2888]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2896]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2904]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2912]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2920]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2928]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #2936]
	movz x1, #25479, lsl #0
	movk x1, #44632, lsl #16
	movk x1, #25935, lsl #32
	movk x1, #32788, lsl #48
	str x1, [x0, #2944]
	movz x1, #43039, lsl #0
	movk x1, #59957, lsl #16
	movk x1, #41615, lsl #32
	movk x1, #30967, lsl #48
	str x1, [x0, #2952]
	movz x1, #38426, lsl #0
	movk x1, #50206, lsl #16
	movk x1, #47599, lsl #32
	movk x1, #33690, lsl #48
	str x1, [x0, #2960]
	movz x1, #55519, lsl #0
	movk x1, #24221, lsl #16
	movk x1, #10592, lsl #32
	movk x1, #48523, lsl #48
	str x1, [x0, #2968]
	movz x1, #16201, lsl #0
	movk x1, #43254, lsl #16
	movk x1, #3228, lsl #32
	movk x1, #61611, lsl #48
	str x1, [x0, #2976]
	movz x1, #30852, lsl #0
	movk x1, #51399, lsl #16
	movk x1, #23108, lsl #32
	movk x1, #63964, lsl #48
	str x1, [x0, #2984]
	movz x1, #55690, lsl #0
	movk x1, #11724, lsl #16
	movk x1, #27961, lsl #32
	movk x1, #30545, lsl #48
	str x1, [x0, #2992]
	movz x1, #17056, lsl #0
	movk x1, #53339, lsl #16
	movk x1, #19728, lsl #32
	movk x1, #4041, lsl #48
	str x1, [x0, #3000]
	movz x1, #77, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #3008]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	str x1, [x0, #2368]
	movz x5, #1, lsl #0
	orr x1, x1, x5
	movz x5, #3, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2440]
	ldr x2, [x0, #64]
	subs x16, x1, x2
	ldr x1, [x0, #2448]
	ldr x2, [x0, #72]
	sbcs x16, x1, x2
	ldr x1, [x0, #2456]
	ldr x2, [x0, #80]
	sbcs x16, x1, x2
	ldr x1, [x0, #2464]
	ldr x2, [x0, #88]
	sbcs x16, x1, x2
	ldr x1, [x0, #2472]
	ldr x2, [x0, #96]
	sbcs x16, x1, x2
	ldr x1, [x0, #2480]
	ldr x2, [x0, #104]
	sbcs x16, x1, x2
	ldr x1, [x0, #2488]
	ldr x2, [x0, #112]
	sbcs x16, x1, x2
	ldr x1, [x0, #2496]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	ldr x1, [x0, #2504]
	ldr x2, [x0, #128]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	mov v29.d[0], x30
	movz x1, #2512, lsl #0
	movz x2, #2440, lsl #0
	movz x3, #2872, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #3016, lsl #0
	movz x2, #2512, lsl #0
	movz x3, #2512, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #3088, lsl #0
	movz x2, #3016, lsl #0
	movz x3, #2512, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #3016, lsl #0
	movz x2, #496, lsl #0
	movz x3, #2512, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #3088]
	ldr x9, [x0, #3096]
	ldr x10, [x0, #3104]
	ldr x11, [x0, #3112]
	ldr x12, [x0, #3120]
	ldr x13, [x0, #3128]
	ldr x14, [x0, #3136]
	ldr x15, [x0, #3144]
	ldr x21, [x0, #3152]
	ldr x2, [x0, #3016]
	adds x8, x8, x2
	ldr x2, [x0, #3024]
	adcs x9, x9, x2
	ldr x2, [x0, #3032]
	adcs x10, x10, x2
	ldr x2, [x0, #3040]
	adcs x11, x11, x2
	ldr x2, [x0, #3048]
	adcs x12, x12, x2
	ldr x2, [x0, #3056]
	adcs x13, x13, x2
	ldr x2, [x0, #3064]
	adcs x14, x14, x2
	ldr x2, [x0, #3072]
	adcs x15, x15, x2
	ldr x2, [x0, #3080]
	adcs x21, x21, x2
	adc x22, x7, x7
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
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #2800]
	str x9, [x0, #2808]
	str x10, [x0, #2816]
	str x11, [x0, #2824]
	str x12, [x0, #2832]
	str x13, [x0, #2840]
	str x14, [x0, #2848]
	str x15, [x0, #2856]
	str x21, [x0, #2864]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2800]
	ldr x9, [x0, #2808]
	ldr x10, [x0, #2816]
	ldr x11, [x0, #2824]
	ldr x12, [x0, #2832]
	ldr x13, [x0, #2840]
	ldr x14, [x0, #2848]
	ldr x15, [x0, #2856]
	ldr x21, [x0, #2864]
	ldr x2, [x0, #2944]
	adds x8, x8, x2
	ldr x2, [x0, #2952]
	adcs x9, x9, x2
	ldr x2, [x0, #2960]
	adcs x10, x10, x2
	ldr x2, [x0, #2968]
	adcs x11, x11, x2
	ldr x2, [x0, #2976]
	adcs x12, x12, x2
	ldr x2, [x0, #2984]
	adcs x13, x13, x2
	ldr x2, [x0, #2992]
	adcs x14, x14, x2
	ldr x2, [x0, #3000]
	adcs x15, x15, x2
	ldr x2, [x0, #3008]
	adcs x21, x21, x2
	adc x22, x7, x7
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
	ldr x2, [x0, #128]
	sbcs x25, x21, x2
	sbcs x2, x22, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	csel x14, x17, x14, hs
	csel x15, x24, x15, hs
	csel x21, x25, x21, hs
	str x8, [x0, #3088]
	str x9, [x0, #3096]
	str x10, [x0, #3104]
	str x11, [x0, #3112]
	str x12, [x0, #3120]
	str x13, [x0, #3128]
	str x14, [x0, #3136]
	str x15, [x0, #3144]
	str x21, [x0, #3152]
	ldr x1, [x0, #3088]
	str x1, [x0, #1072]
	ldr x1, [x0, #3096]
	str x1, [x0, #1080]
	ldr x1, [x0, #3104]
	str x1, [x0, #1088]
	ldr x1, [x0, #3112]
	str x1, [x0, #1096]
	ldr x1, [x0, #3120]
	str x1, [x0, #1104]
	ldr x1, [x0, #3128]
	str x1, [x0, #1112]
	ldr x1, [x0, #3136]
	str x1, [x0, #1120]
	ldr x1, [x0, #3144]
	str x1, [x0, #1128]
	ldr x1, [x0, #3152]
	str x1, [x0, #1136]
	mov v29.d[0], x30
	movz x1, #1648, lsl #0
	movz x2, #3088, lsl #0
	movz x3, #3088, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1144, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1144, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1288, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1288, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1432, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1504, lsl #0
	movz x2, #1432, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1576, lsl #0
	movz x2, #1504, lsl #0
	movz x3, #1648, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1072]
	str x1, [x0, #2152]
	ldr x1, [x0, #1080]
	str x1, [x0, #2160]
	ldr x1, [x0, #1088]
	str x1, [x0, #2168]
	ldr x1, [x0, #1096]
	str x1, [x0, #2176]
	ldr x1, [x0, #1104]
	str x1, [x0, #2184]
	ldr x1, [x0, #1112]
	str x1, [x0, #2192]
	ldr x1, [x0, #1120]
	str x1, [x0, #2200]
	ldr x1, [x0, #1128]
	str x1, [x0, #2208]
	ldr x1, [x0, #1136]
	str x1, [x0, #2216]
	movz x19, #519, lsl #0
20:
	sub x19, x19, #1
	mov v29.d[0], x30
	movz x1, #2152, lsl #0
	movz x2, #2152, lsl #0
	movz x3, #2152, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	cbnz x19, 20b
	mov v29.d[0], x30
	movz x1, #2656, lsl #0
	movz x2, #2152, lsl #0
	movz x3, #352, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #280]
	ldr x9, [x0, #288]
	ldr x10, [x0, #296]
	ldr x11, [x0, #304]
	ldr x12, [x0, #312]
	ldr x13, [x0, #320]
	ldr x14, [x0, #328]
	ldr x15, [x0, #336]
	ldr x21, [x0, #344]
	ldr x2, [x0, #2656]
	subs x8, x8, x2
	ldr x2, [x0, #2664]
	sbcs x9, x9, x2
	ldr x2, [x0, #2672]
	sbcs x10, x10, x2
	ldr x2, [x0, #2680]
	sbcs x11, x11, x2
	ldr x2, [x0, #2688]
	sbcs x12, x12, x2
	ldr x2, [x0, #2696]
	sbcs x13, x13, x2
	ldr x2, [x0, #2704]
	sbcs x14, x14, x2
	ldr x2, [x0, #2712]
	sbcs x15, x15, x2
	ldr x2, [x0, #2720]
	sbcs x21, x21, x2
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
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #2728]
	str x9, [x0, #2736]
	str x10, [x0, #2744]
	str x11, [x0, #2752]
	str x12, [x0, #2760]
	str x13, [x0, #2768]
	str x14, [x0, #2776]
	str x15, [x0, #2784]
	str x21, [x0, #2792]
	ldr x1, [x0, #2656]
	ldr x2, [x0, #2368]
	eor x2, x2, x1
	movz x1, #1, lsl #0
	and x2, x2, x1
	movz x7, #0, lsl #0
	sub x3, x7, x2
	ldr x1, [x0, #2656]
	ldr x2, [x0, #2728]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2656]
	ldr x1, [x0, #2664]
	ldr x2, [x0, #2736]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2664]
	ldr x1, [x0, #2672]
	ldr x2, [x0, #2744]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2672]
	ldr x1, [x0, #2680]
	ldr x2, [x0, #2752]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2680]
	ldr x1, [x0, #2688]
	ldr x2, [x0, #2760]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2688]
	ldr x1, [x0, #2696]
	ldr x2, [x0, #2768]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2696]
	ldr x1, [x0, #2704]
	ldr x2, [x0, #2776]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2704]
	ldr x1, [x0, #2712]
	ldr x2, [x0, #2784]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2712]
	ldr x1, [x0, #2720]
	ldr x2, [x0, #2792]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #2720]
	mov v29.d[0], x30
	movz x1, #2584, lsl #0
	movz x2, #2656, lsl #0
	movz x3, #2872, lsl #0
	bl {vg_p521_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #3016, lsl #0
	movz x2, #2584, lsl #0
	movz x3, #2584, lsl #0
	bl {vg_p521_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #3016]
	ldr x9, [x0, #3024]
	ldr x10, [x0, #3032]
	ldr x11, [x0, #3040]
	ldr x12, [x0, #3048]
	ldr x13, [x0, #3056]
	ldr x14, [x0, #3064]
	ldr x15, [x0, #3072]
	ldr x21, [x0, #3080]
	ldr x2, [x0, #3088]
	subs x8, x8, x2
	ldr x2, [x0, #3096]
	sbcs x9, x9, x2
	ldr x2, [x0, #3104]
	sbcs x10, x10, x2
	ldr x2, [x0, #3112]
	sbcs x11, x11, x2
	ldr x2, [x0, #3120]
	sbcs x12, x12, x2
	ldr x2, [x0, #3128]
	sbcs x13, x13, x2
	ldr x2, [x0, #3136]
	sbcs x14, x14, x2
	ldr x2, [x0, #3144]
	sbcs x15, x15, x2
	ldr x2, [x0, #3152]
	sbcs x21, x21, x2
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
	ldr x2, [x0, #128]
	and x2, x2, x17
	adcs x21, x21, x2
	str x8, [x0, #2800]
	str x9, [x0, #2808]
	str x10, [x0, #2816]
	str x11, [x0, #2824]
	str x12, [x0, #2832]
	str x13, [x0, #2840]
	str x14, [x0, #2848]
	str x15, [x0, #2856]
	str x21, [x0, #2864]
	movz x7, #0, lsl #0
	ldr x1, [x0, #2800]
	ldr x2, [x0, #2808]
	orr x1, x1, x2
	ldr x2, [x0, #2816]
	orr x1, x1, x2
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
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	ldr x1, [x0, #2656]
	ldr x2, [x0, #2368]
	eor x2, x2, x1
	movz x1, #1, lsl #0
	and x2, x2, x1
	movz x7, #0, lsl #0
	sub x3, x7, x2
	movz x7, #0, lsl #0
	add x2, x3, #1
	sub x2, x7, x2
	ldr x1, [x0, #3232]
	and x1, x1, x2
	str x1, [x0, #3232]
	ldr x3, [x0, #3232]
	movz x1, #4, lsl #0
	and x1, x1, x3
	strb w1, [x20, #0]
	add x6, x20, #1
	ldr x1, [x0, #2440]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #58
	str x1, [x17, #0]
	ldr x1, [x0, #2448]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #50
	str x1, [x17, #0]
	ldr x1, [x0, #2456]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #42
	str x1, [x17, #0]
	ldr x1, [x0, #2464]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #34
	str x1, [x17, #0]
	ldr x1, [x0, #2472]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #26
	str x1, [x17, #0]
	ldr x1, [x0, #2480]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #18
	str x1, [x17, #0]
	ldr x1, [x0, #2488]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #10
	str x1, [x17, #0]
	ldr x1, [x0, #2496]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #2
	str x1, [x17, #0]
	ldr x1, [x0, #2504]
	and x1, x1, x3
	lsr x2, x1, #8
	strb w2, [x6, #0]
	strb w1, [x6, #1]
	ldr x1, [x0, #2656]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #124
	str x1, [x17, #0]
	ldr x1, [x0, #2664]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #116
	str x1, [x17, #0]
	ldr x1, [x0, #2672]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #108
	str x1, [x17, #0]
	ldr x1, [x0, #2680]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #100
	str x1, [x17, #0]
	ldr x1, [x0, #2688]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #92
	str x1, [x17, #0]
	ldr x1, [x0, #2696]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #84
	str x1, [x17, #0]
	ldr x1, [x0, #2704]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #76
	str x1, [x17, #0]
	ldr x1, [x0, #2712]
	and x1, x1, x3
	rev x1, x1
	add x17, x6, #68
	str x1, [x17, #0]
	ldr x1, [x0, #2720]
	and x1, x1, x3
	lsr x2, x1, #8
	strb w2, [x6, #66]
	strb w1, [x6, #67]
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
