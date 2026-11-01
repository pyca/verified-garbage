// The functions of `src/ecdsa_p384.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p384_verify:
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
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #64]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #72]
	movz x1, #65534, lsl #0
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
	movz x1, #10611, lsl #0
	movk x1, #52421, lsl #16
	movk x1, #6506, lsl #32
	movk x1, #60652, lsl #48
	str x1, [x0, #112]
	movz x1, #42874, lsl #0
	movk x1, #18608, lsl #16
	movk x1, #3506, lsl #32
	movk x1, #22554, lsl #48
	str x1, [x0, #120]
	movz x1, #11743, lsl #0
	movk x1, #62519, lsl #16
	movk x1, #19841, lsl #32
	movk x1, #51043, lsl #48
	str x1, [x0, #128]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #136]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #144]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #304]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
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
	movz x1, #65532, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #3, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #352]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65532, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #360]
	movz x1, #65531, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #368]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #376]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #384]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #392]
	movz x1, #11724, lsl #0
	movk x1, #40257, lsl #16
	movk x1, #34929, lsl #32
	movk x1, #2065, lsl #48
	str x1, [x0, #400]
	movz x1, #13036, lsl #0
	movk x1, #31308, lsl #16
	movk x1, #44504, lsl #32
	movk x1, #63273, lsl #48
	str x1, [x0, #408]
	movz x1, #558, lsl #0
	movk x1, #6432, lsl #16
	movk x1, #8347, lsl #32
	movk x1, #30706, lsl #48
	str x1, [x0, #416]
	movz x1, #35554, lsl #0
	movk x1, #38035, lsl #16
	movk x1, #19438, lsl #32
	movk x1, #58167, lsl #48
	str x1, [x0, #424]
	movz x1, #8340, lsl #0
	movk x1, #7938, lsl #16
	movk x1, #8692, lsl #32
	movk x1, #46635, lsl #48
	str x1, [x0, #432]
	movz x1, #49145, lsl #0
	movk x1, #24655, lsl #16
	movk x1, #4427, lsl #32
	movk x1, #52488, lsl #48
	str x1, [x0, #440]
	movz x1, #46376, lsl #0
	movk x1, #18880, lsl #16
	movk x1, #30054, lsl #32
	movk x1, #15824, lsl #48
	str x1, [x0, #448]
	movz x1, #52792, lsl #0
	movk x1, #41174, lsl #16
	movk x1, #30946, lsl #32
	movk x1, #8419, lsl #48
	str x1, [x0, #456]
	movz x1, #19822, lsl #0
	movk x1, #21531, lsl #16
	movk x1, #15100, lsl #32
	movk x1, #34716, lsl #48
	str x1, [x0, #464]
	movz x1, #3839, lsl #0
	movk x1, #22947, lsl #16
	movk x1, #34436, lsl #32
	movk x1, #25684, lsl #48
	str x1, [x0, #472]
	movz x1, #56875, lsl #0
	movk x1, #24910, lsl #16
	movk x1, #63267, lsl #32
	movk x1, #33071, lsl #48
	str x1, [x0, #480]
	movz x1, #5395, lsl #0
	movk x1, #10654, lsl #16
	movk x1, #44482, lsl #32
	movk x1, #19770, lsl #48
	str x1, [x0, #488]
	movz x1, #42238, lsl #0
	movk x1, #19203, lsl #16
	movk x1, #15789, lsl #32
	movk x1, #8964, lsl #48
	str x1, [x0, #496]
	movz x1, #43436, lsl #0
	movk x1, #31668, lsl #16
	movk x1, #43199, lsl #32
	movk x1, #41407, lsl #48
	str x1, [x0, #504]
	movz x1, #45136, lsl #0
	movk x1, #11907, lsl #16
	movk x1, #59222, lsl #32
	movk x1, #35757, lsl #48
	str x1, [x0, #512]
	movz x1, #65497, lsl #0
	movk x1, #26868, lsl #16
	movk x1, #21017, lsl #32
	movk x1, #50883, lsl #48
	str x1, [x0, #520]
	movz x1, #43072, lsl #0
	movk x1, #14697, lsl #16
	movk x1, #550, lsl #32
	movk x1, #56704, lsl #48
	str x1, [x0, #528]
	movz x1, #50665, lsl #0
	movk x1, #23061, lsl #16
	movk x1, #43970, lsl #32
	movk x1, #11128, lsl #48
	str x1, [x0, #536]
	movz x1, #2473, lsl #0
	movk x1, #6580, lsl #16
	movk x1, #39716, lsl #32
	movk x1, #11569, lsl #48
	str x1, [x0, #544]
	movz x1, #42009, lsl #0
	movk x1, #57114, lsl #16
	movk x1, #33253, lsl #32
	movk x1, #65341, lsl #48
	str x1, [x0, #552]
	movz x1, #10567, lsl #0
	movk x1, #64696, lsl #16
	movk x1, #18490, lsl #32
	movk x1, #48190, lsl #48
	str x1, [x0, #560]
	movz x1, #7365, lsl #0
	movk x1, #19115, lsl #16
	movk x1, #18711, lsl #32
	movk x1, #54285, lsl #48
	str x1, [x0, #568]
	movz x1, #26773, lsl #0
	movk x1, #10278, lsl #16
	movk x1, #23418, lsl #32
	movk x1, #16304, lsl #48
	str x1, [x0, #576]
	movz x1, #48929, lsl #0
	movk x1, #11065, lsl #16
	movk x1, #60929, lsl #32
	movk x1, #3204, lsl #48
	str x1, [x0, #584]
	movz x1, #54925, lsl #0
	movk x1, #13114, lsl #16
	movk x1, #59029, lsl #32
	movk x1, #4883, lsl #48
	str x1, [x0, #592]
	movz x1, #22661, lsl #0
	movk x1, #46927, lsl #16
	movk x1, #62029, lsl #32
	movk x1, #42981, lsl #48
	str x1, [x0, #600]
	movz x1, #53792, lsl #0
	movk x1, #3016, lsl #16
	movk x1, #45694, lsl #32
	movk x1, #14492, lsl #48
	str x1, [x0, #608]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #616]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #624]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #784]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #792]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #800]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #808]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #816]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65534, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1936]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #2, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1944]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65534, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1952]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #2, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1960]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1968]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1976]
	movz x1, #11724, lsl #0
	movk x1, #40257, lsl #16
	movk x1, #34929, lsl #32
	movk x1, #2065, lsl #48
	str x1, [x0, #1984]
	movz x1, #13036, lsl #0
	movk x1, #31308, lsl #16
	movk x1, #44504, lsl #32
	movk x1, #63273, lsl #48
	str x1, [x0, #1992]
	movz x1, #558, lsl #0
	movk x1, #6432, lsl #16
	movk x1, #8347, lsl #32
	movk x1, #30706, lsl #48
	str x1, [x0, #2000]
	movz x1, #35554, lsl #0
	movk x1, #38035, lsl #16
	movk x1, #19438, lsl #32
	movk x1, #58167, lsl #48
	str x1, [x0, #2008]
	movz x1, #8340, lsl #0
	movk x1, #7938, lsl #16
	movk x1, #8692, lsl #32
	movk x1, #46635, lsl #48
	str x1, [x0, #2016]
	movz x1, #49145, lsl #0
	movk x1, #24655, lsl #16
	movk x1, #4427, lsl #32
	movk x1, #52488, lsl #48
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
	bl {vg_p384_check_point}
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
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	bl {vg_p384_inv_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1984, lsl #0
	movz x2, #1600, lsl #0
	movz x3, #544, lsl #0
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1552, lsl #0
	movz x3, #544, lsl #0
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2032, lsl #0
	movz x2, #1984, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2080, lsl #0
	movz x2, #1936, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1696, lsl #0
	movz x2, #2032, lsl #0
	movz x3, #256, lsl #0
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1744, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #256, lsl #0
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	ldr x5, [x0, #1696]
	ldr x6, [x0, #1704]
	ldr x7, [x0, #1712]
	ldr x8, [x0, #1720]
	ldr x9, [x0, #1728]
	ldr x10, [x0, #1736]
	movz x11, #0, lsl #0
	movz x12, #511, lsl #0
	movz x13, #256, lsl #0
	movz x14, #0, lsl #0
	movz x15, #1, lsl #0
	movz x19, #385, lsl #0
	add x20, x0, #3152
21:
	and x1, x5, x15
	cbnz x1, 22f
	movz x2, #0, lsl #0
	b 23f
22:
	and x2, x5, x12
	and x3, x2, x13
	lsl x3, x3, #1
	sub x2, x2, x3
23:
	strb w2, [x20, #0]
	lsr x3, x2, #8
	strb w3, [x20, #1]
	add x20, x20, #2
	lsr x3, x2, #63
	sub x3, x14, x3
	subs x5, x5, x2
	sbcs x6, x6, x3
	sbcs x7, x7, x3
	sbcs x8, x8, x3
	sbcs x9, x9, x3
	sbcs x10, x10, x3
	sbcs x11, x11, x3
	extr x5, x6, x5, #1
	extr x6, x7, x6, #1
	extr x7, x8, x7, #1
	extr x8, x9, x8, #1
	extr x9, x10, x9, #1
	extr x10, x11, x10, #1
	lsr x11, x11, #1
	sub x19, x19, #1
	cbnz x19, 21b
	ldr x5, [x0, #1744]
	ldr x6, [x0, #1752]
	ldr x7, [x0, #1760]
	ldr x8, [x0, #1768]
	ldr x9, [x0, #1776]
	ldr x10, [x0, #1784]
	movz x11, #0, lsl #0
	movz x12, #31, lsl #0
	movz x13, #16, lsl #0
	movz x14, #0, lsl #0
	movz x15, #1, lsl #0
	movz x19, #385, lsl #0
	add x20, x0, #2704
24:
	and x1, x5, x15
	cbnz x1, 25f
	movz x2, #0, lsl #0
	b 26f
25:
	and x2, x5, x12
	and x3, x2, x13
	lsl x3, x3, #1
	sub x2, x2, x3
26:
	strb w2, [x20, #0]
	add x20, x20, #1
	lsr x3, x2, #63
	sub x3, x14, x3
	subs x5, x5, x2
	sbcs x6, x6, x3
	sbcs x7, x7, x3
	sbcs x8, x8, x3
	sbcs x9, x9, x3
	sbcs x10, x10, x3
	sbcs x11, x11, x3
	extr x5, x6, x5, #1
	extr x6, x7, x6, #1
	extr x7, x8, x7, #1
	extr x8, x9, x8, #1
	extr x9, x10, x9, #1
	extr x10, x11, x10, #1
	lsr x11, x11, #1
	sub x19, x19, #1
	cbnz x19, 24b
	ldr x1, [x0, #1888]
	str x1, [x0, #736]
	ldr x1, [x0, #1896]
	str x1, [x0, #744]
	ldr x1, [x0, #1904]
	str x1, [x0, #752]
	ldr x1, [x0, #1912]
	str x1, [x0, #760]
	ldr x1, [x0, #1920]
	str x1, [x0, #768]
	ldr x1, [x0, #1928]
	str x1, [x0, #776]
	ldr x1, [x0, #2128]
	str x1, [x0, #784]
	ldr x1, [x0, #2136]
	str x1, [x0, #792]
	ldr x1, [x0, #2144]
	str x1, [x0, #800]
	ldr x1, [x0, #2152]
	str x1, [x0, #808]
	ldr x1, [x0, #2160]
	str x1, [x0, #816]
	ldr x1, [x0, #2168]
	str x1, [x0, #824]
	ldr x1, [x0, #304]
	str x1, [x0, #832]
	ldr x1, [x0, #312]
	str x1, [x0, #840]
	ldr x1, [x0, #320]
	str x1, [x0, #848]
	ldr x1, [x0, #328]
	str x1, [x0, #856]
	ldr x1, [x0, #336]
	str x1, [x0, #864]
	ldr x1, [x0, #344]
	str x1, [x0, #872]
	add x20, x0, #0
	ldr x4, [x0, #736]
	str x4, [x20, #4240]
	ldr x4, [x0, #744]
	str x4, [x20, #4248]
	ldr x4, [x0, #752]
	str x4, [x20, #4256]
	ldr x4, [x0, #760]
	str x4, [x20, #4264]
	ldr x4, [x0, #768]
	str x4, [x20, #4272]
	ldr x4, [x0, #776]
	str x4, [x20, #4280]
	ldr x4, [x0, #784]
	str x4, [x20, #4288]
	ldr x4, [x0, #792]
	str x4, [x20, #4296]
	ldr x4, [x0, #800]
	str x4, [x20, #4304]
	ldr x4, [x0, #808]
	str x4, [x20, #4312]
	ldr x4, [x0, #816]
	str x4, [x20, #4320]
	ldr x4, [x0, #824]
	str x4, [x20, #4328]
	ldr x4, [x0, #832]
	str x4, [x20, #4336]
	ldr x4, [x0, #840]
	str x4, [x20, #4344]
	ldr x4, [x0, #848]
	str x4, [x20, #4352]
	ldr x4, [x0, #856]
	str x4, [x20, #4360]
	ldr x4, [x0, #864]
	str x4, [x20, #4368]
	ldr x4, [x0, #872]
	str x4, [x20, #4376]
	add x20, x20, #144
	movz x19, #7, lsl #0
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1888, lsl #0
	movz x3, #1888, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #2128, lsl #0
	movz x3, #2128, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #784, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #736, lsl #0
	movz x2, #1888, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #736]
	adds x8, x8, x2
	ldr x2, [x0, #744]
	adcs x9, x9, x2
	ldr x2, [x0, #752]
	adcs x10, x10, x2
	ldr x2, [x0, #760]
	adcs x11, x11, x2
	ldr x2, [x0, #768]
	adcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #736]
	adds x8, x8, x2
	ldr x2, [x0, #744]
	adcs x9, x9, x2
	ldr x2, [x0, #752]
	adcs x10, x10, x2
	ldr x2, [x0, #760]
	adcs x11, x11, x2
	ldr x2, [x0, #768]
	adcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1168]
	ldr x9, [x0, #1176]
	ldr x10, [x0, #1184]
	ldr x11, [x0, #1192]
	ldr x12, [x0, #1200]
	ldr x13, [x0, #1208]
	ldr x2, [x0, #304]
	subs x8, x8, x2
	ldr x2, [x0, #312]
	sbcs x9, x9, x2
	ldr x2, [x0, #320]
	sbcs x10, x10, x2
	ldr x2, [x0, #328]
	sbcs x11, x11, x2
	ldr x2, [x0, #336]
	sbcs x12, x12, x2
	ldr x2, [x0, #344]
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
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
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
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	str x11, [x0, #1288]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1024, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	ldr x2, [x0, #768]
	sbcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #1024]
	str x9, [x0, #1032]
	str x10, [x0, #1040]
	str x11, [x0, #1048]
	str x12, [x0, #1056]
	str x13, [x0, #1064]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	ldr x2, [x0, #768]
	sbcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #1024]
	str x9, [x0, #1032]
	str x10, [x0, #1040]
	str x11, [x0, #1048]
	str x12, [x0, #1056]
	str x13, [x0, #1064]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #1024]
	subs x8, x8, x2
	ldr x2, [x0, #1032]
	sbcs x9, x9, x2
	ldr x2, [x0, #1040]
	sbcs x10, x10, x2
	ldr x2, [x0, #1048]
	sbcs x11, x11, x2
	ldr x2, [x0, #1056]
	sbcs x12, x12, x2
	ldr x2, [x0, #1064]
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
	mov v29.d[0], x30
	movz x1, #1072, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #784]
	ldr x9, [x0, #792]
	ldr x10, [x0, #800]
	ldr x11, [x0, #808]
	ldr x12, [x0, #816]
	ldr x13, [x0, #824]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	movz x7, #0, lsl #0
	ldr x8, [x0, #784]
	ldr x9, [x0, #792]
	ldr x10, [x0, #800]
	ldr x11, [x0, #808]
	ldr x12, [x0, #816]
	ldr x13, [x0, #824]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	movz x7, #0, lsl #0
	ldr x8, [x0, #784]
	ldr x9, [x0, #792]
	ldr x10, [x0, #800]
	ldr x11, [x0, #808]
	ldr x12, [x0, #816]
	ldr x13, [x0, #824]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x2, [x0, #784]
	subs x8, x8, x2
	ldr x2, [x0, #792]
	sbcs x9, x9, x2
	ldr x2, [x0, #800]
	sbcs x10, x10, x2
	ldr x2, [x0, #808]
	sbcs x11, x11, x2
	ldr x2, [x0, #816]
	sbcs x12, x12, x2
	ldr x2, [x0, #824]
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
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
	movz x7, #0, lsl #0
	ldr x8, [x0, #2128]
	ldr x9, [x0, #2136]
	ldr x10, [x0, #2144]
	ldr x11, [x0, #2152]
	ldr x12, [x0, #2160]
	ldr x13, [x0, #2168]
	ldr x2, [x0, #2128]
	adds x8, x8, x2
	ldr x2, [x0, #2136]
	adcs x9, x9, x2
	ldr x2, [x0, #2144]
	adcs x10, x10, x2
	ldr x2, [x0, #2152]
	adcs x11, x11, x2
	ldr x2, [x0, #2160]
	adcs x12, x12, x2
	ldr x2, [x0, #2168]
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
	str x8, [x0, #832]
	str x9, [x0, #840]
	str x10, [x0, #848]
	str x11, [x0, #856]
	str x12, [x0, #864]
	str x13, [x0, #872]
27:
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	ldr x2, [x0, #768]
	sbcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #1168]
	str x9, [x0, #1176]
	str x10, [x0, #1184]
	str x11, [x0, #1192]
	str x12, [x0, #1200]
	str x13, [x0, #1208]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1168, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #832, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1024, lsl #0
	movz x2, #1024, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #736, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
	ldr x2, [x0, #784]
	subs x8, x8, x2
	ldr x2, [x0, #792]
	sbcs x9, x9, x2
	ldr x2, [x0, #800]
	sbcs x10, x10, x2
	ldr x2, [x0, #808]
	sbcs x11, x11, x2
	ldr x2, [x0, #816]
	sbcs x12, x12, x2
	ldr x2, [x0, #824]
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
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1360, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x2, [x0, #1312]
	subs x8, x8, x2
	ldr x2, [x0, #1320]
	sbcs x9, x9, x2
	ldr x2, [x0, #1328]
	sbcs x10, x10, x2
	ldr x2, [x0, #1336]
	sbcs x11, x11, x2
	ldr x2, [x0, #1344]
	sbcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	movz x1, #1072, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1408]
	ldr x9, [x0, #1416]
	ldr x10, [x0, #1424]
	ldr x11, [x0, #1432]
	ldr x12, [x0, #1440]
	ldr x13, [x0, #1448]
	ldr x2, [x0, #1024]
	subs x8, x8, x2
	ldr x2, [x0, #1032]
	sbcs x9, x9, x2
	ldr x2, [x0, #1040]
	sbcs x10, x10, x2
	ldr x2, [x0, #1048]
	sbcs x11, x11, x2
	ldr x2, [x0, #1056]
	sbcs x12, x12, x2
	ldr x2, [x0, #1064]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #1312]
	subs x8, x8, x2
	ldr x2, [x0, #1320]
	sbcs x9, x9, x2
	ldr x2, [x0, #1328]
	sbcs x10, x10, x2
	ldr x2, [x0, #1336]
	sbcs x11, x11, x2
	ldr x2, [x0, #1344]
	sbcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1024]
	ldr x9, [x0, #1032]
	ldr x10, [x0, #1040]
	ldr x11, [x0, #1048]
	ldr x12, [x0, #1056]
	ldr x13, [x0, #1064]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	ldr x2, [x0, #768]
	sbcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	mov v29.d[0], x30
	movz x1, #784, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #784]
	ldr x9, [x0, #792]
	ldr x10, [x0, #800]
	ldr x11, [x0, #808]
	ldr x12, [x0, #816]
	ldr x13, [x0, #824]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	ldr x4, [x0, #736]
	str x4, [x20, #4240]
	ldr x4, [x0, #744]
	str x4, [x20, #4248]
	ldr x4, [x0, #752]
	str x4, [x20, #4256]
	ldr x4, [x0, #760]
	str x4, [x20, #4264]
	ldr x4, [x0, #768]
	str x4, [x20, #4272]
	ldr x4, [x0, #776]
	str x4, [x20, #4280]
	ldr x4, [x0, #784]
	str x4, [x20, #4288]
	ldr x4, [x0, #792]
	str x4, [x20, #4296]
	ldr x4, [x0, #800]
	str x4, [x20, #4304]
	ldr x4, [x0, #808]
	str x4, [x20, #4312]
	ldr x4, [x0, #816]
	str x4, [x20, #4320]
	ldr x4, [x0, #824]
	str x4, [x20, #4328]
	ldr x4, [x0, #832]
	str x4, [x20, #4336]
	ldr x4, [x0, #840]
	str x4, [x20, #4344]
	ldr x4, [x0, #848]
	str x4, [x20, #4352]
	ldr x4, [x0, #856]
	str x4, [x20, #4360]
	ldr x4, [x0, #864]
	str x4, [x20, #4368]
	ldr x4, [x0, #872]
	str x4, [x20, #4376]
	add x20, x20, #144
	sub x19, x19, #1
	cbnz x19, 27b
	ldr x1, [x0, #4336]
	str x1, [x0, #1264]
	ldr x1, [x0, #4344]
	str x1, [x0, #1272]
	ldr x1, [x0, #4352]
	str x1, [x0, #1280]
	ldr x1, [x0, #4360]
	str x1, [x0, #1288]
	ldr x1, [x0, #4368]
	str x1, [x0, #1296]
	ldr x1, [x0, #4376]
	str x1, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1168]
	str x1, [x0, #5392]
	ldr x1, [x0, #1176]
	str x1, [x0, #5400]
	ldr x1, [x0, #1184]
	str x1, [x0, #5408]
	ldr x1, [x0, #1192]
	str x1, [x0, #5416]
	ldr x1, [x0, #1200]
	str x1, [x0, #5424]
	ldr x1, [x0, #1208]
	str x1, [x0, #5432]
	ldr x1, [x0, #1216]
	str x1, [x0, #5440]
	ldr x1, [x0, #1224]
	str x1, [x0, #5448]
	ldr x1, [x0, #1232]
	str x1, [x0, #5456]
	ldr x1, [x0, #1240]
	str x1, [x0, #5464]
	ldr x1, [x0, #1248]
	str x1, [x0, #5472]
	ldr x1, [x0, #1256]
	str x1, [x0, #5480]
	ldr x1, [x0, #4480]
	str x1, [x0, #1264]
	ldr x1, [x0, #4488]
	str x1, [x0, #1272]
	ldr x1, [x0, #4496]
	str x1, [x0, #1280]
	ldr x1, [x0, #4504]
	str x1, [x0, #1288]
	ldr x1, [x0, #4512]
	str x1, [x0, #1296]
	ldr x1, [x0, #4520]
	str x1, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1168]
	str x1, [x0, #5488]
	ldr x1, [x0, #1176]
	str x1, [x0, #5496]
	ldr x1, [x0, #1184]
	str x1, [x0, #5504]
	ldr x1, [x0, #1192]
	str x1, [x0, #5512]
	ldr x1, [x0, #1200]
	str x1, [x0, #5520]
	ldr x1, [x0, #1208]
	str x1, [x0, #5528]
	ldr x1, [x0, #1216]
	str x1, [x0, #5536]
	ldr x1, [x0, #1224]
	str x1, [x0, #5544]
	ldr x1, [x0, #1232]
	str x1, [x0, #5552]
	ldr x1, [x0, #1240]
	str x1, [x0, #5560]
	ldr x1, [x0, #1248]
	str x1, [x0, #5568]
	ldr x1, [x0, #1256]
	str x1, [x0, #5576]
	ldr x1, [x0, #4624]
	str x1, [x0, #1264]
	ldr x1, [x0, #4632]
	str x1, [x0, #1272]
	ldr x1, [x0, #4640]
	str x1, [x0, #1280]
	ldr x1, [x0, #4648]
	str x1, [x0, #1288]
	ldr x1, [x0, #4656]
	str x1, [x0, #1296]
	ldr x1, [x0, #4664]
	str x1, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1168]
	str x1, [x0, #5584]
	ldr x1, [x0, #1176]
	str x1, [x0, #5592]
	ldr x1, [x0, #1184]
	str x1, [x0, #5600]
	ldr x1, [x0, #1192]
	str x1, [x0, #5608]
	ldr x1, [x0, #1200]
	str x1, [x0, #5616]
	ldr x1, [x0, #1208]
	str x1, [x0, #5624]
	ldr x1, [x0, #1216]
	str x1, [x0, #5632]
	ldr x1, [x0, #1224]
	str x1, [x0, #5640]
	ldr x1, [x0, #1232]
	str x1, [x0, #5648]
	ldr x1, [x0, #1240]
	str x1, [x0, #5656]
	ldr x1, [x0, #1248]
	str x1, [x0, #5664]
	ldr x1, [x0, #1256]
	str x1, [x0, #5672]
	ldr x1, [x0, #4768]
	str x1, [x0, #1264]
	ldr x1, [x0, #4776]
	str x1, [x0, #1272]
	ldr x1, [x0, #4784]
	str x1, [x0, #1280]
	ldr x1, [x0, #4792]
	str x1, [x0, #1288]
	ldr x1, [x0, #4800]
	str x1, [x0, #1296]
	ldr x1, [x0, #4808]
	str x1, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1168]
	str x1, [x0, #5680]
	ldr x1, [x0, #1176]
	str x1, [x0, #5688]
	ldr x1, [x0, #1184]
	str x1, [x0, #5696]
	ldr x1, [x0, #1192]
	str x1, [x0, #5704]
	ldr x1, [x0, #1200]
	str x1, [x0, #5712]
	ldr x1, [x0, #1208]
	str x1, [x0, #5720]
	ldr x1, [x0, #1216]
	str x1, [x0, #5728]
	ldr x1, [x0, #1224]
	str x1, [x0, #5736]
	ldr x1, [x0, #1232]
	str x1, [x0, #5744]
	ldr x1, [x0, #1240]
	str x1, [x0, #5752]
	ldr x1, [x0, #1248]
	str x1, [x0, #5760]
	ldr x1, [x0, #1256]
	str x1, [x0, #5768]
	ldr x1, [x0, #4912]
	str x1, [x0, #1264]
	ldr x1, [x0, #4920]
	str x1, [x0, #1272]
	ldr x1, [x0, #4928]
	str x1, [x0, #1280]
	ldr x1, [x0, #4936]
	str x1, [x0, #1288]
	ldr x1, [x0, #4944]
	str x1, [x0, #1296]
	ldr x1, [x0, #4952]
	str x1, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1168]
	str x1, [x0, #5776]
	ldr x1, [x0, #1176]
	str x1, [x0, #5784]
	ldr x1, [x0, #1184]
	str x1, [x0, #5792]
	ldr x1, [x0, #1192]
	str x1, [x0, #5800]
	ldr x1, [x0, #1200]
	str x1, [x0, #5808]
	ldr x1, [x0, #1208]
	str x1, [x0, #5816]
	ldr x1, [x0, #1216]
	str x1, [x0, #5824]
	ldr x1, [x0, #1224]
	str x1, [x0, #5832]
	ldr x1, [x0, #1232]
	str x1, [x0, #5840]
	ldr x1, [x0, #1240]
	str x1, [x0, #5848]
	ldr x1, [x0, #1248]
	str x1, [x0, #5856]
	ldr x1, [x0, #1256]
	str x1, [x0, #5864]
	ldr x1, [x0, #5056]
	str x1, [x0, #1264]
	ldr x1, [x0, #5064]
	str x1, [x0, #1272]
	ldr x1, [x0, #5072]
	str x1, [x0, #1280]
	ldr x1, [x0, #5080]
	str x1, [x0, #1288]
	ldr x1, [x0, #5088]
	str x1, [x0, #1296]
	ldr x1, [x0, #5096]
	str x1, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1168]
	str x1, [x0, #5872]
	ldr x1, [x0, #1176]
	str x1, [x0, #5880]
	ldr x1, [x0, #1184]
	str x1, [x0, #5888]
	ldr x1, [x0, #1192]
	str x1, [x0, #5896]
	ldr x1, [x0, #1200]
	str x1, [x0, #5904]
	ldr x1, [x0, #1208]
	str x1, [x0, #5912]
	ldr x1, [x0, #1216]
	str x1, [x0, #5920]
	ldr x1, [x0, #1224]
	str x1, [x0, #5928]
	ldr x1, [x0, #1232]
	str x1, [x0, #5936]
	ldr x1, [x0, #1240]
	str x1, [x0, #5944]
	ldr x1, [x0, #1248]
	str x1, [x0, #5952]
	ldr x1, [x0, #1256]
	str x1, [x0, #5960]
	ldr x1, [x0, #5200]
	str x1, [x0, #1264]
	ldr x1, [x0, #5208]
	str x1, [x0, #1272]
	ldr x1, [x0, #5216]
	str x1, [x0, #1280]
	ldr x1, [x0, #5224]
	str x1, [x0, #1288]
	ldr x1, [x0, #5232]
	str x1, [x0, #1296]
	ldr x1, [x0, #5240]
	str x1, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1168]
	str x1, [x0, #5968]
	ldr x1, [x0, #1176]
	str x1, [x0, #5976]
	ldr x1, [x0, #1184]
	str x1, [x0, #5984]
	ldr x1, [x0, #1192]
	str x1, [x0, #5992]
	ldr x1, [x0, #1200]
	str x1, [x0, #6000]
	ldr x1, [x0, #1208]
	str x1, [x0, #6008]
	ldr x1, [x0, #1216]
	str x1, [x0, #6016]
	ldr x1, [x0, #1224]
	str x1, [x0, #6024]
	ldr x1, [x0, #1232]
	str x1, [x0, #6032]
	ldr x1, [x0, #1240]
	str x1, [x0, #6040]
	ldr x1, [x0, #1248]
	str x1, [x0, #6048]
	ldr x1, [x0, #1256]
	str x1, [x0, #6056]
	ldr x1, [x0, #5344]
	str x1, [x0, #1264]
	ldr x1, [x0, #5352]
	str x1, [x0, #1272]
	ldr x1, [x0, #5360]
	str x1, [x0, #1280]
	ldr x1, [x0, #5368]
	str x1, [x0, #1288]
	ldr x1, [x0, #5376]
	str x1, [x0, #1296]
	ldr x1, [x0, #5384]
	str x1, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1264, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	ldr x1, [x0, #1168]
	str x1, [x0, #6064]
	ldr x1, [x0, #1176]
	str x1, [x0, #6072]
	ldr x1, [x0, #1184]
	str x1, [x0, #6080]
	ldr x1, [x0, #1192]
	str x1, [x0, #6088]
	ldr x1, [x0, #1200]
	str x1, [x0, #6096]
	ldr x1, [x0, #1208]
	str x1, [x0, #6104]
	ldr x1, [x0, #1216]
	str x1, [x0, #6112]
	ldr x1, [x0, #1224]
	str x1, [x0, #6120]
	ldr x1, [x0, #1232]
	str x1, [x0, #6128]
	ldr x1, [x0, #1240]
	str x1, [x0, #6136]
	ldr x1, [x0, #1248]
	str x1, [x0, #6144]
	ldr x1, [x0, #1256]
	str x1, [x0, #6152]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #880]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #928]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #936]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #944]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #952]
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
	movz x19, #384, lsl #0
	add x16, x0, x19
	ldrb w2, [x16, #2704]
	cbnz x2, 28f
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
	b 29f
28:
	lsr x3, x2, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	sub x2, x2, #1
	movz x17, #96, lsl #0
	mul x17, x2, x17
	add x16, x0, x17
	ldr x4, [x16, #5392]
	str x4, [x0, #784]
	ldr x4, [x16, #5400]
	str x4, [x0, #792]
	ldr x4, [x16, #5408]
	str x4, [x0, #800]
	ldr x4, [x16, #5416]
	str x4, [x0, #808]
	ldr x4, [x16, #5424]
	str x4, [x0, #816]
	ldr x4, [x16, #5432]
	str x4, [x0, #824]
	ldr x4, [x16, #5440]
	str x4, [x0, #832]
	ldr x4, [x16, #5448]
	str x4, [x0, #840]
	ldr x4, [x16, #5456]
	str x4, [x0, #848]
	ldr x4, [x16, #5464]
	str x4, [x0, #856]
	ldr x4, [x16, #5472]
	str x4, [x0, #864]
	ldr x4, [x16, #5480]
	str x4, [x0, #872]
	movz x17, #144, lsl #0
	mul x2, x2, x17
	add x16, x0, x2
	ldr x4, [x16, #4240]
	str x4, [x0, #1024]
	ldr x4, [x16, #4248]
	str x4, [x0, #1032]
	ldr x4, [x16, #4256]
	str x4, [x0, #1040]
	ldr x4, [x16, #4264]
	str x4, [x0, #1048]
	ldr x4, [x16, #4272]
	str x4, [x0, #1056]
	ldr x4, [x16, #4280]
	str x4, [x0, #1064]
	ldr x4, [x16, #4288]
	str x4, [x0, #1072]
	ldr x4, [x16, #4296]
	str x4, [x0, #1080]
	ldr x4, [x16, #4304]
	str x4, [x0, #1088]
	ldr x4, [x16, #4312]
	str x4, [x0, #1096]
	ldr x4, [x16, #4320]
	str x4, [x0, #1104]
	ldr x4, [x16, #4328]
	str x4, [x0, #1112]
	ldr x4, [x16, #4336]
	str x4, [x0, #1120]
	ldr x4, [x16, #4344]
	str x4, [x0, #1128]
	ldr x4, [x16, #4352]
	str x4, [x0, #1136]
	ldr x4, [x16, #4360]
	str x4, [x0, #1144]
	ldr x4, [x16, #4368]
	str x4, [x0, #1152]
	ldr x4, [x16, #4376]
	str x4, [x0, #1160]
	add x16, x0, x19
	ldrb w3, [x16, #2704]
	lsr x3, x3, #7
	cbnz x3, 210f
	b 211f
210:
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
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
211:
	movz x7, #0, lsl #0
	ldr x1, [x0, #976]
	ldr x2, [x0, #984]
	orr x1, x1, x2
	ldr x2, [x0, #992]
	orr x1, x1, x2
	ldr x2, [x0, #1000]
	orr x1, x1, x2
	ldr x2, [x0, #1008]
	orr x1, x1, x2
	ldr x2, [x0, #1016]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 212f
	movz x7, #0, lsl #0
	ldr x1, [x0, #1120]
	ldr x2, [x0, #1128]
	orr x1, x1, x2
	ldr x2, [x0, #1136]
	orr x1, x1, x2
	ldr x2, [x0, #1144]
	orr x1, x1, x2
	ldr x2, [x0, #1152]
	orr x1, x1, x2
	ldr x2, [x0, #1160]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 214f
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #976, lsl #0
	movz x3, #976, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #880, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #1024, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #928, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #976, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
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
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1408]
	ldr x9, [x0, #1416]
	ldr x10, [x0, #1424]
	ldr x11, [x0, #1432]
	ldr x12, [x0, #1440]
	ldr x13, [x0, #1448]
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
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1312]
	ldr x2, [x0, #1320]
	orr x1, x1, x2
	ldr x2, [x0, #1328]
	orr x1, x1, x2
	ldr x2, [x0, #1336]
	orr x1, x1, x2
	ldr x2, [x0, #1344]
	orr x1, x1, x2
	ldr x2, [x0, #1352]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 216f
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1168, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #736, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #1216]
	subs x8, x8, x2
	ldr x2, [x0, #1224]
	sbcs x9, x9, x2
	ldr x2, [x0, #1232]
	sbcs x10, x10, x2
	ldr x2, [x0, #1240]
	sbcs x11, x11, x2
	ldr x2, [x0, #1248]
	sbcs x12, x12, x2
	ldr x2, [x0, #1256]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	ldr x2, [x0, #768]
	sbcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	mov v29.d[0], x30
	movz x1, #784, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #784]
	ldr x9, [x0, #792]
	ldr x10, [x0, #800]
	ldr x11, [x0, #808]
	ldr x12, [x0, #816]
	ldr x13, [x0, #824]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	mov v29.d[0], x30
	movz x1, #832, lsl #0
	movz x2, #976, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #832, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	b 217f
216:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1408]
	ldr x2, [x0, #1416]
	orr x1, x1, x2
	ldr x2, [x0, #1424]
	orr x1, x1, x2
	ldr x2, [x0, #1432]
	orr x1, x1, x2
	ldr x2, [x0, #1440]
	orr x1, x1, x2
	ldr x2, [x0, #1448]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 218f
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #784]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #792]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #800]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #808]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #816]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	b 219f
218:
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #976, lsl #0
	movz x3, #976, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #928, lsl #0
	movz x3, #928, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #880, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
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
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #736, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
	ldr x2, [x0, #1312]
	adds x8, x8, x2
	ldr x2, [x0, #1320]
	adcs x9, x9, x2
	ldr x2, [x0, #1328]
	adcs x10, x10, x2
	ldr x2, [x0, #1336]
	adcs x11, x11, x2
	ldr x2, [x0, #1344]
	adcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #1312]
	adds x8, x8, x2
	ldr x2, [x0, #1320]
	adcs x9, x9, x2
	ldr x2, [x0, #1328]
	adcs x10, x10, x2
	ldr x2, [x0, #1336]
	adcs x11, x11, x2
	ldr x2, [x0, #1344]
	adcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	str x11, [x0, #1288]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #832, lsl #0
	movz x2, #928, lsl #0
	movz x3, #976, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #832]
	ldr x9, [x0, #840]
	ldr x10, [x0, #848]
	ldr x11, [x0, #856]
	ldr x12, [x0, #864]
	ldr x13, [x0, #872]
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
	str x8, [x0, #832]
	str x9, [x0, #840]
	str x10, [x0, #848]
	str x11, [x0, #856]
	str x12, [x0, #864]
	str x13, [x0, #872]
	mov v29.d[0], x30
	movz x1, #736, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	ldr x2, [x0, #768]
	sbcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	mov v29.d[0], x30
	movz x1, #784, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	movz x7, #0, lsl #0
	ldr x8, [x0, #784]
	ldr x9, [x0, #792]
	ldr x10, [x0, #800]
	ldr x11, [x0, #808]
	ldr x12, [x0, #816]
	ldr x13, [x0, #824]
	ldr x2, [x0, #1216]
	subs x8, x8, x2
	ldr x2, [x0, #1224]
	sbcs x9, x9, x2
	ldr x2, [x0, #1232]
	sbcs x10, x10, x2
	ldr x2, [x0, #1240]
	sbcs x11, x11, x2
	ldr x2, [x0, #1248]
	sbcs x12, x12, x2
	ldr x2, [x0, #1256]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
219:
217:
	b 215f
214:
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
215:
	b 213f
212:
	ldr x1, [x0, #1024]
	str x1, [x0, #736]
	ldr x1, [x0, #1032]
	str x1, [x0, #744]
	ldr x1, [x0, #1040]
	str x1, [x0, #752]
	ldr x1, [x0, #1048]
	str x1, [x0, #760]
	ldr x1, [x0, #1056]
	str x1, [x0, #768]
	ldr x1, [x0, #1064]
	str x1, [x0, #776]
	ldr x1, [x0, #1072]
	str x1, [x0, #784]
	ldr x1, [x0, #1080]
	str x1, [x0, #792]
	ldr x1, [x0, #1088]
	str x1, [x0, #800]
	ldr x1, [x0, #1096]
	str x1, [x0, #808]
	ldr x1, [x0, #1104]
	str x1, [x0, #816]
	ldr x1, [x0, #1112]
	str x1, [x0, #824]
	ldr x1, [x0, #1120]
	str x1, [x0, #832]
	ldr x1, [x0, #1128]
	str x1, [x0, #840]
	ldr x1, [x0, #1136]
	str x1, [x0, #848]
	ldr x1, [x0, #1144]
	str x1, [x0, #856]
	ldr x1, [x0, #1152]
	str x1, [x0, #864]
	ldr x1, [x0, #1160]
	str x1, [x0, #872]
213:
29:
	add x16, x0, x19
	add x16, x16, x19
	ldrb w2, [x16, #3152]
	ldrb w3, [x16, #3153]
	cbnz x2, 220f
	b 221f
220:
	lsr x3, x3, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	sub x2, x2, #1
	movz x3, #192, lsl #0
	mul x2, x2, x3
	adrp x16, {VG_P384_GTAB}
	add x16, x16, {VG_P384_GTAB}
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #1024]
	ldr x4, [x16, #8]
	str x4, [x0, #1032]
	ldr x4, [x16, #16]
	str x4, [x0, #1040]
	ldr x4, [x16, #24]
	str x4, [x0, #1048]
	ldr x4, [x16, #32]
	str x4, [x0, #1056]
	ldr x4, [x16, #40]
	str x4, [x0, #1064]
	ldr x4, [x16, #48]
	str x4, [x0, #1072]
	ldr x4, [x16, #56]
	str x4, [x0, #1080]
	ldr x4, [x16, #64]
	str x4, [x0, #1088]
	ldr x4, [x16, #72]
	str x4, [x0, #1096]
	ldr x4, [x16, #80]
	str x4, [x0, #1104]
	ldr x4, [x16, #88]
	str x4, [x0, #1112]
	ldr x1, [x0, #304]
	str x1, [x0, #1120]
	ldr x1, [x0, #312]
	str x1, [x0, #1128]
	ldr x1, [x0, #320]
	str x1, [x0, #1136]
	ldr x1, [x0, #328]
	str x1, [x0, #1144]
	ldr x1, [x0, #336]
	str x1, [x0, #1152]
	ldr x1, [x0, #344]
	str x1, [x0, #1160]
	add x16, x0, x19
	add x16, x16, x19
	ldrb w3, [x16, #3153]
	lsr x3, x3, #7
	cbnz x3, 222f
	b 223f
222:
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
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
223:
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
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 224f
	ldr x1, [x0, #736]
	str x1, [x0, #1264]
	ldr x1, [x0, #744]
	str x1, [x0, #1272]
	ldr x1, [x0, #752]
	str x1, [x0, #1280]
	ldr x1, [x0, #760]
	str x1, [x0, #1288]
	ldr x1, [x0, #768]
	str x1, [x0, #1296]
	ldr x1, [x0, #776]
	str x1, [x0, #1304]
	ldr x1, [x0, #784]
	str x1, [x0, #1360]
	ldr x1, [x0, #792]
	str x1, [x0, #1368]
	ldr x1, [x0, #800]
	str x1, [x0, #1376]
	ldr x1, [x0, #808]
	str x1, [x0, #1384]
	ldr x1, [x0, #816]
	str x1, [x0, #1392]
	ldr x1, [x0, #824]
	str x1, [x0, #1400]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #832, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #1024, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
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
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1408]
	ldr x9, [x0, #1416]
	ldr x10, [x0, #1424]
	ldr x11, [x0, #1432]
	ldr x12, [x0, #1440]
	ldr x13, [x0, #1448]
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
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1312]
	ldr x2, [x0, #1320]
	orr x1, x1, x2
	ldr x2, [x0, #1328]
	orr x1, x1, x2
	ldr x2, [x0, #1336]
	orr x1, x1, x2
	ldr x2, [x0, #1344]
	orr x1, x1, x2
	ldr x2, [x0, #1352]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 226f
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1168, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #880, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
	ldr x2, [x0, #1216]
	subs x8, x8, x2
	ldr x2, [x0, #1224]
	sbcs x9, x9, x2
	ldr x2, [x0, #1232]
	sbcs x10, x10, x2
	ldr x2, [x0, #1240]
	sbcs x11, x11, x2
	ldr x2, [x0, #1248]
	sbcs x12, x12, x2
	ldr x2, [x0, #1256]
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
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
	mov v29.d[0], x30
	movz x1, #928, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #928, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #928]
	ldr x9, [x0, #936]
	ldr x10, [x0, #944]
	ldr x11, [x0, #952]
	ldr x12, [x0, #960]
	ldr x13, [x0, #968]
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
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
	mov v29.d[0], x30
	movz x1, #976, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	b 227f
226:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1408]
	ldr x2, [x0, #1416]
	orr x1, x1, x2
	ldr x2, [x0, #1424]
	orr x1, x1, x2
	ldr x2, [x0, #1432]
	orr x1, x1, x2
	ldr x2, [x0, #1440]
	orr x1, x1, x2
	ldr x2, [x0, #1448]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 228f
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #880]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #928]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #936]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #944]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #952]
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
	b 229f
228:
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #832, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #784, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #736, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #880, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
	ldr x2, [x0, #1312]
	adds x8, x8, x2
	ldr x2, [x0, #1320]
	adcs x9, x9, x2
	ldr x2, [x0, #1328]
	adcs x10, x10, x2
	ldr x2, [x0, #1336]
	adcs x11, x11, x2
	ldr x2, [x0, #1344]
	adcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
	ldr x2, [x0, #1312]
	adds x8, x8, x2
	ldr x2, [x0, #1320]
	adcs x9, x9, x2
	ldr x2, [x0, #1328]
	adcs x10, x10, x2
	ldr x2, [x0, #1336]
	adcs x11, x11, x2
	ldr x2, [x0, #1344]
	adcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	str x11, [x0, #1288]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #976, lsl #0
	movz x2, #784, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #976]
	ldr x9, [x0, #984]
	ldr x10, [x0, #992]
	ldr x11, [x0, #1000]
	ldr x12, [x0, #1008]
	ldr x13, [x0, #1016]
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
	movz x1, #880, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
	mov v29.d[0], x30
	movz x1, #928, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #928, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	movz x7, #0, lsl #0
	ldr x8, [x0, #928]
	ldr x9, [x0, #936]
	ldr x10, [x0, #944]
	ldr x11, [x0, #952]
	ldr x12, [x0, #960]
	ldr x13, [x0, #968]
	ldr x2, [x0, #1216]
	subs x8, x8, x2
	ldr x2, [x0, #1224]
	sbcs x9, x9, x2
	ldr x2, [x0, #1232]
	sbcs x10, x10, x2
	ldr x2, [x0, #1240]
	sbcs x11, x11, x2
	ldr x2, [x0, #1248]
	sbcs x12, x12, x2
	ldr x2, [x0, #1256]
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
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
229:
227:
	b 225f
224:
	ldr x1, [x0, #1024]
	str x1, [x0, #880]
	ldr x1, [x0, #1032]
	str x1, [x0, #888]
	ldr x1, [x0, #1040]
	str x1, [x0, #896]
	ldr x1, [x0, #1048]
	str x1, [x0, #904]
	ldr x1, [x0, #1056]
	str x1, [x0, #912]
	ldr x1, [x0, #1064]
	str x1, [x0, #920]
	ldr x1, [x0, #1072]
	str x1, [x0, #928]
	ldr x1, [x0, #1080]
	str x1, [x0, #936]
	ldr x1, [x0, #1088]
	str x1, [x0, #944]
	ldr x1, [x0, #1096]
	str x1, [x0, #952]
	ldr x1, [x0, #1104]
	str x1, [x0, #960]
	ldr x1, [x0, #1112]
	str x1, [x0, #968]
	ldr x1, [x0, #1120]
	str x1, [x0, #976]
	ldr x1, [x0, #1128]
	str x1, [x0, #984]
	ldr x1, [x0, #1136]
	str x1, [x0, #992]
	ldr x1, [x0, #1144]
	str x1, [x0, #1000]
	ldr x1, [x0, #1152]
	str x1, [x0, #1008]
	ldr x1, [x0, #1160]
	str x1, [x0, #1016]
225:
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
221:
230:
	sub x19, x19, #1
	ldr x1, [x0, #832]
	ldr x2, [x0, #840]
	ldr x3, [x0, #848]
	ldr x4, [x0, #856]
	ldr x5, [x0, #864]
	ldr x6, [x0, #872]
	mul x7, x1, x2
	mul x8, x1, x3
	mul x9, x1, x4
	movz x10, #0, lsl #0
	mul x11, x1, x5
	adds x7, x10, x7
	mul x12, x1, x6
	adcs x8, x10, x8
	umulh x13, x1, x6
	adcs x9, x10, x9
	umulh x14, x1, x2
	adcs x11, x10, x11
	umulh x15, x1, x3
	adcs x12, x10, x12
	umulh x16, x1, x4
	adcs x13, x10, x13
	umulh x17, x1, x5
	adds x8, x8, x14
	adcs x9, x9, x15
	mul x14, x2, x3
	adcs x11, x11, x16
	mul x15, x2, x4
	adcs x12, x12, x17
	mul x16, x2, x5
	adcs x13, x13, x10
	mul x17, x2, x6
	adds x9, x9, x14
	umulh x14, x2, x6
	adcs x11, x11, x15
	umulh x15, x2, x3
	adcs x12, x12, x16
	umulh x16, x2, x4
	adcs x13, x13, x17
	umulh x17, x2, x5
	adcs x14, x10, x14
	adds x11, x11, x15
	mul x15, x3, x4
	adcs x12, x12, x16
	mul x16, x3, x5
	adcs x13, x13, x17
	mul x17, x3, x6
	adcs x14, x14, x10
	umulh x21, x3, x6
	adds x12, x12, x15
	umulh x15, x3, x4
	adcs x13, x13, x16
	umulh x16, x3, x5
	adcs x14, x14, x17
	adcs x17, x10, x21
	mul x21, x4, x5
	adds x13, x13, x15
	mul x15, x4, x6
	adcs x14, x14, x16
	umulh x16, x4, x6
	adcs x17, x17, x10
	umulh x22, x4, x5
	adds x14, x14, x21
	adcs x15, x17, x15
	mul x17, x5, x6
	adcs x16, x10, x16
	umulh x21, x5, x6
	adds x15, x15, x22
	adcs x16, x16, x10
	adds x16, x16, x17
	adcs x17, x10, x21
	adds x21, x10, x10
	adcs x7, x7, x7
	adcs x8, x8, x8
	adcs x9, x9, x9
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adcs x15, x15, x15
	mul x22, x1, x1
	adcs x16, x16, x16
	umulh x23, x1, x1
	adcs x17, x17, x17
	mul x24, x2, x2
	adcs x25, x10, x10
	str x1, [x0, #1024]
	umulh x1, x2, x2
	adds x21, x21, x22
	mul x22, x3, x3
	adcs x7, x7, x23
	umulh x23, x3, x3
	adcs x8, x8, x24
	mul x24, x4, x4
	adcs x1, x9, x1
	umulh x9, x4, x4
	str x4, [x0, #1032]
	ldr x4, [x0, #64]
	adcs x11, x11, x22
	mul x22, x5, x5
	adcs x12, x12, x23
	umulh x23, x5, x5
	adcs x13, x13, x24
	mul x24, x6, x6
	str x5, [x0, #1040]
	lsl x5, x21, #32
	adcs x9, x14, x9
	umulh x14, x6, x6
	str x6, [x0, #1048]
	sub x6, x10, x4
	add x5, x5, x21
	adcs x15, x15, x22
	umulh x21, x6, x5
	mul x22, x4, x5
	adcs x16, x16, x23
	umulh x23, x4, x5
	adcs x17, x17, x24
	adcs x14, x25, x14
	adds x21, x21, x22
	adcs x22, x23, x5
	adc x23, x10, x10
	subs x7, x7, x21
	lsl x21, x7, #32
	sbcs x8, x8, x22
	add x7, x21, x7
	sbcs x1, x1, x23
	umulh x21, x6, x7
	mul x22, x4, x7
	sbcs x11, x11, x10
	umulh x23, x4, x7
	sbcs x12, x12, x10
	sbc x5, x5, x10
	adds x21, x21, x22
	adcs x22, x23, x7
	adc x23, x10, x10
	subs x8, x8, x21
	lsl x21, x8, #32
	sbcs x1, x1, x22
	add x8, x21, x8
	sbcs x11, x11, x23
	umulh x21, x6, x8
	mul x22, x4, x8
	sbcs x12, x12, x10
	umulh x23, x4, x8
	sbcs x5, x5, x10
	sbc x7, x7, x10
	adds x21, x21, x22
	adcs x22, x23, x8
	adc x23, x10, x10
	subs x1, x1, x21
	lsl x21, x1, #32
	sbcs x11, x11, x22
	add x1, x21, x1
	sbcs x12, x12, x23
	umulh x21, x6, x1
	mul x22, x4, x1
	sbcs x5, x5, x10
	umulh x23, x4, x1
	sbcs x7, x7, x10
	sbc x8, x8, x10
	adds x21, x21, x22
	adcs x22, x23, x1
	adc x23, x10, x10
	subs x11, x11, x21
	lsl x21, x11, #32
	sbcs x12, x12, x22
	add x11, x21, x11
	sbcs x5, x5, x23
	umulh x21, x6, x11
	mul x22, x4, x11
	sbcs x7, x7, x10
	umulh x23, x4, x11
	sbcs x8, x8, x10
	sbc x1, x1, x10
	adds x21, x21, x22
	adcs x22, x23, x11
	adc x23, x10, x10
	subs x12, x12, x21
	lsl x21, x12, #32
	sbcs x5, x5, x22
	add x12, x21, x12
	sbcs x7, x7, x23
	umulh x6, x6, x12
	mul x21, x4, x12
	sbcs x8, x8, x10
	umulh x22, x4, x12
	sbcs x1, x1, x10
	sbc x11, x11, x10
	adds x6, x6, x21
	adcs x21, x22, x12
	adc x22, x10, x10
	subs x5, x5, x6
	sbcs x6, x7, x21
	sbcs x7, x8, x22
	sbcs x1, x1, x10
	sbcs x8, x11, x10
	sbc x11, x12, x10
	adds x5, x5, x13
	adcs x6, x6, x9
	adcs x7, x7, x15
	adcs x1, x1, x16
	adcs x8, x8, x17
	ldr x9, [x0, #72]
	adcs x11, x11, x14
	ldr x12, [x0, #80]
	adc x13, x10, x10
	ldr x14, [x0, #88]
	subs x15, x5, x4
	ldr x16, [x0, #96]
	ldr x17, [x0, #784]
	ldr x21, [x0, #792]
	sbcs x22, x6, x9
	ldr x23, [x0, #104]
	ldr x24, [x0, #800]
	sbcs x25, x7, x12
	str x3, [x0, #1056]
	ldr x3, [x0, #808]
	str x2, [x0, #1064]
	sbcs x2, x1, x14
	str x14, [x0, #1072]
	ldr x14, [x0, #816]
	str x12, [x0, #1080]
	sbcs x12, x8, x16
	str x16, [x0, #1088]
	ldr x16, [x0, #824]
	str x9, [x0, #1096]
	mul x9, x17, x21
	str x4, [x0, #1104]
	sbcs x4, x11, x23
	sbcs x13, x13, x10
	csel x5, x15, x5, hs
	csel x6, x22, x6, hs
	csel x7, x25, x7, hs
	csel x1, x2, x1, hs
	csel x2, x12, x8, hs
	csel x4, x4, x11, hs
	mul x8, x17, x24
	adds x9, x10, x9
	adcs x8, x10, x8
	mul x11, x17, x3
	adcs x11, x10, x11
	mul x12, x17, x14
	adcs x12, x10, x12
	mul x13, x17, x16
	adcs x13, x10, x13
	umulh x15, x17, x16
	adcs x15, x10, x15
	umulh x22, x17, x21
	adds x8, x8, x22
	umulh x22, x17, x24
	adcs x11, x11, x22
	umulh x22, x17, x3
	adcs x12, x12, x22
	umulh x22, x17, x14
	adcs x13, x13, x22
	adcs x15, x15, x10
	mul x22, x21, x24
	adds x11, x11, x22
	mul x22, x21, x3
	adcs x12, x12, x22
	mul x22, x21, x14
	adcs x13, x13, x22
	mul x22, x21, x16
	adcs x15, x15, x22
	umulh x22, x21, x16
	adcs x22, x10, x22
	umulh x25, x21, x24
	adds x12, x12, x25
	umulh x25, x21, x3
	adcs x13, x13, x25
	umulh x25, x21, x14
	adcs x15, x15, x25
	adcs x22, x22, x10
	mul x25, x24, x3
	adds x13, x13, x25
	mul x25, x24, x14
	adcs x15, x15, x25
	mul x25, x24, x16
	adcs x22, x22, x25
	umulh x25, x24, x16
	adcs x25, x10, x25
	str x4, [x0, #1112]
	umulh x4, x24, x3
	adds x4, x15, x4
	umulh x15, x24, x14
	adcs x15, x22, x15
	adcs x22, x25, x10
	mul x25, x3, x14
	adds x15, x15, x25
	mul x25, x3, x16
	adcs x22, x22, x25
	umulh x25, x3, x16
	adcs x25, x10, x25
	str x2, [x0, #1120]
	umulh x2, x3, x14
	adds x2, x22, x2
	adcs x22, x25, x10
	mul x25, x14, x16
	adds x22, x22, x25
	umulh x25, x14, x16
	adcs x25, x10, x25
	str x1, [x0, #1128]
	adds x1, x10, x10
	adcs x9, x9, x9
	adcs x8, x8, x8
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x4, x4, x4
	adcs x15, x15, x15
	adcs x2, x2, x2
	adcs x22, x22, x22
	adcs x25, x25, x25
	str x7, [x0, #1136]
	mul x7, x17, x17
	str x6, [x0, #1144]
	umulh x6, x17, x17
	str x17, [x0, #1152]
	mul x17, x21, x21
	str x5, [x0, #1160]
	adcs x5, x10, x10
	adds x1, x1, x7
	adcs x6, x9, x6
	adcs x7, x8, x17
	umulh x8, x21, x21
	adcs x8, x11, x8
	mul x9, x24, x24
	adcs x9, x12, x9
	umulh x11, x24, x24
	adcs x11, x13, x11
	mul x12, x3, x3
	adcs x4, x4, x12
	umulh x12, x3, x3
	adcs x12, x15, x12
	mul x13, x14, x14
	adcs x2, x2, x13
	umulh x13, x14, x14
	adcs x13, x22, x13
	mul x15, x16, x16
	adcs x15, x25, x15
	lsl x17, x1, #32
	add x1, x17, x1
	umulh x17, x16, x16
	adcs x5, x5, x17
	ldr x17, [x0, #1104]
	sub x22, x10, x17
	umulh x25, x22, x1
	str x16, [x0, #1168]
	mul x16, x17, x1
	adds x16, x25, x16
	umulh x25, x17, x1
	adcs x25, x25, x1
	str x14, [x0, #1176]
	adc x14, x10, x10
	subs x6, x6, x16
	sbcs x7, x7, x25
	sbcs x8, x8, x14
	sbcs x9, x9, x10
	sbcs x11, x11, x10
	sbc x1, x1, x10
	lsl x14, x6, #32
	add x6, x14, x6
	umulh x14, x22, x6
	mul x16, x17, x6
	adds x14, x14, x16
	umulh x16, x17, x6
	adcs x16, x16, x6
	adc x25, x10, x10
	subs x7, x7, x14
	sbcs x8, x8, x16
	sbcs x9, x9, x25
	sbcs x11, x11, x10
	sbcs x1, x1, x10
	sbc x6, x6, x10
	lsl x14, x7, #32
	add x7, x14, x7
	umulh x14, x22, x7
	mul x16, x17, x7
	adds x14, x14, x16
	umulh x16, x17, x7
	adcs x16, x16, x7
	adc x25, x10, x10
	subs x8, x8, x14
	sbcs x9, x9, x16
	sbcs x11, x11, x25
	sbcs x1, x1, x10
	sbcs x6, x6, x10
	sbc x7, x7, x10
	lsl x14, x8, #32
	add x8, x14, x8
	umulh x14, x22, x8
	mul x16, x17, x8
	adds x14, x14, x16
	umulh x16, x17, x8
	adcs x16, x16, x8
	adc x25, x10, x10
	subs x9, x9, x14
	sbcs x11, x11, x16
	sbcs x1, x1, x25
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbc x8, x8, x10
	lsl x14, x9, #32
	add x9, x14, x9
	umulh x14, x22, x9
	mul x16, x17, x9
	adds x14, x14, x16
	umulh x16, x17, x9
	adcs x16, x16, x9
	adc x25, x10, x10
	subs x11, x11, x14
	sbcs x1, x1, x16
	sbcs x6, x6, x25
	sbcs x7, x7, x10
	sbcs x8, x8, x10
	sbc x9, x9, x10
	lsl x14, x11, #32
	add x11, x14, x11
	umulh x14, x22, x11
	mul x16, x17, x11
	adds x14, x14, x16
	umulh x16, x17, x11
	adcs x16, x16, x11
	adc x22, x10, x10
	subs x1, x1, x14
	sbcs x6, x6, x16
	sbcs x7, x7, x22
	sbcs x8, x8, x10
	sbcs x9, x9, x10
	sbc x11, x11, x10
	adds x1, x1, x4
	adcs x4, x6, x12
	adcs x2, x7, x2
	adcs x6, x8, x13
	adcs x7, x9, x15
	adcs x5, x11, x5
	adc x8, x10, x10
	subs x9, x1, x17
	ldr x11, [x0, #1096]
	sbcs x12, x4, x11
	ldr x13, [x0, #1080]
	sbcs x14, x2, x13
	ldr x15, [x0, #1072]
	sbcs x16, x6, x15
	ldr x22, [x0, #1088]
	sbcs x25, x7, x22
	str x3, [x0, #1184]
	ldr x3, [x0, #736]
	str x24, [x0, #1192]
	sbcs x24, x5, x23
	sbcs x8, x8, x10
	csel x1, x9, x1, hs
	csel x4, x12, x4, hs
	csel x2, x14, x2, hs
	csel x6, x16, x6, hs
	csel x7, x25, x7, hs
	csel x5, x24, x5, hs
	ldr x8, [x0, #744]
	ldr x9, [x0, #752]
	ldr x12, [x0, #760]
	ldr x14, [x0, #768]
	ldr x16, [x0, #1160]
	adds x24, x3, x16
	ldr x25, [x0, #776]
	str x5, [x0, #1200]
	ldr x5, [x0, #1144]
	str x7, [x0, #1208]
	adcs x7, x8, x5
	str x6, [x0, #1216]
	ldr x6, [x0, #1136]
	str x2, [x0, #1224]
	adcs x2, x9, x6
	str x4, [x0, #1232]
	ldr x4, [x0, #1128]
	str x1, [x0, #1240]
	adcs x1, x12, x4
	str x21, [x0, #1248]
	ldr x21, [x0, #1120]
	adcs x4, x14, x21
	str x14, [x0, #1256]
	ldr x14, [x0, #1112]
	adcs x21, x25, x14
	adc x14, x10, x10
	str x25, [x0, #1264]
	subs x25, x24, x17
	sbcs x17, x7, x11
	sbcs x11, x2, x13
	sbcs x13, x1, x15
	sbcs x15, x4, x22
	sbcs x22, x21, x23
	sbcs x14, x14, x10
	csel x14, x25, x24, hs
	csel x7, x17, x7, hs
	csel x2, x11, x2, hs
	csel x1, x13, x1, hs
	csel x4, x15, x4, hs
	csel x11, x22, x21, hs
	subs x13, x3, x16
	sbcs x15, x8, x5
	sbcs x17, x9, x6
	ldr x21, [x0, #1128]
	sbcs x22, x12, x21
	ldr x24, [x0, #1256]
	ldr x25, [x0, #1120]
	sbcs x21, x24, x25
	ldr x25, [x0, #1264]
	ldr x6, [x0, #1112]
	sbcs x5, x25, x6
	sbc x6, x10, x10
	ldr x16, [x0, #1104]
	and x25, x16, x6
	adds x13, x13, x25
	ldr x25, [x0, #1096]
	and x24, x25, x6
	adcs x15, x15, x24
	ldr x24, [x0, #1080]
	str x12, [x0, #1272]
	and x12, x24, x6
	adcs x12, x17, x12
	ldr x17, [x0, #1072]
	str x9, [x0, #1280]
	and x9, x17, x6
	adcs x9, x22, x9
	mul x22, x14, x13
	str x8, [x0, #1288]
	ldr x8, [x0, #1088]
	str x3, [x0, #1296]
	and x3, x8, x6
	adcs x3, x21, x3
	and x6, x23, x6
	adcs x5, x5, x6
	adds x6, x10, x22
	mul x21, x14, x15
	adcs x21, x10, x21
	mul x22, x14, x12
	adcs x22, x10, x22
	str x23, [x0, #1304]
	mul x23, x14, x9
	adcs x23, x10, x23
	mul x8, x14, x3
	adcs x8, x10, x8
	mul x17, x14, x5
	adcs x17, x10, x17
	umulh x24, x14, x5
	adcs x24, x10, x24
	umulh x25, x14, x13
	adds x21, x21, x25
	umulh x25, x14, x15
	adcs x22, x22, x25
	umulh x25, x14, x12
	adcs x23, x23, x25
	umulh x25, x14, x9
	adcs x8, x8, x25
	umulh x14, x14, x3
	adcs x14, x17, x14
	adcs x17, x24, x10
	mul x24, x7, x13
	adds x21, x21, x24
	mul x24, x7, x15
	adcs x22, x22, x24
	mul x24, x7, x12
	adcs x23, x23, x24
	mul x24, x7, x9
	adcs x8, x8, x24
	mul x24, x7, x3
	adcs x14, x14, x24
	mul x24, x7, x5
	adcs x17, x17, x24
	umulh x24, x7, x5
	adcs x24, x10, x24
	umulh x25, x7, x13
	adds x22, x22, x25
	umulh x25, x7, x15
	adcs x23, x23, x25
	umulh x25, x7, x12
	adcs x8, x8, x25
	umulh x25, x7, x9
	adcs x14, x14, x25
	umulh x7, x7, x3
	adcs x7, x17, x7
	adcs x17, x24, x10
	mul x24, x2, x13
	adds x22, x22, x24
	mul x24, x2, x15
	adcs x23, x23, x24
	mul x24, x2, x12
	adcs x8, x8, x24
	mul x24, x2, x9
	adcs x14, x14, x24
	mul x24, x2, x3
	adcs x7, x7, x24
	mul x24, x2, x5
	adcs x17, x17, x24
	umulh x24, x2, x5
	adcs x24, x10, x24
	umulh x25, x2, x13
	adds x23, x23, x25
	umulh x25, x2, x15
	adcs x8, x8, x25
	umulh x25, x2, x12
	adcs x14, x14, x25
	umulh x25, x2, x9
	adcs x7, x7, x25
	umulh x2, x2, x3
	adcs x2, x17, x2
	adcs x17, x24, x10
	mul x24, x1, x13
	adds x23, x23, x24
	mul x24, x1, x15
	adcs x8, x8, x24
	mul x24, x1, x12
	adcs x14, x14, x24
	mul x24, x1, x9
	adcs x7, x7, x24
	mul x24, x1, x3
	adcs x2, x2, x24
	mul x24, x1, x5
	adcs x17, x17, x24
	umulh x24, x1, x5
	adcs x24, x10, x24
	umulh x25, x1, x13
	adds x8, x8, x25
	umulh x25, x1, x15
	adcs x14, x14, x25
	umulh x25, x1, x12
	adcs x7, x7, x25
	umulh x25, x1, x9
	adcs x2, x2, x25
	umulh x1, x1, x3
	adcs x1, x17, x1
	adcs x17, x24, x10
	mul x24, x4, x13
	adds x8, x8, x24
	mul x24, x4, x15
	adcs x14, x14, x24
	mul x24, x4, x12
	adcs x7, x7, x24
	mul x24, x4, x9
	adcs x2, x2, x24
	mul x24, x4, x3
	adcs x1, x1, x24
	mul x24, x4, x5
	adcs x17, x17, x24
	umulh x24, x4, x5
	adcs x24, x10, x24
	umulh x25, x4, x13
	adds x14, x14, x25
	umulh x25, x4, x15
	adcs x7, x7, x25
	umulh x25, x4, x12
	adcs x2, x2, x25
	umulh x25, x4, x9
	adcs x1, x1, x25
	umulh x4, x4, x3
	adcs x4, x17, x4
	adcs x17, x24, x10
	mul x24, x11, x13
	adds x14, x14, x24
	umulh x13, x11, x13
	mul x24, x11, x15
	adcs x7, x7, x24
	umulh x15, x11, x15
	mul x24, x11, x12
	adcs x2, x2, x24
	umulh x12, x11, x12
	mul x24, x11, x9
	adcs x1, x1, x24
	umulh x9, x11, x9
	mul x24, x11, x3
	adcs x4, x4, x24
	umulh x3, x11, x3
	mul x24, x11, x5
	umulh x5, x11, x5
	adcs x11, x17, x24
	adcs x5, x10, x5
	adds x7, x7, x13
	adcs x2, x2, x15
	adcs x1, x1, x12
	adcs x4, x4, x9
	adcs x3, x11, x3
	adcs x5, x5, x10
	lsl x9, x6, #32
	add x6, x9, x6
	sub x9, x10, x16
	umulh x11, x9, x6
	mul x12, x16, x6
	adds x11, x11, x12
	umulh x12, x16, x6
	adcs x12, x12, x6
	adc x13, x10, x10
	subs x11, x21, x11
	sbcs x12, x22, x12
	sbcs x13, x23, x13
	sbcs x8, x8, x10
	sbcs x14, x14, x10
	sbc x6, x6, x10
	lsl x15, x11, #32
	add x11, x15, x11
	umulh x15, x9, x11
	mul x17, x16, x11
	adds x15, x15, x17
	umulh x17, x16, x11
	adcs x17, x17, x11
	adc x21, x10, x10
	subs x12, x12, x15
	sbcs x13, x13, x17
	sbcs x8, x8, x21
	sbcs x14, x14, x10
	sbcs x6, x6, x10
	sbc x11, x11, x10
	lsl x15, x12, #32
	add x12, x15, x12
	umulh x15, x9, x12
	mul x17, x16, x12
	adds x15, x15, x17
	umulh x17, x16, x12
	adcs x17, x17, x12
	adc x21, x10, x10
	subs x13, x13, x15
	sbcs x8, x8, x17
	sbcs x14, x14, x21
	sbcs x6, x6, x10
	sbcs x11, x11, x10
	sbc x12, x12, x10
	lsl x15, x13, #32
	add x13, x15, x13
	umulh x15, x9, x13
	mul x17, x16, x13
	adds x15, x15, x17
	umulh x17, x16, x13
	adcs x17, x17, x13
	adc x21, x10, x10
	subs x8, x8, x15
	sbcs x14, x14, x17
	sbcs x6, x6, x21
	sbcs x11, x11, x10
	sbcs x12, x12, x10
	sbc x13, x13, x10
	lsl x15, x8, #32
	add x8, x15, x8
	umulh x15, x9, x8
	mul x17, x16, x8
	adds x15, x15, x17
	umulh x17, x16, x8
	adcs x17, x17, x8
	adc x21, x10, x10
	subs x14, x14, x15
	sbcs x6, x6, x17
	sbcs x11, x11, x21
	sbcs x12, x12, x10
	sbcs x13, x13, x10
	sbc x8, x8, x10
	lsl x15, x14, #32
	add x14, x15, x14
	umulh x9, x9, x14
	mul x15, x16, x14
	adds x9, x9, x15
	umulh x15, x16, x14
	adcs x15, x15, x14
	adc x17, x10, x10
	subs x6, x6, x9
	sbcs x9, x11, x15
	sbcs x11, x12, x17
	sbcs x12, x13, x10
	sbcs x8, x8, x10
	sbc x13, x14, x10
	adds x6, x6, x7
	adcs x2, x9, x2
	adcs x1, x11, x1
	adcs x4, x12, x4
	adcs x3, x8, x3
	adcs x5, x13, x5
	adc x7, x10, x10
	subs x8, x6, x16
	ldr x9, [x0, #1096]
	sbcs x11, x2, x9
	ldr x12, [x0, #1080]
	sbcs x13, x1, x12
	ldr x14, [x0, #1072]
	sbcs x15, x4, x14
	ldr x17, [x0, #1088]
	sbcs x21, x3, x17
	ldr x22, [x0, #1304]
	sbcs x23, x5, x22
	sbcs x7, x7, x10
	csel x6, x8, x6, hs
	csel x2, x11, x2, hs
	csel x1, x13, x1, hs
	csel x4, x15, x4, hs
	csel x3, x21, x3, hs
	csel x5, x23, x5, hs
	ldr x7, [x0, #1152]
	ldr x8, [x0, #1024]
	adds x7, x7, x8
	ldr x8, [x0, #1248]
	ldr x11, [x0, #1064]
	adcs x8, x8, x11
	ldr x11, [x0, #1192]
	ldr x13, [x0, #1056]
	adcs x11, x11, x13
	ldr x13, [x0, #1184]
	ldr x15, [x0, #1032]
	adcs x13, x13, x15
	ldr x15, [x0, #1176]
	ldr x21, [x0, #1040]
	adcs x15, x15, x21
	ldr x21, [x0, #1168]
	ldr x23, [x0, #1048]
	adcs x21, x21, x23
	adc x23, x10, x10
	subs x24, x7, x16
	sbcs x25, x8, x9
	sbcs x9, x11, x12
	sbcs x12, x13, x14
	sbcs x14, x15, x17
	mul x17, x6, x2
	sbcs x16, x21, x22
	sbcs x23, x23, x10
	csel x7, x24, x7, hs
	csel x8, x25, x8, hs
	csel x9, x9, x11, hs
	csel x11, x12, x13, hs
	csel x12, x14, x15, hs
	csel x13, x16, x21, hs
	adds x14, x10, x17
	mul x15, x6, x1
	adcs x15, x10, x15
	mul x16, x6, x4
	adcs x16, x10, x16
	mul x17, x6, x3
	adcs x17, x10, x17
	mul x21, x6, x5
	adcs x21, x10, x21
	umulh x23, x6, x5
	adcs x23, x10, x23
	umulh x24, x6, x2
	adds x15, x15, x24
	umulh x24, x6, x1
	adcs x16, x16, x24
	umulh x24, x6, x4
	adcs x17, x17, x24
	umulh x24, x6, x3
	adcs x21, x21, x24
	adcs x23, x23, x10
	mul x24, x2, x1
	adds x16, x16, x24
	mul x24, x2, x4
	adcs x17, x17, x24
	mul x24, x2, x3
	adcs x21, x21, x24
	mul x24, x2, x5
	adcs x23, x23, x24
	umulh x24, x2, x5
	adcs x24, x10, x24
	umulh x25, x2, x1
	adds x17, x17, x25
	umulh x25, x2, x4
	adcs x21, x21, x25
	umulh x25, x2, x3
	adcs x23, x23, x25
	adcs x24, x24, x10
	mul x25, x1, x4
	adds x21, x21, x25
	mul x25, x1, x3
	adcs x23, x23, x25
	mul x25, x1, x5
	adcs x24, x24, x25
	umulh x25, x1, x5
	adcs x25, x10, x25
	str x13, [x0, #1024]
	umulh x13, x1, x4
	adds x13, x23, x13
	umulh x23, x1, x3
	adcs x23, x24, x23
	adcs x24, x25, x10
	mul x25, x4, x3
	adds x23, x23, x25
	mul x25, x4, x5
	adcs x24, x24, x25
	umulh x25, x4, x5
	adcs x25, x10, x25
	str x12, [x0, #1032]
	umulh x12, x4, x3
	adds x12, x24, x12
	adcs x24, x25, x10
	mul x25, x3, x5
	adds x24, x24, x25
	umulh x25, x3, x5
	adcs x25, x10, x25
	str x11, [x0, #1040]
	adds x11, x10, x10
	adcs x14, x14, x14
	adcs x15, x15, x15
	adcs x16, x16, x16
	adcs x17, x17, x17
	adcs x21, x21, x21
	adcs x13, x13, x13
	adcs x23, x23, x23
	adcs x12, x12, x12
	adcs x24, x24, x24
	adcs x25, x25, x25
	str x9, [x0, #1048]
	mul x9, x6, x6
	str x7, [x0, #1056]
	umulh x7, x6, x6
	str x6, [x0, #1064]
	mul x6, x2, x2
	str x8, [x0, #1152]
	adcs x8, x10, x10
	adds x9, x11, x9
	adcs x7, x14, x7
	adcs x6, x15, x6
	umulh x11, x2, x2
	adcs x11, x16, x11
	mul x14, x1, x1
	adcs x14, x17, x14
	umulh x15, x1, x1
	adcs x15, x21, x15
	mul x16, x4, x4
	adcs x13, x13, x16
	umulh x16, x4, x4
	adcs x16, x23, x16
	mul x17, x3, x3
	adcs x12, x12, x17
	umulh x17, x3, x3
	adcs x17, x24, x17
	mul x21, x5, x5
	adcs x21, x25, x21
	lsl x23, x9, #32
	add x9, x23, x9
	umulh x23, x5, x5
	adcs x8, x8, x23
	ldr x23, [x0, #1104]
	sub x24, x10, x23
	umulh x25, x24, x9
	str x5, [x0, #1168]
	mul x5, x23, x9
	adds x5, x25, x5
	umulh x25, x23, x9
	adcs x25, x25, x9
	str x3, [x0, #1176]
	adc x3, x10, x10
	subs x5, x7, x5
	sbcs x6, x6, x25
	sbcs x3, x11, x3
	sbcs x7, x14, x10
	sbcs x11, x15, x10
	sbc x9, x9, x10
	lsl x14, x5, #32
	add x5, x14, x5
	umulh x14, x24, x5
	mul x15, x23, x5
	adds x14, x14, x15
	umulh x15, x23, x5
	adcs x15, x15, x5
	adc x25, x10, x10
	subs x6, x6, x14
	sbcs x3, x3, x15
	sbcs x7, x7, x25
	sbcs x11, x11, x10
	sbcs x9, x9, x10
	sbc x5, x5, x10
	lsl x14, x6, #32
	add x6, x14, x6
	umulh x14, x24, x6
	mul x15, x23, x6
	adds x14, x14, x15
	umulh x15, x23, x6
	adcs x15, x15, x6
	adc x25, x10, x10
	subs x3, x3, x14
	sbcs x7, x7, x15
	sbcs x11, x11, x25
	sbcs x9, x9, x10
	sbcs x5, x5, x10
	sbc x6, x6, x10
	lsl x14, x3, #32
	add x3, x14, x3
	umulh x14, x24, x3
	mul x15, x23, x3
	adds x14, x14, x15
	umulh x15, x23, x3
	adcs x15, x15, x3
	adc x25, x10, x10
	subs x7, x7, x14
	sbcs x11, x11, x15
	sbcs x9, x9, x25
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbc x3, x3, x10
	lsl x14, x7, #32
	add x7, x14, x7
	umulh x14, x24, x7
	mul x15, x23, x7
	adds x14, x14, x15
	umulh x15, x23, x7
	adcs x15, x15, x7
	adc x25, x10, x10
	subs x11, x11, x14
	sbcs x9, x9, x15
	sbcs x5, x5, x25
	sbcs x6, x6, x10
	sbcs x3, x3, x10
	sbc x7, x7, x10
	lsl x14, x11, #32
	add x11, x14, x11
	umulh x14, x24, x11
	mul x15, x23, x11
	adds x14, x14, x15
	umulh x15, x23, x11
	adcs x15, x15, x11
	adc x24, x10, x10
	subs x9, x9, x14
	sbcs x5, x5, x15
	sbcs x6, x6, x24
	sbcs x3, x3, x10
	sbcs x7, x7, x10
	sbc x11, x11, x10
	adds x9, x9, x13
	adcs x5, x5, x16
	adcs x6, x6, x12
	adcs x3, x3, x17
	adcs x7, x7, x21
	adcs x8, x11, x8
	adc x11, x10, x10
	subs x12, x9, x23
	ldr x13, [x0, #1096]
	sbcs x14, x5, x13
	ldr x15, [x0, #1080]
	sbcs x16, x6, x15
	ldr x17, [x0, #1072]
	sbcs x21, x3, x17
	ldr x24, [x0, #1088]
	sbcs x25, x7, x24
	str x4, [x0, #1184]
	ldr x4, [x0, #1296]
	str x1, [x0, #1192]
	ldr x1, [x0, #1240]
	str x2, [x0, #1248]
	mul x2, x4, x1
	sbcs x24, x8, x22
	sbcs x11, x11, x10
	csel x9, x12, x9, hs
	csel x5, x14, x5, hs
	csel x6, x16, x6, hs
	csel x3, x21, x3, hs
	csel x7, x25, x7, hs
	csel x8, x24, x8, hs
	adds x2, x10, x2
	ldr x11, [x0, #1232]
	mul x12, x4, x11
	adcs x12, x10, x12
	ldr x14, [x0, #1224]
	mul x16, x4, x14
	adcs x16, x10, x16
	ldr x21, [x0, #1216]
	mul x24, x4, x21
	adcs x24, x10, x24
	ldr x25, [x0, #1208]
	str x8, [x0, #1312]
	mul x8, x4, x25
	adcs x8, x10, x8
	str x7, [x0, #1320]
	ldr x7, [x0, #1200]
	str x3, [x0, #1328]
	mul x3, x4, x7
	adcs x3, x10, x3
	str x6, [x0, #1336]
	umulh x6, x4, x7
	adcs x6, x10, x6
	str x5, [x0, #1344]
	umulh x5, x4, x1
	adds x5, x12, x5
	umulh x12, x4, x11
	adcs x12, x16, x12
	umulh x16, x4, x14
	adcs x16, x24, x16
	umulh x24, x4, x21
	adcs x8, x8, x24
	umulh x4, x4, x25
	adcs x3, x3, x4
	adcs x4, x6, x10
	ldr x6, [x0, #1288]
	mul x24, x6, x1
	adds x5, x5, x24
	mul x24, x6, x11
	adcs x12, x12, x24
	mul x24, x6, x14
	adcs x16, x16, x24
	mul x24, x6, x21
	adcs x8, x8, x24
	mul x24, x6, x25
	adcs x3, x3, x24
	mul x24, x6, x7
	adcs x4, x4, x24
	umulh x24, x6, x7
	adcs x24, x10, x24
	str x9, [x0, #1296]
	umulh x9, x6, x1
	adds x9, x12, x9
	umulh x12, x6, x11
	adcs x12, x16, x12
	umulh x16, x6, x14
	adcs x8, x8, x16
	umulh x16, x6, x21
	adcs x3, x3, x16
	umulh x6, x6, x25
	adcs x4, x4, x6
	adcs x6, x24, x10
	ldr x16, [x0, #1280]
	mul x24, x16, x1
	adds x9, x9, x24
	mul x24, x16, x11
	adcs x12, x12, x24
	mul x24, x16, x14
	adcs x8, x8, x24
	mul x24, x16, x21
	adcs x3, x3, x24
	mul x24, x16, x25
	adcs x4, x4, x24
	mul x24, x16, x7
	adcs x6, x6, x24
	umulh x24, x16, x7
	adcs x24, x10, x24
	umulh x22, x16, x1
	adds x12, x12, x22
	umulh x22, x16, x11
	adcs x8, x8, x22
	umulh x22, x16, x14
	adcs x3, x3, x22
	umulh x22, x16, x21
	adcs x4, x4, x22
	umulh x16, x16, x25
	adcs x6, x6, x16
	adcs x16, x24, x10
	ldr x22, [x0, #1272]
	mul x24, x22, x1
	adds x12, x12, x24
	mul x24, x22, x11
	adcs x8, x8, x24
	mul x24, x22, x14
	adcs x3, x3, x24
	mul x24, x22, x21
	adcs x4, x4, x24
	mul x24, x22, x25
	adcs x6, x6, x24
	mul x24, x22, x7
	adcs x16, x16, x24
	umulh x24, x22, x7
	adcs x24, x10, x24
	umulh x17, x22, x1
	adds x8, x8, x17
	umulh x17, x22, x11
	adcs x3, x3, x17
	umulh x17, x22, x14
	adcs x4, x4, x17
	umulh x17, x22, x21
	adcs x6, x6, x17
	umulh x17, x22, x25
	adcs x16, x16, x17
	adcs x17, x24, x10
	ldr x22, [x0, #1256]
	mul x24, x22, x1
	adds x8, x8, x24
	mul x24, x22, x11
	adcs x3, x3, x24
	mul x24, x22, x14
	adcs x4, x4, x24
	mul x24, x22, x21
	adcs x6, x6, x24
	mul x24, x22, x25
	adcs x16, x16, x24
	mul x24, x22, x7
	adcs x17, x17, x24
	umulh x24, x22, x7
	adcs x24, x10, x24
	umulh x15, x22, x1
	adds x3, x3, x15
	umulh x15, x22, x11
	adcs x4, x4, x15
	umulh x15, x22, x14
	adcs x6, x6, x15
	umulh x15, x22, x21
	adcs x15, x16, x15
	umulh x16, x22, x25
	adcs x16, x17, x16
	adcs x17, x24, x10
	ldr x22, [x0, #1264]
	mul x24, x22, x1
	adds x3, x3, x24
	mul x24, x22, x11
	adcs x4, x4, x24
	mul x24, x22, x14
	adcs x6, x6, x24
	mul x24, x22, x21
	adcs x15, x15, x24
	mul x24, x22, x25
	adcs x16, x16, x24
	mul x24, x22, x7
	adcs x17, x17, x24
	umulh x24, x22, x7
	adcs x24, x10, x24
	umulh x7, x22, x1
	adds x4, x4, x7
	umulh x7, x22, x11
	adcs x6, x6, x7
	umulh x7, x22, x14
	adcs x7, x15, x7
	umulh x15, x22, x21
	adcs x15, x16, x15
	umulh x16, x22, x25
	adcs x16, x17, x16
	adcs x17, x24, x10
	lsl x22, x2, #32
	add x2, x22, x2
	sub x22, x10, x23
	umulh x24, x22, x2
	mul x25, x23, x2
	adds x24, x24, x25
	umulh x25, x23, x2
	adcs x25, x25, x2
	adc x21, x10, x10
	subs x5, x5, x24
	sbcs x9, x9, x25
	sbcs x12, x12, x21
	sbcs x8, x8, x10
	sbcs x3, x3, x10
	sbc x2, x2, x10
	lsl x21, x5, #32
	add x5, x21, x5
	umulh x21, x22, x5
	mul x24, x23, x5
	adds x21, x21, x24
	umulh x24, x23, x5
	adcs x24, x24, x5
	adc x25, x10, x10
	subs x9, x9, x21
	sbcs x12, x12, x24
	sbcs x8, x8, x25
	sbcs x3, x3, x10
	sbcs x2, x2, x10
	sbc x5, x5, x10
	lsl x21, x9, #32
	add x9, x21, x9
	umulh x21, x22, x9
	mul x24, x23, x9
	adds x21, x21, x24
	umulh x24, x23, x9
	adcs x24, x24, x9
	adc x25, x10, x10
	subs x12, x12, x21
	sbcs x8, x8, x24
	sbcs x3, x3, x25
	sbcs x2, x2, x10
	sbcs x5, x5, x10
	sbc x9, x9, x10
	lsl x21, x12, #32
	add x12, x21, x12
	umulh x21, x22, x12
	mul x24, x23, x12
	adds x21, x21, x24
	umulh x24, x23, x12
	adcs x24, x24, x12
	adc x25, x10, x10
	subs x8, x8, x21
	sbcs x3, x3, x24
	sbcs x2, x2, x25
	sbcs x5, x5, x10
	sbcs x9, x9, x10
	sbc x12, x12, x10
	lsl x21, x8, #32
	add x8, x21, x8
	umulh x21, x22, x8
	mul x24, x23, x8
	adds x21, x21, x24
	umulh x24, x23, x8
	adcs x24, x24, x8
	adc x25, x10, x10
	subs x3, x3, x21
	sbcs x2, x2, x24
	sbcs x5, x5, x25
	sbcs x9, x9, x10
	sbcs x12, x12, x10
	sbc x8, x8, x10
	lsl x21, x3, #32
	add x3, x21, x3
	umulh x21, x22, x3
	mul x22, x23, x3
	adds x21, x21, x22
	umulh x22, x23, x3
	adcs x22, x22, x3
	adc x24, x10, x10
	subs x2, x2, x21
	sbcs x5, x5, x22
	sbcs x9, x9, x24
	sbcs x12, x12, x10
	sbcs x8, x8, x10
	sbc x3, x3, x10
	adds x2, x2, x4
	adcs x4, x5, x6
	adcs x5, x9, x7
	adcs x6, x12, x15
	adcs x7, x8, x16
	adcs x3, x3, x17
	adc x8, x10, x10
	subs x9, x2, x23
	sbcs x12, x4, x13
	ldr x15, [x0, #1080]
	sbcs x16, x5, x15
	ldr x17, [x0, #1072]
	sbcs x21, x6, x17
	ldr x22, [x0, #1088]
	sbcs x24, x7, x22
	ldr x25, [x0, #1056]
	ldr x14, [x0, #1152]
	mul x1, x25, x14
	ldr x11, [x0, #1304]
	sbcs x22, x3, x11
	sbcs x8, x8, x10
	csel x2, x9, x2, hs
	csel x4, x12, x4, hs
	csel x5, x16, x5, hs
	csel x6, x21, x6, hs
	csel x7, x24, x7, hs
	csel x3, x22, x3, hs
	adds x1, x10, x1
	ldr x8, [x0, #1048]
	mul x9, x25, x8
	adcs x9, x10, x9
	ldr x12, [x0, #1040]
	mul x16, x25, x12
	adcs x16, x10, x16
	ldr x21, [x0, #1032]
	mul x22, x25, x21
	adcs x22, x10, x22
	ldr x24, [x0, #1024]
	str x3, [x0, #1256]
	mul x3, x25, x24
	adcs x3, x10, x3
	str x7, [x0, #1264]
	umulh x7, x25, x24
	adcs x7, x10, x7
	str x6, [x0, #1272]
	umulh x6, x25, x14
	adds x6, x9, x6
	umulh x9, x25, x8
	adcs x9, x16, x9
	umulh x16, x25, x12
	adcs x16, x22, x16
	umulh x22, x25, x21
	adcs x3, x3, x22
	adcs x7, x7, x10
	mul x22, x14, x8
	adds x9, x9, x22
	mul x22, x14, x12
	adcs x16, x16, x22
	mul x22, x14, x21
	adcs x3, x3, x22
	mul x22, x14, x24
	adcs x7, x7, x22
	umulh x22, x14, x24
	adcs x22, x10, x22
	str x5, [x0, #1280]
	umulh x5, x14, x8
	adds x5, x16, x5
	umulh x16, x14, x12
	adcs x3, x3, x16
	umulh x16, x14, x21
	adcs x7, x7, x16
	adcs x16, x22, x10
	mul x22, x8, x12
	adds x3, x3, x22
	mul x22, x8, x21
	adcs x7, x7, x22
	mul x22, x8, x24
	adcs x16, x16, x22
	umulh x22, x8, x24
	adcs x22, x10, x22
	str x4, [x0, #1288]
	umulh x4, x8, x12
	adds x4, x7, x4
	umulh x7, x8, x21
	adcs x7, x16, x7
	adcs x16, x22, x10
	mul x22, x12, x21
	adds x7, x7, x22
	mul x22, x12, x24
	adcs x16, x16, x22
	umulh x22, x12, x24
	adcs x22, x10, x22
	str x2, [x0, #1352]
	umulh x2, x12, x21
	adds x2, x16, x2
	adcs x16, x22, x10
	mul x22, x21, x24
	adds x16, x16, x22
	umulh x22, x21, x24
	adcs x22, x10, x22
	adds x11, x10, x10
	adcs x1, x1, x1
	adcs x6, x6, x6
	adcs x9, x9, x9
	adcs x5, x5, x5
	adcs x3, x3, x3
	adcs x4, x4, x4
	adcs x7, x7, x7
	adcs x2, x2, x2
	adcs x16, x16, x16
	adcs x22, x22, x22
	mul x17, x25, x25
	umulh x25, x25, x25
	mul x15, x14, x14
	umulh x14, x14, x14
	adcs x13, x10, x10
	adds x11, x11, x17
	adcs x1, x1, x25
	adcs x6, x6, x15
	adcs x9, x9, x14
	mul x14, x8, x8
	adcs x5, x5, x14
	umulh x8, x8, x8
	adcs x3, x3, x8
	mul x8, x12, x12
	adcs x4, x4, x8
	umulh x8, x12, x12
	adcs x7, x7, x8
	mul x8, x21, x21
	adcs x2, x2, x8
	umulh x8, x21, x21
	adcs x8, x16, x8
	mul x12, x24, x24
	adcs x12, x22, x12
	umulh x14, x24, x24
	adcs x13, x13, x14
	lsl x14, x11, #32
	add x11, x14, x11
	sub x14, x10, x23
	umulh x15, x14, x11
	mul x16, x23, x11
	adds x15, x15, x16
	umulh x16, x23, x11
	adcs x16, x16, x11
	adc x17, x10, x10
	subs x1, x1, x15
	sbcs x6, x6, x16
	sbcs x9, x9, x17
	sbcs x5, x5, x10
	sbcs x3, x3, x10
	sbc x11, x11, x10
	lsl x15, x1, #32
	add x1, x15, x1
	umulh x15, x14, x1
	mul x16, x23, x1
	adds x15, x15, x16
	umulh x16, x23, x1
	adcs x16, x16, x1
	adc x17, x10, x10
	subs x6, x6, x15
	sbcs x9, x9, x16
	sbcs x5, x5, x17
	sbcs x3, x3, x10
	sbcs x11, x11, x10
	sbc x1, x1, x10
	lsl x15, x6, #32
	add x6, x15, x6
	umulh x15, x14, x6
	mul x16, x23, x6
	adds x15, x15, x16
	umulh x16, x23, x6
	adcs x16, x16, x6
	adc x17, x10, x10
	subs x9, x9, x15
	sbcs x5, x5, x16
	sbcs x3, x3, x17
	sbcs x11, x11, x10
	sbcs x1, x1, x10
	sbc x6, x6, x10
	lsl x15, x9, #32
	add x9, x15, x9
	umulh x15, x14, x9
	mul x16, x23, x9
	adds x15, x15, x16
	umulh x16, x23, x9
	adcs x16, x16, x9
	adc x17, x10, x10
	subs x5, x5, x15
	sbcs x3, x3, x16
	sbcs x11, x11, x17
	sbcs x1, x1, x10
	sbcs x6, x6, x10
	sbc x9, x9, x10
	lsl x15, x5, #32
	add x5, x15, x5
	umulh x15, x14, x5
	mul x16, x23, x5
	adds x15, x15, x16
	umulh x16, x23, x5
	adcs x16, x16, x5
	adc x17, x10, x10
	subs x3, x3, x15
	sbcs x11, x11, x16
	sbcs x1, x1, x17
	sbcs x6, x6, x10
	sbcs x9, x9, x10
	sbc x5, x5, x10
	lsl x15, x3, #32
	add x3, x15, x3
	umulh x14, x14, x3
	mul x15, x23, x3
	adds x14, x14, x15
	umulh x15, x23, x3
	adcs x15, x15, x3
	adc x16, x10, x10
	subs x11, x11, x14
	sbcs x1, x1, x15
	sbcs x6, x6, x16
	sbcs x9, x9, x10
	sbcs x5, x5, x10
	sbc x3, x3, x10
	adds x4, x11, x4
	adcs x1, x1, x7
	adcs x2, x6, x2
	adcs x6, x9, x8
	adcs x5, x5, x12
	adcs x3, x3, x13
	adc x7, x10, x10
	subs x8, x4, x23
	ldr x9, [x0, #1096]
	sbcs x11, x1, x9
	ldr x12, [x0, #1080]
	sbcs x13, x2, x12
	ldr x14, [x0, #1072]
	sbcs x15, x6, x14
	ldr x16, [x0, #1088]
	sbcs x17, x5, x16
	ldr x21, [x0, #1304]
	sbcs x22, x3, x21
	sbcs x7, x7, x10
	csel x4, x8, x4, hs
	csel x1, x11, x1, hs
	csel x2, x13, x2, hs
	csel x6, x15, x6, hs
	csel x5, x17, x5, hs
	csel x3, x22, x3, hs
	ldr x7, [x0, #1296]
	subs x7, x23, x7
	ldr x8, [x0, #1344]
	sbcs x8, x9, x8
	ldr x11, [x0, #1336]
	sbcs x11, x12, x11
	ldr x13, [x0, #1328]
	sbcs x13, x14, x13
	ldr x15, [x0, #1320]
	sbcs x15, x16, x15
	ldr x17, [x0, #1312]
	sbcs x17, x21, x17
	movz x22, #9, lsl #0
	mul x24, x22, x8
	umulh x8, x22, x8
	umulh x25, x22, x7
	adds x24, x24, x25
	mul x7, x22, x7
	mul x25, x22, x11
	adcs x8, x25, x8
	umulh x11, x22, x11
	mul x25, x22, x13
	adcs x11, x25, x11
	umulh x13, x22, x13
	mul x25, x22, x15
	adcs x13, x25, x13
	umulh x15, x22, x15
	mul x25, x22, x17
	umulh x17, x22, x17
	adcs x15, x25, x15
	adcs x17, x10, x17
	movz x22, #12, lsl #0
	ldr x25, [x0, #1352]
	mul x21, x22, x25
	adds x7, x7, x21
	ldr x21, [x0, #1288]
	mul x16, x22, x21
	adcs x16, x24, x16
	ldr x24, [x0, #1280]
	mul x14, x22, x24
	adcs x8, x8, x14
	ldr x14, [x0, #1272]
	mul x12, x22, x14
	adcs x11, x11, x12
	ldr x12, [x0, #1264]
	mul x9, x22, x12
	adcs x9, x13, x9
	ldr x13, [x0, #1256]
	mul x23, x22, x13
	adcs x15, x15, x23
	umulh x23, x22, x13
	adcs x17, x17, x23
	umulh x23, x22, x25
	adds x16, x16, x23
	umulh x23, x22, x21
	adcs x8, x8, x23
	umulh x23, x22, x24
	adcs x11, x11, x23
	umulh x23, x22, x14
	adcs x9, x9, x23
	umulh x22, x22, x12
	adcs x15, x15, x22
	adcs x17, x17, x10
	movz x22, #1, lsl #0
	add x17, x17, x22
	lsl x23, x17, #32
	subs x13, x17, x23
	sbc x23, x23, x10
	adds x7, x7, x13
	adcs x13, x16, x23
	adcs x8, x8, x17
	adcs x11, x11, x10
	adcs x9, x9, x10
	adcs x15, x15, x10
	sbc x16, x10, x10
	lsr x17, x16, #32
	adds x7, x7, x17
	eor x17, x16, x17
	adcs x13, x13, x17
	lsl x17, x16, #1
	adcs x8, x8, x17
	adcs x11, x11, x16
	adcs x9, x9, x16
	adcs x15, x15, x16
	ldr x16, [x0, #1160]
	subs x4, x4, x16
	ldr x16, [x0, #1144]
	sbcs x1, x1, x16
	ldr x16, [x0, #1136]
	sbcs x2, x2, x16
	ldr x16, [x0, #1128]
	sbcs x6, x6, x16
	ldr x16, [x0, #1120]
	sbcs x5, x5, x16
	ldr x16, [x0, #1112]
	sbcs x3, x3, x16
	sbc x16, x10, x10
	ldr x17, [x0, #1104]
	and x23, x17, x16
	adds x4, x4, x23
	ldr x23, [x0, #1096]
	and x12, x23, x16
	adcs x1, x1, x12
	ldr x12, [x0, #1080]
	and x14, x12, x16
	adcs x2, x2, x14
	ldr x14, [x0, #1072]
	and x24, x14, x16
	adcs x6, x6, x24
	ldr x24, [x0, #1240]
	ldr x21, [x0, #1232]
	mul x25, x24, x21
	str x22, [x0, #1024]
	ldr x22, [x0, #1088]
	str x15, [x0, #1032]
	and x15, x22, x16
	adcs x5, x5, x15
	ldr x15, [x0, #1304]
	and x16, x15, x16
	adcs x3, x3, x16
	adds x16, x10, x25
	ldr x25, [x0, #1224]
	str x9, [x0, #1040]
	mul x9, x24, x25
	adcs x9, x10, x9
	str x11, [x0, #1048]
	ldr x11, [x0, #1216]
	str x8, [x0, #1056]
	mul x8, x24, x11
	adcs x8, x10, x8
	str x13, [x0, #1112]
	ldr x13, [x0, #1208]
	str x7, [x0, #1120]
	mul x7, x24, x13
	adcs x7, x10, x7
	str x3, [x0, #1128]
	ldr x3, [x0, #1200]
	str x5, [x0, #1136]
	mul x5, x24, x3
	adcs x5, x10, x5
	str x6, [x0, #1144]
	umulh x6, x24, x3
	adcs x6, x10, x6
	str x2, [x0, #1152]
	umulh x2, x24, x21
	adds x2, x9, x2
	umulh x9, x24, x25
	adcs x8, x8, x9
	umulh x9, x24, x11
	adcs x7, x7, x9
	umulh x9, x24, x13
	adcs x5, x5, x9
	adcs x6, x6, x10
	mul x9, x21, x25
	adds x8, x8, x9
	mul x9, x21, x11
	adcs x7, x7, x9
	mul x9, x21, x13
	adcs x5, x5, x9
	mul x9, x21, x3
	adcs x6, x6, x9
	umulh x9, x21, x3
	adcs x9, x10, x9
	str x1, [x0, #1160]
	umulh x1, x21, x25
	adds x1, x7, x1
	umulh x7, x21, x11
	adcs x5, x5, x7
	umulh x7, x21, x13
	adcs x6, x6, x7
	adcs x7, x9, x10
	mul x9, x25, x11
	adds x5, x5, x9
	mul x9, x25, x13
	adcs x6, x6, x9
	mul x9, x25, x3
	adcs x7, x7, x9
	umulh x9, x25, x3
	adcs x9, x10, x9
	str x4, [x0, #1296]
	umulh x4, x25, x11
	adds x4, x6, x4
	umulh x6, x25, x13
	adcs x6, x7, x6
	adcs x7, x9, x10
	mul x9, x11, x13
	adds x6, x6, x9
	mul x9, x11, x3
	adcs x7, x7, x9
	umulh x9, x11, x3
	adcs x9, x10, x9
	umulh x15, x11, x13
	adds x7, x7, x15
	adcs x9, x9, x10
	mul x15, x13, x3
	adds x9, x9, x15
	umulh x15, x13, x3
	adcs x15, x10, x15
	adds x22, x10, x10
	adcs x16, x16, x16
	adcs x2, x2, x2
	adcs x8, x8, x8
	adcs x1, x1, x1
	adcs x5, x5, x5
	adcs x4, x4, x4
	adcs x6, x6, x6
	adcs x7, x7, x7
	adcs x9, x9, x9
	adcs x15, x15, x15
	mul x14, x24, x24
	umulh x12, x24, x24
	mul x24, x21, x21
	adcs x23, x10, x10
	adds x14, x22, x14
	adcs x12, x16, x12
	adcs x2, x2, x24
	umulh x16, x21, x21
	adcs x8, x8, x16
	mul x16, x25, x25
	adcs x1, x1, x16
	umulh x16, x25, x25
	adcs x5, x5, x16
	mul x16, x11, x11
	adcs x4, x4, x16
	umulh x16, x11, x11
	adcs x6, x6, x16
	mul x16, x13, x13
	adcs x7, x7, x16
	umulh x16, x13, x13
	adcs x9, x9, x16
	mul x16, x3, x3
	adcs x15, x15, x16
	lsl x16, x14, #32
	add x14, x16, x14
	umulh x16, x3, x3
	adcs x16, x23, x16
	sub x22, x10, x17
	umulh x23, x22, x14
	mul x24, x17, x14
	adds x23, x23, x24
	umulh x24, x17, x14
	adcs x24, x24, x14
	adc x3, x10, x10
	subs x12, x12, x23
	sbcs x2, x2, x24
	sbcs x3, x8, x3
	sbcs x1, x1, x10
	sbcs x5, x5, x10
	sbc x8, x14, x10
	lsl x14, x12, #32
	add x12, x14, x12
	umulh x14, x22, x12
	mul x23, x17, x12
	adds x14, x14, x23
	umulh x23, x17, x12
	adcs x23, x23, x12
	adc x24, x10, x10
	subs x2, x2, x14
	sbcs x3, x3, x23
	sbcs x1, x1, x24
	sbcs x5, x5, x10
	sbcs x8, x8, x10
	sbc x12, x12, x10
	lsl x14, x2, #32
	add x2, x14, x2
	umulh x14, x22, x2
	mul x23, x17, x2
	adds x14, x14, x23
	umulh x23, x17, x2
	adcs x23, x23, x2
	adc x24, x10, x10
	subs x3, x3, x14
	sbcs x1, x1, x23
	sbcs x5, x5, x24
	sbcs x8, x8, x10
	sbcs x12, x12, x10
	sbc x2, x2, x10
	lsl x14, x3, #32
	add x3, x14, x3
	umulh x14, x22, x3
	mul x23, x17, x3
	adds x14, x14, x23
	umulh x23, x17, x3
	adcs x23, x23, x3
	adc x24, x10, x10
	subs x1, x1, x14
	sbcs x5, x5, x23
	sbcs x8, x8, x24
	sbcs x12, x12, x10
	sbcs x2, x2, x10
	sbc x3, x3, x10
	lsl x14, x1, #32
	add x1, x14, x1
	umulh x14, x22, x1
	mul x23, x17, x1
	adds x14, x14, x23
	umulh x23, x17, x1
	adcs x23, x23, x1
	adc x24, x10, x10
	subs x5, x5, x14
	sbcs x8, x8, x23
	sbcs x12, x12, x24
	sbcs x2, x2, x10
	sbcs x3, x3, x10
	sbc x1, x1, x10
	lsl x14, x5, #32
	add x5, x14, x5
	umulh x14, x22, x5
	mul x22, x17, x5
	adds x14, x14, x22
	umulh x22, x17, x5
	adcs x22, x22, x5
	adc x23, x10, x10
	subs x8, x8, x14
	sbcs x12, x12, x22
	sbcs x2, x2, x23
	sbcs x3, x3, x10
	sbcs x1, x1, x10
	sbc x5, x5, x10
	adds x4, x8, x4
	adcs x6, x12, x6
	adcs x2, x2, x7
	adcs x3, x3, x9
	adcs x1, x1, x15
	adcs x5, x5, x16
	adc x7, x10, x10
	subs x8, x4, x17
	ldr x9, [x0, #1096]
	sbcs x12, x6, x9
	ldr x14, [x0, #1080]
	sbcs x15, x2, x14
	ldr x16, [x0, #1072]
	sbcs x22, x3, x16
	ldr x23, [x0, #1088]
	sbcs x24, x1, x23
	ldr x23, [x0, #1304]
	sbcs x16, x5, x23
	sbcs x7, x7, x10
	csel x4, x8, x4, hs
	csel x6, x12, x6, hs
	csel x2, x15, x2, hs
	csel x3, x22, x3, hs
	csel x1, x24, x1, hs
	csel x5, x16, x5, hs
	ldr x7, [x0, #1296]
	ldr x8, [x0, #1240]
	subs x7, x7, x8
	ldr x8, [x0, #1160]
	sbcs x8, x8, x21
	ldr x12, [x0, #1152]
	sbcs x12, x12, x25
	ldr x15, [x0, #1144]
	sbcs x11, x15, x11
	ldr x15, [x0, #1136]
	sbcs x13, x15, x13
	ldr x15, [x0, #1128]
	ldr x16, [x0, #1200]
	sbcs x15, x15, x16
	sbc x16, x10, x10
	and x21, x17, x16
	adds x7, x7, x21
	str x7, [x0, #976]
	and x7, x9, x16
	adcs x7, x8, x7
	str x7, [x0, #984]
	and x7, x14, x16
	adcs x7, x12, x7
	str x7, [x0, #992]
	ldr x7, [x0, #1072]
	and x8, x7, x16
	adcs x8, x11, x8
	str x8, [x0, #1000]
	ldr x8, [x0, #1120]
	ldr x11, [x0, #1064]
	mul x12, x8, x11
	ldr x21, [x0, #1088]
	and x22, x21, x16
	adcs x13, x13, x22
	str x13, [x0, #1008]
	and x13, x23, x16
	adcs x13, x15, x13
	str x13, [x0, #1016]
	adds x12, x10, x12
	ldr x13, [x0, #1248]
	mul x15, x8, x13
	adcs x15, x10, x15
	ldr x16, [x0, #1192]
	mul x22, x8, x16
	adcs x22, x10, x22
	ldr x24, [x0, #1184]
	mul x25, x8, x24
	adcs x25, x10, x25
	str x5, [x0, #1128]
	ldr x5, [x0, #1176]
	str x1, [x0, #1136]
	mul x1, x8, x5
	adcs x1, x10, x1
	str x3, [x0, #1144]
	ldr x3, [x0, #1168]
	str x2, [x0, #1152]
	mul x2, x8, x3
	adcs x2, x10, x2
	str x6, [x0, #1160]
	umulh x6, x8, x3
	adcs x6, x10, x6
	str x4, [x0, #1200]
	umulh x4, x8, x11
	adds x4, x15, x4
	umulh x15, x8, x13
	adcs x15, x22, x15
	umulh x22, x8, x16
	adcs x22, x25, x22
	umulh x25, x8, x24
	adcs x1, x1, x25
	umulh x25, x8, x5
	adcs x2, x2, x25
	adcs x6, x6, x10
	ldr x25, [x0, #1112]
	mul x8, x25, x11
	adds x4, x4, x8
	mul x8, x25, x13
	adcs x8, x15, x8
	mul x15, x25, x16
	adcs x15, x22, x15
	mul x22, x25, x24
	adcs x1, x1, x22
	mul x22, x25, x5
	adcs x2, x2, x22
	mul x22, x25, x3
	adcs x6, x6, x22
	umulh x22, x25, x3
	adcs x22, x10, x22
	umulh x23, x25, x11
	adds x8, x8, x23
	umulh x23, x25, x13
	adcs x15, x15, x23
	umulh x23, x25, x16
	adcs x1, x1, x23
	umulh x23, x25, x24
	adcs x2, x2, x23
	umulh x23, x25, x5
	adcs x6, x6, x23
	adcs x22, x22, x10
	ldr x23, [x0, #1056]
	mul x25, x23, x11
	adds x8, x8, x25
	mul x25, x23, x13
	adcs x15, x15, x25
	mul x25, x23, x16
	adcs x1, x1, x25
	mul x25, x23, x24
	adcs x2, x2, x25
	mul x25, x23, x5
	adcs x6, x6, x25
	mul x25, x23, x3
	adcs x22, x22, x25
	umulh x25, x23, x3
	adcs x25, x10, x25
	umulh x21, x23, x11
	adds x15, x15, x21
	umulh x21, x23, x13
	adcs x1, x1, x21
	umulh x21, x23, x16
	adcs x2, x2, x21
	umulh x21, x23, x24
	adcs x6, x6, x21
	umulh x21, x23, x5
	adcs x21, x22, x21
	adcs x22, x25, x10
	ldr x25, [x0, #1048]
	mul x23, x25, x11
	adds x15, x15, x23
	mul x23, x25, x13
	adcs x1, x1, x23
	mul x23, x25, x16
	adcs x2, x2, x23
	mul x23, x25, x24
	adcs x6, x6, x23
	mul x23, x25, x5
	adcs x21, x21, x23
	mul x23, x25, x3
	adcs x22, x22, x23
	umulh x23, x25, x3
	adcs x23, x10, x23
	umulh x7, x25, x11
	adds x1, x1, x7
	umulh x7, x25, x13
	adcs x2, x2, x7
	umulh x7, x25, x16
	adcs x6, x6, x7
	umulh x7, x25, x24
	adcs x7, x21, x7
	umulh x21, x25, x5
	adcs x21, x22, x21
	adcs x22, x23, x10
	ldr x23, [x0, #1040]
	mul x25, x23, x11
	adds x1, x1, x25
	mul x25, x23, x13
	adcs x2, x2, x25
	mul x25, x23, x16
	adcs x6, x6, x25
	mul x25, x23, x24
	adcs x7, x7, x25
	mul x25, x23, x5
	adcs x21, x21, x25
	mul x25, x23, x3
	adcs x22, x22, x25
	umulh x25, x23, x3
	adcs x25, x10, x25
	umulh x14, x23, x11
	adds x2, x2, x14
	umulh x14, x23, x13
	adcs x6, x6, x14
	umulh x14, x23, x16
	adcs x7, x7, x14
	umulh x14, x23, x24
	adcs x14, x21, x14
	umulh x21, x23, x5
	adcs x21, x22, x21
	adcs x22, x25, x10
	ldr x25, [x0, #1032]
	mul x23, x25, x11
	adds x2, x2, x23
	umulh x11, x25, x11
	mul x23, x25, x13
	adcs x6, x6, x23
	umulh x13, x25, x13
	mul x23, x25, x16
	adcs x7, x7, x23
	umulh x16, x25, x16
	mul x23, x25, x24
	adcs x14, x14, x23
	umulh x23, x25, x24
	mul x24, x25, x5
	adcs x21, x21, x24
	umulh x5, x25, x5
	mul x24, x25, x3
	adcs x22, x22, x24
	umulh x3, x25, x3
	adcs x3, x10, x3
	adds x6, x6, x11
	adcs x7, x7, x13
	adcs x11, x14, x16
	adcs x13, x21, x23
	adcs x5, x22, x5
	adcs x3, x3, x10
	lsl x14, x12, #32
	add x12, x14, x12
	sub x14, x10, x17
	umulh x16, x14, x12
	mul x21, x17, x12
	adds x16, x16, x21
	umulh x21, x17, x12
	adcs x21, x21, x12
	adc x22, x10, x10
	subs x4, x4, x16
	sbcs x8, x8, x21
	sbcs x15, x15, x22
	sbcs x1, x1, x10
	sbcs x2, x2, x10
	sbc x12, x12, x10
	lsl x16, x4, #32
	add x4, x16, x4
	umulh x16, x14, x4
	mul x21, x17, x4
	adds x16, x16, x21
	umulh x21, x17, x4
	adcs x21, x21, x4
	adc x22, x10, x10
	subs x8, x8, x16
	sbcs x15, x15, x21
	sbcs x1, x1, x22
	sbcs x2, x2, x10
	sbcs x12, x12, x10
	sbc x4, x4, x10
	lsl x16, x8, #32
	add x8, x16, x8
	umulh x16, x14, x8
	mul x21, x17, x8
	adds x16, x16, x21
	umulh x21, x17, x8
	adcs x21, x21, x8
	adc x22, x10, x10
	subs x15, x15, x16
	sbcs x1, x1, x21
	sbcs x2, x2, x22
	sbcs x12, x12, x10
	sbcs x4, x4, x10
	sbc x8, x8, x10
	lsl x16, x15, #32
	add x15, x16, x15
	umulh x16, x14, x15
	mul x21, x17, x15
	adds x16, x16, x21
	umulh x21, x17, x15
	adcs x21, x21, x15
	adc x22, x10, x10
	subs x1, x1, x16
	sbcs x2, x2, x21
	sbcs x12, x12, x22
	sbcs x4, x4, x10
	sbcs x8, x8, x10
	sbc x15, x15, x10
	lsl x16, x1, #32
	add x1, x16, x1
	umulh x16, x14, x1
	mul x21, x17, x1
	adds x16, x16, x21
	umulh x21, x17, x1
	adcs x21, x21, x1
	adc x22, x10, x10
	subs x2, x2, x16
	sbcs x12, x12, x21
	sbcs x4, x4, x22
	sbcs x8, x8, x10
	sbcs x15, x15, x10
	sbc x1, x1, x10
	lsl x16, x2, #32
	add x2, x16, x2
	umulh x14, x14, x2
	mul x16, x17, x2
	adds x14, x14, x16
	umulh x16, x17, x2
	adcs x16, x16, x2
	adc x21, x10, x10
	subs x12, x12, x14
	sbcs x4, x4, x16
	sbcs x8, x8, x21
	sbcs x14, x15, x10
	sbcs x1, x1, x10
	sbc x2, x2, x10
	adds x6, x12, x6
	adcs x4, x4, x7
	adcs x7, x8, x11
	adcs x8, x14, x13
	adcs x1, x1, x5
	adcs x2, x2, x3
	adc x3, x10, x10
	subs x5, x6, x17
	sbcs x11, x4, x9
	ldr x12, [x0, #1080]
	sbcs x13, x7, x12
	ldr x14, [x0, #1072]
	sbcs x15, x8, x14
	ldr x16, [x0, #1088]
	sbcs x21, x1, x16
	ldr x22, [x0, #1304]
	sbcs x23, x2, x22
	sbcs x3, x3, x10
	csel x3, x5, x6, hs
	csel x4, x11, x4, hs
	csel x5, x13, x7, hs
	csel x6, x15, x8, hs
	csel x1, x21, x1, hs
	csel x2, x23, x2, hs
	ldr x7, [x0, #1120]
	subs x7, x17, x7
	ldr x8, [x0, #1112]
	sbcs x8, x9, x8
	ldr x11, [x0, #1056]
	sbcs x11, x12, x11
	ldr x13, [x0, #1048]
	sbcs x13, x14, x13
	ldr x15, [x0, #1040]
	sbcs x15, x16, x15
	sbcs x21, x22, x25
	ldr x23, [x0, #1024]
	mul x24, x23, x8
	umulh x8, x23, x8
	umulh x25, x23, x7
	adds x24, x24, x25
	mul x7, x23, x7
	mul x25, x23, x11
	adcs x8, x25, x8
	umulh x11, x23, x11
	mul x25, x23, x13
	adcs x11, x25, x11
	umulh x13, x23, x13
	mul x25, x23, x15
	adcs x13, x25, x13
	umulh x15, x23, x15
	mul x25, x23, x21
	adcs x15, x25, x15
	umulh x21, x23, x21
	adcs x21, x10, x21
	movz x25, #4, lsl #0
	str x2, [x0, #1032]
	ldr x2, [x0, #1352]
	str x1, [x0, #1040]
	mul x1, x25, x2
	adds x1, x7, x1
	umulh x2, x25, x2
	ldr x7, [x0, #1288]
	str x6, [x0, #1048]
	mul x6, x25, x7
	adcs x6, x24, x6
	umulh x7, x25, x7
	ldr x24, [x0, #1280]
	str x5, [x0, #1056]
	mul x5, x25, x24
	adcs x5, x8, x5
	umulh x8, x25, x24
	ldr x24, [x0, #1272]
	str x4, [x0, #1064]
	mul x4, x25, x24
	adcs x4, x11, x4
	umulh x11, x25, x24
	ldr x24, [x0, #1264]
	str x3, [x0, #1112]
	mul x3, x25, x24
	adcs x3, x13, x3
	umulh x13, x25, x24
	ldr x24, [x0, #1256]
	mul x22, x25, x24
	umulh x24, x25, x24
	adcs x15, x15, x22
	adcs x21, x21, x24
	adds x2, x6, x2
	adcs x5, x5, x7
	adcs x4, x4, x8
	adcs x3, x3, x11
	adcs x6, x15, x13
	adcs x7, x21, x10
	add x7, x7, x23
	lsl x8, x7, #32
	subs x11, x7, x8
	sbc x8, x8, x10
	adds x1, x1, x11
	adcs x2, x2, x8
	adcs x5, x5, x7
	adcs x4, x4, x10
	adcs x3, x3, x10
	adcs x6, x6, x10
	sbc x7, x10, x10
	lsr x8, x7, #32
	adds x1, x1, x8
	str x1, [x0, #880]
	eor x1, x7, x8
	adcs x1, x2, x1
	lsl x2, x7, #1
	adcs x2, x5, x2
	adcs x4, x4, x7
	adcs x3, x3, x7
	adcs x5, x6, x7
	ldr x6, [x0, #1200]
	subs x6, x17, x6
	ldr x7, [x0, #1160]
	sbcs x7, x9, x7
	movz x8, #8, lsl #0
	ldr x9, [x0, #1152]
	sbcs x9, x12, x9
	mul x11, x8, x7
	umulh x12, x8, x6
	ldr x13, [x0, #1144]
	sbcs x13, x14, x13
	mul x14, x8, x9
	umulh x7, x8, x7
	ldr x15, [x0, #1136]
	sbcs x15, x16, x15
	mul x16, x8, x13
	umulh x9, x8, x9
	ldr x17, [x0, #1304]
	ldr x21, [x0, #1128]
	sbcs x17, x17, x21
	mul x21, x8, x15
	umulh x13, x8, x13
	mul x22, x8, x17
	adds x11, x11, x12
	umulh x12, x8, x15
	adcs x7, x14, x7
	umulh x14, x8, x17
	movz x15, #3, lsl #0
	mul x6, x8, x6
	adcs x8, x16, x9
	ldr x9, [x0, #1112]
	mul x16, x15, x9
	adcs x13, x21, x13
	ldr x17, [x0, #1064]
	mul x21, x15, x17
	adcs x12, x22, x12
	ldr x22, [x0, #1056]
	mul x24, x15, x22
	adcs x14, x10, x14
	ldr x25, [x0, #1048]
	str x5, [x0, #1072]
	mul x5, x15, x25
	adds x6, x6, x16
	ldr x16, [x0, #1040]
	str x3, [x0, #1080]
	mul x3, x15, x16
	adcs x11, x11, x21
	ldr x21, [x0, #1032]
	str x4, [x0, #1088]
	mul x4, x15, x21
	adcs x7, x7, x24
	umulh x21, x15, x21
	adcs x5, x8, x5
	umulh x8, x15, x9
	adcs x3, x13, x3
	umulh x9, x15, x17
	adcs x4, x12, x4
	umulh x12, x15, x22
	adcs x13, x14, x21
	umulh x14, x15, x25
	adds x8, x11, x8
	umulh x11, x15, x16
	adcs x7, x7, x9
	adcs x5, x5, x12
	adcs x3, x3, x14
	adcs x4, x4, x11
	adcs x9, x13, x10
	add x9, x9, x23
	lsl x11, x9, #32
	subs x12, x9, x11
	sbc x11, x11, x10
	adds x6, x6, x12
	adcs x8, x8, x11
	adcs x7, x7, x9
	adcs x5, x5, x10
	adcs x3, x3, x10
	adcs x4, x4, x10
	sbc x9, x10, x10
	lsr x10, x9, #32
	eor x11, x9, x10
	adds x6, x6, x10
	lsl x10, x9, #1
	adcs x8, x8, x11
	adcs x7, x7, x10
	adcs x5, x5, x9
	adcs x3, x3, x9
	adcs x4, x4, x9
	str x1, [x0, #888]
	str x2, [x0, #896]
	ldr x1, [x0, #1088]
	str x1, [x0, #904]
	ldr x1, [x0, #1080]
	str x1, [x0, #912]
	ldr x1, [x0, #1072]
	str x1, [x0, #920]
	str x6, [x0, #928]
	str x8, [x0, #936]
	str x7, [x0, #944]
	str x5, [x0, #952]
	str x3, [x0, #960]
	str x4, [x0, #968]
	add x16, x0, x19
	ldrb w2, [x16, #2704]
	cbnz x2, 231f
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
	b 232f
231:
	lsr x3, x2, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	sub x2, x2, #1
	movz x17, #96, lsl #0
	mul x17, x2, x17
	add x16, x0, x17
	ldr x4, [x16, #5392]
	str x4, [x0, #784]
	ldr x4, [x16, #5400]
	str x4, [x0, #792]
	ldr x4, [x16, #5408]
	str x4, [x0, #800]
	ldr x4, [x16, #5416]
	str x4, [x0, #808]
	ldr x4, [x16, #5424]
	str x4, [x0, #816]
	ldr x4, [x16, #5432]
	str x4, [x0, #824]
	ldr x4, [x16, #5440]
	str x4, [x0, #832]
	ldr x4, [x16, #5448]
	str x4, [x0, #840]
	ldr x4, [x16, #5456]
	str x4, [x0, #848]
	ldr x4, [x16, #5464]
	str x4, [x0, #856]
	ldr x4, [x16, #5472]
	str x4, [x0, #864]
	ldr x4, [x16, #5480]
	str x4, [x0, #872]
	movz x17, #144, lsl #0
	mul x2, x2, x17
	add x16, x0, x2
	ldr x4, [x16, #4240]
	str x4, [x0, #1024]
	ldr x4, [x16, #4248]
	str x4, [x0, #1032]
	ldr x4, [x16, #4256]
	str x4, [x0, #1040]
	ldr x4, [x16, #4264]
	str x4, [x0, #1048]
	ldr x4, [x16, #4272]
	str x4, [x0, #1056]
	ldr x4, [x16, #4280]
	str x4, [x0, #1064]
	ldr x4, [x16, #4288]
	str x4, [x0, #1072]
	ldr x4, [x16, #4296]
	str x4, [x0, #1080]
	ldr x4, [x16, #4304]
	str x4, [x0, #1088]
	ldr x4, [x16, #4312]
	str x4, [x0, #1096]
	ldr x4, [x16, #4320]
	str x4, [x0, #1104]
	ldr x4, [x16, #4328]
	str x4, [x0, #1112]
	ldr x4, [x16, #4336]
	str x4, [x0, #1120]
	ldr x4, [x16, #4344]
	str x4, [x0, #1128]
	ldr x4, [x16, #4352]
	str x4, [x0, #1136]
	ldr x4, [x16, #4360]
	str x4, [x0, #1144]
	ldr x4, [x16, #4368]
	str x4, [x0, #1152]
	ldr x4, [x16, #4376]
	str x4, [x0, #1160]
	add x16, x0, x19
	ldrb w3, [x16, #2704]
	lsr x3, x3, #7
	cbnz x3, 233f
	b 234f
233:
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
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
234:
	movz x7, #0, lsl #0
	ldr x1, [x0, #976]
	ldr x2, [x0, #984]
	orr x1, x1, x2
	ldr x2, [x0, #992]
	orr x1, x1, x2
	ldr x2, [x0, #1000]
	orr x1, x1, x2
	ldr x2, [x0, #1008]
	orr x1, x1, x2
	ldr x2, [x0, #1016]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 235f
	movz x7, #0, lsl #0
	ldr x1, [x0, #1120]
	ldr x2, [x0, #1128]
	orr x1, x1, x2
	ldr x2, [x0, #1136]
	orr x1, x1, x2
	ldr x2, [x0, #1144]
	orr x1, x1, x2
	ldr x2, [x0, #1152]
	orr x1, x1, x2
	ldr x2, [x0, #1160]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 237f
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #976, lsl #0
	movz x3, #976, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #880, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #1024, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #928, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #976, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
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
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1408]
	ldr x9, [x0, #1416]
	ldr x10, [x0, #1424]
	ldr x11, [x0, #1432]
	ldr x12, [x0, #1440]
	ldr x13, [x0, #1448]
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
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1312]
	ldr x2, [x0, #1320]
	orr x1, x1, x2
	ldr x2, [x0, #1328]
	orr x1, x1, x2
	ldr x2, [x0, #1336]
	orr x1, x1, x2
	ldr x2, [x0, #1344]
	orr x1, x1, x2
	ldr x2, [x0, #1352]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 239f
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1168, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #736, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #1216]
	subs x8, x8, x2
	ldr x2, [x0, #1224]
	sbcs x9, x9, x2
	ldr x2, [x0, #1232]
	sbcs x10, x10, x2
	ldr x2, [x0, #1240]
	sbcs x11, x11, x2
	ldr x2, [x0, #1248]
	sbcs x12, x12, x2
	ldr x2, [x0, #1256]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	ldr x2, [x0, #768]
	sbcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	mov v29.d[0], x30
	movz x1, #784, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #784]
	ldr x9, [x0, #792]
	ldr x10, [x0, #800]
	ldr x11, [x0, #808]
	ldr x12, [x0, #816]
	ldr x13, [x0, #824]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	mov v29.d[0], x30
	movz x1, #832, lsl #0
	movz x2, #976, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #832, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	b 240f
239:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1408]
	ldr x2, [x0, #1416]
	orr x1, x1, x2
	ldr x2, [x0, #1424]
	orr x1, x1, x2
	ldr x2, [x0, #1432]
	orr x1, x1, x2
	ldr x2, [x0, #1440]
	orr x1, x1, x2
	ldr x2, [x0, #1448]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 241f
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #784]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #792]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #800]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #808]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #816]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	b 242f
241:
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #976, lsl #0
	movz x3, #976, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #928, lsl #0
	movz x3, #928, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #880, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
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
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #736, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
	ldr x2, [x0, #1312]
	adds x8, x8, x2
	ldr x2, [x0, #1320]
	adcs x9, x9, x2
	ldr x2, [x0, #1328]
	adcs x10, x10, x2
	ldr x2, [x0, #1336]
	adcs x11, x11, x2
	ldr x2, [x0, #1344]
	adcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
	ldr x2, [x0, #1312]
	adds x8, x8, x2
	ldr x2, [x0, #1320]
	adcs x9, x9, x2
	ldr x2, [x0, #1328]
	adcs x10, x10, x2
	ldr x2, [x0, #1336]
	adcs x11, x11, x2
	ldr x2, [x0, #1344]
	adcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	str x11, [x0, #1288]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #832, lsl #0
	movz x2, #928, lsl #0
	movz x3, #976, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #832]
	ldr x9, [x0, #840]
	ldr x10, [x0, #848]
	ldr x11, [x0, #856]
	ldr x12, [x0, #864]
	ldr x13, [x0, #872]
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
	str x8, [x0, #832]
	str x9, [x0, #840]
	str x10, [x0, #848]
	str x11, [x0, #856]
	str x12, [x0, #864]
	str x13, [x0, #872]
	mov v29.d[0], x30
	movz x1, #736, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	str x12, [x0, #768]
	str x13, [x0, #776]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	ldr x2, [x0, #768]
	sbcs x12, x12, x2
	ldr x2, [x0, #776]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	mov v29.d[0], x30
	movz x1, #784, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	movz x7, #0, lsl #0
	ldr x8, [x0, #784]
	ldr x9, [x0, #792]
	ldr x10, [x0, #800]
	ldr x11, [x0, #808]
	ldr x12, [x0, #816]
	ldr x13, [x0, #824]
	ldr x2, [x0, #1216]
	subs x8, x8, x2
	ldr x2, [x0, #1224]
	sbcs x9, x9, x2
	ldr x2, [x0, #1232]
	sbcs x10, x10, x2
	ldr x2, [x0, #1240]
	sbcs x11, x11, x2
	ldr x2, [x0, #1248]
	sbcs x12, x12, x2
	ldr x2, [x0, #1256]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
242:
240:
	b 238f
237:
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
238:
	b 236f
235:
	ldr x1, [x0, #1024]
	str x1, [x0, #736]
	ldr x1, [x0, #1032]
	str x1, [x0, #744]
	ldr x1, [x0, #1040]
	str x1, [x0, #752]
	ldr x1, [x0, #1048]
	str x1, [x0, #760]
	ldr x1, [x0, #1056]
	str x1, [x0, #768]
	ldr x1, [x0, #1064]
	str x1, [x0, #776]
	ldr x1, [x0, #1072]
	str x1, [x0, #784]
	ldr x1, [x0, #1080]
	str x1, [x0, #792]
	ldr x1, [x0, #1088]
	str x1, [x0, #800]
	ldr x1, [x0, #1096]
	str x1, [x0, #808]
	ldr x1, [x0, #1104]
	str x1, [x0, #816]
	ldr x1, [x0, #1112]
	str x1, [x0, #824]
	ldr x1, [x0, #1120]
	str x1, [x0, #832]
	ldr x1, [x0, #1128]
	str x1, [x0, #840]
	ldr x1, [x0, #1136]
	str x1, [x0, #848]
	ldr x1, [x0, #1144]
	str x1, [x0, #856]
	ldr x1, [x0, #1152]
	str x1, [x0, #864]
	ldr x1, [x0, #1160]
	str x1, [x0, #872]
236:
232:
	add x16, x0, x19
	add x16, x16, x19
	ldrb w2, [x16, #3152]
	ldrb w3, [x16, #3153]
	cbnz x2, 243f
	b 244f
243:
	lsr x3, x3, #7
	lsl x4, x3, #8
	sub x2, x2, x4
	movz x4, #0, lsl #0
	sub x3, x4, x3
	eor x2, x2, x3
	sub x2, x2, x3
	add x2, x2, #1
	lsr x2, x2, #1
	sub x2, x2, #1
	movz x3, #192, lsl #0
	mul x2, x2, x3
	adrp x16, {VG_P384_GTAB}
	add x16, x16, {VG_P384_GTAB}
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #1024]
	ldr x4, [x16, #8]
	str x4, [x0, #1032]
	ldr x4, [x16, #16]
	str x4, [x0, #1040]
	ldr x4, [x16, #24]
	str x4, [x0, #1048]
	ldr x4, [x16, #32]
	str x4, [x0, #1056]
	ldr x4, [x16, #40]
	str x4, [x0, #1064]
	ldr x4, [x16, #48]
	str x4, [x0, #1072]
	ldr x4, [x16, #56]
	str x4, [x0, #1080]
	ldr x4, [x16, #64]
	str x4, [x0, #1088]
	ldr x4, [x16, #72]
	str x4, [x0, #1096]
	ldr x4, [x16, #80]
	str x4, [x0, #1104]
	ldr x4, [x16, #88]
	str x4, [x0, #1112]
	ldr x1, [x0, #304]
	str x1, [x0, #1120]
	ldr x1, [x0, #312]
	str x1, [x0, #1128]
	ldr x1, [x0, #320]
	str x1, [x0, #1136]
	ldr x1, [x0, #328]
	str x1, [x0, #1144]
	ldr x1, [x0, #336]
	str x1, [x0, #1152]
	ldr x1, [x0, #344]
	str x1, [x0, #1160]
	add x16, x0, x19
	add x16, x16, x19
	ldrb w3, [x16, #3153]
	lsr x3, x3, #7
	cbnz x3, 245f
	b 246f
245:
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
	str x8, [x0, #1072]
	str x9, [x0, #1080]
	str x10, [x0, #1088]
	str x11, [x0, #1096]
	str x12, [x0, #1104]
	str x13, [x0, #1112]
246:
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
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 247f
	ldr x1, [x0, #736]
	str x1, [x0, #1264]
	ldr x1, [x0, #744]
	str x1, [x0, #1272]
	ldr x1, [x0, #752]
	str x1, [x0, #1280]
	ldr x1, [x0, #760]
	str x1, [x0, #1288]
	ldr x1, [x0, #768]
	str x1, [x0, #1296]
	ldr x1, [x0, #776]
	str x1, [x0, #1304]
	ldr x1, [x0, #784]
	str x1, [x0, #1360]
	ldr x1, [x0, #792]
	str x1, [x0, #1368]
	ldr x1, [x0, #800]
	str x1, [x0, #1376]
	ldr x1, [x0, #808]
	str x1, [x0, #1384]
	ldr x1, [x0, #816]
	str x1, [x0, #1392]
	ldr x1, [x0, #824]
	str x1, [x0, #1400]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #832, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #1024, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1072, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1408, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
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
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1408]
	ldr x9, [x0, #1416]
	ldr x10, [x0, #1424]
	ldr x11, [x0, #1432]
	ldr x12, [x0, #1440]
	ldr x13, [x0, #1448]
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
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1312]
	ldr x2, [x0, #1320]
	orr x1, x1, x2
	ldr x2, [x0, #1328]
	orr x1, x1, x2
	ldr x2, [x0, #1336]
	orr x1, x1, x2
	ldr x2, [x0, #1344]
	orr x1, x1, x2
	ldr x2, [x0, #1352]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 249f
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1168, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #1264, lsl #0
	movz x3, #1168, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #880, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #1408, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
	ldr x2, [x0, #1216]
	subs x8, x8, x2
	ldr x2, [x0, #1224]
	sbcs x9, x9, x2
	ldr x2, [x0, #1232]
	sbcs x10, x10, x2
	ldr x2, [x0, #1240]
	sbcs x11, x11, x2
	ldr x2, [x0, #1248]
	sbcs x12, x12, x2
	ldr x2, [x0, #1256]
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
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
	mov v29.d[0], x30
	movz x1, #928, lsl #0
	movz x2, #1408, lsl #0
	movz x3, #928, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1360, lsl #0
	movz x2, #1360, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #928]
	ldr x9, [x0, #936]
	ldr x10, [x0, #944]
	ldr x11, [x0, #952]
	ldr x12, [x0, #960]
	ldr x13, [x0, #968]
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
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
	mov v29.d[0], x30
	movz x1, #976, lsl #0
	movz x2, #832, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	b 250f
249:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1408]
	ldr x2, [x0, #1416]
	orr x1, x1, x2
	ldr x2, [x0, #1424]
	orr x1, x1, x2
	ldr x2, [x0, #1432]
	orr x1, x1, x2
	ldr x2, [x0, #1440]
	orr x1, x1, x2
	ldr x2, [x0, #1448]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	cbnz x2, 251f
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #880]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #928]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #936]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #944]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #952]
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
	b 252f
251:
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #832, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #784, lsl #0
	movz x3, #784, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	mov v29.d[0], x30
	movz x1, #1264, lsl #0
	movz x2, #736, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #736]
	ldr x9, [x0, #744]
	ldr x10, [x0, #752]
	ldr x11, [x0, #760]
	ldr x12, [x0, #768]
	ldr x13, [x0, #776]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	mov v29.d[0], x30
	movz x1, #1312, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #880, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
	ldr x2, [x0, #1312]
	adds x8, x8, x2
	ldr x2, [x0, #1320]
	adcs x9, x9, x2
	ldr x2, [x0, #1328]
	adcs x10, x10, x2
	ldr x2, [x0, #1336]
	adcs x11, x11, x2
	ldr x2, [x0, #1344]
	adcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
	ldr x2, [x0, #1312]
	adds x8, x8, x2
	ldr x2, [x0, #1320]
	adcs x9, x9, x2
	ldr x2, [x0, #1328]
	adcs x10, x10, x2
	ldr x2, [x0, #1336]
	adcs x11, x11, x2
	ldr x2, [x0, #1344]
	adcs x12, x12, x2
	ldr x2, [x0, #1352]
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
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	str x11, [x0, #1288]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	mov v29.d[0], x30
	movz x1, #976, lsl #0
	movz x2, #784, lsl #0
	movz x3, #832, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #976]
	ldr x9, [x0, #984]
	ldr x10, [x0, #992]
	ldr x11, [x0, #1000]
	ldr x12, [x0, #1008]
	ldr x13, [x0, #1016]
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
	movz x1, #880, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #1312, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
	mov v29.d[0], x30
	movz x1, #928, lsl #0
	movz x2, #1312, lsl #0
	movz x3, #928, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1216, lsl #0
	movz x2, #1216, lsl #0
	movz x3, #1216, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	movz x7, #0, lsl #0
	ldr x8, [x0, #928]
	ldr x9, [x0, #936]
	ldr x10, [x0, #944]
	ldr x11, [x0, #952]
	ldr x12, [x0, #960]
	ldr x13, [x0, #968]
	ldr x2, [x0, #1216]
	subs x8, x8, x2
	ldr x2, [x0, #1224]
	sbcs x9, x9, x2
	ldr x2, [x0, #1232]
	sbcs x10, x10, x2
	ldr x2, [x0, #1240]
	sbcs x11, x11, x2
	ldr x2, [x0, #1248]
	sbcs x12, x12, x2
	ldr x2, [x0, #1256]
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
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
252:
250:
	b 248f
247:
	ldr x1, [x0, #1024]
	str x1, [x0, #880]
	ldr x1, [x0, #1032]
	str x1, [x0, #888]
	ldr x1, [x0, #1040]
	str x1, [x0, #896]
	ldr x1, [x0, #1048]
	str x1, [x0, #904]
	ldr x1, [x0, #1056]
	str x1, [x0, #912]
	ldr x1, [x0, #1064]
	str x1, [x0, #920]
	ldr x1, [x0, #1072]
	str x1, [x0, #928]
	ldr x1, [x0, #1080]
	str x1, [x0, #936]
	ldr x1, [x0, #1088]
	str x1, [x0, #944]
	ldr x1, [x0, #1096]
	str x1, [x0, #952]
	ldr x1, [x0, #1104]
	str x1, [x0, #960]
	ldr x1, [x0, #1112]
	str x1, [x0, #968]
	ldr x1, [x0, #1120]
	str x1, [x0, #976]
	ldr x1, [x0, #1128]
	str x1, [x0, #984]
	ldr x1, [x0, #1136]
	str x1, [x0, #992]
	ldr x1, [x0, #1144]
	str x1, [x0, #1000]
	ldr x1, [x0, #1152]
	str x1, [x0, #1008]
	ldr x1, [x0, #1160]
	str x1, [x0, #1016]
248:
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
244:
	cbnz x19, 230b
	ldr x1, [x0, #736]
	str x1, [x0, #1024]
	ldr x1, [x0, #744]
	str x1, [x0, #1032]
	ldr x1, [x0, #752]
	str x1, [x0, #1040]
	ldr x1, [x0, #760]
	str x1, [x0, #1048]
	ldr x1, [x0, #768]
	str x1, [x0, #1056]
	ldr x1, [x0, #776]
	str x1, [x0, #1064]
	ldr x1, [x0, #784]
	str x1, [x0, #1072]
	ldr x1, [x0, #792]
	str x1, [x0, #1080]
	ldr x1, [x0, #800]
	str x1, [x0, #1088]
	ldr x1, [x0, #808]
	str x1, [x0, #1096]
	ldr x1, [x0, #816]
	str x1, [x0, #1104]
	ldr x1, [x0, #824]
	str x1, [x0, #1112]
	ldr x1, [x0, #832]
	str x1, [x0, #1120]
	ldr x1, [x0, #840]
	str x1, [x0, #1128]
	ldr x1, [x0, #848]
	str x1, [x0, #1136]
	ldr x1, [x0, #856]
	str x1, [x0, #1144]
	ldr x1, [x0, #864]
	str x1, [x0, #1152]
	ldr x1, [x0, #872]
	str x1, [x0, #1160]
	mov v29.d[0], x30
	movz x1, #736, lsl #0
	movz x2, #1024, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1168, lsl #0
	movz x2, #1120, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_p384_sqr_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #832, lsl #0
	movz x2, #1168, lsl #0
	movz x3, #1120, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1072]
	ldr x9, [x0, #1080]
	ldr x10, [x0, #1088]
	ldr x11, [x0, #1096]
	ldr x12, [x0, #1104]
	ldr x13, [x0, #1112]
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
	str x8, [x0, #784]
	str x9, [x0, #792]
	str x10, [x0, #800]
	str x11, [x0, #808]
	str x12, [x0, #816]
	str x13, [x0, #824]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1120]
	ldr x2, [x0, #1128]
	orr x1, x1, x2
	ldr x2, [x0, #1136]
	orr x1, x1, x2
	ldr x2, [x0, #1144]
	orr x1, x1, x2
	ldr x2, [x0, #1152]
	orr x1, x1, x2
	ldr x2, [x0, #1160]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x9, [x0, #784]
	bic x9, x9, x2, ror #0
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #65535, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #784]
	ldr x9, [x0, #792]
	bic x9, x9, x2, ror #0
	movz x4, #65535, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #792]
	ldr x9, [x0, #800]
	bic x9, x9, x2, ror #0
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #800]
	ldr x9, [x0, #808]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #808]
	ldr x9, [x0, #816]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #816]
	ldr x9, [x0, #824]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #824]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65534, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1696]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #2, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1704]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65534, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1712]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #2, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1720]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1728]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1736]
	movz x1, #10611, lsl #0
	movk x1, #52421, lsl #16
	movk x1, #61430, lsl #32
	movk x1, #8230, lsl #48
	str x1, [x0, #1456]
	movz x1, #36369, lsl #0
	movk x1, #23492, lsl #16
	movk x1, #36779, lsl #32
	movk x1, #56366, lsl #48
	str x1, [x0, #1464]
	movz x1, #25353, lsl #0
	movk x1, #21966, lsl #16
	movk x1, #57478, lsl #32
	movk x1, #2248, lsl #48
	str x1, [x0, #1472]
	movz x1, #26540, lsl #0
	movk x1, #55655, lsl #16
	movk x1, #15251, lsl #32
	movk x1, #19537, lsl #48
	str x1, [x0, #1480]
	movz x1, #31586, lsl #0
	movk x1, #48026, lsl #16
	movk x1, #19841, lsl #32
	movk x1, #51043, lsl #48
	str x1, [x0, #1488]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1496]
	movz x1, #54924, lsl #0
	movk x1, #13114, lsl #16
	movk x1, #59030, lsl #32
	movk x1, #4883, lsl #48
	str x1, [x0, #112]
	movz x1, #22661, lsl #0
	movk x1, #46927, lsl #16
	movk x1, #62028, lsl #32
	movk x1, #42981, lsl #48
	str x1, [x0, #120]
	movz x1, #53791, lsl #0
	movk x1, #3016, lsl #16
	movk x1, #45694, lsl #32
	movk x1, #14492, lsl #48
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
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #1, lsl #32
	movk x6, #0, lsl #48
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
	adcs x15, x15, x7
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
	adcs x15, x15, x7
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
	adcs x8, x8, x7
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
	adcs x8, x8, x7
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
	adcs x9, x9, x7
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
	adcs x9, x9, x7
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
	adcs x10, x10, x7
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
	adcs x10, x10, x7
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
	adcs x11, x11, x7
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
	adcs x11, x11, x7
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
	adcs x12, x12, x7
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
	adcs x12, x12, x7
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
	bl {vg_p384_mul_mod_p}
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
	bl {vg_p384_mul_mod_p}
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
