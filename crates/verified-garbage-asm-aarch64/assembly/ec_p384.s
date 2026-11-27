// The functions of `src/ec_p384.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p384_public_key:
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
	bl {vg_p384_comb}
	mov v29.d[0], x30
	bl {vg_p384_inv_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1696, lsl #0
	movz x2, #736, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1744, lsl #0
	movz x2, #1696, lsl #0
	movz x3, #256, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1888, lsl #0
	movz x2, #784, lsl #0
	movz x3, #1456, lsl #0
	bl {vg_p384_mul_mod_p}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2128, lsl #0
	movz x2, #1888, lsl #0
	movz x3, #256, lsl #0
	bl {vg_p384_mul_mod_p}
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
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	ret
	.p2align 6
