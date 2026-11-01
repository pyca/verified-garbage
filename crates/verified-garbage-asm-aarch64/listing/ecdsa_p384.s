// The functions of `src/ecdsa_p384.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p384_sign:
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
	movz x7, #0, lsl #0
	str x7, [x0, #2608]
	movz x19, #0, lsl #0
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
	movz x7, #0, lsl #0
	ldrb w4, [x16, #2230]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	adrp x16, {VG_P384_COMB}
	add x16, x16, {VG_P384_COMB}
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
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[0], x6
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v0.16b, v20.16b, v16.16b
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v1.16b, v20.16b, v16.16b
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	str q0, [x0, #1072]
	str q1, [x0, #1088]
	str q2, [x0, #1104]
	subs x4, x2, x5
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1120]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1128]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1136]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1144]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1152]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
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
	movz x7, #0, lsl #0
	ldrb w4, [x16, #2230]
	sub x3, x7, x4
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
	movz x19, #1, lsl #0
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
	ldrb w4, [x16, #2223]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #2230]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	adrp x16, {VG_P384_COMB}
	add x16, x16, {VG_P384_COMB}
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
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[0], x6
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v0.16b, v20.16b, v16.16b
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v1.16b, v20.16b, v16.16b
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	str q0, [x0, #1072]
	str q1, [x0, #1088]
	str q2, [x0, #1104]
	subs x4, x2, x5
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1120]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1128]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1136]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1144]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1152]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
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
	movz x7, #0, lsl #0
	ldrb w4, [x16, #2230]
	sub x3, x7, x4
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
21:
	add x19, x19, #1
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
	ldrb w4, [x16, #2223]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #2230]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	sub x19, x19, #1
	adrp x30, {VG_P384_COMB}
	add x30, x30, {VG_P384_COMB}
	movz x17, #6144, lsl #0
	add x5, x19, #1
	mul x17, x5, x17
	add x30, x30, x17
	movz x5, #1, lsl #0
	dup v19.2d, x2
	dup v28.2d, x5
	add v18.2d, v28.2d, v28.2d
	ldr x4, [x0, #832]
	movi v17.2d, #0
	ldr x5, [x0, #840]
	ldr x16, [x0, #848]
	ldr x17, [x0, #856]
	sub v17.2d, v17.2d, v28.2d
	ldr x21, [x0, #864]
	ldr x22, [x0, #872]
	movz x7, #0, lsl #0
	movi v30.2d, #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movi v0.2d, #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movi v1.2d, #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movi v2.2d, #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	mul x2, x4, x5
	movi v4.2d, #0
	adds x9, x9, x2
	mul x2, x4, x16
	adcs x10, x10, x2
	movi v5.2d, #0
	mul x2, x4, x17
	adcs x11, x11, x2
	mul x2, x4, x21
	movi v6.2d, #0
	adcs x12, x12, x2
	mul x2, x4, x22
	adcs x13, x13, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x4, x22
	adcs x14, x14, x2
	umulh x2, x4, x5
	adds x10, x10, x2
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x4, x16
	adcs x11, x11, x2
	umulh x2, x4, x17
	ldr q20, [x30, #0]
	adcs x12, x12, x2
	umulh x2, x4, x21
	adcs x13, x13, x2
	ldr q21, [x30, #16]
	adcs x14, x14, x7
	mul x2, x5, x16
	adds x11, x11, x2
	ldr q22, [x30, #32]
	mul x2, x5, x17
	adcs x12, x12, x2
	mul x2, x5, x21
	bit v0.16b, v20.16b, v16.16b
	adcs x13, x13, x2
	mul x2, x5, x22
	adcs x14, x14, x2
	umulh x2, x5, x22
	bit v1.16b, v21.16b, v16.16b
	adcs x15, x15, x2
	umulh x2, x5, x16
	adds x12, x12, x2
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x5, x17
	adcs x13, x13, x2
	umulh x2, x5, x21
	add v30.2d, v30.2d, v18.2d
	adcs x14, x14, x2
	adcs x15, x15, x7
	mul x2, x16, x17
	cmeq v31.2d, v30.2d, v19.2d
	adds x13, x13, x2
	mul x2, x16, x21
	adcs x14, x14, x2
	ldr q24, [x30, #96]
	mul x2, x16, x22
	adcs x15, x15, x2
	umulh x2, x16, x22
	adcs x6, x6, x2
	ldr q25, [x30, #112]
	umulh x2, x16, x17
	adds x14, x14, x2
	umulh x2, x16, x21
	ldr q26, [x30, #128]
	adcs x15, x15, x2
	adcs x6, x6, x7
	mul x2, x17, x21
	bit v4.16b, v24.16b, v31.16b
	adds x15, x15, x2
	mul x2, x17, x22
	adcs x6, x6, x2
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x17, x22
	adcs x23, x23, x2
	umulh x2, x17, x21
	bit v6.16b, v26.16b, v31.16b
	adds x6, x6, x2
	adcs x23, x23, x7
	mul x2, x21, x22
	adds x23, x23, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x21, x22
	adcs x24, x24, x2
	adds x8, x8, x8
	cmeq v16.2d, v17.2d, v19.2d
	adcs x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	ldr q20, [x30, #192]
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	ldr q21, [x30, #208]
	adcs x15, x15, x15
	adcs x6, x6, x6
	adcs x23, x23, x23
	ldr q22, [x30, #224]
	adcs x24, x24, x24
	adcs x25, x25, x25
	mul x2, x4, x4
	adds x8, x8, x2
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x4, x4
	adcs x9, x9, x2
	mul x2, x5, x5
	bit v1.16b, v21.16b, v16.16b
	adcs x10, x10, x2
	umulh x2, x5, x5
	adcs x11, x11, x2
	bit v2.16b, v22.16b, v16.16b
	mul x2, x16, x16
	adcs x12, x12, x2
	umulh x2, x16, x16
	add v30.2d, v30.2d, v18.2d
	adcs x13, x13, x2
	mul x2, x17, x17
	adcs x14, x14, x2
	cmeq v31.2d, v30.2d, v19.2d
	umulh x2, x17, x17
	adcs x15, x15, x2
	mul x2, x21, x21
	adcs x6, x6, x2
	ldr q24, [x30, #288]
	umulh x2, x21, x21
	adcs x23, x23, x2
	mul x2, x22, x22
	ldr q25, [x30, #304]
	adcs x24, x24, x2
	umulh x2, x22, x22
	adcs x25, x25, x2
	ldr q26, [x30, #320]
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	bit v4.16b, v24.16b, v31.16b
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	bit v6.16b, v26.16b, v31.16b
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	add v17.2d, v17.2d, v18.2d
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	cmeq v16.2d, v17.2d, v19.2d
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	ldr q20, [x30, #384]
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	ldr q21, [x30, #400]
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	ldr q22, [x30, #416]
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	bit v0.16b, v20.16b, v16.16b
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	bit v1.16b, v21.16b, v16.16b
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	bit v2.16b, v22.16b, v16.16b
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	add v30.2d, v30.2d, v18.2d
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	ldr q24, [x30, #480]
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	ldr q25, [x30, #496]
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	ldr q26, [x30, #512]
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	bit v4.16b, v24.16b, v31.16b
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	bit v5.16b, v25.16b, v31.16b
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	bit v6.16b, v26.16b, v31.16b
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	add v17.2d, v17.2d, v18.2d
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	cmeq v16.2d, v17.2d, v19.2d
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	ldr q20, [x30, #576]
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	ldr q21, [x30, #592]
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	ldr q22, [x30, #608]
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	bit v0.16b, v20.16b, v16.16b
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	bit v1.16b, v21.16b, v16.16b
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	bit v2.16b, v22.16b, v16.16b
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	add v30.2d, v30.2d, v18.2d
	adcs x12, x12, x24
	adcs x13, x13, x25
	adc x21, x7, x7
	cmeq v31.2d, v30.2d, v19.2d
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	ldr q24, [x30, #672]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr q25, [x30, #688]
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	ldr q26, [x30, #704]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	sbcs x2, x21, x7
	bit v4.16b, v24.16b, v31.16b
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	bit v5.16b, v25.16b, v31.16b
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	bit v6.16b, v26.16b, v31.16b
	str x8, [x0, #1168]
	str x9, [x0, #1176]
	str x10, [x0, #1184]
	add v17.2d, v17.2d, v18.2d
	str x11, [x0, #1192]
	str x12, [x0, #1200]
	str x13, [x0, #1208]
	cmeq v16.2d, v17.2d, v19.2d
	ldr x4, [x0, #1168]
	ldr x5, [x0, #1176]
	ldr x16, [x0, #1184]
	ldr x17, [x0, #1192]
	ldr q20, [x30, #768]
	ldr x21, [x0, #1200]
	ldr x22, [x0, #1208]
	movz x7, #0, lsl #0
	ldr q21, [x30, #784]
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	ldr q22, [x30, #800]
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	bit v0.16b, v20.16b, v16.16b
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	bit v1.16b, v21.16b, v16.16b
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #1024]
	bit v2.16b, v22.16b, v16.16b
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	add v30.2d, v30.2d, v18.2d
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	cmeq v31.2d, v30.2d, v19.2d
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	ldr q24, [x30, #864]
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	ldr q25, [x30, #880]
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	ldr q26, [x30, #896]
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	bit v4.16b, v24.16b, v31.16b
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	bit v6.16b, v26.16b, v31.16b
	ldr x1, [x0, #1032]
	mul x2, x1, x4
	adds x9, x9, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	cmeq v16.2d, v17.2d, v19.2d
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	ldr q20, [x30, #960]
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	ldr q21, [x30, #976]
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	ldr q22, [x30, #992]
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	bit v2.16b, v22.16b, v16.16b
	ldr x1, [x0, #1040]
	mul x2, x1, x4
	adds x10, x10, x2
	add v30.2d, v30.2d, v18.2d
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	cmeq v31.2d, v30.2d, v19.2d
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr q24, [x30, #1056]
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	ldr q25, [x30, #1072]
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	ldr q26, [x30, #1088]
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	bit v5.16b, v25.16b, v31.16b
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	bit v6.16b, v26.16b, v31.16b
	adcs x6, x6, x7
	ldr x1, [x0, #1048]
	mul x2, x1, x4
	adds x11, x11, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	cmeq v16.2d, v17.2d, v19.2d
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr q20, [x30, #1152]
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	ldr q21, [x30, #1168]
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	ldr q22, [x30, #1184]
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	bit v1.16b, v21.16b, v16.16b
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	bit v2.16b, v22.16b, v16.16b
	adcs x23, x23, x7
	ldr x1, [x0, #1056]
	mul x2, x1, x4
	add v30.2d, v30.2d, v18.2d
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	cmeq v31.2d, v30.2d, v19.2d
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	ldr q24, [x30, #1248]
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	ldr q25, [x30, #1264]
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	ldr q26, [x30, #1280]
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	bit v4.16b, v24.16b, v31.16b
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	bit v6.16b, v26.16b, v31.16b
	adcs x24, x24, x7
	ldr x1, [x0, #1064]
	mul x2, x1, x4
	add v17.2d, v17.2d, v18.2d
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	cmeq v16.2d, v17.2d, v19.2d
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	ldr q20, [x30, #1344]
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	ldr q21, [x30, #1360]
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	ldr q22, [x30, #1376]
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	bit v0.16b, v20.16b, v16.16b
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	bit v2.16b, v22.16b, v16.16b
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	add v30.2d, v30.2d, v18.2d
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	cmeq v31.2d, v30.2d, v19.2d
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	ldr q24, [x30, #1440]
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	ldr q25, [x30, #1456]
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	ldr q26, [x30, #1472]
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	bit v4.16b, v24.16b, v31.16b
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	bit v5.16b, v25.16b, v31.16b
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	bit v6.16b, v26.16b, v31.16b
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	add v17.2d, v17.2d, v18.2d
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	cmeq v16.2d, v17.2d, v19.2d
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	ldr q20, [x30, #1536]
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	ldr q21, [x30, #1552]
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	ldr q22, [x30, #1568]
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	bit v0.16b, v20.16b, v16.16b
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	bit v1.16b, v21.16b, v16.16b
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	bit v2.16b, v22.16b, v16.16b
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	add v30.2d, v30.2d, v18.2d
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	ldr q24, [x30, #1632]
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	ldr q25, [x30, #1648]
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	ldr q26, [x30, #1664]
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	bit v4.16b, v24.16b, v31.16b
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	bit v5.16b, v25.16b, v31.16b
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	bit v6.16b, v26.16b, v31.16b
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	add v17.2d, v17.2d, v18.2d
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	cmeq v16.2d, v17.2d, v19.2d
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	ldr q20, [x30, #1728]
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	ldr q21, [x30, #1744]
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	ldr q22, [x30, #1760]
	adcs x13, x13, x25
	adc x21, x7, x7
	ldr x2, [x0, #64]
	bit v0.16b, v20.16b, v16.16b
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	bit v1.16b, v21.16b, v16.16b
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	bit v2.16b, v22.16b, v16.16b
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	add v30.2d, v30.2d, v18.2d
	sbcs x16, x13, x2
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	cmeq v31.2d, v30.2d, v19.2d
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	ldr q24, [x30, #1824]
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1216]
	ldr q25, [x30, #1840]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	ldr q26, [x30, #1856]
	str x13, [x0, #1256]
	ldr x4, [x0, #1168]
	ldr x5, [x0, #1176]
	bit v4.16b, v24.16b, v31.16b
	ldr x16, [x0, #1184]
	ldr x17, [x0, #1192]
	ldr x21, [x0, #1200]
	bit v5.16b, v25.16b, v31.16b
	ldr x22, [x0, #1208]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	bit v6.16b, v26.16b, v31.16b
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	add v17.2d, v17.2d, v18.2d
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	cmeq v16.2d, v17.2d, v19.2d
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	ldr q20, [x30, #1920]
	movz x25, #0, lsl #0
	ldr x1, [x0, #832]
	mul x2, x1, x4
	ldr q21, [x30, #1936]
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	ldr q22, [x30, #1952]
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	bit v0.16b, v20.16b, v16.16b
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	bit v1.16b, v21.16b, v16.16b
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	add v30.2d, v30.2d, v18.2d
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	cmeq v31.2d, v30.2d, v19.2d
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	ldr q24, [x30, #2016]
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #840]
	mul x2, x1, x4
	ldr q25, [x30, #2032]
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	ldr q26, [x30, #2048]
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	bit v4.16b, v24.16b, v31.16b
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	bit v5.16b, v25.16b, v31.16b
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	bit v6.16b, v26.16b, v31.16b
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	add v17.2d, v17.2d, v18.2d
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	ldr q20, [x30, #2112]
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #848]
	ldr q21, [x30, #2128]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	ldr q22, [x30, #2144]
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	bit v0.16b, v20.16b, v16.16b
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	bit v1.16b, v21.16b, v16.16b
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	bit v2.16b, v22.16b, v16.16b
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	add v30.2d, v30.2d, v18.2d
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	cmeq v31.2d, v30.2d, v19.2d
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	ldr q24, [x30, #2208]
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #856]
	ldr q25, [x30, #2224]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	ldr q26, [x30, #2240]
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	bit v4.16b, v24.16b, v31.16b
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	bit v5.16b, v25.16b, v31.16b
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	bit v6.16b, v26.16b, v31.16b
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	cmeq v16.2d, v17.2d, v19.2d
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	ldr q20, [x30, #2304]
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr q21, [x30, #2320]
	ldr x1, [x0, #864]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	ldr q22, [x30, #2336]
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	bit v0.16b, v20.16b, v16.16b
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	bit v1.16b, v21.16b, v16.16b
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	add v30.2d, v30.2d, v18.2d
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	cmeq v31.2d, v30.2d, v19.2d
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	ldr q24, [x30, #2400]
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr q25, [x30, #2416]
	ldr x1, [x0, #872]
	mul x2, x1, x4
	adds x13, x13, x2
	ldr q26, [x30, #2432]
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	bit v4.16b, v24.16b, v31.16b
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	bit v5.16b, v25.16b, v31.16b
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	bit v6.16b, v26.16b, v31.16b
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	add v17.2d, v17.2d, v18.2d
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	ldr q20, [x30, #2496]
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr q21, [x30, #2512]
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	ldr q22, [x30, #2528]
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	bit v1.16b, v21.16b, v16.16b
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	bit v2.16b, v22.16b, v16.16b
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	add v30.2d, v30.2d, v18.2d
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	cmeq v31.2d, v30.2d, v19.2d
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	ldr q24, [x30, #2592]
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	ldr q25, [x30, #2608]
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	ldr q26, [x30, #2624]
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	bit v4.16b, v24.16b, v31.16b
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	bit v5.16b, v25.16b, v31.16b
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	bit v6.16b, v26.16b, v31.16b
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	add v17.2d, v17.2d, v18.2d
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	cmeq v16.2d, v17.2d, v19.2d
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	ldr q20, [x30, #2688]
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	ldr q21, [x30, #2704]
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	ldr q22, [x30, #2720]
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	bit v0.16b, v20.16b, v16.16b
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	bit v1.16b, v21.16b, v16.16b
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	bit v2.16b, v22.16b, v16.16b
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	add v30.2d, v30.2d, v18.2d
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	ldr q24, [x30, #2784]
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	ldr q25, [x30, #2800]
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	ldr q26, [x30, #2816]
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	bit v4.16b, v24.16b, v31.16b
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	bit v5.16b, v25.16b, v31.16b
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	bit v6.16b, v26.16b, v31.16b
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
	add v17.2d, v17.2d, v18.2d
	adc x21, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	cmeq v16.2d, v17.2d, v19.2d
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr q20, [x30, #2880]
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	ldr q21, [x30, #2896]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr q22, [x30, #2912]
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	bit v0.16b, v20.16b, v16.16b
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	bit v1.16b, v21.16b, v16.16b
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	bit v2.16b, v22.16b, v16.16b
	str x11, [x0, #1288]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	add v30.2d, v30.2d, v18.2d
	ldr x4, [x0, #1264]
	ldr x5, [x0, #1272]
	ldr x16, [x0, #1280]
	cmeq v31.2d, v30.2d, v19.2d
	ldr x17, [x0, #1288]
	ldr x21, [x0, #1296]
	ldr x22, [x0, #1304]
	ldr q24, [x30, #2976]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	ldr q25, [x30, #2992]
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr q26, [x30, #3008]
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	bit v4.16b, v24.16b, v31.16b
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	bit v5.16b, v25.16b, v31.16b
	ldr x1, [x0, #1072]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	bit v6.16b, v26.16b, v31.16b
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	cmeq v16.2d, v17.2d, v19.2d
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	ldr q20, [x30, #3072]
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	ldr q21, [x30, #3088]
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	ldr q22, [x30, #3104]
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	bit v1.16b, v21.16b, v16.16b
	ldr x1, [x0, #1080]
	mul x2, x1, x4
	adds x9, x9, x2
	bit v2.16b, v22.16b, v16.16b
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	add v30.2d, v30.2d, v18.2d
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	cmeq v31.2d, v30.2d, v19.2d
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	ldr q24, [x30, #3168]
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	ldr q25, [x30, #3184]
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	ldr q26, [x30, #3200]
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	bit v4.16b, v24.16b, v31.16b
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	bit v5.16b, v25.16b, v31.16b
	ldr x1, [x0, #1088]
	mul x2, x1, x4
	adds x10, x10, x2
	bit v6.16b, v26.16b, v31.16b
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	add v17.2d, v17.2d, v18.2d
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	cmeq v16.2d, v17.2d, v19.2d
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	ldr q20, [x30, #3264]
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	ldr q21, [x30, #3280]
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	ldr q22, [x30, #3296]
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	bit v0.16b, v20.16b, v16.16b
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	bit v1.16b, v21.16b, v16.16b
	adcs x6, x6, x7
	ldr x1, [x0, #1096]
	mul x2, x1, x4
	bit v2.16b, v22.16b, v16.16b
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	add v30.2d, v30.2d, v18.2d
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	cmeq v31.2d, v30.2d, v19.2d
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	ldr q24, [x30, #3360]
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	ldr q25, [x30, #3376]
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	ldr q26, [x30, #3392]
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	bit v4.16b, v24.16b, v31.16b
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	bit v5.16b, v25.16b, v31.16b
	adcs x23, x23, x7
	ldr x1, [x0, #1104]
	mul x2, x1, x4
	bit v6.16b, v26.16b, v31.16b
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	cmeq v16.2d, v17.2d, v19.2d
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	ldr q20, [x30, #3456]
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	ldr q21, [x30, #3472]
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	ldr q22, [x30, #3488]
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	bit v1.16b, v21.16b, v16.16b
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #1112]
	mul x2, x1, x4
	bit v2.16b, v22.16b, v16.16b
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	add v30.2d, v30.2d, v18.2d
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	cmeq v31.2d, v30.2d, v19.2d
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	ldr q24, [x30, #3552]
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	ldr q25, [x30, #3568]
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	ldr q26, [x30, #3584]
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	bit v5.16b, v25.16b, v31.16b
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	bit v6.16b, v26.16b, v31.16b
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	add v17.2d, v17.2d, v18.2d
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	cmeq v16.2d, v17.2d, v19.2d
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	ldr q20, [x30, #3648]
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	ldr q21, [x30, #3664]
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	ldr q22, [x30, #3680]
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	bit v1.16b, v21.16b, v16.16b
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	bit v2.16b, v22.16b, v16.16b
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	add v30.2d, v30.2d, v18.2d
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	cmeq v31.2d, v30.2d, v19.2d
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	ldr q24, [x30, #3744]
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	ldr q25, [x30, #3760]
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	ldr q26, [x30, #3776]
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	bit v4.16b, v24.16b, v31.16b
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	bit v5.16b, v25.16b, v31.16b
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	bit v6.16b, v26.16b, v31.16b
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	add v17.2d, v17.2d, v18.2d
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	cmeq v16.2d, v17.2d, v19.2d
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	ldr q20, [x30, #3840]
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	ldr q21, [x30, #3856]
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	ldr q22, [x30, #3872]
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	bit v0.16b, v20.16b, v16.16b
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	bit v1.16b, v21.16b, v16.16b
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	bit v2.16b, v22.16b, v16.16b
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	add v30.2d, v30.2d, v18.2d
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	ldr q24, [x30, #3936]
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	ldr q25, [x30, #3952]
	adcs x13, x13, x25
	adc x21, x7, x7
	ldr x2, [x0, #64]
	ldr q26, [x30, #3968]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	bit v4.16b, v24.16b, v31.16b
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	bit v5.16b, v25.16b, v31.16b
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	bit v6.16b, v26.16b, v31.16b
	sbcs x16, x13, x2
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	add v17.2d, v17.2d, v18.2d
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	cmeq v16.2d, v17.2d, v19.2d
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1264]
	ldr q20, [x30, #4032]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	str x11, [x0, #1288]
	ldr q21, [x30, #4048]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr q22, [x30, #4064]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	bit v0.16b, v20.16b, v16.16b
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
	ldr x2, [x0, #736]
	bit v1.16b, v21.16b, v16.16b
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	bit v2.16b, v22.16b, v16.16b
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	add v30.2d, v30.2d, v18.2d
	sbcs x11, x11, x2
	ldr x2, [x0, #768]
	sbcs x12, x12, x2
	ldr x2, [x0, #776]
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x13, x13, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	ldr q24, [x30, #4128]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	ldr q25, [x30, #4144]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	ldr q26, [x30, #4160]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	bit v4.16b, v24.16b, v31.16b
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	bit v5.16b, v25.16b, v31.16b
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	bit v6.16b, v26.16b, v31.16b
	adcs x13, x13, x2
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	add v17.2d, v17.2d, v18.2d
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	cmeq v16.2d, v17.2d, v19.2d
	str x13, [x0, #1256]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr q20, [x30, #4224]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr q21, [x30, #4240]
	ldr x13, [x0, #1304]
	ldr x2, [x0, #784]
	subs x8, x8, x2
	ldr q22, [x30, #4256]
	ldr x2, [x0, #792]
	sbcs x9, x9, x2
	ldr x2, [x0, #800]
	bit v0.16b, v20.16b, v16.16b
	sbcs x10, x10, x2
	ldr x2, [x0, #808]
	sbcs x11, x11, x2
	bit v1.16b, v21.16b, v16.16b
	ldr x2, [x0, #816]
	sbcs x12, x12, x2
	ldr x2, [x0, #824]
	bit v2.16b, v22.16b, v16.16b
	sbcs x13, x13, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	add v30.2d, v30.2d, v18.2d
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	cmeq v31.2d, v30.2d, v19.2d
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	ldr q24, [x30, #4320]
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	ldr q25, [x30, #4336]
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	ldr q26, [x30, #4352]
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	bit v4.16b, v24.16b, v31.16b
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	bit v5.16b, v25.16b, v31.16b
	str x11, [x0, #1288]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	bit v6.16b, v26.16b, v31.16b
	ldr x4, [x0, #1216]
	ldr x5, [x0, #1224]
	ldr x16, [x0, #1232]
	add v17.2d, v17.2d, v18.2d
	ldr x17, [x0, #1240]
	ldr x21, [x0, #1248]
	ldr x22, [x0, #1256]
	cmeq v16.2d, v17.2d, v19.2d
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	ldr q20, [x30, #4416]
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr q21, [x30, #4432]
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	ldr q22, [x30, #4448]
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	bit v0.16b, v20.16b, v16.16b
	mul x2, x4, x5
	adds x9, x9, x2
	mul x2, x4, x16
	bit v1.16b, v21.16b, v16.16b
	adcs x10, x10, x2
	mul x2, x4, x17
	adcs x11, x11, x2
	mul x2, x4, x21
	bit v2.16b, v22.16b, v16.16b
	adcs x12, x12, x2
	mul x2, x4, x22
	adcs x13, x13, x2
	add v30.2d, v30.2d, v18.2d
	umulh x2, x4, x22
	adcs x14, x14, x2
	umulh x2, x4, x5
	cmeq v31.2d, v30.2d, v19.2d
	adds x10, x10, x2
	umulh x2, x4, x16
	adcs x11, x11, x2
	ldr q24, [x30, #4512]
	umulh x2, x4, x17
	adcs x12, x12, x2
	umulh x2, x4, x21
	ldr q25, [x30, #4528]
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x2, x5, x16
	adds x11, x11, x2
	ldr q26, [x30, #4544]
	mul x2, x5, x17
	adcs x12, x12, x2
	mul x2, x5, x21
	bit v4.16b, v24.16b, v31.16b
	adcs x13, x13, x2
	mul x2, x5, x22
	adcs x14, x14, x2
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x5, x22
	adcs x15, x15, x2
	umulh x2, x5, x16
	bit v6.16b, v26.16b, v31.16b
	adds x12, x12, x2
	umulh x2, x5, x17
	adcs x13, x13, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x5, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	mul x2, x16, x17
	cmeq v16.2d, v17.2d, v19.2d
	adds x13, x13, x2
	mul x2, x16, x21
	adcs x14, x14, x2
	ldr q20, [x30, #4608]
	mul x2, x16, x22
	adcs x15, x15, x2
	umulh x2, x16, x22
	ldr q21, [x30, #4624]
	adcs x6, x6, x2
	umulh x2, x16, x17
	adds x14, x14, x2
	ldr q22, [x30, #4640]
	umulh x2, x16, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	bit v0.16b, v20.16b, v16.16b
	mul x2, x17, x21
	adds x15, x15, x2
	mul x2, x17, x22
	adcs x6, x6, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x17, x22
	adcs x23, x23, x2
	umulh x2, x17, x21
	bit v2.16b, v22.16b, v16.16b
	adds x6, x6, x2
	adcs x23, x23, x7
	mul x2, x21, x22
	add v30.2d, v30.2d, v18.2d
	adds x23, x23, x2
	umulh x2, x21, x22
	adcs x24, x24, x2
	cmeq v31.2d, v30.2d, v19.2d
	adds x8, x8, x8
	adcs x9, x9, x9
	adcs x10, x10, x10
	ldr q24, [x30, #4704]
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	ldr q25, [x30, #4720]
	adcs x15, x15, x15
	adcs x6, x6, x6
	adcs x23, x23, x23
	ldr q26, [x30, #4736]
	adcs x24, x24, x24
	adcs x25, x25, x25
	mul x2, x4, x4
	bit v4.16b, v24.16b, v31.16b
	adds x8, x8, x2
	umulh x2, x4, x4
	adcs x9, x9, x2
	bit v5.16b, v25.16b, v31.16b
	mul x2, x5, x5
	adcs x10, x10, x2
	umulh x2, x5, x5
	bit v6.16b, v26.16b, v31.16b
	adcs x11, x11, x2
	mul x2, x16, x16
	adcs x12, x12, x2
	umulh x2, x16, x16
	add v17.2d, v17.2d, v18.2d
	adcs x13, x13, x2
	mul x2, x17, x17
	adcs x14, x14, x2
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x17, x17
	adcs x15, x15, x2
	mul x2, x21, x21
	ldr q20, [x30, #4800]
	adcs x6, x6, x2
	umulh x2, x21, x21
	adcs x23, x23, x2
	ldr q21, [x30, #4816]
	mul x2, x22, x22
	adcs x24, x24, x2
	umulh x2, x22, x22
	ldr q22, [x30, #4832]
	adcs x25, x25, x2
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	bit v0.16b, v20.16b, v16.16b
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	bit v2.16b, v22.16b, v16.16b
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	add v30.2d, v30.2d, v18.2d
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	cmeq v31.2d, v30.2d, v19.2d
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	ldr q24, [x30, #4896]
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	ldr q25, [x30, #4912]
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	ldr q26, [x30, #4928]
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	bit v4.16b, v24.16b, v31.16b
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	bit v5.16b, v25.16b, v31.16b
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	bit v6.16b, v26.16b, v31.16b
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	add v17.2d, v17.2d, v18.2d
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	cmeq v16.2d, v17.2d, v19.2d
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	ldr q20, [x30, #4992]
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	ldr q21, [x30, #5008]
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	ldr q22, [x30, #5024]
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	bit v0.16b, v20.16b, v16.16b
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	bit v1.16b, v21.16b, v16.16b
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	bit v2.16b, v22.16b, v16.16b
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	add v30.2d, v30.2d, v18.2d
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	ldr q24, [x30, #5088]
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	ldr q25, [x30, #5104]
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	ldr q26, [x30, #5120]
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	bit v4.16b, v24.16b, v31.16b
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	bit v5.16b, v25.16b, v31.16b
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	bit v6.16b, v26.16b, v31.16b
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	add v17.2d, v17.2d, v18.2d
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
	cmeq v16.2d, v17.2d, v19.2d
	adc x21, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr q20, [x30, #5184]
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr q21, [x30, #5200]
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	ldr q22, [x30, #5216]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	bit v0.16b, v20.16b, v16.16b
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	bit v1.16b, v21.16b, v16.16b
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	bit v2.16b, v22.16b, v16.16b
	csel x13, x16, x13, hs
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	add v30.2d, v30.2d, v18.2d
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	cmeq v31.2d, v30.2d, v19.2d
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr q24, [x30, #5280]
	ldr x17, [x0, #1336]
	ldr x21, [x0, #1344]
	ldr x22, [x0, #1352]
	ldr q25, [x30, #5296]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	ldr q26, [x30, #5312]
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	bit v4.16b, v24.16b, v31.16b
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	bit v5.16b, v25.16b, v31.16b
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	bit v6.16b, v26.16b, v31.16b
	ldr x1, [x0, #1216]
	mul x2, x1, x4
	adds x8, x8, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	cmeq v16.2d, v17.2d, v19.2d
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	ldr q20, [x30, #5376]
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	ldr q21, [x30, #5392]
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	ldr q22, [x30, #5408]
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	bit v1.16b, v21.16b, v16.16b
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	bit v2.16b, v22.16b, v16.16b
	ldr x1, [x0, #1224]
	mul x2, x1, x4
	adds x9, x9, x2
	add v30.2d, v30.2d, v18.2d
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	cmeq v31.2d, v30.2d, v19.2d
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr q24, [x30, #5472]
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	ldr q25, [x30, #5488]
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	ldr q26, [x30, #5504]
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	bit v5.16b, v25.16b, v31.16b
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	bit v6.16b, v26.16b, v31.16b
	adcs x15, x15, x7
	ldr x1, [x0, #1232]
	mul x2, x1, x4
	add v17.2d, v17.2d, v18.2d
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	cmeq v16.2d, v17.2d, v19.2d
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr q20, [x30, #5568]
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	ldr q21, [x30, #5584]
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	ldr q22, [x30, #5600]
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	bit v0.16b, v20.16b, v16.16b
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	bit v1.16b, v21.16b, v16.16b
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	bit v2.16b, v22.16b, v16.16b
	adcs x6, x6, x7
	ldr x1, [x0, #1240]
	mul x2, x1, x4
	add v30.2d, v30.2d, v18.2d
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	cmeq v31.2d, v30.2d, v19.2d
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	ldr q24, [x30, #5664]
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	ldr q25, [x30, #5680]
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	ldr q26, [x30, #5696]
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	bit v4.16b, v24.16b, v31.16b
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	bit v6.16b, v26.16b, v31.16b
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #1248]
	mul x2, x1, x4
	add v17.2d, v17.2d, v18.2d
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	cmeq v16.2d, v17.2d, v19.2d
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	ldr q20, [x30, #5760]
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	ldr q21, [x30, #5776]
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	ldr q22, [x30, #5792]
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	bit v0.16b, v20.16b, v16.16b
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	bit v2.16b, v22.16b, v16.16b
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #1256]
	add v30.2d, v30.2d, v18.2d
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	cmeq v31.2d, v30.2d, v19.2d
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	ldr q24, [x30, #5856]
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	ldr q25, [x30, #5872]
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	ldr q26, [x30, #5888]
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	bit v5.16b, v25.16b, v31.16b
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	bit v6.16b, v26.16b, v31.16b
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	add v17.2d, v17.2d, v18.2d
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	cmeq v16.2d, v17.2d, v19.2d
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	ldr q20, [x30, #5952]
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	ldr q21, [x30, #5968]
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	ldr q22, [x30, #5984]
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	bit v0.16b, v20.16b, v16.16b
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	bit v2.16b, v22.16b, v16.16b
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	add v30.2d, v30.2d, v18.2d
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	cmeq v31.2d, v30.2d, v19.2d
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	ldr q24, [x30, #6048]
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	ldr q25, [x30, #6064]
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	ldr q26, [x30, #6080]
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	bit v4.16b, v24.16b, v31.16b
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	bit v5.16b, v25.16b, v31.16b
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	bit v6.16b, v26.16b, v31.16b
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	orr v0.16b, v0.16b, v4.16b
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	orr v1.16b, v1.16b, v5.16b
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	orr v2.16b, v2.16b, v6.16b
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	mov v3.16b, v0.16b
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	mov v7.16b, v1.16b
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	mov v23.16b, v2.16b
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	movi v17.2d, #0
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	sub v17.2d, v17.2d, v28.2d
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	movi v30.2d, #0
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	movi v0.2d, #0
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	movi v1.2d, #0
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	movi v2.2d, #0
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	movi v4.2d, #0
	adcs x13, x13, x25
	adc x21, x7, x7
	ldr x2, [x0, #64]
	movi v5.2d, #0
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	movi v6.2d, #0
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	add v17.2d, v17.2d, v18.2d
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	cmeq v16.2d, v17.2d, v19.2d
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	ldr q20, [x30, #48]
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	ldr q21, [x30, #64]
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1360]
	ldr q22, [x30, #80]
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	bit v0.16b, v20.16b, v16.16b
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	ldr x4, [x0, #1312]
	bit v1.16b, v21.16b, v16.16b
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	ldr x21, [x0, #1344]
	bit v2.16b, v22.16b, v16.16b
	ldr x22, [x0, #1352]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	add v30.2d, v30.2d, v18.2d
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	cmeq v31.2d, v30.2d, v19.2d
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	ldr q24, [x30, #144]
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	ldr q25, [x30, #160]
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #736]
	mul x2, x1, x4
	ldr q26, [x30, #176]
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	bit v4.16b, v24.16b, v31.16b
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	bit v5.16b, v25.16b, v31.16b
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	bit v6.16b, v26.16b, v31.16b
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	add v17.2d, v17.2d, v18.2d
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	cmeq v16.2d, v17.2d, v19.2d
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	ldr q20, [x30, #240]
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	ldr q21, [x30, #256]
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #744]
	ldr q22, [x30, #272]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	bit v0.16b, v20.16b, v16.16b
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	bit v1.16b, v21.16b, v16.16b
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	bit v2.16b, v22.16b, v16.16b
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	add v30.2d, v30.2d, v18.2d
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	cmeq v31.2d, v30.2d, v19.2d
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	ldr q24, [x30, #336]
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	ldr q25, [x30, #352]
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #752]
	ldr q26, [x30, #368]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	bit v4.16b, v24.16b, v31.16b
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	bit v5.16b, v25.16b, v31.16b
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	bit v6.16b, v26.16b, v31.16b
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	add v17.2d, v17.2d, v18.2d
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	ldr q20, [x30, #432]
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	ldr q21, [x30, #448]
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr q22, [x30, #464]
	ldr x1, [x0, #760]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	bit v0.16b, v20.16b, v16.16b
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	bit v1.16b, v21.16b, v16.16b
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	bit v2.16b, v22.16b, v16.16b
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	add v30.2d, v30.2d, v18.2d
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	cmeq v31.2d, v30.2d, v19.2d
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	ldr q24, [x30, #528]
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	ldr q25, [x30, #544]
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr q26, [x30, #560]
	ldr x1, [x0, #768]
	mul x2, x1, x4
	adds x12, x12, x2
	bit v4.16b, v24.16b, v31.16b
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	bit v5.16b, v25.16b, v31.16b
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	bit v6.16b, v26.16b, v31.16b
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	cmeq v16.2d, v17.2d, v19.2d
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	ldr q20, [x30, #624]
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	ldr q21, [x30, #640]
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr q22, [x30, #656]
	ldr x1, [x0, #776]
	mul x2, x1, x4
	adds x13, x13, x2
	bit v0.16b, v20.16b, v16.16b
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	bit v1.16b, v21.16b, v16.16b
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	bit v2.16b, v22.16b, v16.16b
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	add v30.2d, v30.2d, v18.2d
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	cmeq v31.2d, v30.2d, v19.2d
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	ldr q24, [x30, #720]
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	ldr q25, [x30, #736]
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	ldr q26, [x30, #752]
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	bit v4.16b, v24.16b, v31.16b
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	bit v6.16b, v26.16b, v31.16b
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	add v17.2d, v17.2d, v18.2d
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	cmeq v16.2d, v17.2d, v19.2d
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	ldr q20, [x30, #816]
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	ldr q21, [x30, #832]
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	ldr q22, [x30, #848]
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	bit v0.16b, v20.16b, v16.16b
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	bit v1.16b, v21.16b, v16.16b
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	add v30.2d, v30.2d, v18.2d
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	ldr q24, [x30, #912]
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	ldr q25, [x30, #928]
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	ldr q26, [x30, #944]
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	bit v4.16b, v24.16b, v31.16b
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	bit v5.16b, v25.16b, v31.16b
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	bit v6.16b, v26.16b, v31.16b
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	add v17.2d, v17.2d, v18.2d
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	cmeq v16.2d, v17.2d, v19.2d
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	ldr q20, [x30, #1008]
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	ldr q21, [x30, #1024]
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	ldr q22, [x30, #1040]
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	bit v0.16b, v20.16b, v16.16b
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	bit v1.16b, v21.16b, v16.16b
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	bit v2.16b, v22.16b, v16.16b
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	add v30.2d, v30.2d, v18.2d
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
	cmeq v31.2d, v30.2d, v19.2d
	adc x21, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr q24, [x30, #1104]
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	ldr q25, [x30, #1120]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	ldr q26, [x30, #1136]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	bit v4.16b, v24.16b, v31.16b
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	bit v5.16b, v25.16b, v31.16b
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	bit v6.16b, v26.16b, v31.16b
	csel x13, x16, x13, hs
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	add v17.2d, v17.2d, v18.2d
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	cmeq v16.2d, v17.2d, v19.2d
	ldr x4, [x0, #1264]
	ldr x5, [x0, #1272]
	ldr x16, [x0, #1280]
	ldr q20, [x30, #1200]
	ldr x17, [x0, #1288]
	ldr x21, [x0, #1296]
	ldr x22, [x0, #1304]
	ldr q21, [x30, #1216]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	ldr q22, [x30, #1232]
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	bit v0.16b, v20.16b, v16.16b
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	bit v1.16b, v21.16b, v16.16b
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	bit v2.16b, v22.16b, v16.16b
	mul x2, x4, x5
	adds x9, x9, x2
	mul x2, x4, x16
	add v30.2d, v30.2d, v18.2d
	adcs x10, x10, x2
	mul x2, x4, x17
	adcs x11, x11, x2
	cmeq v31.2d, v30.2d, v19.2d
	mul x2, x4, x21
	adcs x12, x12, x2
	mul x2, x4, x22
	ldr q24, [x30, #1296]
	adcs x13, x13, x2
	umulh x2, x4, x22
	adcs x14, x14, x2
	umulh x2, x4, x5
	ldr q25, [x30, #1312]
	adds x10, x10, x2
	umulh x2, x4, x16
	adcs x11, x11, x2
	ldr q26, [x30, #1328]
	umulh x2, x4, x17
	adcs x12, x12, x2
	umulh x2, x4, x21
	bit v4.16b, v24.16b, v31.16b
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x2, x5, x16
	bit v5.16b, v25.16b, v31.16b
	adds x11, x11, x2
	mul x2, x5, x17
	adcs x12, x12, x2
	bit v6.16b, v26.16b, v31.16b
	mul x2, x5, x21
	adcs x13, x13, x2
	mul x2, x5, x22
	adcs x14, x14, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x5, x22
	adcs x15, x15, x2
	umulh x2, x5, x16
	cmeq v16.2d, v17.2d, v19.2d
	adds x12, x12, x2
	umulh x2, x5, x17
	adcs x13, x13, x2
	ldr q20, [x30, #1392]
	umulh x2, x5, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr q21, [x30, #1408]
	mul x2, x16, x17
	adds x13, x13, x2
	mul x2, x16, x21
	ldr q22, [x30, #1424]
	adcs x14, x14, x2
	mul x2, x16, x22
	adcs x15, x15, x2
	umulh x2, x16, x22
	bit v0.16b, v20.16b, v16.16b
	adcs x6, x6, x2
	umulh x2, x16, x17
	adds x14, x14, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x16, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	bit v2.16b, v22.16b, v16.16b
	mul x2, x17, x21
	adds x15, x15, x2
	mul x2, x17, x22
	add v30.2d, v30.2d, v18.2d
	adcs x6, x6, x2
	umulh x2, x17, x22
	adcs x23, x23, x2
	cmeq v31.2d, v30.2d, v19.2d
	umulh x2, x17, x21
	adds x6, x6, x2
	adcs x23, x23, x7
	mul x2, x21, x22
	ldr q24, [x30, #1488]
	adds x23, x23, x2
	umulh x2, x21, x22
	adcs x24, x24, x2
	ldr q25, [x30, #1504]
	adds x8, x8, x8
	adcs x9, x9, x9
	adcs x10, x10, x10
	ldr q26, [x30, #1520]
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	bit v4.16b, v24.16b, v31.16b
	adcs x14, x14, x14
	adcs x15, x15, x15
	adcs x6, x6, x6
	bit v5.16b, v25.16b, v31.16b
	adcs x23, x23, x23
	adcs x24, x24, x24
	adcs x25, x25, x25
	mul x2, x4, x4
	bit v6.16b, v26.16b, v31.16b
	adds x8, x8, x2
	umulh x2, x4, x4
	adcs x9, x9, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x5, x5
	adcs x10, x10, x2
	umulh x2, x5, x5
	cmeq v16.2d, v17.2d, v19.2d
	adcs x11, x11, x2
	mul x2, x16, x16
	adcs x12, x12, x2
	ldr q20, [x30, #1584]
	umulh x2, x16, x16
	adcs x13, x13, x2
	mul x2, x17, x17
	ldr q21, [x30, #1600]
	adcs x14, x14, x2
	umulh x2, x17, x17
	adcs x15, x15, x2
	mul x2, x21, x21
	ldr q22, [x30, #1616]
	adcs x6, x6, x2
	umulh x2, x21, x21
	adcs x23, x23, x2
	bit v0.16b, v20.16b, v16.16b
	mul x2, x22, x22
	adcs x24, x24, x2
	umulh x2, x22, x22
	bit v1.16b, v21.16b, v16.16b
	adcs x25, x25, x2
	ldr x17, [x0, #64]
	sub x16, x7, x17
	bit v2.16b, v22.16b, v16.16b
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	add v30.2d, v30.2d, v18.2d
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	cmeq v31.2d, v30.2d, v19.2d
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	ldr q24, [x30, #1680]
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	ldr q25, [x30, #1696]
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	ldr q26, [x30, #1712]
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	bit v4.16b, v24.16b, v31.16b
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	bit v5.16b, v25.16b, v31.16b
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	bit v6.16b, v26.16b, v31.16b
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add v17.2d, v17.2d, v18.2d
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	ldr q20, [x30, #1776]
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	ldr q21, [x30, #1792]
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	ldr q22, [x30, #1808]
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	bit v0.16b, v20.16b, v16.16b
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	bit v1.16b, v21.16b, v16.16b
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	bit v2.16b, v22.16b, v16.16b
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	add v30.2d, v30.2d, v18.2d
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	cmeq v31.2d, v30.2d, v19.2d
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	ldr q24, [x30, #1872]
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	ldr q25, [x30, #1888]
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	ldr q26, [x30, #1904]
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	bit v4.16b, v24.16b, v31.16b
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	bit v6.16b, v26.16b, v31.16b
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	add v17.2d, v17.2d, v18.2d
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	cmeq v16.2d, v17.2d, v19.2d
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	ldr q20, [x30, #1968]
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
	ldr q21, [x30, #1984]
	adc x21, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr q22, [x30, #2000]
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	bit v0.16b, v20.16b, v16.16b
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	bit v1.16b, v21.16b, v16.16b
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	bit v2.16b, v22.16b, v16.16b
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	add v30.2d, v30.2d, v18.2d
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	cmeq v31.2d, v30.2d, v19.2d
	csel x13, x16, x13, hs
	str x8, [x0, #880]
	str x9, [x0, #888]
	ldr q24, [x30, #2064]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	ldr q25, [x30, #2080]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr q26, [x30, #2096]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	bit v4.16b, v24.16b, v31.16b
	ldr x13, [x0, #920]
	ldr x2, [x0, #1360]
	subs x8, x8, x2
	bit v5.16b, v25.16b, v31.16b
	ldr x2, [x0, #1368]
	sbcs x9, x9, x2
	ldr x2, [x0, #1376]
	bit v6.16b, v26.16b, v31.16b
	sbcs x10, x10, x2
	ldr x2, [x0, #1384]
	sbcs x11, x11, x2
	add v17.2d, v17.2d, v18.2d
	ldr x2, [x0, #1392]
	sbcs x12, x12, x2
	ldr x2, [x0, #1400]
	sbcs x13, x13, x2
	cmeq v16.2d, v17.2d, v19.2d
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	ldr q20, [x30, #2160]
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	ldr q21, [x30, #2176]
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	ldr q22, [x30, #2192]
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	bit v0.16b, v20.16b, v16.16b
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	bit v1.16b, v21.16b, v16.16b
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	bit v2.16b, v22.16b, v16.16b
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	add v30.2d, v30.2d, v18.2d
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	cmeq v31.2d, v30.2d, v19.2d
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr q24, [x30, #2256]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
	ldr q25, [x30, #2272]
	ldr x2, [x0, #1312]
	adds x8, x8, x2
	ldr x2, [x0, #1320]
	ldr q26, [x30, #2288]
	adcs x9, x9, x2
	ldr x2, [x0, #1328]
	adcs x10, x10, x2
	bit v4.16b, v24.16b, v31.16b
	ldr x2, [x0, #1336]
	adcs x11, x11, x2
	ldr x2, [x0, #1344]
	bit v5.16b, v25.16b, v31.16b
	adcs x12, x12, x2
	ldr x2, [x0, #1352]
	adcs x13, x13, x2
	bit v6.16b, v26.16b, v31.16b
	adc x14, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	add v17.2d, v17.2d, v18.2d
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	cmeq v16.2d, v17.2d, v19.2d
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	ldr q20, [x30, #2352]
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr q21, [x30, #2368]
	sbcs x2, x14, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	ldr q22, [x30, #2384]
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	bit v0.16b, v20.16b, v16.16b
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	bit v1.16b, v21.16b, v16.16b
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	bit v2.16b, v22.16b, v16.16b
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	add v30.2d, v30.2d, v18.2d
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	cmeq v31.2d, v30.2d, v19.2d
	ldr x13, [x0, #920]
	ldr x2, [x0, #1408]
	subs x8, x8, x2
	ldr x2, [x0, #1416]
	ldr q24, [x30, #2448]
	sbcs x9, x9, x2
	ldr x2, [x0, #1424]
	sbcs x10, x10, x2
	ldr q25, [x30, #2464]
	ldr x2, [x0, #1432]
	sbcs x11, x11, x2
	ldr x2, [x0, #1440]
	ldr q26, [x30, #2480]
	sbcs x12, x12, x2
	ldr x2, [x0, #1448]
	sbcs x13, x13, x2
	bit v4.16b, v24.16b, v31.16b
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	bit v5.16b, v25.16b, v31.16b
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	bit v6.16b, v26.16b, v31.16b
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	add v17.2d, v17.2d, v18.2d
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	cmeq v16.2d, v17.2d, v19.2d
	ldr x2, [x0, #96]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr q20, [x30, #2544]
	ldr x2, [x0, #104]
	and x2, x2, x17
	adcs x13, x13, x2
	ldr q21, [x30, #2560]
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	ldr q22, [x30, #2576]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	bit v0.16b, v20.16b, v16.16b
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	bit v1.16b, v21.16b, v16.16b
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
	bit v2.16b, v22.16b, v16.16b
	ldr x2, [x0, #880]
	subs x8, x8, x2
	ldr x2, [x0, #888]
	add v30.2d, v30.2d, v18.2d
	sbcs x9, x9, x2
	ldr x2, [x0, #896]
	sbcs x10, x10, x2
	ldr x2, [x0, #904]
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x11, x11, x2
	ldr x2, [x0, #912]
	sbcs x12, x12, x2
	ldr q24, [x30, #2640]
	ldr x2, [x0, #920]
	sbcs x13, x13, x2
	sbc x17, x7, x7
	ldr q25, [x30, #2656]
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr q26, [x30, #2672]
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	bit v4.16b, v24.16b, v31.16b
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	bit v5.16b, v25.16b, v31.16b
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	bit v6.16b, v26.16b, v31.16b
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	add v17.2d, v17.2d, v18.2d
	and x2, x2, x17
	adcs x13, x13, x2
	str x8, [x0, #1312]
	cmeq v16.2d, v17.2d, v19.2d
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	ldr q20, [x30, #2736]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr q21, [x30, #2752]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	ldr x21, [x0, #1344]
	ldr q22, [x30, #2768]
	ldr x22, [x0, #1352]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	bit v0.16b, v20.16b, v16.16b
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	bit v1.16b, v21.16b, v16.16b
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	bit v2.16b, v22.16b, v16.16b
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	add v30.2d, v30.2d, v18.2d
	movz x25, #0, lsl #0
	ldr x1, [x0, #1264]
	mul x2, x1, x4
	cmeq v31.2d, v30.2d, v19.2d
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	ldr q24, [x30, #2832]
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	ldr q25, [x30, #2848]
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	ldr q26, [x30, #2864]
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	bit v5.16b, v25.16b, v31.16b
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	bit v6.16b, v26.16b, v31.16b
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	add v17.2d, v17.2d, v18.2d
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #1272]
	cmeq v16.2d, v17.2d, v19.2d
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	ldr q20, [x30, #2928]
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	ldr q21, [x30, #2944]
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	ldr q22, [x30, #2960]
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	bit v0.16b, v20.16b, v16.16b
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	add v30.2d, v30.2d, v18.2d
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #1280]
	cmeq v31.2d, v30.2d, v19.2d
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	ldr q24, [x30, #3024]
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	ldr q25, [x30, #3040]
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	ldr q26, [x30, #3056]
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	bit v4.16b, v24.16b, v31.16b
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	bit v6.16b, v26.16b, v31.16b
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	add v17.2d, v17.2d, v18.2d
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #1288]
	cmeq v16.2d, v17.2d, v19.2d
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	ldr q20, [x30, #3120]
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	ldr q21, [x30, #3136]
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	ldr q22, [x30, #3152]
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	bit v0.16b, v20.16b, v16.16b
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	bit v2.16b, v22.16b, v16.16b
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	add v30.2d, v30.2d, v18.2d
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	cmeq v31.2d, v30.2d, v19.2d
	ldr x1, [x0, #1296]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	ldr q24, [x30, #3216]
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	ldr q25, [x30, #3232]
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	ldr q26, [x30, #3248]
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	bit v5.16b, v25.16b, v31.16b
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	bit v6.16b, v26.16b, v31.16b
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	cmeq v16.2d, v17.2d, v19.2d
	ldr x1, [x0, #1304]
	mul x2, x1, x4
	adds x13, x13, x2
	ldr q20, [x30, #3312]
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	ldr q21, [x30, #3328]
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	ldr q22, [x30, #3344]
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	bit v1.16b, v21.16b, v16.16b
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	add v30.2d, v30.2d, v18.2d
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	cmeq v31.2d, v30.2d, v19.2d
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	ldr q24, [x30, #3408]
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	ldr q25, [x30, #3424]
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	ldr q26, [x30, #3440]
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	bit v4.16b, v24.16b, v31.16b
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	bit v5.16b, v25.16b, v31.16b
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	bit v6.16b, v26.16b, v31.16b
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	add v17.2d, v17.2d, v18.2d
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	cmeq v16.2d, v17.2d, v19.2d
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	ldr q20, [x30, #3504]
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	ldr q21, [x30, #3520]
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	ldr q22, [x30, #3536]
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	bit v0.16b, v20.16b, v16.16b
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	bit v1.16b, v21.16b, v16.16b
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	bit v2.16b, v22.16b, v16.16b
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	add v30.2d, v30.2d, v18.2d
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	cmeq v31.2d, v30.2d, v19.2d
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	ldr q24, [x30, #3600]
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	ldr q25, [x30, #3616]
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	ldr q26, [x30, #3632]
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	bit v4.16b, v24.16b, v31.16b
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	bit v5.16b, v25.16b, v31.16b
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	bit v6.16b, v26.16b, v31.16b
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add v17.2d, v17.2d, v18.2d
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	ldr q20, [x30, #3696]
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	ldr q21, [x30, #3712]
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	ldr q22, [x30, #3728]
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	bit v0.16b, v20.16b, v16.16b
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
	bit v1.16b, v21.16b, v16.16b
	adc x21, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	bit v2.16b, v22.16b, v16.16b
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	add v30.2d, v30.2d, v18.2d
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	ldr q24, [x30, #3792]
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	ldr q25, [x30, #3808]
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	ldr q26, [x30, #3824]
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	bit v4.16b, v24.16b, v31.16b
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	bit v5.16b, v25.16b, v31.16b
	ldr x4, [x0, #1360]
	ldr x5, [x0, #1368]
	ldr x16, [x0, #1376]
	bit v6.16b, v26.16b, v31.16b
	ldr x17, [x0, #1384]
	ldr x21, [x0, #1392]
	ldr x22, [x0, #1400]
	add v17.2d, v17.2d, v18.2d
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	cmeq v16.2d, v17.2d, v19.2d
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr q20, [x30, #3888]
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	ldr q21, [x30, #3904]
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr q22, [x30, #3920]
	ldr x1, [x0, #784]
	mul x2, x1, x4
	adds x8, x8, x2
	bit v0.16b, v20.16b, v16.16b
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	bit v1.16b, v21.16b, v16.16b
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	bit v2.16b, v22.16b, v16.16b
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	add v30.2d, v30.2d, v18.2d
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	cmeq v31.2d, v30.2d, v19.2d
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	ldr q24, [x30, #3984]
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	ldr q25, [x30, #4000]
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr q26, [x30, #4016]
	ldr x1, [x0, #792]
	mul x2, x1, x4
	adds x9, x9, x2
	bit v4.16b, v24.16b, v31.16b
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	bit v5.16b, v25.16b, v31.16b
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	bit v6.16b, v26.16b, v31.16b
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	cmeq v16.2d, v17.2d, v19.2d
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	ldr q20, [x30, #4080]
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	ldr q21, [x30, #4096]
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	ldr q22, [x30, #4112]
	adcs x15, x15, x7
	ldr x1, [x0, #800]
	mul x2, x1, x4
	adds x10, x10, x2
	bit v0.16b, v20.16b, v16.16b
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	bit v1.16b, v21.16b, v16.16b
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	bit v2.16b, v22.16b, v16.16b
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	add v30.2d, v30.2d, v18.2d
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	cmeq v31.2d, v30.2d, v19.2d
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	ldr q24, [x30, #4176]
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	ldr q25, [x30, #4192]
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	ldr q26, [x30, #4208]
	adcs x6, x6, x7
	ldr x1, [x0, #808]
	mul x2, x1, x4
	bit v4.16b, v24.16b, v31.16b
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	bit v5.16b, v25.16b, v31.16b
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	bit v6.16b, v26.16b, v31.16b
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	add v17.2d, v17.2d, v18.2d
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	ldr q20, [x30, #4272]
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	ldr q21, [x30, #4288]
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	ldr q22, [x30, #4304]
	adcs x23, x23, x7
	ldr x1, [x0, #816]
	mul x2, x1, x4
	bit v0.16b, v20.16b, v16.16b
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	bit v1.16b, v21.16b, v16.16b
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	bit v2.16b, v22.16b, v16.16b
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	add v30.2d, v30.2d, v18.2d
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	cmeq v31.2d, v30.2d, v19.2d
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	ldr q24, [x30, #4368]
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	ldr q25, [x30, #4384]
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	ldr q26, [x30, #4400]
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #824]
	bit v4.16b, v24.16b, v31.16b
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	bit v5.16b, v25.16b, v31.16b
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	bit v6.16b, v26.16b, v31.16b
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	cmeq v16.2d, v17.2d, v19.2d
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	ldr q20, [x30, #4464]
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	ldr q21, [x30, #4480]
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	ldr q22, [x30, #4496]
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	bit v0.16b, v20.16b, v16.16b
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	bit v1.16b, v21.16b, v16.16b
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	bit v2.16b, v22.16b, v16.16b
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	add v30.2d, v30.2d, v18.2d
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	cmeq v31.2d, v30.2d, v19.2d
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	ldr q24, [x30, #4560]
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	ldr q25, [x30, #4576]
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	ldr q26, [x30, #4592]
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	bit v4.16b, v24.16b, v31.16b
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	bit v5.16b, v25.16b, v31.16b
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	bit v6.16b, v26.16b, v31.16b
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	add v17.2d, v17.2d, v18.2d
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	cmeq v16.2d, v17.2d, v19.2d
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	ldr q20, [x30, #4656]
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	ldr q21, [x30, #4672]
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	ldr q22, [x30, #4688]
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	bit v0.16b, v20.16b, v16.16b
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	bit v1.16b, v21.16b, v16.16b
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	bit v2.16b, v22.16b, v16.16b
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	add v30.2d, v30.2d, v18.2d
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	cmeq v31.2d, v30.2d, v19.2d
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	ldr q24, [x30, #4752]
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	ldr q25, [x30, #4768]
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	ldr q26, [x30, #4784]
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	bit v4.16b, v24.16b, v31.16b
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	bit v5.16b, v25.16b, v31.16b
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	bit v6.16b, v26.16b, v31.16b
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	add v17.2d, v17.2d, v18.2d
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	cmeq v16.2d, v17.2d, v19.2d
	adcs x13, x13, x25
	adc x21, x7, x7
	ldr x2, [x0, #64]
	ldr q20, [x30, #4848]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr q21, [x30, #4864]
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	ldr q22, [x30, #4880]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	sbcs x6, x12, x2
	bit v0.16b, v20.16b, v16.16b
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	bit v1.16b, v21.16b, v16.16b
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	bit v2.16b, v22.16b, v16.16b
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1360]
	add v30.2d, v30.2d, v18.2d
	str x9, [x0, #1368]
	str x10, [x0, #1376]
	str x11, [x0, #1384]
	cmeq v31.2d, v30.2d, v19.2d
	str x12, [x0, #1392]
	str x13, [x0, #1400]
	movz x7, #0, lsl #0
	ldr q24, [x30, #4944]
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr q25, [x30, #4960]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
	ldr x2, [x0, #1360]
	ldr q26, [x30, #4976]
	subs x8, x8, x2
	ldr x2, [x0, #1368]
	sbcs x9, x9, x2
	bit v4.16b, v24.16b, v31.16b
	ldr x2, [x0, #1376]
	sbcs x10, x10, x2
	ldr x2, [x0, #1384]
	bit v5.16b, v25.16b, v31.16b
	sbcs x11, x11, x2
	ldr x2, [x0, #1392]
	sbcs x12, x12, x2
	bit v6.16b, v26.16b, v31.16b
	ldr x2, [x0, #1400]
	sbcs x13, x13, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	add v17.2d, v17.2d, v18.2d
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	cmeq v16.2d, v17.2d, v19.2d
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	ldr q20, [x30, #5040]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	ldr q21, [x30, #5056]
	and x2, x2, x17
	adcs x11, x11, x2
	ldr x2, [x0, #96]
	ldr q22, [x30, #5072]
	and x2, x2, x17
	adcs x12, x12, x2
	ldr x2, [x0, #104]
	and x2, x2, x17
	bit v0.16b, v20.16b, v16.16b
	adcs x13, x13, x2
	str x8, [x0, #928]
	str x9, [x0, #936]
	bit v1.16b, v21.16b, v16.16b
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	bit v2.16b, v22.16b, v16.16b
	str x13, [x0, #968]
	ldr x4, [x0, #1216]
	ldr x5, [x0, #1224]
	add v30.2d, v30.2d, v18.2d
	ldr x16, [x0, #1232]
	ldr x17, [x0, #1240]
	ldr x21, [x0, #1248]
	cmeq v31.2d, v30.2d, v19.2d
	ldr x22, [x0, #1256]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	ldr q24, [x30, #5136]
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	ldr q25, [x30, #5152]
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	ldr q26, [x30, #5168]
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	bit v4.16b, v24.16b, v31.16b
	movz x25, #0, lsl #0
	ldr x1, [x0, #832]
	mul x2, x1, x4
	bit v5.16b, v25.16b, v31.16b
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	bit v6.16b, v26.16b, v31.16b
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	cmeq v16.2d, v17.2d, v19.2d
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	ldr q20, [x30, #5232]
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	ldr q21, [x30, #5248]
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	ldr q22, [x30, #5264]
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	bit v0.16b, v20.16b, v16.16b
	adcs x14, x14, x7
	ldr x1, [x0, #840]
	mul x2, x1, x4
	bit v1.16b, v21.16b, v16.16b
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	bit v2.16b, v22.16b, v16.16b
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	add v30.2d, v30.2d, v18.2d
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	cmeq v31.2d, v30.2d, v19.2d
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	ldr q24, [x30, #5328]
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	ldr q25, [x30, #5344]
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	ldr q26, [x30, #5360]
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	bit v4.16b, v24.16b, v31.16b
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #848]
	mul x2, x1, x4
	bit v5.16b, v25.16b, v31.16b
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	bit v6.16b, v26.16b, v31.16b
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	add v17.2d, v17.2d, v18.2d
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	cmeq v16.2d, v17.2d, v19.2d
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	ldr q20, [x30, #5424]
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	ldr q21, [x30, #5440]
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	ldr q22, [x30, #5456]
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	bit v0.16b, v20.16b, v16.16b
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #856]
	bit v1.16b, v21.16b, v16.16b
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	bit v2.16b, v22.16b, v16.16b
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	add v30.2d, v30.2d, v18.2d
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	cmeq v31.2d, v30.2d, v19.2d
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	ldr q24, [x30, #5520]
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	ldr q25, [x30, #5536]
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	ldr q26, [x30, #5552]
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	bit v4.16b, v24.16b, v31.16b
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #864]
	bit v5.16b, v25.16b, v31.16b
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	bit v6.16b, v26.16b, v31.16b
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	cmeq v16.2d, v17.2d, v19.2d
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	ldr q20, [x30, #5616]
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	ldr q21, [x30, #5632]
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	ldr q22, [x30, #5648]
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	bit v1.16b, v21.16b, v16.16b
	ldr x1, [x0, #872]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	bit v2.16b, v22.16b, v16.16b
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	add v30.2d, v30.2d, v18.2d
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	cmeq v31.2d, v30.2d, v19.2d
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	ldr q24, [x30, #5712]
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	ldr q25, [x30, #5728]
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	ldr q26, [x30, #5744]
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	bit v5.16b, v25.16b, v31.16b
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	bit v6.16b, v26.16b, v31.16b
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	add v17.2d, v17.2d, v18.2d
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	cmeq v16.2d, v17.2d, v19.2d
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	ldr q20, [x30, #5808]
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	ldr q21, [x30, #5824]
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	ldr q22, [x30, #5840]
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	bit v0.16b, v20.16b, v16.16b
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	bit v1.16b, v21.16b, v16.16b
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	bit v2.16b, v22.16b, v16.16b
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	add v30.2d, v30.2d, v18.2d
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	cmeq v31.2d, v30.2d, v19.2d
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	ldr q24, [x30, #5904]
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	ldr q25, [x30, #5920]
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	ldr q26, [x30, #5936]
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	bit v5.16b, v25.16b, v31.16b
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	bit v6.16b, v26.16b, v31.16b
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	add v17.2d, v17.2d, v18.2d
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	cmeq v16.2d, v17.2d, v19.2d
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	ldr q20, [x30, #6000]
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	ldr q21, [x30, #6016]
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	ldr q22, [x30, #6032]
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	bit v0.16b, v20.16b, v16.16b
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	bit v1.16b, v21.16b, v16.16b
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	bit v2.16b, v22.16b, v16.16b
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	add v30.2d, v30.2d, v18.2d
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	cmeq v31.2d, v30.2d, v19.2d
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	ldr q24, [x30, #6096]
	adcs x12, x12, x24
	adcs x13, x13, x25
	adc x21, x7, x7
	ldr q25, [x30, #6112]
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	ldr q26, [x30, #6128]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	bit v4.16b, v24.16b, v31.16b
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	ldr x2, [x0, #96]
	bit v5.16b, v25.16b, v31.16b
	sbcs x6, x12, x2
	ldr x2, [x0, #104]
	sbcs x16, x13, x2
	sbcs x2, x21, x7
	bit v6.16b, v26.16b, v31.16b
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	orr v0.16b, v0.16b, v4.16b
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	orr v1.16b, v1.16b, v5.16b
	str x8, [x0, #976]
	str x9, [x0, #984]
	str x10, [x0, #992]
	orr v2.16b, v2.16b, v6.16b
	str x11, [x0, #1000]
	str x12, [x0, #1008]
	str x13, [x0, #1016]
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
	sbc x3, x7, x7
	ldr x1, [x0, #1024]
	ldr x2, [x0, #880]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #880]
	ldr x1, [x0, #1032]
	ldr x2, [x0, #888]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #888]
	ldr x1, [x0, #1040]
	ldr x2, [x0, #896]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #896]
	ldr x1, [x0, #1048]
	ldr x2, [x0, #904]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #904]
	ldr x1, [x0, #1056]
	ldr x2, [x0, #912]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #912]
	ldr x1, [x0, #1064]
	ldr x2, [x0, #920]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #920]
	ldr x1, [x0, #1072]
	ldr x2, [x0, #928]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #928]
	ldr x1, [x0, #1080]
	ldr x2, [x0, #936]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #936]
	ldr x1, [x0, #1088]
	ldr x2, [x0, #944]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #944]
	ldr x1, [x0, #1096]
	ldr x2, [x0, #952]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #952]
	ldr x1, [x0, #1104]
	ldr x2, [x0, #960]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #960]
	ldr x1, [x0, #1112]
	ldr x2, [x0, #968]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #968]
	ldr x1, [x0, #1120]
	ldr x2, [x0, #976]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #976]
	ldr x1, [x0, #1128]
	ldr x2, [x0, #984]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #984]
	ldr x1, [x0, #1136]
	ldr x2, [x0, #992]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #992]
	ldr x1, [x0, #1144]
	ldr x2, [x0, #1000]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1000]
	ldr x1, [x0, #1152]
	ldr x2, [x0, #1008]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1008]
	ldr x1, [x0, #1160]
	ldr x2, [x0, #1016]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1016]
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
	ldrb w4, [x16, #2223]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #2230]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	movz x5, #1, lsl #0
	subs x16, x2, x5
	sbc x3, x7, x7
	ldr x1, [x0, #880]
	ldr x2, [x0, #736]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #736]
	ldr x1, [x0, #888]
	ldr x2, [x0, #744]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #744]
	ldr x1, [x0, #896]
	ldr x2, [x0, #752]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #752]
	ldr x1, [x0, #904]
	ldr x2, [x0, #760]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #760]
	ldr x1, [x0, #912]
	ldr x2, [x0, #768]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #768]
	ldr x1, [x0, #920]
	ldr x2, [x0, #776]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #776]
	ldr x1, [x0, #928]
	ldr x2, [x0, #784]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #784]
	ldr x1, [x0, #936]
	ldr x2, [x0, #792]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #792]
	ldr x1, [x0, #944]
	ldr x2, [x0, #800]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #800]
	ldr x1, [x0, #952]
	ldr x2, [x0, #808]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #808]
	ldr x1, [x0, #960]
	ldr x2, [x0, #816]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #816]
	ldr x1, [x0, #968]
	ldr x2, [x0, #824]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #824]
	ldr x1, [x0, #976]
	ldr x2, [x0, #832]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #832]
	ldr x1, [x0, #984]
	ldr x2, [x0, #840]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #840]
	ldr x1, [x0, #992]
	ldr x2, [x0, #848]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #848]
	ldr x1, [x0, #1000]
	ldr x2, [x0, #856]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #856]
	ldr x1, [x0, #1008]
	ldr x2, [x0, #864]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #864]
	ldr x1, [x0, #1016]
	ldr x2, [x0, #872]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #872]
	add x19, x19, #1
	sub x4, x19, #55
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
	ldrb w4, [x16, #2223]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #2230]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	movz x5, #1, lsl #0
	movi v16.2d, #0
	cmeq v16.2d, v16.2d, v19.2d
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[0], x6
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v0.16b, v20.16b, v16.16b
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v1.16b, v20.16b, v16.16b
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	str q3, [x0, #1024]
	str q7, [x0, #1040]
	str q23, [x0, #1056]
	str q0, [x0, #1072]
	str q1, [x0, #1088]
	str q2, [x0, #1104]
	subs x4, x2, x5
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1120]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1128]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1136]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1144]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #1152]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
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
	movz x7, #0, lsl #0
	ldrb w4, [x16, #2230]
	sub x3, x7, x4
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
	sub x4, x19, #54
	cbnz x4, 21b
	ldr x4, [x0, #832]
	ldr x5, [x0, #840]
	ldr x16, [x0, #848]
	ldr x17, [x0, #856]
	ldr x21, [x0, #864]
	ldr x22, [x0, #872]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	mul x2, x4, x5
	adds x9, x9, x2
	mul x2, x4, x16
	adcs x10, x10, x2
	mul x2, x4, x17
	adcs x11, x11, x2
	mul x2, x4, x21
	adcs x12, x12, x2
	mul x2, x4, x22
	adcs x13, x13, x2
	umulh x2, x4, x22
	adcs x14, x14, x2
	umulh x2, x4, x5
	adds x10, x10, x2
	umulh x2, x4, x16
	adcs x11, x11, x2
	umulh x2, x4, x17
	adcs x12, x12, x2
	umulh x2, x4, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x2, x5, x16
	adds x11, x11, x2
	mul x2, x5, x17
	adcs x12, x12, x2
	mul x2, x5, x21
	adcs x13, x13, x2
	mul x2, x5, x22
	adcs x14, x14, x2
	umulh x2, x5, x22
	adcs x15, x15, x2
	umulh x2, x5, x16
	adds x12, x12, x2
	umulh x2, x5, x17
	adcs x13, x13, x2
	umulh x2, x5, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	mul x2, x16, x17
	adds x13, x13, x2
	mul x2, x16, x21
	adcs x14, x14, x2
	mul x2, x16, x22
	adcs x15, x15, x2
	umulh x2, x16, x22
	adcs x6, x6, x2
	umulh x2, x16, x17
	adds x14, x14, x2
	umulh x2, x16, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	mul x2, x17, x21
	adds x15, x15, x2
	mul x2, x17, x22
	adcs x6, x6, x2
	umulh x2, x17, x22
	adcs x23, x23, x2
	umulh x2, x17, x21
	adds x6, x6, x2
	adcs x23, x23, x7
	mul x2, x21, x22
	adds x23, x23, x2
	umulh x2, x21, x22
	adcs x24, x24, x2
	adds x8, x8, x8
	adcs x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adcs x15, x15, x15
	adcs x6, x6, x6
	adcs x23, x23, x23
	adcs x24, x24, x24
	adcs x25, x25, x25
	mul x2, x4, x4
	adds x8, x8, x2
	umulh x2, x4, x4
	adcs x9, x9, x2
	mul x2, x5, x5
	adcs x10, x10, x2
	umulh x2, x5, x5
	adcs x11, x11, x2
	mul x2, x16, x16
	adcs x12, x12, x2
	umulh x2, x16, x16
	adcs x13, x13, x2
	mul x2, x17, x17
	adcs x14, x14, x2
	umulh x2, x17, x17
	adcs x15, x15, x2
	mul x2, x21, x21
	adcs x6, x6, x2
	umulh x2, x21, x21
	adcs x23, x23, x2
	mul x2, x22, x22
	adcs x24, x24, x2
	umulh x2, x22, x22
	adcs x25, x25, x2
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1168]
	str x9, [x0, #1176]
	str x10, [x0, #1184]
	str x11, [x0, #1192]
	str x12, [x0, #1200]
	str x13, [x0, #1208]
	ldr x4, [x0, #1168]
	ldr x5, [x0, #1176]
	ldr x16, [x0, #1184]
	ldr x17, [x0, #1192]
	ldr x21, [x0, #1200]
	ldr x22, [x0, #1208]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #1024]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #1032]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #1040]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #1048]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #1056]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #1064]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	ldr x4, [x0, #1168]
	ldr x5, [x0, #1176]
	ldr x16, [x0, #1184]
	ldr x17, [x0, #1192]
	ldr x21, [x0, #1200]
	ldr x22, [x0, #1208]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #832]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #840]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #848]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #856]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #864]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #872]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	ldr x4, [x0, #1264]
	ldr x5, [x0, #1272]
	ldr x16, [x0, #1280]
	ldr x17, [x0, #1288]
	ldr x21, [x0, #1296]
	ldr x22, [x0, #1304]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #1072]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #1080]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #1088]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #1096]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #1104]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #1112]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	movz x7, #0, lsl #0
	ldr x8, [x0, #1216]
	ldr x9, [x0, #1224]
	ldr x10, [x0, #1232]
	ldr x11, [x0, #1240]
	ldr x12, [x0, #1248]
	ldr x13, [x0, #1256]
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
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1264]
	ldr x9, [x0, #1272]
	ldr x10, [x0, #1280]
	ldr x11, [x0, #1288]
	ldr x12, [x0, #1296]
	ldr x13, [x0, #1304]
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
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x10, [x0, #1280]
	str x11, [x0, #1288]
	str x12, [x0, #1296]
	str x13, [x0, #1304]
	ldr x4, [x0, #1216]
	ldr x5, [x0, #1224]
	ldr x16, [x0, #1232]
	ldr x17, [x0, #1240]
	ldr x21, [x0, #1248]
	ldr x22, [x0, #1256]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	mul x2, x4, x5
	adds x9, x9, x2
	mul x2, x4, x16
	adcs x10, x10, x2
	mul x2, x4, x17
	adcs x11, x11, x2
	mul x2, x4, x21
	adcs x12, x12, x2
	mul x2, x4, x22
	adcs x13, x13, x2
	umulh x2, x4, x22
	adcs x14, x14, x2
	umulh x2, x4, x5
	adds x10, x10, x2
	umulh x2, x4, x16
	adcs x11, x11, x2
	umulh x2, x4, x17
	adcs x12, x12, x2
	umulh x2, x4, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x2, x5, x16
	adds x11, x11, x2
	mul x2, x5, x17
	adcs x12, x12, x2
	mul x2, x5, x21
	adcs x13, x13, x2
	mul x2, x5, x22
	adcs x14, x14, x2
	umulh x2, x5, x22
	adcs x15, x15, x2
	umulh x2, x5, x16
	adds x12, x12, x2
	umulh x2, x5, x17
	adcs x13, x13, x2
	umulh x2, x5, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	mul x2, x16, x17
	adds x13, x13, x2
	mul x2, x16, x21
	adcs x14, x14, x2
	mul x2, x16, x22
	adcs x15, x15, x2
	umulh x2, x16, x22
	adcs x6, x6, x2
	umulh x2, x16, x17
	adds x14, x14, x2
	umulh x2, x16, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	mul x2, x17, x21
	adds x15, x15, x2
	mul x2, x17, x22
	adcs x6, x6, x2
	umulh x2, x17, x22
	adcs x23, x23, x2
	umulh x2, x17, x21
	adds x6, x6, x2
	adcs x23, x23, x7
	mul x2, x21, x22
	adds x23, x23, x2
	umulh x2, x21, x22
	adcs x24, x24, x2
	adds x8, x8, x8
	adcs x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adcs x15, x15, x15
	adcs x6, x6, x6
	adcs x23, x23, x23
	adcs x24, x24, x24
	adcs x25, x25, x25
	mul x2, x4, x4
	adds x8, x8, x2
	umulh x2, x4, x4
	adcs x9, x9, x2
	mul x2, x5, x5
	adcs x10, x10, x2
	umulh x2, x5, x5
	adcs x11, x11, x2
	mul x2, x16, x16
	adcs x12, x12, x2
	umulh x2, x16, x16
	adcs x13, x13, x2
	mul x2, x17, x17
	adcs x14, x14, x2
	umulh x2, x17, x17
	adcs x15, x15, x2
	mul x2, x21, x21
	adcs x6, x6, x2
	umulh x2, x21, x21
	adcs x23, x23, x2
	mul x2, x22, x22
	adcs x24, x24, x2
	umulh x2, x22, x22
	adcs x25, x25, x2
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	ldr x21, [x0, #1344]
	ldr x22, [x0, #1352]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #1216]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #1224]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #1232]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #1240]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #1248]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #1256]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	ldr x21, [x0, #1344]
	ldr x22, [x0, #1352]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #736]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #744]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #752]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #760]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #768]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #776]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	ldr x4, [x0, #1264]
	ldr x5, [x0, #1272]
	ldr x16, [x0, #1280]
	ldr x17, [x0, #1288]
	ldr x21, [x0, #1296]
	ldr x22, [x0, #1304]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	mul x2, x4, x5
	adds x9, x9, x2
	mul x2, x4, x16
	adcs x10, x10, x2
	mul x2, x4, x17
	adcs x11, x11, x2
	mul x2, x4, x21
	adcs x12, x12, x2
	mul x2, x4, x22
	adcs x13, x13, x2
	umulh x2, x4, x22
	adcs x14, x14, x2
	umulh x2, x4, x5
	adds x10, x10, x2
	umulh x2, x4, x16
	adcs x11, x11, x2
	umulh x2, x4, x17
	adcs x12, x12, x2
	umulh x2, x4, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x2, x5, x16
	adds x11, x11, x2
	mul x2, x5, x17
	adcs x12, x12, x2
	mul x2, x5, x21
	adcs x13, x13, x2
	mul x2, x5, x22
	adcs x14, x14, x2
	umulh x2, x5, x22
	adcs x15, x15, x2
	umulh x2, x5, x16
	adds x12, x12, x2
	umulh x2, x5, x17
	adcs x13, x13, x2
	umulh x2, x5, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	mul x2, x16, x17
	adds x13, x13, x2
	mul x2, x16, x21
	adcs x14, x14, x2
	mul x2, x16, x22
	adcs x15, x15, x2
	umulh x2, x16, x22
	adcs x6, x6, x2
	umulh x2, x16, x17
	adds x14, x14, x2
	umulh x2, x16, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	mul x2, x17, x21
	adds x15, x15, x2
	mul x2, x17, x22
	adcs x6, x6, x2
	umulh x2, x17, x22
	adcs x23, x23, x2
	umulh x2, x17, x21
	adds x6, x6, x2
	adcs x23, x23, x7
	mul x2, x21, x22
	adds x23, x23, x2
	umulh x2, x21, x22
	adcs x24, x24, x2
	adds x8, x8, x8
	adcs x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adcs x15, x15, x15
	adcs x6, x6, x6
	adcs x23, x23, x23
	adcs x24, x24, x24
	adcs x25, x25, x25
	mul x2, x4, x4
	adds x8, x8, x2
	umulh x2, x4, x4
	adcs x9, x9, x2
	mul x2, x5, x5
	adcs x10, x10, x2
	umulh x2, x5, x5
	adcs x11, x11, x2
	mul x2, x16, x16
	adcs x12, x12, x2
	umulh x2, x16, x16
	adcs x13, x13, x2
	mul x2, x17, x17
	adcs x14, x14, x2
	umulh x2, x17, x17
	adcs x15, x15, x2
	mul x2, x21, x21
	adcs x6, x6, x2
	umulh x2, x21, x21
	adcs x23, x23, x2
	mul x2, x22, x22
	adcs x24, x24, x2
	umulh x2, x22, x22
	adcs x25, x25, x2
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
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
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	movz x7, #0, lsl #0
	ldr x8, [x0, #880]
	ldr x9, [x0, #888]
	ldr x10, [x0, #896]
	ldr x11, [x0, #904]
	ldr x12, [x0, #912]
	ldr x13, [x0, #920]
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	str x10, [x0, #896]
	str x11, [x0, #904]
	str x12, [x0, #912]
	str x13, [x0, #920]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1312]
	ldr x9, [x0, #1320]
	ldr x10, [x0, #1328]
	ldr x11, [x0, #1336]
	ldr x12, [x0, #1344]
	ldr x13, [x0, #1352]
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
	str x8, [x0, #1312]
	str x9, [x0, #1320]
	str x10, [x0, #1328]
	str x11, [x0, #1336]
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	ldr x21, [x0, #1344]
	ldr x22, [x0, #1352]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #1264]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #1272]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #1280]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #1288]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #1296]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #1304]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	ldr x4, [x0, #1360]
	ldr x5, [x0, #1368]
	ldr x16, [x0, #1376]
	ldr x17, [x0, #1384]
	ldr x21, [x0, #1392]
	ldr x22, [x0, #1400]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #784]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #792]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #800]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #808]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #816]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #824]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	str x8, [x0, #928]
	str x9, [x0, #936]
	str x10, [x0, #944]
	str x11, [x0, #952]
	str x12, [x0, #960]
	str x13, [x0, #968]
	ldr x4, [x0, #1216]
	ldr x5, [x0, #1224]
	ldr x16, [x0, #1232]
	ldr x17, [x0, #1240]
	ldr x21, [x0, #1248]
	ldr x22, [x0, #1256]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #832]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #840]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #848]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #856]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #864]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #872]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	sbc x3, x7, x7
	ldr x1, [x0, #1024]
	ldr x2, [x0, #880]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #880]
	ldr x1, [x0, #1032]
	ldr x2, [x0, #888]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #888]
	ldr x1, [x0, #1040]
	ldr x2, [x0, #896]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #896]
	ldr x1, [x0, #1048]
	ldr x2, [x0, #904]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #904]
	ldr x1, [x0, #1056]
	ldr x2, [x0, #912]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #912]
	ldr x1, [x0, #1064]
	ldr x2, [x0, #920]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #920]
	ldr x1, [x0, #1072]
	ldr x2, [x0, #928]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #928]
	ldr x1, [x0, #1080]
	ldr x2, [x0, #936]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #936]
	ldr x1, [x0, #1088]
	ldr x2, [x0, #944]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #944]
	ldr x1, [x0, #1096]
	ldr x2, [x0, #952]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #952]
	ldr x1, [x0, #1104]
	ldr x2, [x0, #960]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #960]
	ldr x1, [x0, #1112]
	ldr x2, [x0, #968]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #968]
	ldr x1, [x0, #1120]
	ldr x2, [x0, #976]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #976]
	ldr x1, [x0, #1128]
	ldr x2, [x0, #984]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #984]
	ldr x1, [x0, #1136]
	ldr x2, [x0, #992]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #992]
	ldr x1, [x0, #1144]
	ldr x2, [x0, #1000]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1000]
	ldr x1, [x0, #1152]
	ldr x2, [x0, #1008]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1008]
	ldr x1, [x0, #1160]
	ldr x2, [x0, #1016]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1016]
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
	ldrb w4, [x16, #2223]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #2230]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	movz x5, #1, lsl #0
	subs x16, x2, x5
	sbc x3, x7, x7
	ldr x1, [x0, #880]
	ldr x2, [x0, #736]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #736]
	ldr x1, [x0, #888]
	ldr x2, [x0, #744]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #744]
	ldr x1, [x0, #896]
	ldr x2, [x0, #752]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #752]
	ldr x1, [x0, #904]
	ldr x2, [x0, #760]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #760]
	ldr x1, [x0, #912]
	ldr x2, [x0, #768]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #768]
	ldr x1, [x0, #920]
	ldr x2, [x0, #776]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #776]
	ldr x1, [x0, #928]
	ldr x2, [x0, #784]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #784]
	ldr x1, [x0, #936]
	ldr x2, [x0, #792]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #792]
	ldr x1, [x0, #944]
	ldr x2, [x0, #800]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #800]
	ldr x1, [x0, #952]
	ldr x2, [x0, #808]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #808]
	ldr x1, [x0, #960]
	ldr x2, [x0, #816]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #816]
	ldr x1, [x0, #968]
	ldr x2, [x0, #824]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #824]
	ldr x1, [x0, #976]
	ldr x2, [x0, #832]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #832]
	ldr x1, [x0, #984]
	ldr x2, [x0, #840]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #840]
	ldr x1, [x0, #992]
	ldr x2, [x0, #848]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #848]
	ldr x1, [x0, #1000]
	ldr x2, [x0, #856]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #856]
	ldr x1, [x0, #1008]
	ldr x2, [x0, #864]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #864]
	ldr x1, [x0, #1016]
	ldr x2, [x0, #872]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #872]
	add x19, x19, #1
	sub x4, x19, #55
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
	sbc x3, x7, x7
	ldr x1, [x0, #208]
	ldr x2, [x0, #784]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #784]
	ldr x1, [x0, #216]
	ldr x2, [x0, #792]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #792]
	ldr x1, [x0, #224]
	ldr x2, [x0, #800]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #800]
	ldr x1, [x0, #232]
	ldr x2, [x0, #808]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #808]
	ldr x1, [x0, #240]
	ldr x2, [x0, #816]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #816]
	ldr x1, [x0, #248]
	ldr x2, [x0, #824]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #824]
	sub x4, x7, #1
	eor x3, x3, x4
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #784]
	orr x1, x1, x2
	str x1, [x0, #784]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #792]
	orr x1, x1, x2
	str x1, [x0, #792]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #800]
	orr x1, x1, x2
	str x1, [x0, #800]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #808]
	orr x1, x1, x2
	str x1, [x0, #808]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #816]
	orr x1, x1, x2
	str x1, [x0, #816]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #824]
	orr x1, x1, x2
	str x1, [x0, #824]
	ldr x4, [x0, #832]
	ldr x5, [x0, #840]
	ldr x16, [x0, #848]
	ldr x17, [x0, #856]
	ldr x21, [x0, #864]
	ldr x22, [x0, #872]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #736]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #744]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #752]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #760]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #768]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #776]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	ldr x4, [x0, #832]
	ldr x5, [x0, #840]
	ldr x16, [x0, #848]
	ldr x17, [x0, #856]
	ldr x21, [x0, #864]
	ldr x22, [x0, #872]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	mul x2, x4, x5
	adds x9, x9, x2
	mul x2, x4, x16
	adcs x10, x10, x2
	mul x2, x4, x17
	adcs x11, x11, x2
	mul x2, x4, x21
	adcs x12, x12, x2
	mul x2, x4, x22
	adcs x13, x13, x2
	umulh x2, x4, x22
	adcs x14, x14, x2
	umulh x2, x4, x5
	adds x10, x10, x2
	umulh x2, x4, x16
	adcs x11, x11, x2
	umulh x2, x4, x17
	adcs x12, x12, x2
	umulh x2, x4, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x2, x5, x16
	adds x11, x11, x2
	mul x2, x5, x17
	adcs x12, x12, x2
	mul x2, x5, x21
	adcs x13, x13, x2
	mul x2, x5, x22
	adcs x14, x14, x2
	umulh x2, x5, x22
	adcs x15, x15, x2
	umulh x2, x5, x16
	adds x12, x12, x2
	umulh x2, x5, x17
	adcs x13, x13, x2
	umulh x2, x5, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	mul x2, x16, x17
	adds x13, x13, x2
	mul x2, x16, x21
	adcs x14, x14, x2
	mul x2, x16, x22
	adcs x15, x15, x2
	umulh x2, x16, x22
	adcs x6, x6, x2
	umulh x2, x16, x17
	adds x14, x14, x2
	umulh x2, x16, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	mul x2, x17, x21
	adds x15, x15, x2
	mul x2, x17, x22
	adcs x6, x6, x2
	umulh x2, x17, x22
	adcs x23, x23, x2
	umulh x2, x17, x21
	adds x6, x6, x2
	adcs x23, x23, x7
	mul x2, x21, x22
	adds x23, x23, x2
	umulh x2, x21, x22
	adcs x24, x24, x2
	adds x8, x8, x8
	adcs x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adcs x15, x15, x15
	adcs x6, x6, x6
	adcs x23, x23, x23
	adcs x24, x24, x24
	adcs x25, x25, x25
	mul x2, x4, x4
	adds x8, x8, x2
	umulh x2, x4, x4
	adcs x9, x9, x2
	mul x2, x5, x5
	adcs x10, x10, x2
	umulh x2, x5, x5
	adcs x11, x11, x2
	mul x2, x16, x16
	adcs x12, x12, x2
	umulh x2, x16, x16
	adcs x13, x13, x2
	mul x2, x17, x17
	adcs x14, x14, x2
	umulh x2, x17, x17
	adcs x15, x15, x2
	mul x2, x21, x21
	adcs x6, x6, x2
	umulh x2, x21, x21
	adcs x23, x23, x2
	mul x2, x22, x22
	adcs x24, x24, x2
	umulh x2, x22, x22
	adcs x25, x25, x2
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x0, #1168]
	str x9, [x0, #1176]
	str x10, [x0, #1184]
	str x11, [x0, #1192]
	str x12, [x0, #1200]
	str x13, [x0, #1208]
	ldr x4, [x0, #832]
	ldr x5, [x0, #840]
	ldr x16, [x0, #848]
	ldr x17, [x0, #856]
	ldr x21, [x0, #864]
	ldr x22, [x0, #872]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	ldr x1, [x0, #1168]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x21
	adcs x12, x12, x2
	mul x2, x1, x22
	adcs x13, x13, x2
	umulh x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x1, [x0, #1176]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x21
	adcs x13, x13, x2
	mul x2, x1, x22
	adcs x14, x14, x2
	umulh x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x1, [x0, #1184]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x21
	adcs x14, x14, x2
	mul x2, x1, x22
	adcs x15, x15, x2
	umulh x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	ldr x1, [x0, #1192]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x21
	adcs x15, x15, x2
	mul x2, x1, x22
	adcs x6, x6, x2
	umulh x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x21
	adcs x6, x6, x2
	adcs x23, x23, x7
	ldr x1, [x0, #1200]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x21
	adcs x6, x6, x2
	mul x2, x1, x22
	adcs x23, x23, x2
	umulh x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x6, x6, x2
	umulh x2, x1, x21
	adcs x23, x23, x2
	adcs x24, x24, x7
	ldr x1, [x0, #1208]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x6, x6, x2
	mul x2, x1, x21
	adcs x23, x23, x2
	mul x2, x1, x22
	adcs x24, x24, x2
	umulh x2, x1, x22
	adcs x25, x25, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x6, x6, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x21
	adcs x24, x24, x2
	adcs x25, x25, x7
	ldr x17, [x0, #64]
	sub x16, x7, x17
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
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
	sbcs x2, x21, x7
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
	bl {vg_p384_mul_mod_n}
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
	bl {vg_p384_inv_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1888, lsl #0
	movz x2, #1792, lsl #0
	movz x3, #544, lsl #0
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1936, lsl #0
	movz x2, #1600, lsl #0
	movz x3, #544, lsl #0
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #1984, lsl #0
	movz x2, #1648, lsl #0
	movz x3, #544, lsl #0
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2032, lsl #0
	movz x2, #1888, lsl #0
	movz x3, #1936, lsl #0
	bl {vg_p384_mul_mod_n}
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
	bl {vg_p384_mul_mod_n}
	umov x30, v29.d[0]
	mov v29.d[0], x30
	movz x1, #2128, lsl #0
	movz x2, #2080, lsl #0
	movz x3, #256, lsl #0
	bl {vg_p384_mul_mod_n}
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
