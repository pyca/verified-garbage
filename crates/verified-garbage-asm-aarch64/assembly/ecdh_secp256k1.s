// The functions of `src/ecdh_secp256k1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_secp256k1:
	add x4, x3, #0
	add x6, x2, #0
	add x3, x1, #0
	add x2, x2, #1
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
	ldr x5, [x3, #24]
	rev x5, x5
	str x5, [x0, #1056]
	ldr x5, [x3, #16]
	rev x5, x5
	str x5, [x0, #1064]
	ldr x5, [x3, #8]
	rev x5, x5
	str x5, [x0, #1072]
	ldr x5, [x3, #0]
	rev x5, x5
	str x5, [x0, #1080]
	ldr x5, [x1, #24]
	rev x5, x5
	str x5, [x0, #1088]
	ldr x5, [x1, #16]
	rev x5, x5
	str x5, [x0, #1096]
	ldr x5, [x1, #8]
	rev x5, x5
	str x5, [x0, #1104]
	ldr x5, [x1, #0]
	rev x5, x5
	str x5, [x0, #1112]
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #1120]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1128]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1136]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1144]
	movz x1, #64559, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65534, lsl #32
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
	movz x1, #16705, lsl #0
	movk x1, #53302, lsl #16
	movk x1, #24204, lsl #32
	movk x1, #49106, lsl #48
	str x1, [x0, #96]
	movz x1, #41019, lsl #0
	movk x1, #44872, lsl #16
	movk x1, #56550, lsl #32
	movk x1, #47790, lsl #48
	str x1, [x0, #104]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #112]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #120]
	movz x1, #0, lsl #0
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #192]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #200]
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
	movz x1, #977, lsl #0
	movk x1, #0, lsl #16
	movk x1, #1, lsl #32
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
	movz x1, #6839, lsl #0
	movk x1, #0, lsl #16
	movk x1, #7, lsl #32
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
	movz x1, #8343, lsl #0
	movk x1, #18558, lsl #16
	movk x1, #11866, lsl #32
	movk x1, #55094, lsl #48
	str x1, [x0, #320]
	movz x1, #26331, lsl #0
	movk x1, #10684, lsl #16
	movk x1, #10579, lsl #32
	movk x1, #8990, lsl #48
	str x1, [x0, #328]
	movz x1, #4764, lsl #0
	movk x1, #13309, lsl #16
	movk x1, #18624, lsl #32
	movk x1, #38815, lsl #48
	str x1, [x0, #336]
	movz x1, #40776, lsl #0
	movk x1, #59656, lsl #16
	movk x1, #58947, lsl #32
	movk x1, #39297, lsl #48
	str x1, [x0, #344]
	movz x1, #44002, lsl #0
	movk x1, #54235, lsl #16
	movk x1, #42706, lsl #32
	movk x1, #45406, lsl #48
	str x1, [x0, #352]
	movz x1, #50765, lsl #0
	movk x1, #7965, lsl #16
	movk x1, #23901, lsl #32
	movk x1, #36348, lsl #48
	str x1, [x0, #360]
	movz x1, #49462, lsl #0
	movk x1, #44057, lsl #16
	movk x1, #46490, lsl #32
	movk x1, #28854, lsl #48
	str x1, [x0, #368]
	movz x1, #33494, lsl #0
	movk x1, #54437, lsl #16
	movk x1, #34079, lsl #32
	movk x1, #53055, lsl #48
	str x1, [x0, #376]
	movz x1, #53568, lsl #0
	movk x1, #26583, lsl #16
	movk x1, #61972, lsl #32
	movk x1, #35180, lsl #48
	str x1, [x0, #384]
	movz x1, #63608, lsl #0
	movk x1, #3708, lsl #16
	movk x1, #38594, lsl #32
	movk x1, #29716, lsl #48
	str x1, [x0, #392]
	movz x1, #1990, lsl #0
	movk x1, #23501, lsl #16
	movk x1, #62948, lsl #32
	movk x1, #59031, lsl #48
	str x1, [x0, #400]
	movz x1, #39877, lsl #0
	movk x1, #33222, lsl #16
	movk x1, #7381, lsl #32
	movk x1, #40295, lsl #48
	str x1, [x0, #408]
	movz x1, #48831, lsl #0
	movk x1, #12233, lsl #16
	movk x1, #41331, lsl #32
	movk x1, #16429, lsl #48
	str x1, [x0, #416]
	movz x1, #24516, lsl #0
	movk x1, #20663, lsl #16
	movk x1, #8985, lsl #32
	movk x1, #17745, lsl #48
	str x1, [x0, #424]
	movz x1, #1, lsl #0
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
	str x1, [x0, #512]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #520]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #528]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #536]
	movz x1, #977, lsl #0
	movk x1, #0, lsl #16
	movk x1, #1, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #544]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #552]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #560]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #568]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #576]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #584]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #592]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #600]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1472]
	movz x19, #32, lsl #0
	movz x5, #1, lsl #0
20:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #1056]
	lsl x17, x19, #3
	add x17, x0, x17
	and x2, x1, x5
	strb w2, [x17, #1504]
	lsr x2, x1, #1
	and x2, x2, x5
	strb w2, [x17, #1505]
	lsr x2, x1, #2
	and x2, x2, x5
	strb w2, [x17, #1506]
	lsr x2, x1, #3
	and x2, x2, x5
	strb w2, [x17, #1507]
	lsr x2, x1, #4
	and x2, x2, x5
	strb w2, [x17, #1508]
	lsr x2, x1, #5
	and x2, x2, x5
	strb w2, [x17, #1509]
	lsr x2, x1, #6
	and x2, x2, x5
	strb w2, [x17, #1510]
	lsr x2, x1, #7
	and x2, x2, x5
	strb w2, [x17, #1511]
	cbnz x19, 20b
	movz x1, #37025, lsl #0
	movk x1, #14, lsl #16
	movk x1, #1954, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1312]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1320]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1336]
	movz x1, #6839, lsl #0
	movk x1, #0, lsl #16
	movk x1, #7, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1344]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1352]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1368]
	add x2, x6, #33
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #1216]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1224]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1232]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1240]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	movz x5, #4, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	mov v28.d[0], x30
	bl {vg_secp256k1_check_point}
	umov x30, v28.d[0]
	movz x1, #20517, lsl #0
	movk x1, #0, lsl #16
	movk x1, #21, lsl #32
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
	ldr x1, [x0, #1280]
	str x1, [x0, #512]
	ldr x1, [x0, #1288]
	str x1, [x0, #520]
	ldr x1, [x0, #1296]
	str x1, [x0, #528]
	ldr x1, [x0, #1304]
	str x1, [x0, #536]
	ldr x1, [x0, #1440]
	str x1, [x0, #544]
	ldr x1, [x0, #1448]
	str x1, [x0, #552]
	ldr x1, [x0, #1456]
	str x1, [x0, #560]
	ldr x1, [x0, #1464]
	str x1, [x0, #568]
	movz x1, #20517, lsl #0
	movk x1, #0, lsl #16
	movk x1, #21, lsl #32
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
	mov v29.d[0], x30
	bl {vg_secp256k1_mul}
	umov x30, v29.d[0]
	movz x1, #6839, lsl #0
	movk x1, #0, lsl #16
	movk x1, #7, lsl #32
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
	mov v29.d[0], x30
	bl {vg_secp256k1_inv_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x4, [x0, #992]
	ldr x5, [x0, #1000]
	ldr x16, [x0, #1008]
	ldr x17, [x0, #1016]
	movz x6, #13617, lsl #0
	movk x6, #53797, lsl #16
	movk x6, #2333, lsl #32
	movk x6, #55352, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #512]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #520]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	adcs x8, x8, x7
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x13, x13, x2
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
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #528]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	adcs x9, x9, x7
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
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
	ldr x3, [x0, #88]
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
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #536]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	adcs x10, x10, x7
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
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
	adcs x8, x8, x2
	ldr x3, [x0, #88]
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
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #64]
	subs x1, x12, x2
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1152]
	str x13, [x0, #1160]
	str x8, [x0, #1168]
	str x9, [x0, #1176]
	movz x7, #0, lsl #0
	ldr x4, [x0, #192]
	ldr x5, [x0, #200]
	ldr x16, [x0, #208]
	ldr x17, [x0, #216]
	movz x6, #13617, lsl #0
	movk x6, #53797, lsl #16
	movk x6, #2333, lsl #32
	movk x6, #55352, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1152]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1160]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	adcs x8, x8, x7
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x13, x13, x2
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
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1168]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	adcs x9, x9, x7
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
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
	ldr x3, [x0, #88]
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
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1176]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	adcs x10, x10, x7
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
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
	adcs x8, x8, x2
	ldr x3, [x0, #88]
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
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #64]
	subs x1, x12, x2
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x8, [x0, #1200]
	str x9, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1088]
	ldr x2, [x0, #96]
	subs x16, x1, x2
	ldr x1, [x0, #1096]
	ldr x2, [x0, #104]
	sbcs x16, x1, x2
	ldr x1, [x0, #1104]
	ldr x2, [x0, #112]
	sbcs x16, x1, x2
	ldr x1, [x0, #1112]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1088]
	ldr x2, [x0, #1096]
	orr x1, x1, x2
	ldr x2, [x0, #1104]
	orr x1, x1, x2
	ldr x2, [x0, #1112]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	movz x7, #0, lsl #0
	ldr x1, [x0, #576]
	ldr x2, [x0, #584]
	orr x1, x1, x2
	ldr x2, [x0, #592]
	orr x1, x1, x2
	ldr x2, [x0, #600]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	ldr x3, [x0, #1472]
	ldr x1, [x0, #1184]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #24]
	ldr x1, [x0, #1192]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #16]
	ldr x1, [x0, #1200]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #8]
	ldr x1, [x0, #1208]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #0]
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
