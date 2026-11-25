// The functions of `src/ecdsa_p256.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_verify:
	sub sp, sp, #80
	add x5, sp, #0
	lsr x10, x2, #7
	movz x11, #127, lsl #0
	and x12, x2, x11
	add x12, x12, #96
	lsr x12, x12, #7
	orr x11, x10, x12
	cbnz x11, 20f
	movz x12, #0, lsl #0
	strb w12, [x5, #0]
	strb w12, [x5, #1]
	strb w12, [x5, #2]
	strb w12, [x5, #3]
	strb w12, [x5, #4]
	strb w12, [x5, #5]
	strb w12, [x5, #6]
	strb w12, [x5, #7]
	strb w12, [x5, #8]
	strb w12, [x5, #9]
	strb w12, [x5, #10]
	strb w12, [x5, #11]
	strb w12, [x5, #12]
	strb w12, [x5, #13]
	strb w12, [x5, #14]
	strb w12, [x5, #15]
	strb w12, [x5, #16]
	strb w12, [x5, #17]
	strb w12, [x5, #18]
	strb w12, [x5, #19]
	strb w12, [x5, #20]
	strb w12, [x5, #21]
	strb w12, [x5, #22]
	strb w12, [x5, #23]
	strb w12, [x5, #24]
	strb w12, [x5, #25]
	strb w12, [x5, #26]
	strb w12, [x5, #27]
	strb w12, [x5, #28]
	strb w12, [x5, #29]
	strb w12, [x5, #30]
	strb w12, [x5, #31]
	strb w12, [x5, #32]
	strb w12, [x5, #33]
	strb w12, [x5, #34]
	strb w12, [x5, #35]
	strb w12, [x5, #36]
	strb w12, [x5, #37]
	strb w12, [x5, #38]
	strb w12, [x5, #39]
	strb w12, [x5, #40]
	strb w12, [x5, #41]
	strb w12, [x5, #42]
	strb w12, [x5, #43]
	strb w12, [x5, #44]
	strb w12, [x5, #45]
	strb w12, [x5, #46]
	strb w12, [x5, #47]
	strb w12, [x5, #48]
	strb w12, [x5, #49]
	strb w12, [x5, #50]
	strb w12, [x5, #51]
	strb w12, [x5, #52]
	strb w12, [x5, #53]
	strb w12, [x5, #54]
	strb w12, [x5, #55]
	strb w12, [x5, #56]
	strb w12, [x5, #57]
	strb w12, [x5, #58]
	strb w12, [x5, #59]
	strb w12, [x5, #60]
	strb w12, [x5, #61]
	strb w12, [x5, #62]
	strb w12, [x5, #63]
	strb w12, [x5, #64]
	strb w12, [x5, #65]
	strb w12, [x5, #66]
	strb w12, [x5, #67]
	strb w12, [x5, #68]
	strb w12, [x5, #69]
	strb w12, [x5, #70]
	strb w12, [x5, #71]
	add x13, x5, #32
	sub x13, x13, x2
	cbz x2, 22f
24:
	ldrb w9, [x1, #0]
	strb w9, [x13, #0]
	add x1, x1, #1
	add x13, x13, #1
	sub x2, x2, #1
	cbnz x2, 24b
	b 23f
22:
23:
	b 21f
20:
	ldrb w9, [x1, #0]
	strb w9, [x5, #0]
	ldrb w9, [x1, #1]
	strb w9, [x5, #1]
	ldrb w9, [x1, #2]
	strb w9, [x5, #2]
	ldrb w9, [x1, #3]
	strb w9, [x5, #3]
	ldrb w9, [x1, #4]
	strb w9, [x5, #4]
	ldrb w9, [x1, #5]
	strb w9, [x5, #5]
	ldrb w9, [x1, #6]
	strb w9, [x5, #6]
	ldrb w9, [x1, #7]
	strb w9, [x5, #7]
	ldrb w9, [x1, #8]
	strb w9, [x5, #8]
	ldrb w9, [x1, #9]
	strb w9, [x5, #9]
	ldrb w9, [x1, #10]
	strb w9, [x5, #10]
	ldrb w9, [x1, #11]
	strb w9, [x5, #11]
	ldrb w9, [x1, #12]
	strb w9, [x5, #12]
	ldrb w9, [x1, #13]
	strb w9, [x5, #13]
	ldrb w9, [x1, #14]
	strb w9, [x5, #14]
	ldrb w9, [x1, #15]
	strb w9, [x5, #15]
	ldrb w9, [x1, #16]
	strb w9, [x5, #16]
	ldrb w9, [x1, #17]
	strb w9, [x5, #17]
	ldrb w9, [x1, #18]
	strb w9, [x5, #18]
	ldrb w9, [x1, #19]
	strb w9, [x5, #19]
	ldrb w9, [x1, #20]
	strb w9, [x5, #20]
	ldrb w9, [x1, #21]
	strb w9, [x5, #21]
	ldrb w9, [x1, #22]
	strb w9, [x5, #22]
	ldrb w9, [x1, #23]
	strb w9, [x5, #23]
	ldrb w9, [x1, #24]
	strb w9, [x5, #24]
	ldrb w9, [x1, #25]
	strb w9, [x5, #25]
	ldrb w9, [x1, #26]
	strb w9, [x5, #26]
	ldrb w9, [x1, #27]
	strb w9, [x5, #27]
	ldrb w9, [x1, #28]
	strb w9, [x5, #28]
	ldrb w9, [x1, #29]
	strb w9, [x5, #29]
	ldrb w9, [x1, #30]
	strb w9, [x5, #30]
	ldrb w9, [x1, #31]
	strb w9, [x5, #31]
21:
	add x1, x5, #0
	add x2, x3, #0
	add x3, x4, #0
	add x4, x3, #0
	add x6, x0, #0
	add x3, x2, #0
	add x8, x2, #32
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
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #64]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #72]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #80]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #88]
	movz x1, #9553, lsl #0
	movk x1, #64611, lsl #16
	movk x1, #51906, lsl #32
	movk x1, #62393, lsl #48
	str x1, [x0, #96]
	movz x1, #40580, lsl #0
	movk x1, #42775, lsl #16
	movk x1, #64173, lsl #32
	movk x1, #48358, lsl #48
	str x1, [x0, #104]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #112]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #224]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #232]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #240]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #248]
	movz x1, #65532, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #256]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #3, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #272]
	movz x1, #4, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65532, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #280]
	movz x1, #48607, lsl #0
	movk x1, #10692, lsl #16
	movk x1, #57186, lsl #32
	movk x1, #55452, lsl #48
	str x1, [x0, #288]
	movz x1, #12432, lsl #0
	movk x1, #30852, lsl #16
	movk x1, #1485, lsl #32
	movk x1, #44272, lsl #48
	str x1, [x0, #296]
	movz x1, #11990, lsl #0
	movk x1, #63265, lsl #16
	movk x1, #8363, lsl #32
	movk x1, #58786, lsl #48
	str x1, [x0, #304]
	movz x1, #18484, lsl #0
	movk x1, #1159, lsl #16
	movk x1, #1565, lsl #32
	movk x1, #56368, lsl #48
	str x1, [x0, #312]
	movz x1, #5180, lsl #0
	movk x1, #6313, lsl #16
	movk x1, #12500, lsl #32
	movk x1, #31207, lsl #48
	str x1, [x0, #320]
	movz x1, #46593, lsl #0
	movk x1, #24557, lsl #16
	movk x1, #38396, lsl #32
	movk x1, #30138, lsl #48
	str x1, [x0, #328]
	movz x1, #9488, lsl #0
	movk x1, #30562, lsl #16
	movk x1, #29483, lsl #32
	movk x1, #31227, lsl #48
	str x1, [x0, #336]
	movz x1, #21958, lsl #0
	movk x1, #42295, lsl #16
	movk x1, #24438, lsl #32
	movk x1, #6288, lsl #48
	str x1, [x0, #344]
	movz x1, #22026, lsl #0
	movk x1, #52885, lsl #16
	movk x1, #21335, lsl #32
	movk x1, #56818, lsl #48
	str x1, [x0, #352]
	movz x1, #58460, lsl #0
	movk x1, #47641, lsl #16
	movk x1, #47332, lsl #32
	movk x1, #35658, lsl #48
	str x1, [x0, #360]
	movz x1, #62245, lsl #0
	movk x1, #56609, lsl #16
	movk x1, #34440, lsl #32
	movk x1, #53992, lsl #48
	str x1, [x0, #368]
	movz x1, #23941, lsl #0
	movk x1, #9608, lsl #16
	movk x1, #65304, lsl #32
	movk x1, #34161, lsl #48
	str x1, [x0, #376]
	movz x1, #61090, lsl #0
	movk x1, #48761, lsl #16
	movk x1, #19605, lsl #32
	movk x1, #33572, lsl #48
	str x1, [x0, #384]
	movz x1, #28582, lsl #0
	movk x1, #18877, lsl #16
	movk x1, #31132, lsl #32
	movk x1, #18073, lsl #48
	str x1, [x0, #392]
	movz x1, #60505, lsl #0
	movk x1, #11115, lsl #16
	movk x1, #45625, lsl #32
	movk x1, #10309, lsl #48
	str x1, [x0, #400]
	movz x1, #22048, lsl #0
	movk x1, #62425, lsl #16
	movk x1, #11668, lsl #32
	movk x1, #26337, lsl #48
	str x1, [x0, #408]
	movz x1, #55983, lsl #0
	movk x1, #924, lsl #16
	movk x1, #13629, lsl #32
	movk x1, #3142, lsl #48
	str x1, [x0, #416]
	movz x1, #24955, lsl #0
	movk x1, #22760, lsl #16
	movk x1, #1362, lsl #32
	movk x1, #17177, lsl #48
	str x1, [x0, #424]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #432]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #544]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #552]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #560]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
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
25:
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
	cbnz x19, 25b
	ldr x5, [x8, #24]
	rev x5, x5
	str x5, [x0, #1024]
	ldr x5, [x8, #16]
	rev x5, x5
	str x5, [x0, #1032]
	ldr x5, [x8, #8]
	rev x5, x5
	str x5, [x0, #1040]
	ldr x5, [x8, #0]
	rev x5, x5
	str x5, [x0, #1048]
	movz x1, #3, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1312]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65531, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1320]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1328]
	movz x1, #65533, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #4, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1336]
	movz x1, #48607, lsl #0
	movk x1, #10692, lsl #16
	movk x1, #57186, lsl #32
	movk x1, #55452, lsl #48
	str x1, [x0, #1344]
	movz x1, #12432, lsl #0
	movk x1, #30852, lsl #16
	movk x1, #1485, lsl #32
	movk x1, #44272, lsl #48
	str x1, [x0, #1352]
	movz x1, #11990, lsl #0
	movk x1, #63265, lsl #16
	movk x1, #8363, lsl #32
	movk x1, #58786, lsl #48
	str x1, [x0, #1360]
	movz x1, #18484, lsl #0
	movk x1, #1159, lsl #16
	movk x1, #1565, lsl #32
	movk x1, #56368, lsl #48
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
	bl {vg_p256_check_point}
	umov x30, v28.d[0]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1056]
	ldr x2, [x0, #96]
	subs x16, x1, x2
	ldr x1, [x0, #1064]
	ldr x2, [x0, #104]
	sbcs x16, x1, x2
	ldr x1, [x0, #1072]
	ldr x2, [x0, #112]
	sbcs x16, x1, x2
	ldr x1, [x0, #1080]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1056]
	ldr x2, [x0, #1064]
	orr x1, x1, x2
	ldr x2, [x0, #1072]
	orr x1, x1, x2
	ldr x2, [x0, #1080]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1024]
	ldr x2, [x0, #96]
	subs x16, x1, x2
	ldr x1, [x0, #1032]
	ldr x2, [x0, #104]
	sbcs x16, x1, x2
	ldr x1, [x0, #1040]
	ldr x2, [x0, #112]
	sbcs x16, x1, x2
	ldr x1, [x0, #1048]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1024]
	ldr x2, [x0, #1032]
	orr x1, x1, x2
	ldr x2, [x0, #1040]
	orr x1, x1, x2
	ldr x2, [x0, #1048]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	movz x7, #0, lsl #0
	ldr x4, [x0, #384]
	ldr x5, [x0, #392]
	ldr x16, [x0, #400]
	ldr x17, [x0, #408]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1024]
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1032]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1040]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1048]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	str x26, [x0, #7800]
	str x27, [x0, #7808]
	str x28, [x0, #7816]
	str x30, [x0, #7824]
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #9, lsl #0
	ldr x2, [x0, #96]
	str x2, [x0, #2272]
	ldr x2, [x0, #104]
	str x2, [x0, #2280]
	ldr x2, [x0, #112]
	str x2, [x0, #2288]
	ldr x2, [x0, #120]
	str x2, [x0, #2296]
	str x12, [x0, #2304]
	ldr x2, [x0, #1248]
	str x2, [x0, #2312]
	ldr x2, [x0, #1256]
	str x2, [x0, #2320]
	ldr x2, [x0, #1264]
	str x2, [x0, #2328]
	ldr x2, [x0, #1272]
	str x2, [x0, #2336]
	str x12, [x0, #2344]
	str x12, [x0, #2352]
	str x12, [x0, #2360]
	str x12, [x0, #2368]
	str x12, [x0, #2376]
	str x12, [x0, #2384]
	str x12, [x0, #2392]
	str x12, [x0, #2400]
	str x12, [x0, #2408]
	str x11, [x0, #2384]
26:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #2272]
	ldr x3, [x0, #2312]
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #1, lsl #0
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	lsr x2, x4, #63
	lsr x3, x6, #63
	lsr x8, x5, #63
	movz x9, #0, lsl #0
	sub x2, x9, x2
	sub x3, x9, x3
	lsr x10, x7, #63
	sub x8, x9, x8
	ldr x11, [x0, #2312]
	mul x12, x5, x11
	sub x10, x9, x10
	umulh x13, x5, x11
	mul x14, x7, x11
	umulh x15, x7, x11
	ldr x16, [x0, #2272]
	mul x17, x4, x16
	mul x20, x6, x16
	umulh x21, x4, x16
	adds x12, x12, x9
	umulh x22, x6, x16
	ldr x23, [x0, #2280]
	mul x24, x4, x23
	ldr x25, [x0, #2320]
	mul x26, x5, x25
	adc x13, x13, x9
	adds x14, x14, x9
	umulh x27, x5, x25
	mul x28, x6, x23
	mul x30, x7, x25
	adc x15, x15, x9
	adds x12, x17, x12
	umulh x17, x7, x25
	umulh x25, x4, x23
	adc x13, x13, x9
	adds x20, x20, x14
	umulh x14, x6, x23
	str x20, [x0, #7104]
	ldr x20, [x0, #2288]
	mul x11, x4, x20
	adc x15, x15, x9
	adds x24, x24, x21
	ldr x21, [x0, #2328]
	mul x23, x5, x21
	adc x25, x25, x9
	adds x13, x26, x13
	adc x27, x27, x9
	adds x22, x28, x22
	umulh x26, x5, x21
	adc x14, x14, x9
	adds x30, x30, x15
	mul x28, x6, x20
	adc x17, x17, x9
	adds x24, x24, x13
	mul x15, x7, x21
	adc x27, x27, x9
	adds x22, x22, x30
	umulh x13, x7, x21
	adc x17, x17, x9
	adds x23, x23, x27
	umulh x30, x4, x20
	adc x26, x26, x9
	adds x11, x11, x25
	umulh x27, x6, x20
	adc x30, x30, x9
	adds x28, x28, x14
	ldr x25, [x0, #2296]
	mul x14, x4, x25
	adc x27, x27, x9
	adds x15, x15, x17
	adc x13, x13, x9
	adds x11, x11, x23
	ldr x17, [x0, #2336]
	mul x23, x5, x17
	adc x26, x26, x9
	adds x28, x28, x15
	adc x13, x13, x9
	umulh x15, x4, x25
	adds x14, x14, x30
	adc x15, x15, x9
	ldr x30, [x0, #2304]
	str x28, [x0, #7112]
	mul x28, x4, x30
	adds x28, x28, x15
	mul x30, x6, x30
	umulh x15, x5, x17
	adds x23, x23, x26
	adc x15, x15, x9
	adds x14, x14, x23
	adc x15, x15, x9
	ldr x26, [x0, #2344]
	mul x23, x5, x26
	adds x23, x23, x15
	adds x23, x28, x23
	mul x26, x7, x26
	and x15, x16, x2
	and x16, x16, x3
	ldr x28, [x0, #2280]
	str x22, [x0, #7120]
	and x22, x28, x2
	and x28, x28, x3
	str x28, [x0, #7128]
	and x28, x20, x2
	and x20, x20, x3
	str x20, [x0, #7136]
	and x20, x25, x2
	subs x24, x24, x15
	sbcs x22, x11, x22
	sbcs x28, x14, x28
	sbcs x23, x23, x20
	ldr x15, [x0, #2312]
	and x11, x15, x8
	and x15, x15, x10
	ldr x14, [x0, #2320]
	and x20, x14, x8
	and x14, x14, x10
	str x2, [x0, #7144]
	and x2, x21, x8
	and x21, x21, x10
	str x21, [x0, #7152]
	and x21, x17, x8
	subs x24, x24, x11
	sbcs x22, x22, x20
	sbcs x2, x28, x2
	sbcs x23, x23, x21
	extr x12, x24, x12, #59
	str x12, [x0, #2272]
	ldr x11, [x0, #2352]
	mul x20, x4, x11
	extr x24, x22, x24, #59
	str x24, [x0, #2280]
	extr x22, x2, x22, #59
	str x22, [x0, #2288]
	ldr x28, [x0, #2384]
	mul x21, x5, x28
	extr x2, x23, x2, #59
	lsr x12, x23, #63
	sub x12, x9, x12
	extr x23, x12, x23, #59
	str x23, [x0, #2304]
	mul x24, x6, x25
	umulh x22, x6, x25
	adds x27, x24, x27
	and x25, x25, x3
	str x2, [x0, #2296]
	adc x22, x22, x9
	adds x30, x30, x22
	umulh x12, x5, x28
	adds x21, x21, x9
	adc x12, x12, x9
	adds x20, x20, x21
	umulh x23, x4, x11
	adc x12, x12, x9
	mul x24, x7, x17
	umulh x2, x7, x17
	adds x24, x24, x13
	and x17, x17, x10
	adc x2, x2, x9
	adds x24, x27, x24
	adc x2, x2, x9
	adds x2, x26, x2
	movz x22, #48207, lsl #0
	movk x22, #60928, lsl #16
	adds x30, x30, x2
	ldr x21, [x0, #2360]
	mul x13, x4, x21
	ldr x27, [x0, #7120]
	subs x16, x27, x16
	ldr x26, [x0, #7112]
	ldr x2, [x0, #7128]
	sbcs x2, x26, x2
	movk x22, #51370, lsl #32
	ldr x27, [x0, #2392]
	mul x26, x5, x27
	str x10, [x0, #7128]
	ldr x10, [x0, #7136]
	sbcs x24, x24, x10
	sbcs x30, x30, x25
	movk x22, #52433, lsl #48
	umulh x10, x5, x27
	subs x16, x16, x15
	mul x25, x20, x22
	sbcs x2, x2, x14
	umulh x15, x4, x21
	ldr x14, [x0, #7152]
	sbcs x24, x24, x14
	ldr x14, [x0, #2368]
	str x22, [x0, #7152]
	mul x22, x4, x14
	sbcs x30, x30, x17
	adds x23, x13, x23
	ldr x17, [x0, #96]
	mul x13, x25, x17
	ldr x27, [x0, #7104]
	extr x27, x16, x27, #59
	str x27, [x0, #2312]
	extr x16, x2, x16, #59
	str x16, [x0, #2320]
	umulh x27, x25, x17
	adc x15, x15, x9
	adds x26, x26, x12
	ldr x16, [x0, #2400]
	mul x12, x5, x16
	extr x2, x24, x2, #59
	str x2, [x0, #2328]
	adc x10, x10, x9
	adds x23, x23, x26
	umulh x2, x5, x16
	extr x24, x30, x24, #59
	str x24, [x0, #2336]
	umulh x26, x4, x14
	adc x10, x10, x9
	adds x22, x22, x15
	ldr x24, [x0, #7144]
	and x15, x11, x24
	adc x26, x26, x9
	adds x12, x12, x10
	ldr x10, [x0, #104]
	mul x17, x25, x10
	adc x2, x2, x9
	adds x12, x22, x12
	adc x2, x2, x9
	adds x13, x13, x9
	adc x27, x27, x9
	adds x13, x20, x13
	umulh x22, x25, x10
	and x20, x28, x8
	adc x27, x27, x9
	adds x17, x17, x27
	ldr x13, [x0, #2376]
	mul x27, x4, x13
	umulh x4, x4, x13
	adc x22, x22, x9
	adds x27, x27, x26
	adc x4, x4, x9
	lsr x26, x30, #63
	sub x26, x9, x26
	extr x30, x26, x30, #59
	str x30, [x0, #2344]
	mul x26, x6, x11
	ldr x30, [x0, #2408]
	mul x10, x5, x30
	umulh x5, x5, x30
	adds x10, x10, x2
	adc x5, x5, x9
	adds x10, x27, x10
	adc x5, x5, x9
	adds x4, x4, x5
	umulh x2, x6, x11
	and x27, x21, x24
	and x5, x14, x24
	and x24, x13, x24
	subs x15, x23, x15
	sbcs x27, x12, x27
	sbcs x10, x10, x5
	mul x23, x7, x28
	sbcs x4, x4, x24
	umulh x12, x7, x28
	adds x23, x23, x9
	adc x12, x12, x9
	adds x26, x26, x23
	mul x5, x6, x21
	adc x12, x12, x9
	ldr x24, [x0, #2392]
	and x23, x24, x8
	and x28, x16, x8
	and x8, x30, x8
	subs x15, x15, x20
	sbcs x27, x27, x23
	sbcs x10, x10, x28
	mul x20, x7, x24
	sbcs x4, x4, x8
	umulh x23, x7, x24
	adds x15, x15, x17
	umulh x28, x6, x21
	and x11, x11, x3
	adc x22, x22, x9
	adds x5, x5, x2
	mul x8, x6, x14
	adc x28, x28, x9
	adds x20, x20, x12
	mul x17, x7, x16
	adc x23, x23, x9
	adds x20, x5, x20
	umulh x2, x7, x16
	adc x23, x23, x9
	adds x17, x17, x23
	umulh x12, x6, x14
	adc x2, x2, x9
	adds x8, x8, x28
	mul x5, x6, x13
	umulh x6, x6, x13
	adc x12, x12, x9
	adds x8, x8, x17
	mul x23, x7, x30
	umulh x7, x7, x30
	adc x2, x2, x9
	adds x5, x5, x12
	ldr x28, [x0, #112]
	mul x17, x25, x28
	adc x6, x6, x9
	adds x23, x23, x2
	adc x7, x7, x9
	adds x23, x5, x23
	umulh x12, x25, x28
	adc x7, x7, x9
	adds x17, x17, x22
	ldr x2, [x0, #120]
	mul x5, x25, x2
	umulh x25, x25, x2
	adc x12, x12, x9
	adds x27, x27, x17
	adc x12, x12, x9
	adds x7, x6, x7
	lsr x22, x4, #63
	adds x12, x5, x12
	add x17, x9, x9
	sub x22, x9, x22
	ldr x6, [x0, #2384]
	ldr x5, [x0, #7128]
	and x6, x6, x5
	and x21, x21, x3
	and x24, x24, x5
	and x14, x14, x3
	and x3, x13, x3
	and x16, x16, x5
	and x5, x30, x5
	adc x25, x25, x9
	subs x20, x20, x11
	sbcs x21, x8, x21
	sbcs x23, x23, x14
	sbcs x7, x7, x3
	subs x20, x20, x6
	sbcs x21, x21, x24
	sbcs x23, x23, x16
	sbcs x7, x7, x5
	adds x12, x10, x12
	adc x25, x25, x9
	ldr x13, [x0, #7152]
	mul x13, x26, x13
	adds x25, x4, x25
	lsr x30, x7, #63
	adcs x22, x22, x9
	ldr x11, [x0, #96]
	mul x8, x13, x11
	sub x30, x9, x30
	lsr x14, x22, #63
	umulh x3, x13, x11
	sub x14, x9, x14
	adds x8, x8, x9
	adc x3, x3, x9
	and x6, x11, x14
	adds x26, x26, x8
	ldr x24, [x0, #104]
	and x16, x24, x14
	and x5, x28, x14
	and x14, x2, x14
	adc x3, x3, x9
	adds x15, x15, x6
	mul x10, x13, x24
	umulh x4, x13, x24
	adcs x27, x27, x16
	adcs x5, x12, x5
	mul x8, x13, x28
	umulh x26, x13, x28
	adcs x25, x25, x14
	adcs x22, x22, x17
	adds x10, x10, x3
	mul x6, x13, x2
	umulh x13, x13, x2
	adc x4, x4, x9
	adds x10, x20, x10
	adc x4, x4, x9
	subs x15, x15, x11
	sbcs x27, x27, x24
	sbcs x5, x5, x28
	sbcs x25, x25, x2
	sbcs x22, x22, x17
	adds x8, x8, x4
	adc x26, x26, x9
	adds x21, x21, x8
	adc x26, x26, x9
	adds x6, x6, x26
	lsr x22, x22, #63
	adc x13, x13, x9
	adds x6, x23, x6
	sub x22, x9, x22
	adc x13, x13, x9
	and x16, x11, x22
	and x12, x24, x22
	and x14, x28, x22
	and x22, x2, x22
	adds x13, x7, x13
	adcs x30, x30, x9
	adds x15, x15, x16
	adcs x12, x27, x12
	str x15, [x0, #2352]
	str x15, [x0, #2416]
	lsr x3, x30, #63
	adcs x5, x5, x14
	str x12, [x0, #2360]
	sub x3, x9, x3
	adcs x22, x25, x22
	str x5, [x0, #2368]
	and x20, x11, x3
	and x4, x24, x3
	and x8, x28, x3
	and x3, x2, x3
	str x22, [x0, #2376]
	adds x20, x10, x20
	adcs x21, x21, x4
	adcs x8, x6, x8
	adcs x13, x13, x3
	adcs x30, x30, x17
	subs x20, x20, x11
	sbcs x21, x21, x24
	sbcs x8, x8, x28
	sbcs x13, x13, x2
	sbcs x30, x30, x17
	lsr x30, x30, #63
	sub x9, x9, x30
	and x11, x11, x9
	and x24, x24, x9
	and x28, x28, x9
	and x9, x2, x9
	adds x20, x20, x11
	adcs x24, x21, x24
	str x20, [x0, #2384]
	adcs x28, x8, x28
	str x24, [x0, #2392]
	adcs x13, x13, x9
	str x28, [x0, #2400]
	str x13, [x0, #2408]
	cbnz x19, 26b
	ldr x2, [x0, #2312]
	ldr x3, [x0, #2320]
	orr x2, x2, x3
	ldr x3, [x0, #2328]
	orr x2, x2, x3
	ldr x3, [x0, #2336]
	orr x2, x2, x3
	ldr x3, [x0, #2344]
	orr x2, x2, x3
	cbnz x2, 27f
	movz x12, #0, lsl #0
	ldr x3, [x0, #2272]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #22264, lsl #0
	movk x2, #32284, lsl #16
	movk x2, #50551, lsl #32
	movk x2, #65351, lsl #48
	movz x3, #52825, lsl #0
	movk x3, #32326, lsl #16
	movk x3, #1355, lsl #32
	movk x3, #62578, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2416]
	movz x2, #50577, lsl #0
	movk x2, #28032, lsl #16
	movk x2, #64865, lsl #32
	movk x2, #59691, lsl #48
	movz x3, #55538, lsl #0
	movk x3, #14742, lsl #16
	movk x3, #64844, lsl #32
	movk x3, #54202, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2424]
	movz x2, #32160, lsl #0
	movk x2, #51336, lsl #16
	movk x2, #58564, lsl #32
	movk x2, #48423, lsl #48
	movz x3, #33374, lsl #0
	movk x3, #14199, lsl #16
	movk x3, #6971, lsl #32
	movk x3, #17112, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2432]
	movz x2, #38636, lsl #0
	movk x2, #11399, lsl #16
	movk x2, #37161, lsl #32
	movk x2, #17001, lsl #48
	movz x3, #26900, lsl #0
	movk x3, #54136, lsl #16
	movk x3, #28373, lsl #32
	movk x3, #48534, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2440]
	movz x7, #0, lsl #0
	ldr x4, [x0, #2416]
	ldr x5, [x0, #2424]
	ldr x16, [x0, #2432]
	ldr x17, [x0, #2440]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #2352]
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #2360]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #2368]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #2376]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #992]
	str x13, [x0, #1000]
	str x8, [x0, #1008]
	str x9, [x0, #1016]
	b 28f
27:
	movz x19, #1, lsl #0
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #2272]
	ldr x3, [x0, #2312]
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #1, lsl #0
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	lsr x2, x4, #63
	lsr x3, x6, #63
	lsr x8, x5, #63
	movz x9, #0, lsl #0
	sub x2, x9, x2
	sub x3, x9, x3
	lsr x10, x7, #63
	sub x8, x9, x8
	ldr x11, [x0, #2312]
	mul x12, x5, x11
	sub x10, x9, x10
	umulh x13, x5, x11
	mul x14, x7, x11
	umulh x15, x7, x11
	ldr x16, [x0, #2272]
	mul x17, x4, x16
	mul x20, x6, x16
	umulh x21, x4, x16
	adds x12, x12, x9
	umulh x22, x6, x16
	ldr x23, [x0, #2280]
	mul x24, x4, x23
	ldr x25, [x0, #2320]
	mul x26, x5, x25
	adc x13, x13, x9
	adds x14, x14, x9
	umulh x27, x5, x25
	mul x28, x6, x23
	mul x30, x7, x25
	adc x15, x15, x9
	adds x12, x17, x12
	umulh x17, x7, x25
	umulh x25, x4, x23
	adc x13, x13, x9
	adds x20, x20, x14
	umulh x14, x6, x23
	str x20, [x0, #7104]
	ldr x20, [x0, #2288]
	mul x11, x4, x20
	adc x15, x15, x9
	adds x24, x24, x21
	ldr x21, [x0, #2328]
	mul x23, x5, x21
	adc x25, x25, x9
	adds x13, x26, x13
	adc x27, x27, x9
	adds x22, x28, x22
	umulh x26, x5, x21
	adc x14, x14, x9
	adds x30, x30, x15
	mul x28, x6, x20
	adc x17, x17, x9
	adds x24, x24, x13
	mul x15, x7, x21
	adc x27, x27, x9
	adds x22, x22, x30
	umulh x13, x7, x21
	adc x17, x17, x9
	adds x23, x23, x27
	umulh x30, x4, x20
	adc x26, x26, x9
	adds x11, x11, x25
	umulh x27, x6, x20
	adc x30, x30, x9
	adds x28, x28, x14
	ldr x25, [x0, #2296]
	mul x14, x4, x25
	adc x27, x27, x9
	adds x15, x15, x17
	adc x13, x13, x9
	adds x11, x11, x23
	ldr x17, [x0, #2336]
	mul x23, x5, x17
	adc x26, x26, x9
	adds x28, x28, x15
	adc x13, x13, x9
	umulh x15, x4, x25
	adds x14, x14, x30
	adc x15, x15, x9
	ldr x30, [x0, #2304]
	str x28, [x0, #7112]
	mul x28, x4, x30
	adds x28, x28, x15
	mul x30, x6, x30
	umulh x15, x5, x17
	adds x23, x23, x26
	adc x15, x15, x9
	adds x14, x14, x23
	adc x15, x15, x9
	ldr x26, [x0, #2344]
	mul x23, x5, x26
	adds x23, x23, x15
	adds x23, x28, x23
	mul x26, x7, x26
	and x15, x16, x2
	and x16, x16, x3
	ldr x28, [x0, #2280]
	str x22, [x0, #7120]
	and x22, x28, x2
	and x28, x28, x3
	str x28, [x0, #7128]
	and x28, x20, x2
	and x20, x20, x3
	str x20, [x0, #7136]
	and x20, x25, x2
	subs x24, x24, x15
	sbcs x22, x11, x22
	sbcs x28, x14, x28
	sbcs x23, x23, x20
	ldr x15, [x0, #2312]
	and x11, x15, x8
	and x15, x15, x10
	ldr x14, [x0, #2320]
	and x20, x14, x8
	and x14, x14, x10
	str x2, [x0, #7144]
	and x2, x21, x8
	and x21, x21, x10
	str x21, [x0, #7152]
	and x21, x17, x8
	subs x24, x24, x11
	sbcs x22, x22, x20
	sbcs x2, x28, x2
	sbcs x23, x23, x21
	extr x12, x24, x12, #59
	str x12, [x0, #2272]
	ldr x11, [x0, #2352]
	mul x20, x4, x11
	extr x24, x22, x24, #59
	str x24, [x0, #2280]
	extr x22, x2, x22, #59
	str x22, [x0, #2288]
	ldr x28, [x0, #2384]
	mul x21, x5, x28
	extr x2, x23, x2, #59
	lsr x12, x23, #63
	sub x12, x9, x12
	extr x23, x12, x23, #59
	str x23, [x0, #2304]
	mul x24, x6, x25
	umulh x22, x6, x25
	adds x27, x24, x27
	and x25, x25, x3
	str x2, [x0, #2296]
	adc x22, x22, x9
	adds x30, x30, x22
	umulh x12, x5, x28
	adds x21, x21, x9
	adc x12, x12, x9
	adds x20, x20, x21
	umulh x23, x4, x11
	adc x12, x12, x9
	mul x24, x7, x17
	umulh x2, x7, x17
	adds x24, x24, x13
	and x17, x17, x10
	adc x2, x2, x9
	adds x24, x27, x24
	adc x2, x2, x9
	adds x2, x26, x2
	movz x22, #48207, lsl #0
	movk x22, #60928, lsl #16
	adds x30, x30, x2
	ldr x21, [x0, #2360]
	mul x13, x4, x21
	ldr x27, [x0, #7120]
	subs x16, x27, x16
	ldr x26, [x0, #7112]
	ldr x2, [x0, #7128]
	sbcs x2, x26, x2
	movk x22, #51370, lsl #32
	ldr x27, [x0, #2392]
	mul x26, x5, x27
	str x10, [x0, #7128]
	ldr x10, [x0, #7136]
	sbcs x24, x24, x10
	sbcs x30, x30, x25
	movk x22, #52433, lsl #48
	umulh x10, x5, x27
	subs x16, x16, x15
	mul x25, x20, x22
	sbcs x2, x2, x14
	umulh x15, x4, x21
	ldr x14, [x0, #7152]
	sbcs x24, x24, x14
	ldr x14, [x0, #2368]
	str x22, [x0, #7152]
	mul x22, x4, x14
	sbcs x30, x30, x17
	adds x23, x13, x23
	ldr x17, [x0, #96]
	mul x13, x25, x17
	ldr x27, [x0, #7104]
	extr x27, x16, x27, #59
	str x27, [x0, #2312]
	extr x16, x2, x16, #59
	str x16, [x0, #2320]
	umulh x27, x25, x17
	adc x15, x15, x9
	adds x26, x26, x12
	ldr x16, [x0, #2400]
	mul x12, x5, x16
	extr x2, x24, x2, #59
	str x2, [x0, #2328]
	adc x10, x10, x9
	adds x23, x23, x26
	umulh x2, x5, x16
	extr x24, x30, x24, #59
	str x24, [x0, #2336]
	umulh x26, x4, x14
	adc x10, x10, x9
	adds x22, x22, x15
	ldr x24, [x0, #7144]
	and x15, x11, x24
	adc x26, x26, x9
	adds x12, x12, x10
	ldr x10, [x0, #104]
	mul x17, x25, x10
	adc x2, x2, x9
	adds x12, x22, x12
	adc x2, x2, x9
	adds x13, x13, x9
	adc x27, x27, x9
	adds x13, x20, x13
	umulh x22, x25, x10
	and x20, x28, x8
	adc x27, x27, x9
	adds x17, x17, x27
	ldr x13, [x0, #2376]
	mul x27, x4, x13
	umulh x4, x4, x13
	adc x22, x22, x9
	adds x27, x27, x26
	adc x4, x4, x9
	lsr x26, x30, #63
	sub x26, x9, x26
	extr x30, x26, x30, #59
	str x30, [x0, #2344]
	mul x26, x6, x11
	ldr x30, [x0, #2408]
	mul x10, x5, x30
	umulh x5, x5, x30
	adds x10, x10, x2
	adc x5, x5, x9
	adds x10, x27, x10
	adc x5, x5, x9
	adds x4, x4, x5
	umulh x2, x6, x11
	and x27, x21, x24
	and x5, x14, x24
	and x24, x13, x24
	subs x15, x23, x15
	sbcs x27, x12, x27
	sbcs x10, x10, x5
	mul x23, x7, x28
	sbcs x4, x4, x24
	umulh x12, x7, x28
	adds x23, x23, x9
	adc x12, x12, x9
	adds x26, x26, x23
	mul x5, x6, x21
	adc x12, x12, x9
	ldr x24, [x0, #2392]
	and x23, x24, x8
	and x28, x16, x8
	and x8, x30, x8
	subs x15, x15, x20
	sbcs x27, x27, x23
	sbcs x10, x10, x28
	mul x20, x7, x24
	sbcs x4, x4, x8
	umulh x23, x7, x24
	adds x15, x15, x17
	umulh x28, x6, x21
	and x11, x11, x3
	adc x22, x22, x9
	adds x5, x5, x2
	mul x8, x6, x14
	adc x28, x28, x9
	adds x20, x20, x12
	mul x17, x7, x16
	adc x23, x23, x9
	adds x20, x5, x20
	umulh x2, x7, x16
	adc x23, x23, x9
	adds x17, x17, x23
	umulh x12, x6, x14
	adc x2, x2, x9
	adds x8, x8, x28
	mul x5, x6, x13
	umulh x6, x6, x13
	adc x12, x12, x9
	adds x8, x8, x17
	mul x23, x7, x30
	umulh x7, x7, x30
	adc x2, x2, x9
	adds x5, x5, x12
	ldr x28, [x0, #112]
	mul x17, x25, x28
	adc x6, x6, x9
	adds x23, x23, x2
	adc x7, x7, x9
	adds x23, x5, x23
	umulh x12, x25, x28
	adc x7, x7, x9
	adds x17, x17, x22
	ldr x2, [x0, #120]
	mul x5, x25, x2
	umulh x25, x25, x2
	adc x12, x12, x9
	adds x27, x27, x17
	adc x12, x12, x9
	adds x7, x6, x7
	lsr x22, x4, #63
	adds x12, x5, x12
	add x17, x9, x9
	sub x22, x9, x22
	ldr x6, [x0, #2384]
	ldr x5, [x0, #7128]
	and x6, x6, x5
	and x21, x21, x3
	and x24, x24, x5
	and x14, x14, x3
	and x3, x13, x3
	and x16, x16, x5
	and x5, x30, x5
	adc x25, x25, x9
	subs x20, x20, x11
	sbcs x21, x8, x21
	sbcs x23, x23, x14
	sbcs x7, x7, x3
	subs x20, x20, x6
	sbcs x21, x21, x24
	sbcs x23, x23, x16
	sbcs x7, x7, x5
	adds x12, x10, x12
	adc x25, x25, x9
	ldr x13, [x0, #7152]
	mul x13, x26, x13
	adds x25, x4, x25
	lsr x30, x7, #63
	adcs x22, x22, x9
	ldr x11, [x0, #96]
	mul x8, x13, x11
	sub x30, x9, x30
	lsr x14, x22, #63
	umulh x3, x13, x11
	sub x14, x9, x14
	adds x8, x8, x9
	adc x3, x3, x9
	and x6, x11, x14
	adds x26, x26, x8
	ldr x24, [x0, #104]
	and x16, x24, x14
	and x5, x28, x14
	and x14, x2, x14
	adc x3, x3, x9
	adds x15, x15, x6
	mul x10, x13, x24
	umulh x4, x13, x24
	adcs x27, x27, x16
	adcs x5, x12, x5
	mul x8, x13, x28
	umulh x26, x13, x28
	adcs x25, x25, x14
	adcs x22, x22, x17
	adds x10, x10, x3
	mul x6, x13, x2
	umulh x13, x13, x2
	adc x4, x4, x9
	adds x10, x20, x10
	adc x4, x4, x9
	subs x15, x15, x11
	sbcs x27, x27, x24
	sbcs x5, x5, x28
	sbcs x25, x25, x2
	sbcs x22, x22, x17
	adds x8, x8, x4
	adc x26, x26, x9
	adds x21, x21, x8
	adc x26, x26, x9
	adds x6, x6, x26
	lsr x22, x22, #63
	adc x13, x13, x9
	adds x6, x23, x6
	sub x22, x9, x22
	adc x13, x13, x9
	and x16, x11, x22
	and x12, x24, x22
	and x14, x28, x22
	and x22, x2, x22
	adds x13, x7, x13
	adcs x30, x30, x9
	adds x15, x15, x16
	adcs x12, x27, x12
	str x15, [x0, #2352]
	str x15, [x0, #2416]
	lsr x3, x30, #63
	adcs x5, x5, x14
	str x12, [x0, #2360]
	sub x3, x9, x3
	adcs x22, x25, x22
	str x5, [x0, #2368]
	and x20, x11, x3
	and x4, x24, x3
	and x8, x28, x3
	and x3, x2, x3
	str x22, [x0, #2376]
	adds x20, x10, x20
	adcs x21, x21, x4
	adcs x8, x6, x8
	adcs x13, x13, x3
	adcs x30, x30, x17
	subs x20, x20, x11
	sbcs x21, x21, x24
	sbcs x8, x8, x28
	sbcs x13, x13, x2
	sbcs x30, x30, x17
	lsr x30, x30, #63
	sub x9, x9, x30
	and x11, x11, x9
	and x24, x24, x9
	and x28, x28, x9
	and x9, x2, x9
	adds x20, x20, x11
	adcs x24, x21, x24
	str x20, [x0, #2384]
	adcs x28, x8, x28
	str x24, [x0, #2392]
	adcs x13, x13, x9
	str x28, [x0, #2400]
	str x13, [x0, #2408]
	movz x12, #0, lsl #0
	ldr x3, [x0, #2272]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #46200, lsl #0
	movk x2, #57457, lsl #16
	movk x2, #22743, lsl #32
	movk x2, #19242, lsl #48
	movz x3, #28889, lsl #0
	movk x3, #7153, lsl #16
	movk x3, #29163, lsl #32
	movk x3, #43151, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2416]
	movz x2, #48664, lsl #0
	movk x2, #30555, lsl #16
	movk x2, #54976, lsl #32
	movk x2, #15943, lsl #48
	movz x3, #57452, lsl #0
	movk x3, #12219, lsl #16
	movk x3, #9197, lsl #32
	movk x3, #32415, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2424]
	movz x2, #46111, lsl #0
	movk x2, #4367, lsl #16
	movk x2, #39065, lsl #32
	movk x2, #42236, lsl #48
	movz x3, #19424, lsl #0
	movk x3, #61168, lsl #16
	movk x3, #26470, lsl #32
	movk x3, #23299, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2432]
	movz x2, #56719, lsl #0
	movk x2, #37106, lsl #16
	movk x2, #9517, lsl #32
	movk x2, #19762, lsl #48
	movz x3, #8817, lsl #0
	movk x3, #28429, lsl #16
	movk x3, #56017, lsl #32
	movk x3, #45773, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2440]
	movz x7, #0, lsl #0
	ldr x4, [x0, #2416]
	ldr x5, [x0, #2424]
	ldr x16, [x0, #2432]
	ldr x17, [x0, #2440]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #2352]
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #2360]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #2368]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #2376]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #992]
	str x13, [x0, #1000]
	str x8, [x0, #1008]
	str x9, [x0, #1016]
28:
	ldr x26, [x0, #7800]
	ldr x27, [x0, #7808]
	ldr x28, [x0, #7816]
	ldr x30, [x0, #7824]
	movz x7, #0, lsl #0
	ldr x4, [x0, #384]
	ldr x5, [x0, #392]
	ldr x16, [x0, #400]
	ldr x17, [x0, #408]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1088]
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1096]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1104]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1112]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	movz x7, #0, lsl #0
	ldr x4, [x0, #384]
	ldr x5, [x0, #392]
	ldr x16, [x0, #400]
	ldr x17, [x0, #408]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1056]
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1064]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1072]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1080]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x8, [x0, #1328]
	str x9, [x0, #1336]
	movz x7, #0, lsl #0
	ldr x4, [x0, #992]
	ldr x5, [x0, #1000]
	ldr x16, [x0, #1008]
	ldr x17, [x0, #1016]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1344]
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1352]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1360]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1368]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1376]
	str x13, [x0, #1384]
	str x8, [x0, #1392]
	str x9, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x4, [x0, #992]
	ldr x5, [x0, #1000]
	ldr x16, [x0, #1008]
	ldr x17, [x0, #1016]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1312]
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1320]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1328]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1336]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1408]
	str x13, [x0, #1416]
	str x8, [x0, #1424]
	str x9, [x0, #1432]
	movz x7, #0, lsl #0
	ldr x4, [x0, #192]
	ldr x5, [x0, #200]
	ldr x16, [x0, #208]
	ldr x17, [x0, #216]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1376]
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1384]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1392]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1400]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
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
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1408]
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1416]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1424]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1432]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
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
	str x26, [x0, #7800]
	str x27, [x0, #7808]
	str x28, [x0, #7816]
	str x30, [x0, #7824]
	ldr x5, [x0, #1152]
	ldr x6, [x0, #1160]
	ldr x7, [x0, #1168]
	ldr x8, [x0, #1176]
	movz x9, #0, lsl #0
	movz x10, #511, lsl #0
	movz x11, #256, lsl #0
	movz x12, #0, lsl #0
	movz x13, #1, lsl #0
	movz x19, #257, lsl #0
	add x20, x0, #2112
	str x12, [x0, #2112]
	str x12, [x0, #2120]
	str x12, [x0, #2128]
	str x12, [x0, #2136]
	str x12, [x0, #2144]
	str x12, [x0, #2152]
	str x12, [x0, #2160]
	str x12, [x0, #2168]
	str x12, [x0, #2176]
	str x12, [x0, #2184]
	str x12, [x0, #2192]
	str x12, [x0, #2200]
	str x12, [x0, #2208]
	str x12, [x0, #2216]
	str x12, [x0, #2224]
	str x12, [x0, #2232]
	str x12, [x0, #2240]
	str x12, [x0, #2248]
	str x12, [x0, #2256]
	str x12, [x0, #2264]
	str x12, [x0, #2272]
	str x12, [x0, #2280]
	str x12, [x0, #2288]
	str x12, [x0, #2296]
	str x12, [x0, #2304]
	str x12, [x0, #2312]
	str x12, [x0, #2320]
	str x12, [x0, #2328]
	str x12, [x0, #2336]
	str x12, [x0, #2344]
	str x12, [x0, #2352]
	str x12, [x0, #2360]
	str x12, [x0, #2368]
	str x12, [x0, #2376]
	str x12, [x0, #2384]
	str x12, [x0, #2392]
	str x12, [x0, #2400]
	str x12, [x0, #2408]
	str x12, [x0, #2416]
	str x12, [x0, #2424]
	str x12, [x0, #2432]
	str x12, [x0, #2440]
	str x12, [x0, #2448]
	str x12, [x0, #2456]
	str x12, [x0, #2464]
	str x12, [x0, #2472]
	str x12, [x0, #2480]
	str x12, [x0, #2488]
	str x12, [x0, #2496]
	str x12, [x0, #2504]
	str x12, [x0, #2512]
	str x12, [x0, #2520]
	str x12, [x0, #2528]
	str x12, [x0, #2536]
	str x12, [x0, #2544]
	str x12, [x0, #2552]
	str x12, [x0, #2560]
	str x12, [x0, #2568]
	str x12, [x0, #2576]
	str x12, [x0, #2584]
	str x12, [x0, #2592]
	str x12, [x0, #2600]
	str x12, [x0, #2608]
	str x12, [x0, #2616]
	str x12, [x0, #2624]
29:
	and x1, x5, x13
	cbnz x1, 210f
	extr x5, x6, x5, #1
	extr x6, x7, x6, #1
	extr x7, x8, x7, #1
	extr x8, x9, x8, #1
	lsr x9, x9, #1
	add x20, x20, #2
	b 211f
210:
	and x2, x5, x10
	and x3, x2, x11
	lsl x3, x3, #1
	sub x2, x2, x3
	strb w2, [x20, #0]
	lsr x3, x2, #8
	strb w3, [x20, #1]
	lsr x3, x2, #63
	sub x3, x12, x3
	subs x5, x5, x2
	sbcs x6, x6, x3
	sbcs x7, x7, x3
	sbcs x8, x8, x3
	sbc x9, x9, x3
	extr x5, x6, x5, #9
	extr x6, x7, x6, #9
	extr x7, x8, x7, #9
	extr x8, x9, x8, #9
	lsr x9, x9, #9
	add x20, x20, #18
211:
	orr x19, x5, x6
	orr x19, x19, x7
	orr x19, x19, x8
	orr x19, x19, x9
	cbnz x19, 29b
	ldr x5, [x0, #1184]
	ldr x6, [x0, #1192]
	ldr x7, [x0, #1200]
	ldr x8, [x0, #1208]
	movz x9, #0, lsl #0
	movz x10, #31, lsl #0
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
	movz x13, #1, lsl #0
	movz x19, #257, lsl #0
	add x20, x0, #1824
	str x12, [x0, #1824]
	str x12, [x0, #1832]
	str x12, [x0, #1840]
	str x12, [x0, #1848]
	str x12, [x0, #1856]
	str x12, [x0, #1864]
	str x12, [x0, #1872]
	str x12, [x0, #1880]
	str x12, [x0, #1888]
	str x12, [x0, #1896]
	str x12, [x0, #1904]
	str x12, [x0, #1912]
	str x12, [x0, #1920]
	str x12, [x0, #1928]
	str x12, [x0, #1936]
	str x12, [x0, #1944]
	str x12, [x0, #1952]
	str x12, [x0, #1960]
	str x12, [x0, #1968]
	str x12, [x0, #1976]
	str x12, [x0, #1984]
	str x12, [x0, #1992]
	str x12, [x0, #2000]
	str x12, [x0, #2008]
	str x12, [x0, #2016]
	str x12, [x0, #2024]
	str x12, [x0, #2032]
	str x12, [x0, #2040]
	str x12, [x0, #2048]
	str x12, [x0, #2056]
	str x12, [x0, #2064]
	str x12, [x0, #2072]
	str x12, [x0, #2080]
212:
	and x1, x5, x13
	cbnz x1, 213f
	extr x5, x6, x5, #1
	extr x6, x7, x6, #1
	extr x7, x8, x7, #1
	extr x8, x9, x8, #1
	lsr x9, x9, #1
	add x20, x20, #1
	b 214f
213:
	and x2, x5, x10
	and x3, x2, x11
	lsl x3, x3, #1
	sub x2, x2, x3
	strb w2, [x20, #0]
	lsr x3, x2, #63
	sub x3, x12, x3
	subs x5, x5, x2
	sbcs x6, x6, x3
	sbcs x7, x7, x3
	sbcs x8, x8, x3
	sbc x9, x9, x3
	extr x5, x6, x5, #5
	extr x6, x7, x6, #5
	extr x7, x8, x7, #5
	extr x8, x9, x8, #5
	lsr x9, x9, #5
	add x20, x20, #5
214:
	orr x19, x5, x6
	orr x19, x19, x7
	orr x19, x19, x8
	orr x19, x19, x9
	cbnz x19, 212b
	ldr x1, [x0, #1280]
	str x1, [x0, #704]
	ldr x1, [x0, #1288]
	str x1, [x0, #712]
	ldr x1, [x0, #1296]
	str x1, [x0, #720]
	ldr x1, [x0, #1304]
	str x1, [x0, #728]
	ldr x1, [x0, #1440]
	str x1, [x0, #736]
	ldr x1, [x0, #1448]
	str x1, [x0, #744]
	ldr x1, [x0, #1456]
	str x1, [x0, #752]
	ldr x1, [x0, #1464]
	str x1, [x0, #760]
	ldr x1, [x0, #224]
	str x1, [x0, #768]
	ldr x1, [x0, #232]
	str x1, [x0, #776]
	ldr x1, [x0, #240]
	str x1, [x0, #784]
	ldr x1, [x0, #248]
	str x1, [x0, #792]
	ldr x1, [x0, #224]
	str x1, [x0, #5400]
	ldr x1, [x0, #232]
	str x1, [x0, #5408]
	ldr x1, [x0, #240]
	str x1, [x0, #5416]
	ldr x1, [x0, #248]
	str x1, [x0, #5424]
	ldr x1, [x0, #224]
	str x1, [x0, #5432]
	ldr x1, [x0, #232]
	str x1, [x0, #5440]
	ldr x1, [x0, #240]
	str x1, [x0, #5448]
	ldr x1, [x0, #248]
	str x1, [x0, #5456]
	movz x19, #1, lsl #0
	sub x1, x19, #1
	movz x2, #96, lsl #0
	mul x1, x1, x2
	add x16, x0, #2848
	add x16, x16, x1
	ldr x1, [x0, #704]
	str x1, [x16, #0]
	ldr x1, [x0, #712]
	str x1, [x16, #8]
	ldr x1, [x0, #720]
	str x1, [x16, #16]
	ldr x1, [x0, #728]
	str x1, [x16, #24]
	ldr x1, [x0, #736]
	str x1, [x16, #32]
	ldr x1, [x0, #744]
	str x1, [x16, #40]
	ldr x1, [x0, #752]
	str x1, [x16, #48]
	ldr x1, [x0, #760]
	str x1, [x16, #56]
	ldr x1, [x0, #768]
	str x1, [x16, #64]
	ldr x1, [x0, #776]
	str x1, [x16, #72]
	ldr x1, [x0, #784]
	str x1, [x16, #80]
	ldr x1, [x0, #792]
	str x1, [x16, #88]
	sub x1, x19, #1
	lsl x1, x1, #6
	movz x2, #6000, lsl #0
	add x16, x0, x2
	add x16, x16, x1
	ldr x1, [x0, #5400]
	str x1, [x16, #0]
	ldr x1, [x0, #5408]
	str x1, [x16, #8]
	ldr x1, [x0, #5416]
	str x1, [x16, #16]
	ldr x1, [x0, #5424]
	str x1, [x16, #24]
	ldr x1, [x0, #5432]
	str x1, [x16, #32]
	ldr x1, [x0, #5440]
	str x1, [x16, #40]
	ldr x1, [x0, #5448]
	str x1, [x16, #48]
	ldr x1, [x0, #5456]
	str x1, [x16, #56]
	ldr x1, [x0, #1280]
	ldr x2, [x0, #1288]
	mul x3, x1, x2
	umulh x4, x1, x1
	umulh x5, x1, x2
	ldr x6, [x0, #1296]
	mul x7, x1, x6
	mul x8, x1, x1
	umulh x9, x1, x6
	mul x10, x2, x2
	ldr x11, [x0, #1304]
	mul x12, x1, x11
	mul x13, x2, x6
	umulh x14, x2, x2
	ldr x15, [x0, #1440]
	ldr x16, [x0, #1448]
	mul x17, x15, x16
	umulh x20, x15, x15
	lsl x21, x8, #32
	umulh x22, x15, x16
	adds x7, x5, x7
	umulh x23, x1, x11
	ldr x24, [x0, #1456]
	mul x25, x15, x24
	mul x26, x15, x15
	adcs x12, x12, x9
	umulh x27, x2, x6
	mul x28, x2, x11
	adcs x28, x23, x28
	umulh x30, x2, x11
	mul x5, x6, x11
	adcs x5, x5, x30
	umulh x9, x6, x11
	movz x23, #0, lsl #0
	adc x9, x9, x23
	adds x13, x12, x13
	adcs x27, x28, x27
	sub x30, x8, x21
	adcs x5, x5, x23
	adc x9, x9, x23
	adds x25, x22, x25
	umulh x12, x15, x24
	mul x28, x6, x6
	umulh x22, x6, x6
	mul x6, x11, x11
	umulh x2, x11, x11
	ldr x11, [x0, #1464]
	mul x1, x15, x11
	adcs x1, x1, x12
	umulh x12, x15, x11
	mul x15, x16, x24
	str x26, [x0, #7104]
	umulh x26, x16, x24
	str x30, [x0, #7112]
	mul x30, x16, x11
	adcs x30, x12, x30
	umulh x12, x16, x11
	mul x16, x24, x11
	adcs x16, x16, x12
	umulh x12, x24, x11
	adc x12, x12, x23
	adds x15, x1, x15
	adcs x26, x30, x26
	adcs x16, x16, x23
	adc x12, x12, x23
	adds x3, x3, x3
	adcs x7, x7, x7
	adcs x13, x13, x13
	adcs x27, x27, x27
	adcs x5, x5, x5
	adcs x9, x9, x9
	adc x1, x23, x23
	adds x4, x3, x4
	adcs x7, x7, x10
	adcs x14, x13, x14
	adcs x27, x27, x28
	adcs x5, x5, x22
	adcs x9, x9, x6
	adc x2, x1, x2
	adds x17, x17, x17
	adcs x25, x25, x25
	adcs x15, x15, x15
	adcs x26, x26, x26
	adcs x16, x16, x16
	adcs x12, x12, x12
	extr x30, x4, x8, #32
	adc x3, x23, x23
	adds x20, x17, x20
	ldr x10, [x0, #1448]
	mul x13, x10, x10
	adcs x25, x25, x13
	umulh x28, x10, x10
	adcs x15, x15, x28
	mul x22, x24, x24
	adcs x26, x26, x22
	umulh x6, x24, x24
	adcs x16, x16, x6
	mul x1, x11, x11
	adcs x12, x12, x1
	umulh x17, x11, x11
	adc x17, x3, x17
	adds x4, x4, x21
	adcs x7, x7, x30
	extr x13, x7, x4, #32
	adcs x14, x14, x13
	ldr x28, [x0, #7112]
	add x22, x14, x28
	extr x6, x22, x7, #32
	adcs x27, x27, x6
	lsr x1, x22, #32
	adcs x5, x5, x1
	adcs x9, x9, x23
	adc x2, x2, x23
	subs x21, x8, x21
	sbcs x30, x8, x30
	sbcs x13, x4, x13
	sbcs x6, x7, x6
	sbc x1, x22, x1
	adds x14, x14, x28
	adcs x30, x30, x4
	adcs x7, x13, x7
	adcs x22, x6, x22
	adc x1, x1, x23
	adds x30, x27, x30
	ldr x3, [x0, #7104]
	extr x21, x20, x3, #32
	adcs x7, x5, x7
	lsl x8, x3, #32
	adcs x22, x9, x22
	movz x28, #1, lsl #0
	orr x14, x28, x28
	movk x14, #0, lsl #16
	adcs x1, x2, x1
	sub x4, x3, x8
	movk x14, #65535, lsl #32
	movk x14, #65535, lsl #48
	adc x13, x23, x23
	adds x20, x20, x8
	adcs x25, x25, x21
	extr x6, x25, x20, #32
	adcs x15, x15, x6
	add x27, x15, x4
	extr x5, x27, x25, #32
	adcs x26, x26, x5
	lsr x9, x27, #32
	adcs x16, x16, x9
	adcs x12, x12, x23
	adc x17, x17, x23
	subs x8, x3, x8
	sbcs x21, x3, x21
	sbcs x6, x20, x6
	sbcs x5, x25, x5
	sbc x9, x27, x9
	adds x15, x15, x4
	adcs x21, x21, x20
	adcs x25, x6, x25
	adcs x27, x5, x27
	adc x9, x9, x23
	adds x2, x30, x28
	ldr x8, [x0, #72]
	sbcs x3, x7, x8
	sbcs x4, x22, x23
	ldr x15, [x0, #88]
	sbcs x20, x1, x15
	sbcs x13, x13, x23
	csel x2, x2, x30, hs
	csel x7, x3, x7, hs
	csel x22, x4, x22, hs
	csel x20, x20, x1, hs
	adds x21, x26, x21
	adcs x25, x16, x25
	adcs x27, x12, x27
	adcs x9, x17, x9
	adc x6, x23, x23
	adds x5, x21, x28
	sbcs x13, x25, x8
	sbcs x30, x27, x23
	sbcs x3, x9, x15
	sbcs x6, x6, x23
	csel x5, x5, x21, hs
	csel x13, x13, x25, hs
	csel x30, x30, x27, hs
	csel x9, x3, x9, hs
	ldr x4, [x0, #1280]
	umulh x1, x4, x5
	mul x26, x4, x5
	mul x16, x4, x13
	umulh x12, x4, x13
	mul x17, x4, x30
	adds x1, x16, x1
	umulh x6, x4, x30
	adcs x17, x17, x12
	mul x21, x4, x9
	adcs x21, x21, x6
	umulh x4, x4, x9
	ldr x25, [x0, #1288]
	mul x27, x25, x5
	adcs x4, x23, x4
	mul x3, x5, x13
	umulh x16, x5, x13
	mul x12, x5, x30
	adds x16, x16, x12
	umulh x6, x5, x30
	mul x12, x5, x9
	adcs x12, x12, x6
	umulh x6, x5, x9
	mul x11, x13, x30
	umulh x24, x13, x30
	mul x10, x13, x9
	adcs x10, x6, x10
	umulh x6, x13, x9
	mul x15, x30, x9
	adcs x6, x15, x6
	umulh x15, x30, x9
	adc x15, x15, x23
	adds x11, x12, x11
	adcs x24, x10, x24
	adcs x6, x6, x23
	adc x15, x15, x23
	adds x3, x3, x3
	adcs x16, x16, x16
	adcs x11, x11, x11
	adcs x24, x24, x24
	adcs x6, x6, x6
	adcs x15, x15, x15
	adc x12, x23, x23
	mul x10, x5, x5
	umulh x8, x5, x5
	adds x8, x3, x8
	mul x3, x13, x13
	adcs x16, x16, x3
	umulh x3, x13, x13
	adcs x11, x11, x3
	mul x3, x30, x30
	adcs x24, x24, x3
	umulh x3, x30, x30
	adcs x6, x6, x3
	mul x3, x9, x9
	adcs x3, x15, x3
	umulh x15, x9, x9
	adc x15, x12, x15
	ldr x12, [x0, #224]
	subs x2, x2, x12
	ldr x12, [x0, #232]
	sbcs x7, x7, x12
	ldr x12, [x0, #240]
	sbcs x22, x22, x12
	ldr x12, [x0, #248]
	sbcs x12, x20, x12
	lsl x20, x10, #32
	sub x28, x10, x20
	str x12, [x0, #7104]
	extr x12, x8, x10, #32
	str x22, [x0, #7112]
	lsl x22, x26, #32
	str x7, [x0, #7120]
	lsr x7, x26, #32
	str x2, [x0, #7128]
	mul x2, x26, x14
	umulh x26, x26, x14
	str x14, [x0, #7136]
	mul x14, x25, x13
	str x10, [x0, #7144]
	mul x10, x25, x30
	str x15, [x0, #7152]
	mul x15, x25, x9
	str x3, [x0, #7160]
	umulh x3, x25, x9
	str x6, [x0, #7168]
	umulh x6, x25, x5
	str x24, [x0, #7176]
	umulh x24, x25, x13
	umulh x25, x25, x30
	str x28, [x0, #7184]
	ldr x28, [x0, #1296]
	str x11, [x0, #7192]
	mul x11, x28, x5
	str x11, [x0, #7200]
	mul x11, x28, x13
	str x11, [x0, #7208]
	mul x11, x28, x30
	str x11, [x0, #7216]
	mul x11, x28, x9
	str x11, [x0, #7224]
	umulh x11, x28, x9
	str x11, [x0, #7232]
	umulh x11, x28, x5
	str x11, [x0, #7240]
	umulh x11, x28, x13
	umulh x28, x28, x30
	str x28, [x0, #7248]
	ldr x28, [x0, #1304]
	str x11, [x0, #7256]
	mul x11, x28, x5
	umulh x5, x28, x5
	str x5, [x0, #7264]
	mul x5, x28, x13
	umulh x13, x28, x13
	str x13, [x0, #7272]
	mul x13, x28, x30
	umulh x30, x28, x30
	str x30, [x0, #7280]
	mul x30, x28, x9
	umulh x9, x28, x9
	sbc x28, x23, x23
	adds x1, x1, x22
	adcs x17, x17, x7
	adcs x21, x21, x2
	adcs x4, x4, x26
	adcs x22, x23, x23
	adds x1, x1, x27
	adcs x14, x17, x14
	adcs x21, x21, x10
	adcs x4, x4, x15
	adcs x3, x22, x3
	adds x14, x14, x6
	adcs x21, x21, x24
	adcs x4, x4, x25
	adcs x3, x3, x23
	adds x8, x8, x20
	adcs x16, x16, x12
	extr x7, x16, x8, #32
	ldr x2, [x0, #7192]
	adcs x2, x2, x7
	ldr x26, [x0, #7184]
	add x27, x2, x26
	extr x17, x27, x16, #32
	ldr x10, [x0, #7176]
	adcs x10, x10, x17
	lsr x15, x27, #32
	ldr x22, [x0, #7168]
	adcs x22, x22, x15
	ldr x6, [x0, #7160]
	adcs x6, x6, x23
	ldr x24, [x0, #7152]
	adc x24, x24, x23
	ldr x25, [x0, #7144]
	subs x20, x25, x20
	sbcs x12, x25, x12
	sbcs x7, x8, x7
	sbcs x17, x16, x17
	sbc x15, x27, x15
	adds x2, x2, x26
	adcs x8, x12, x8
	adcs x16, x7, x16
	adcs x17, x17, x27
	adc x15, x15, x23
	adds x8, x10, x8
	adcs x16, x22, x16
	adcs x17, x6, x17
	adcs x24, x24, x15
	adc x20, x23, x23
	ldr x25, [x0, #7128]
	adds x25, x25, x28
	lsl x26, x1, #32
	lsr x2, x1, #32
	ldr x12, [x0, #7136]
	mul x7, x1, x12
	umulh x1, x1, x12
	lsr x27, x28, #32
	ldr x10, [x0, #7120]
	adcs x10, x10, x27
	ldr x22, [x0, #7112]
	adcs x22, x22, x23
	lsl x6, x28, #32
	sub x6, x6, x28
	ldr x15, [x0, #7104]
	adc x6, x15, x6
	adds x14, x14, x26
	adcs x21, x21, x2
	adcs x4, x4, x7
	adcs x3, x3, x1
	adcs x27, x23, x23
	ldr x28, [x0, #7200]
	adds x28, x14, x28
	ldr x15, [x0, #7208]
	adcs x21, x21, x15
	ldr x26, [x0, #7216]
	adcs x4, x4, x26
	ldr x2, [x0, #7224]
	adcs x3, x3, x2
	ldr x7, [x0, #7232]
	adcs x7, x27, x7
	ldr x1, [x0, #7240]
	adds x21, x21, x1
	ldr x14, [x0, #7256]
	adcs x4, x4, x14
	ldr x15, [x0, #7248]
	adcs x15, x3, x15
	adcs x7, x7, x23
	movz x26, #1, lsl #0
	adds x2, x8, x26
	ldr x27, [x0, #72]
	sbcs x1, x16, x27
	sbcs x14, x17, x23
	ldr x3, [x0, #88]
	sbcs x27, x24, x3
	sbcs x20, x20, x23
	csel x2, x2, x8, hs
	csel x1, x1, x16, hs
	csel x17, x14, x17, hs
	csel x24, x27, x24, hs
	lsl x20, x28, #32
	adds x21, x21, x20
	lsr x8, x28, #32
	adcs x4, x4, x8
	mul x16, x28, x12
	adcs x16, x15, x16
	umulh x28, x28, x12
	adcs x7, x7, x28
	adcs x14, x23, x23
	adds x21, x21, x11
	adcs x4, x4, x5
	adcs x16, x16, x13
	adcs x7, x7, x30
	adcs x9, x14, x9
	adds x27, x25, x25
	lsl x20, x21, #32
	lsr x8, x21, #32
	mul x15, x21, x12
	umulh x21, x21, x12
	adcs x28, x10, x10
	adcs x11, x22, x22
	adcs x5, x6, x6
	adc x13, x23, x23
	ldr x30, [x0, #7264]
	adds x4, x4, x30
	ldr x14, [x0, #7272]
	adcs x14, x16, x14
	ldr x30, [x0, #7280]
	adcs x7, x7, x30
	adcs x9, x9, x23
	adds x4, x4, x20
	adcs x8, x14, x8
	adcs x7, x7, x15
	adcs x9, x9, x21
	adcs x16, x23, x23
	adds x30, x4, x26
	ldr x20, [x0, #72]
	sbcs x14, x8, x20
	sbcs x15, x7, x23
	sbcs x21, x9, x3
	sbcs x16, x16, x23
	csel x30, x30, x4, hs
	csel x8, x14, x8, hs
	csel x15, x15, x7, hs
	csel x9, x21, x9, hs
	adds x30, x30, x30
	adcs x8, x8, x8
	adcs x15, x15, x15
	adcs x9, x9, x9
	adc x16, x23, x23
	adds x4, x30, x26
	sbcs x14, x8, x20
	sbcs x7, x15, x23
	sbcs x21, x9, x3
	sbcs x16, x16, x23
	csel x30, x4, x30, hs
	csel x8, x14, x8, hs
	csel x7, x7, x15, hs
	csel x21, x21, x9, hs
	adds x30, x30, x30
	adcs x8, x8, x8
	adcs x7, x7, x7
	adcs x21, x21, x21
	adc x16, x23, x23
	adds x4, x30, x26
	sbcs x14, x8, x20
	sbcs x15, x7, x23
	sbcs x9, x21, x3
	sbcs x16, x16, x23
	csel x30, x4, x30, hs
	csel x8, x14, x8, hs
	csel x7, x15, x7, hs
	csel x21, x9, x21, hs
	str x21, [x0, #920]
	str x30, [x0, #896]
	str x8, [x0, #904]
	str x7, [x0, #912]
	adds x16, x27, x26
	sbcs x4, x28, x20
	sbcs x14, x11, x23
	sbcs x15, x5, x3
	sbcs x13, x13, x23
	csel x16, x16, x27, hs
	csel x28, x4, x28, hs
	csel x11, x14, x11, hs
	csel x5, x15, x5, hs
	adds x25, x16, x25
	adcs x10, x28, x10
	adcs x11, x11, x22
	adcs x5, x5, x6
	adc x9, x23, x23
	adds x13, x25, x26
	sbcs x27, x10, x20
	sbcs x4, x11, x23
	sbcs x14, x5, x3
	sbcs x9, x9, x23
	csel x13, x13, x25, hs
	csel x27, x27, x10, hs
	csel x4, x4, x11, hs
	csel x5, x14, x5, hs
	umulh x15, x13, x13
	mul x16, x13, x27
	umulh x28, x13, x27
	mul x22, x13, x13
	mul x6, x13, x4
	adds x28, x28, x6
	mul x9, x27, x27
	umulh x25, x13, x4
	mul x10, x13, x5
	adcs x10, x10, x25
	umulh x11, x13, x5
	mul x14, x27, x4
	umulh x6, x27, x4
	mul x25, x27, x5
	adcs x25, x11, x25
	umulh x11, x27, x5
	mul x12, x4, x5
	adcs x11, x12, x11
	umulh x12, x4, x5
	adc x12, x12, x23
	adds x14, x10, x14
	adcs x6, x25, x6
	adcs x11, x11, x23
	adc x12, x12, x23
	adds x16, x16, x16
	adcs x28, x28, x28
	adcs x14, x14, x14
	adcs x6, x6, x6
	adcs x11, x11, x11
	adcs x12, x12, x12
	adc x10, x23, x23
	adds x15, x16, x15
	adcs x28, x28, x9
	umulh x25, x27, x27
	adcs x14, x14, x25
	mul x16, x4, x4
	adcs x6, x6, x16
	umulh x9, x4, x4
	adcs x11, x11, x9
	mul x25, x5, x5
	adcs x25, x12, x25
	umulh x16, x5, x5
	adc x16, x10, x16
	lsl x9, x22, #32
	sub x12, x22, x9
	extr x10, x15, x22, #32
	adds x15, x15, x9
	adcs x28, x28, x10
	str x5, [x0, #7280]
	extr x5, x28, x15, #32
	adcs x14, x14, x5
	str x4, [x0, #7272]
	add x4, x14, x12
	str x27, [x0, #7264]
	extr x27, x4, x28, #32
	adcs x6, x6, x27
	str x13, [x0, #7248]
	lsr x13, x4, #32
	adcs x11, x11, x13
	adcs x25, x25, x23
	adc x16, x16, x23
	subs x9, x22, x9
	sbcs x10, x22, x10
	sbcs x5, x15, x5
	sbcs x27, x28, x27
	sbc x13, x4, x13
	adds x14, x14, x12
	adcs x15, x10, x15
	adcs x28, x5, x28
	adcs x27, x27, x4
	adc x13, x13, x23
	adds x15, x6, x15
	adcs x28, x11, x28
	adcs x27, x25, x27
	adcs x16, x16, x13
	adc x9, x23, x23
	adds x2, x2, x2
	adcs x1, x1, x1
	adcs x17, x17, x17
	adcs x24, x24, x24
	adc x22, x23, x23
	adds x12, x15, x26
	sbcs x14, x28, x20
	sbcs x10, x27, x23
	sbcs x5, x16, x3
	sbcs x9, x9, x23
	csel x12, x12, x15, hs
	csel x14, x14, x28, hs
	csel x27, x10, x27, hs
	csel x16, x5, x16, hs
	subs x12, x12, x30
	sbcs x14, x14, x8
	sbcs x27, x27, x7
	sbcs x16, x16, x21
	sbc x4, x23, x23
	adds x12, x12, x4
	lsr x6, x4, #32
	adcs x6, x14, x6
	adcs x27, x27, x23
	lsl x11, x4, #32
	sub x11, x11, x4
	adc x11, x16, x11
	subs x12, x12, x30
	sbcs x6, x6, x8
	sbcs x27, x27, x7
	sbcs x11, x11, x21
	sbc x25, x23, x23
	adds x12, x12, x25
	str x12, [x0, #704]
	lsr x13, x25, #32
	adcs x6, x6, x13
	adcs x27, x27, x23
	str x6, [x0, #712]
	str x27, [x0, #720]
	lsl x9, x25, #32
	sub x25, x9, x25
	adc x11, x11, x25
	subs x30, x30, x12
	sbcs x8, x8, x6
	sbcs x27, x7, x27
	sbcs x21, x21, x11
	str x11, [x0, #728]
	sbc x15, x23, x23
	adds x28, x2, x26
	sbcs x10, x1, x20
	sbcs x5, x17, x23
	lsr x14, x15, #32
	lsl x4, x15, #32
	sub x4, x4, x15
	sbcs x16, x24, x3
	sbcs x22, x22, x23
	csel x2, x28, x2, hs
	csel x10, x10, x1, hs
	csel x5, x5, x17, hs
	csel x16, x16, x24, hs
	adds x2, x2, x2
	adcs x10, x10, x10
	adcs x5, x5, x5
	adcs x16, x16, x16
	adc x13, x23, x23
	adds x9, x2, x26
	sbcs x25, x10, x20
	sbcs x12, x5, x23
	sbcs x6, x16, x3
	sbcs x13, x13, x23
	csel x2, x9, x2, hs
	csel x10, x25, x10, hs
	csel x5, x12, x5, hs
	csel x6, x6, x16, hs
	adds x2, x2, x2
	adcs x10, x10, x10
	adcs x5, x5, x5
	adcs x6, x6, x6
	adc x7, x23, x23
	adds x11, x2, x26
	sbcs x22, x10, x20
	sbcs x28, x5, x23
	sbcs x1, x6, x3
	sbcs x7, x7, x23
	csel x2, x11, x2, hs
	csel x10, x22, x10, hs
	csel x5, x28, x5, hs
	csel x6, x1, x6, hs
	adds x30, x30, x15
	adcs x14, x8, x14
	ldr x17, [x0, #7248]
	umulh x24, x17, x30
	mul x13, x17, x30
	ldr x9, [x0, #7264]
	mul x25, x9, x30
	umulh x12, x9, x30
	str x2, [x0, #864]
	str x10, [x0, #872]
	str x5, [x0, #880]
	str x6, [x0, #888]
	adcs x27, x27, x23
	adc x4, x21, x4
	ldr x16, [x0, #1440]
	adds x16, x16, x16
	ldr x7, [x0, #1448]
	adcs x7, x7, x7
	ldr x11, [x0, #1456]
	adcs x11, x11, x11
	ldr x22, [x0, #1464]
	adcs x22, x22, x22
	adc x28, x23, x23
	mul x1, x17, x14
	adds x24, x1, x24
	mul x15, x17, x27
	mul x8, x17, x4
	umulh x21, x17, x14
	adcs x15, x15, x21
	umulh x1, x17, x27
	adcs x8, x8, x1
	umulh x17, x17, x4
	adcs x17, x23, x17
	lsl x21, x13, #32
	adds x21, x24, x21
	lsr x1, x13, #32
	adcs x15, x15, x1
	ldr x24, [x0, #7136]
	mul x1, x13, x24
	adcs x8, x8, x1
	umulh x13, x13, x24
	adcs x17, x17, x13
	adcs x1, x23, x23
	adds x25, x21, x25
	mul x13, x9, x14
	adcs x13, x15, x13
	mul x21, x9, x27
	adcs x21, x8, x21
	mul x15, x9, x4
	adcs x17, x17, x15
	umulh x8, x9, x4
	adcs x1, x1, x8
	adds x13, x13, x12
	umulh x15, x9, x14
	adcs x21, x21, x15
	umulh x9, x9, x27
	adcs x17, x17, x9
	ldr x8, [x0, #7272]
	mul x12, x8, x30
	adcs x1, x1, x23
	lsl x15, x25, #32
	adds x13, x13, x15
	lsr x9, x25, #32
	adcs x21, x21, x9
	mul x15, x25, x24
	adcs x17, x17, x15
	umulh x25, x25, x24
	adcs x25, x1, x25
	mul x9, x8, x14
	adcs x15, x23, x23
	adds x12, x13, x12
	adcs x9, x21, x9
	umulh x1, x8, x30
	mul x13, x8, x27
	adcs x17, x17, x13
	mul x21, x8, x4
	adcs x21, x25, x21
	umulh x13, x8, x4
	adcs x13, x15, x13
	adds x9, x9, x1
	umulh x25, x8, x14
	adcs x17, x17, x25
	umulh x8, x8, x27
	ldr x15, [x0, #7280]
	mul x1, x15, x30
	adcs x21, x21, x8
	mul x25, x15, x14
	umulh x30, x15, x30
	umulh x14, x15, x14
	adcs x13, x13, x23
	lsl x8, x12, #32
	adds x9, x9, x8
	lsr x8, x12, #32
	adcs x17, x17, x8
	mul x8, x12, x24
	adcs x8, x21, x8
	umulh x12, x12, x24
	adcs x13, x13, x12
	mul x21, x15, x27
	umulh x27, x15, x27
	adcs x12, x23, x23
	adds x9, x9, x1
	adcs x17, x17, x25
	mul x1, x15, x4
	umulh x15, x15, x4
	lsl x25, x9, #32
	adcs x21, x8, x21
	lsr x4, x9, #32
	adcs x1, x13, x1
	mul x8, x9, x24
	adcs x15, x12, x15
	adds x13, x16, x26
	umulh x9, x9, x24
	sbcs x12, x7, x20
	sbcs x24, x11, x23
	sbcs x6, x22, x3
	sbcs x28, x28, x23
	csel x16, x13, x16, hs
	csel x7, x12, x7, hs
	csel x11, x24, x11, hs
	csel x6, x6, x22, hs
	adds x17, x17, x30
	adcs x21, x21, x14
	adcs x1, x1, x27
	adcs x15, x15, x23
	adds x17, x17, x25
	adcs x4, x21, x4
	adcs x1, x1, x8
	mul x28, x16, x7
	umulh x13, x16, x16
	umulh x12, x16, x7
	mul x24, x16, x11
	mul x22, x16, x16
	umulh x30, x16, x11
	mul x14, x7, x7
	mul x27, x16, x6
	adcs x15, x15, x9
	mul x25, x7, x11
	str x16, [x0, #768]
	str x7, [x0, #776]
	str x11, [x0, #784]
	str x6, [x0, #792]
	adcs x21, x23, x23
	adds x24, x12, x24
	adcs x27, x27, x30
	lsl x8, x22, #32
	umulh x9, x16, x6
	umulh x12, x7, x11
	mul x30, x7, x6
	adcs x30, x9, x30
	umulh x9, x7, x6
	mul x16, x11, x6
	adcs x16, x16, x9
	umulh x9, x11, x6
	adc x9, x9, x23
	adds x25, x27, x25
	adcs x12, x30, x12
	adcs x16, x16, x23
	adc x9, x9, x23
	adds x28, x28, x28
	adcs x24, x24, x24
	adcs x25, x25, x25
	adcs x12, x12, x12
	adcs x16, x16, x16
	adcs x9, x9, x9
	adc x27, x23, x23
	adds x13, x28, x13
	adcs x14, x24, x14
	umulh x30, x7, x7
	adcs x30, x25, x30
	mul x28, x11, x11
	adcs x28, x12, x28
	umulh x24, x11, x11
	adcs x24, x16, x24
	mul x25, x6, x6
	adcs x9, x9, x25
	umulh x12, x6, x6
	adc x12, x27, x12
	adds x16, x17, x26
	sbcs x25, x4, x20
	sbcs x27, x1, x23
	sbcs x6, x15, x3
	sbcs x21, x21, x23
	csel x16, x16, x17, hs
	csel x25, x25, x4, hs
	csel x1, x27, x1, hs
	csel x15, x6, x15, hs
	subs x2, x16, x2
	extr x21, x13, x22, #32
	sbcs x10, x25, x10
	sub x17, x22, x8
	sbcs x5, x1, x5
	ldr x4, [x0, #888]
	sbcs x15, x15, x4
	sbc x27, x23, x23
	adds x13, x13, x8
	adcs x14, x14, x21
	extr x6, x14, x13, #32
	adcs x30, x30, x6
	lsr x16, x27, #32
	lsl x25, x27, #32
	sub x25, x25, x27
	add x1, x30, x17
	extr x4, x1, x14, #32
	adcs x28, x28, x4
	lsr x11, x1, #32
	adcs x24, x24, x11
	adcs x9, x9, x23
	adc x12, x12, x23
	subs x8, x22, x8
	sbcs x22, x22, x21
	sbcs x6, x13, x6
	sbcs x4, x14, x4
	sbc x11, x1, x11
	adds x17, x30, x17
	adcs x22, x22, x13
	adcs x6, x6, x14
	adcs x4, x4, x1
	adc x11, x11, x23
	adds x27, x2, x27
	adcs x16, x10, x16
	str x27, [x0, #736]
	adcs x5, x5, x23
	str x16, [x0, #744]
	adc x15, x15, x25
	str x5, [x0, #752]
	str x15, [x0, #760]
	adds x22, x28, x22
	adcs x6, x24, x6
	adcs x4, x9, x4
	adcs x11, x12, x11
	adc x8, x23, x23
	adds x21, x22, x26
	sbcs x30, x6, x20
	sbcs x17, x4, x23
	sbcs x13, x11, x3
	sbcs x8, x8, x23
	csel x22, x21, x22, hs
	csel x6, x30, x6, hs
	csel x17, x17, x4, hs
	csel x13, x13, x11, hs
	ldr x14, [x0, #768]
	umulh x1, x22, x14
	mul x2, x22, x14
	mul x10, x22, x7
	umulh x27, x22, x7
	ldr x16, [x0, #784]
	mul x25, x22, x16
	umulh x5, x22, x16
	ldr x15, [x0, #792]
	mul x28, x22, x15
	umulh x24, x22, x15
	mul x9, x6, x14
	mul x12, x6, x7
	umulh x8, x6, x14
	mul x21, x6, x16
	umulh x30, x6, x7
	str x22, [x0, #5400]
	mul x4, x6, x15
	adds x10, x10, x1
	umulh x11, x6, x15
	adcs x25, x25, x27
	umulh x22, x6, x16
	str x6, [x0, #5408]
	mul x1, x17, x14
	adcs x28, x28, x5
	mul x27, x17, x7
	str x17, [x0, #5416]
	str x13, [x0, #5424]
	adcs x24, x23, x24
	lsl x6, x2, #32
	adds x10, x10, x6
	lsr x5, x2, #32
	adcs x25, x25, x5
	ldr x6, [x0, #7136]
	mul x5, x2, x6
	adcs x28, x28, x5
	umulh x2, x2, x6
	adcs x24, x24, x2
	umulh x5, x17, x14
	adcs x2, x23, x23
	adds x10, x10, x9
	adcs x25, x25, x12
	mul x9, x17, x16
	adcs x28, x28, x21
	umulh x12, x17, x7
	adcs x24, x24, x4
	mul x21, x17, x15
	adcs x11, x2, x11
	umulh x4, x17, x15
	adds x25, x25, x8
	umulh x17, x17, x16
	mul x2, x13, x14
	adcs x28, x28, x30
	mul x8, x13, x7
	adcs x22, x24, x22
	umulh x14, x13, x14
	lsl x30, x10, #32
	umulh x7, x13, x7
	adcs x11, x11, x23
	adds x25, x25, x30
	lsr x24, x10, #32
	adcs x28, x28, x24
	mul x30, x10, x6
	adcs x30, x22, x30
	umulh x10, x10, x6
	mul x24, x13, x16
	adcs x11, x11, x10
	umulh x16, x13, x16
	mul x22, x13, x15
	umulh x13, x13, x15
	adcs x10, x23, x23
	adds x25, x25, x1
	adcs x28, x28, x27
	lsl x15, x25, #32
	lsr x1, x25, #32
	adcs x30, x30, x9
	mul x27, x25, x6
	adcs x21, x11, x21
	umulh x25, x25, x6
	adcs x4, x10, x4
	adds x28, x28, x5
	adcs x12, x30, x12
	adcs x21, x21, x17
	adcs x4, x4, x23
	adds x28, x28, x15
	adcs x1, x12, x1
	adcs x21, x21, x27
	adcs x4, x4, x25
	adcs x9, x23, x23
	adds x28, x28, x2
	adcs x1, x1, x8
	lsl x11, x28, #32
	lsr x10, x28, #32
	mul x5, x28, x6
	umulh x28, x28, x6
	adcs x24, x21, x24
	adcs x4, x4, x22
	adcs x13, x9, x13
	adds x14, x1, x14
	adcs x24, x24, x7
	adcs x4, x4, x16
	adcs x13, x13, x23
	adds x11, x14, x11
	adcs x24, x24, x10
	adcs x4, x4, x5
	adcs x13, x13, x28
	adcs x30, x23, x23
	adds x26, x11, x26
	sbcs x20, x24, x20
	sbcs x17, x4, x23
	sbcs x3, x13, x3
	sbcs x30, x30, x23
	csel x26, x26, x11, hs
	csel x24, x20, x24, hs
	csel x4, x17, x4, hs
	csel x13, x3, x13, hs
	str x26, [x0, #5432]
	str x24, [x0, #5440]
	str x4, [x0, #5448]
	str x13, [x0, #5456]
	ldr x1, [x0, #704]
	str x1, [x0, #608]
	ldr x1, [x0, #712]
	str x1, [x0, #616]
	ldr x1, [x0, #720]
	str x1, [x0, #624]
	ldr x1, [x0, #728]
	str x1, [x0, #632]
	ldr x1, [x0, #736]
	str x1, [x0, #640]
	ldr x1, [x0, #744]
	str x1, [x0, #648]
	ldr x1, [x0, #752]
	str x1, [x0, #656]
	ldr x1, [x0, #760]
	str x1, [x0, #664]
	ldr x1, [x0, #896]
	str x1, [x0, #704]
	ldr x1, [x0, #904]
	str x1, [x0, #712]
	ldr x1, [x0, #912]
	str x1, [x0, #720]
	ldr x1, [x0, #920]
	str x1, [x0, #728]
	ldr x1, [x0, #864]
	str x1, [x0, #736]
	ldr x1, [x0, #872]
	str x1, [x0, #744]
	ldr x1, [x0, #880]
	str x1, [x0, #752]
	ldr x1, [x0, #888]
	str x1, [x0, #760]
215:
	add x19, x19, #1
	ldr x1, [x0, #608]
	ldr x2, [x0, #704]
	subs x3, x1, x2
	ldr x4, [x0, #616]
	ldr x5, [x0, #712]
	sbcs x6, x4, x5
	ldr x7, [x0, #624]
	ldr x8, [x0, #720]
	sbcs x9, x7, x8
	ldr x10, [x0, #632]
	ldr x11, [x0, #728]
	sbcs x12, x10, x11
	movz x13, #0, lsl #0
	sbc x14, x13, x13
	adds x3, x3, x14
	lsr x15, x14, #32
	lsl x16, x14, #32
	adcs x15, x6, x15
	umulh x17, x3, x3
	mul x20, x3, x3
	sub x16, x16, x14
	mul x21, x3, x15
	adcs x9, x9, x13
	umulh x22, x3, x15
	mul x23, x15, x15
	umulh x24, x15, x15
	mul x25, x3, x9
	adc x12, x12, x16
	umulh x26, x3, x9
	adds x25, x22, x25
	lsl x27, x20, #32
	mul x28, x3, x12
	adcs x28, x28, x26
	umulh x30, x3, x12
	mul x6, x15, x9
	umulh x14, x15, x9
	mul x16, x15, x12
	adcs x16, x30, x16
	umulh x22, x15, x12
	mul x26, x9, x12
	adcs x26, x26, x22
	umulh x30, x9, x12
	adc x30, x30, x13
	adds x6, x28, x6
	adcs x14, x16, x14
	adcs x26, x26, x13
	adc x30, x30, x13
	adds x21, x21, x21
	adcs x25, x25, x25
	adcs x6, x6, x6
	adcs x14, x14, x14
	adcs x26, x26, x26
	adcs x30, x30, x30
	adc x22, x13, x13
	adds x17, x21, x17
	adcs x25, x25, x23
	adcs x24, x6, x24
	mul x28, x9, x9
	adcs x14, x14, x28
	umulh x16, x9, x9
	adcs x26, x26, x16
	mul x21, x12, x12
	adcs x30, x30, x21
	umulh x23, x12, x12
	adc x23, x22, x23
	sub x6, x20, x27
	extr x28, x17, x20, #32
	adds x17, x17, x27
	adcs x25, x25, x28
	extr x16, x25, x17, #32
	adcs x24, x24, x16
	add x21, x24, x6
	extr x22, x21, x25, #32
	adcs x14, x14, x22
	lsr x11, x21, #32
	adcs x26, x26, x11
	adcs x30, x30, x13
	adc x23, x23, x13
	subs x27, x20, x27
	sbcs x28, x20, x28
	sbcs x16, x17, x16
	sbcs x22, x25, x22
	sbc x11, x21, x11
	adds x24, x24, x6
	adcs x28, x28, x17
	adcs x25, x16, x25
	adcs x21, x22, x21
	adc x11, x11, x13
	adds x28, x14, x28
	movz x27, #1, lsl #0
	orr x20, x27, x27
	movk x20, #0, lsl #16
	adcs x25, x26, x25
	ldr x6, [x0, #768]
	umulh x24, x6, x3
	adcs x21, x30, x21
	adcs x11, x23, x11
	movk x20, #65535, lsl #32
	mul x17, x6, x3
	movk x20, #65535, lsl #48
	adc x16, x13, x13
	adds x22, x28, x27
	ldr x14, [x0, #72]
	sbcs x26, x25, x14
	sbcs x30, x21, x13
	ldr x23, [x0, #88]
	sbcs x8, x11, x23
	sbcs x16, x16, x13
	csel x22, x22, x28, hs
	csel x25, x26, x25, hs
	csel x21, x30, x21, hs
	csel x8, x8, x11, hs
	mul x16, x6, x15
	adds x16, x16, x24
	mul x28, x6, x9
	mul x26, x6, x12
	umulh x30, x6, x15
	adcs x28, x28, x30
	umulh x11, x6, x9
	adcs x11, x26, x11
	umulh x6, x6, x12
	adcs x6, x13, x6
	lsl x24, x17, #32
	adds x16, x16, x24
	lsr x30, x17, #32
	adcs x28, x28, x30
	mul x26, x17, x20
	adcs x11, x11, x26
	umulh x17, x17, x20
	adcs x17, x6, x17
	adcs x24, x13, x13
	ldr x30, [x0, #776]
	mul x26, x30, x3
	adds x26, x16, x26
	mul x6, x30, x15
	adcs x6, x28, x6
	mul x16, x30, x9
	adcs x16, x11, x16
	mul x28, x30, x12
	adcs x28, x17, x28
	umulh x11, x30, x12
	adcs x11, x24, x11
	umulh x17, x30, x3
	adds x6, x6, x17
	umulh x24, x30, x15
	adcs x24, x16, x24
	umulh x30, x30, x9
	adcs x28, x28, x30
	adcs x11, x11, x13
	lsl x17, x26, #32
	adds x6, x6, x17
	lsr x16, x26, #32
	adcs x16, x24, x16
	mul x30, x26, x20
	adcs x28, x28, x30
	umulh x26, x26, x20
	adcs x11, x11, x26
	adcs x17, x13, x13
	ldr x24, [x0, #784]
	mul x30, x24, x3
	adds x30, x6, x30
	mul x26, x24, x15
	adcs x16, x16, x26
	mul x6, x24, x9
	adcs x6, x28, x6
	mul x26, x24, x12
	adcs x26, x11, x26
	umulh x28, x24, x12
	adcs x28, x17, x28
	umulh x11, x24, x3
	adds x16, x16, x11
	umulh x17, x24, x15
	adcs x6, x6, x17
	umulh x24, x24, x9
	adcs x26, x26, x24
	adcs x28, x28, x13
	lsl x11, x30, #32
	adds x11, x16, x11
	lsr x17, x30, #32
	adcs x6, x6, x17
	mul x24, x30, x20
	adcs x26, x26, x24
	umulh x30, x30, x20
	adcs x28, x28, x30
	adcs x16, x13, x13
	ldr x17, [x0, #792]
	mul x24, x17, x3
	adds x24, x11, x24
	umulh x3, x17, x3
	mul x30, x17, x15
	adcs x30, x6, x30
	umulh x15, x17, x15
	mul x11, x17, x9
	adcs x11, x26, x11
	umulh x9, x17, x9
	mul x6, x17, x12
	umulh x12, x17, x12
	adcs x6, x28, x6
	adcs x16, x16, x12
	adds x30, x30, x3
	adcs x11, x11, x15
	adcs x9, x6, x9
	adcs x16, x16, x13
	lsl x26, x24, #32
	adds x30, x30, x26
	lsr x17, x24, #32
	adcs x11, x11, x17
	mul x28, x24, x20
	adcs x28, x9, x28
	umulh x24, x24, x20
	adcs x16, x16, x24
	umulh x12, x1, x22
	adcs x3, x13, x13
	adds x15, x30, x27
	sbcs x6, x11, x14
	sbcs x26, x28, x13
	sbcs x17, x16, x23
	sbcs x3, x3, x13
	csel x30, x15, x30, hs
	csel x11, x6, x11, hs
	csel x28, x26, x28, hs
	csel x17, x17, x16, hs
	str x30, [x0, #768]
	str x11, [x0, #776]
	str x28, [x0, #784]
	str x17, [x0, #792]
	mul x9, x1, x22
	mul x24, x1, x25
	adds x24, x24, x12
	mul x3, x1, x21
	mul x15, x1, x8
	umulh x6, x1, x25
	adcs x3, x3, x6
	umulh x26, x1, x21
	adcs x15, x15, x26
	umulh x1, x1, x8
	adcs x1, x13, x1
	lsl x16, x9, #32
	adds x24, x24, x16
	lsr x12, x9, #32
	adcs x3, x3, x12
	mul x6, x9, x20
	adcs x15, x15, x6
	umulh x9, x9, x20
	adcs x1, x1, x9
	adcs x26, x13, x13
	mul x16, x4, x22
	adds x16, x24, x16
	mul x12, x4, x25
	adcs x12, x3, x12
	mul x6, x4, x21
	adcs x15, x15, x6
	mul x9, x4, x8
	adcs x1, x1, x9
	umulh x24, x4, x8
	adcs x24, x26, x24
	umulh x3, x4, x22
	adds x12, x12, x3
	umulh x6, x4, x25
	adcs x15, x15, x6
	umulh x4, x4, x21
	adcs x4, x1, x4
	adcs x24, x24, x13
	lsl x9, x16, #32
	adds x12, x12, x9
	lsr x26, x16, #32
	adcs x15, x15, x26
	mul x3, x16, x20
	adcs x3, x4, x3
	umulh x16, x16, x20
	adcs x24, x24, x16
	adcs x6, x13, x13
	mul x1, x7, x22
	adds x12, x12, x1
	mul x9, x7, x25
	adcs x15, x15, x9
	mul x26, x7, x21
	adcs x3, x3, x26
	mul x4, x7, x8
	adcs x4, x24, x4
	umulh x16, x7, x8
	adcs x16, x6, x16
	umulh x1, x7, x22
	adds x15, x15, x1
	umulh x9, x7, x25
	adcs x9, x3, x9
	umulh x7, x7, x21
	adcs x4, x4, x7
	adcs x16, x16, x13
	lsl x26, x12, #32
	adds x15, x15, x26
	lsr x24, x12, #32
	adcs x24, x9, x24
	mul x6, x12, x20
	adcs x4, x4, x6
	umulh x12, x12, x20
	adcs x16, x16, x12
	adcs x1, x13, x13
	mul x3, x10, x22
	adds x15, x15, x3
	mul x7, x10, x25
	adcs x24, x24, x7
	mul x26, x10, x21
	adcs x26, x4, x26
	mul x9, x10, x8
	adcs x16, x16, x9
	umulh x6, x10, x8
	adcs x6, x1, x6
	umulh x12, x10, x22
	adds x12, x24, x12
	umulh x3, x10, x25
	adcs x26, x26, x3
	umulh x10, x10, x21
	adcs x16, x16, x10
	adcs x6, x6, x13
	lsl x7, x15, #32
	adds x7, x12, x7
	lsr x4, x15, #32
	adcs x26, x26, x4
	mul x9, x15, x20
	adcs x16, x16, x9
	umulh x15, x15, x20
	adcs x6, x6, x15
	umulh x1, x2, x22
	adcs x24, x13, x13
	adds x3, x7, x27
	sbcs x10, x26, x14
	sbcs x12, x16, x13
	sbcs x4, x6, x23
	sbcs x24, x24, x13
	csel x3, x3, x7, hs
	csel x26, x10, x26, hs
	csel x16, x12, x16, hs
	csel x6, x4, x6, hs
	str x3, [x0, #608]
	str x26, [x0, #616]
	str x16, [x0, #624]
	str x6, [x0, #632]
	mul x9, x2, x22
	mul x15, x2, x25
	adds x1, x15, x1
	mul x24, x2, x21
	mul x7, x2, x8
	umulh x10, x2, x25
	adcs x10, x24, x10
	umulh x12, x2, x21
	adcs x7, x7, x12
	umulh x2, x2, x8
	adcs x2, x13, x2
	lsl x4, x9, #32
	adds x1, x1, x4
	lsr x15, x9, #32
	adcs x10, x10, x15
	mul x24, x9, x20
	adcs x7, x7, x24
	umulh x9, x9, x20
	adcs x2, x2, x9
	adcs x12, x13, x13
	mul x4, x5, x22
	adds x1, x1, x4
	mul x15, x5, x25
	adcs x10, x10, x15
	mul x24, x5, x21
	adcs x24, x7, x24
	mul x9, x5, x8
	adcs x2, x2, x9
	umulh x4, x5, x8
	adcs x4, x12, x4
	umulh x15, x5, x22
	adds x15, x10, x15
	umulh x7, x5, x25
	adcs x24, x24, x7
	umulh x5, x5, x21
	adcs x2, x2, x5
	adcs x4, x4, x13
	lsl x9, x1, #32
	adds x9, x15, x9
	lsr x12, x1, #32
	adcs x24, x24, x12
	mul x10, x1, x20
	adcs x2, x2, x10
	umulh x1, x1, x20
	adcs x4, x4, x1
	adcs x7, x13, x13
	ldr x5, [x0, #720]
	mul x15, x5, x22
	adds x9, x9, x15
	mul x12, x5, x25
	adcs x12, x24, x12
	mul x10, x5, x21
	adcs x2, x2, x10
	mul x1, x5, x8
	adcs x4, x4, x1
	umulh x15, x5, x8
	adcs x15, x7, x15
	umulh x24, x5, x22
	adds x12, x12, x24
	umulh x10, x5, x25
	adcs x2, x2, x10
	umulh x5, x5, x21
	adcs x4, x4, x5
	adcs x15, x15, x13
	lsl x1, x9, #32
	adds x12, x12, x1
	lsr x7, x9, #32
	adcs x2, x2, x7
	mul x24, x9, x20
	adcs x4, x4, x24
	umulh x9, x9, x20
	adcs x15, x15, x9
	adcs x10, x13, x13
	ldr x5, [x0, #728]
	mul x1, x5, x22
	adds x1, x12, x1
	mul x7, x5, x25
	adcs x7, x2, x7
	mul x24, x5, x21
	adcs x24, x4, x24
	mul x9, x5, x8
	adcs x15, x15, x9
	umulh x12, x5, x8
	adcs x12, x10, x12
	umulh x2, x5, x22
	adds x7, x7, x2
	umulh x4, x5, x25
	adcs x24, x24, x4
	umulh x5, x5, x21
	adcs x5, x15, x5
	adcs x12, x12, x13
	lsl x9, x1, #32
	adds x7, x7, x9
	lsr x10, x1, #32
	adcs x24, x24, x10
	mul x2, x1, x20
	adcs x2, x5, x2
	umulh x1, x1, x20
	adcs x12, x12, x1
	adcs x4, x13, x13
	adds x15, x7, x27
	sbcs x9, x24, x14
	sbcs x10, x2, x13
	sbcs x5, x12, x23
	sbcs x4, x4, x13
	csel x7, x15, x7, hs
	csel x24, x9, x24, hs
	csel x2, x10, x2, hs
	csel x5, x5, x12, hs
	ldr x1, [x0, #640]
	ldr x4, [x0, #736]
	subs x4, x1, x4
	ldr x15, [x0, #648]
	ldr x9, [x0, #744]
	sbcs x9, x15, x9
	ldr x10, [x0, #656]
	ldr x12, [x0, #752]
	sbcs x12, x10, x12
	ldr x17, [x0, #664]
	ldr x28, [x0, #760]
	sbcs x28, x17, x28
	sbc x11, x13, x13
	adds x4, x4, x11
	lsr x30, x11, #32
	adcs x9, x9, x30
	adcs x12, x12, x13
	lsl x30, x11, #32
	sub x30, x30, x11
	adc x28, x28, x30
	mul x11, x4, x9
	umulh x30, x4, x9
	str x8, [x0, #7104]
	mul x8, x4, x12
	adds x8, x30, x8
	umulh x30, x4, x12
	str x21, [x0, #7112]
	mul x21, x4, x28
	adcs x21, x21, x30
	umulh x30, x4, x28
	str x25, [x0, #7120]
	mul x25, x9, x12
	str x22, [x0, #7128]
	umulh x22, x9, x12
	mul x17, x9, x28
	adcs x30, x30, x17
	umulh x17, x9, x28
	mul x10, x12, x28
	adcs x10, x10, x17
	umulh x17, x12, x28
	adc x17, x17, x13
	adds x25, x21, x25
	adcs x22, x30, x22
	adcs x10, x10, x13
	adc x17, x17, x13
	adds x11, x11, x11
	adcs x8, x8, x8
	adcs x25, x25, x25
	adcs x22, x22, x22
	adcs x10, x10, x10
	adcs x17, x17, x17
	adc x21, x13, x13
	mul x30, x4, x4
	umulh x15, x4, x4
	adds x11, x11, x15
	mul x15, x9, x9
	adcs x15, x8, x15
	umulh x8, x9, x9
	adcs x25, x25, x8
	mul x8, x12, x12
	adcs x8, x22, x8
	umulh x22, x12, x12
	adcs x22, x10, x22
	mul x10, x28, x28
	adcs x10, x17, x10
	umulh x17, x28, x28
	adc x17, x21, x17
	lsl x21, x30, #32
	str x28, [x0, #7136]
	sub x28, x30, x21
	str x12, [x0, #7144]
	extr x12, x11, x30, #32
	adds x11, x11, x21
	adcs x15, x15, x12
	str x9, [x0, #7152]
	extr x9, x15, x11, #32
	adcs x25, x25, x9
	str x4, [x0, #7160]
	add x4, x25, x28
	extr x1, x4, x15, #32
	adcs x8, x8, x1
	str x20, [x0, #7168]
	lsr x20, x4, #32
	adcs x22, x22, x20
	adcs x10, x10, x13
	adc x17, x17, x13
	subs x21, x30, x21
	sbcs x12, x30, x12
	sbcs x9, x11, x9
	sbcs x1, x15, x1
	sbc x20, x4, x20
	adds x28, x25, x28
	adcs x11, x12, x11
	adcs x15, x9, x15
	adcs x1, x1, x4
	adc x20, x20, x13
	adds x11, x8, x11
	adcs x22, x22, x15
	adcs x10, x10, x1
	adcs x20, x17, x20
	adc x21, x13, x13
	adds x30, x11, x27
	sbcs x25, x22, x14
	sbcs x28, x10, x13
	sbcs x12, x20, x23
	sbcs x21, x21, x13
	csel x11, x30, x11, hs
	csel x22, x25, x22, hs
	csel x10, x28, x10, hs
	csel x20, x12, x20, hs
	subs x9, x3, x7
	sbcs x4, x26, x24
	sbcs x8, x16, x2
	sbcs x15, x6, x5
	sbc x1, x13, x13
	adds x9, x9, x1
	lsr x17, x1, #32
	adcs x17, x4, x17
	adcs x8, x8, x13
	lsl x21, x1, #32
	sub x21, x21, x1
	adc x15, x15, x21
	ldr x30, [x0, #640]
	mul x25, x30, x9
	mul x28, x30, x17
	mul x12, x30, x8
	mul x4, x30, x15
	umulh x1, x30, x9
	adds x28, x28, x1
	umulh x21, x30, x17
	adcs x12, x12, x21
	umulh x1, x30, x8
	adcs x1, x4, x1
	umulh x30, x30, x15
	adcs x30, x13, x30
	lsl x21, x25, #32
	adds x28, x28, x21
	lsr x4, x25, #32
	adcs x12, x12, x4
	ldr x21, [x0, #7168]
	mul x4, x25, x21
	adcs x1, x1, x4
	umulh x25, x25, x21
	adcs x25, x30, x25
	adcs x4, x13, x13
	ldr x30, [x0, #648]
	mul x23, x30, x9
	adds x23, x28, x23
	mul x28, x30, x17
	adcs x28, x12, x28
	mul x12, x30, x8
	adcs x1, x1, x12
	mul x12, x30, x15
	adcs x12, x25, x12
	umulh x25, x30, x15
	adcs x25, x4, x25
	umulh x4, x30, x9
	adds x28, x28, x4
	umulh x4, x30, x17
	adcs x1, x1, x4
	umulh x30, x30, x8
	adcs x12, x12, x30
	adcs x25, x25, x13
	lsl x4, x23, #32
	adds x28, x28, x4
	lsr x30, x23, #32
	adcs x1, x1, x30
	mul x4, x23, x21
	adcs x4, x12, x4
	umulh x23, x23, x21
	adcs x25, x25, x23
	adcs x30, x13, x13
	subs x11, x11, x3
	sbcs x22, x22, x26
	sbcs x10, x10, x16
	sbcs x20, x20, x6
	ldr x12, [x0, #656]
	mul x23, x12, x9
	mul x14, x12, x17
	mul x27, x12, x8
	mul x6, x12, x15
	umulh x16, x12, x15
	umulh x26, x12, x9
	umulh x3, x12, x17
	umulh x12, x12, x8
	str x5, [x0, #7176]
	ldr x5, [x0, #664]
	str x2, [x0, #7184]
	mul x2, x5, x9
	umulh x9, x5, x9
	str x9, [x0, #7192]
	mul x9, x5, x17
	umulh x17, x5, x17
	str x17, [x0, #7200]
	mul x17, x5, x8
	umulh x8, x5, x8
	str x8, [x0, #7208]
	mul x8, x5, x15
	umulh x5, x5, x15
	sbc x15, x13, x13
	adds x23, x28, x23
	adcs x1, x1, x14
	adcs x27, x4, x27
	adcs x6, x25, x6
	adcs x16, x30, x16
	adds x1, x1, x26
	adcs x27, x27, x3
	adcs x6, x6, x12
	adcs x16, x16, x13
	adds x11, x11, x15
	lsl x28, x23, #32
	lsr x14, x23, #32
	mul x4, x23, x21
	umulh x23, x23, x21
	lsr x25, x15, #32
	adcs x25, x22, x25
	adcs x10, x10, x13
	lsl x30, x15, #32
	sub x30, x30, x15
	adc x20, x20, x30
	adds x1, x1, x28
	adcs x14, x27, x14
	adcs x6, x6, x4
	adcs x16, x16, x23
	adcs x26, x13, x13
	subs x11, x11, x7
	sbcs x25, x25, x24
	ldr x3, [x0, #7184]
	sbcs x10, x10, x3
	ldr x12, [x0, #7176]
	sbcs x20, x20, x12
	sbc x22, x13, x13
	adds x1, x1, x2
	adcs x9, x14, x9
	adcs x17, x6, x17
	adcs x16, x16, x8
	adcs x5, x26, x5
	ldr x15, [x0, #7192]
	adds x9, x9, x15
	ldr x30, [x0, #7200]
	adcs x17, x17, x30
	ldr x28, [x0, #7208]
	adcs x16, x16, x28
	adcs x5, x5, x13
	adds x11, x11, x22
	str x11, [x0, #704]
	lsl x27, x1, #32
	lsr x4, x1, #32
	mul x23, x1, x21
	umulh x1, x1, x21
	lsr x7, x22, #32
	adcs x25, x25, x7
	adcs x10, x10, x13
	str x25, [x0, #712]
	str x10, [x0, #720]
	lsl x24, x22, #32
	sub x24, x24, x22
	adc x24, x20, x24
	adds x27, x9, x27
	adcs x17, x17, x4
	adcs x16, x16, x23
	adcs x5, x5, x1
	str x24, [x0, #728]
	adcs x3, x13, x13
	ldr x12, [x0, #608]
	subs x11, x12, x11
	ldr x2, [x0, #616]
	sbcs x25, x2, x25
	ldr x14, [x0, #624]
	sbcs x10, x14, x10
	ldr x6, [x0, #632]
	sbcs x6, x6, x24
	sbc x8, x13, x13
	movz x26, #1, lsl #0
	adds x15, x27, x26
	ldr x30, [x0, #72]
	sbcs x28, x17, x30
	sbcs x7, x16, x13
	ldr x22, [x0, #88]
	sbcs x20, x5, x22
	sbcs x3, x3, x13
	csel x27, x15, x27, hs
	csel x17, x28, x17, hs
	csel x16, x7, x16, hs
	csel x5, x20, x5, hs
	adds x11, x11, x8
	str x27, [x0, #640]
	str x17, [x0, #648]
	str x16, [x0, #656]
	str x5, [x0, #664]
	lsr x9, x8, #32
	adcs x9, x25, x9
	adcs x10, x10, x13
	lsl x4, x8, #32
	sub x4, x4, x8
	adc x6, x6, x4
	ldr x23, [x0, #7160]
	mul x1, x23, x11
	mul x12, x23, x9
	mul x2, x23, x10
	mul x14, x23, x6
	umulh x24, x23, x11
	adds x12, x12, x24
	umulh x3, x23, x9
	adcs x2, x2, x3
	umulh x15, x23, x10
	adcs x15, x14, x15
	umulh x23, x23, x6
	adcs x23, x13, x23
	lsl x28, x1, #32
	adds x12, x12, x28
	lsr x7, x1, #32
	adcs x2, x2, x7
	mul x20, x1, x21
	adcs x15, x15, x20
	umulh x1, x1, x21
	adcs x1, x23, x1
	adcs x25, x13, x13
	ldr x8, [x0, #7152]
	mul x4, x8, x11
	adds x12, x12, x4
	mul x24, x8, x9
	adcs x2, x2, x24
	mul x3, x8, x10
	adcs x15, x15, x3
	mul x14, x8, x6
	adcs x14, x1, x14
	umulh x28, x8, x6
	adcs x28, x25, x28
	umulh x7, x8, x11
	adds x2, x2, x7
	umulh x20, x8, x9
	adcs x15, x15, x20
	umulh x8, x8, x10
	adcs x14, x14, x8
	adcs x28, x28, x13
	lsl x23, x12, #32
	adds x2, x2, x23
	lsr x4, x12, #32
	adcs x15, x15, x4
	mul x24, x12, x21
	adcs x24, x14, x24
	umulh x12, x12, x21
	adcs x28, x28, x12
	adcs x3, x13, x13
	ldr x1, [x0, #7144]
	mul x25, x1, x11
	adds x25, x2, x25
	mul x7, x1, x9
	adcs x7, x15, x7
	mul x20, x1, x10
	adcs x20, x24, x20
	mul x8, x1, x6
	adcs x8, x28, x8
	umulh x23, x1, x6
	adcs x23, x3, x23
	umulh x4, x1, x11
	adds x7, x7, x4
	umulh x14, x1, x9
	adcs x20, x20, x14
	umulh x1, x1, x10
	adcs x8, x8, x1
	adcs x23, x23, x13
	lsl x12, x25, #32
	adds x7, x7, x12
	lsr x2, x25, #32
	adcs x2, x20, x2
	mul x15, x25, x21
	adcs x8, x8, x15
	umulh x25, x25, x21
	adcs x23, x23, x25
	adcs x24, x13, x13
	ldr x28, [x0, #7136]
	mul x3, x28, x11
	adds x3, x7, x3
	umulh x11, x28, x11
	mul x4, x28, x9
	adcs x4, x2, x4
	umulh x9, x28, x9
	mul x14, x28, x10
	adcs x14, x8, x14
	umulh x10, x28, x10
	mul x1, x28, x6
	umulh x28, x28, x6
	adcs x1, x23, x1
	adcs x28, x24, x28
	adds x4, x4, x11
	adcs x14, x14, x9
	adcs x1, x1, x10
	adcs x28, x28, x13
	lsl x12, x3, #32
	adds x12, x4, x12
	lsr x20, x3, #32
	adcs x14, x14, x20
	mul x15, x3, x21
	adcs x1, x1, x15
	umulh x3, x3, x21
	adcs x28, x28, x3
	ldr x25, [x0, #5400]
	ldr x7, [x0, #7128]
	umulh x2, x25, x7
	adcs x8, x13, x13
	adds x6, x12, x26
	sbcs x23, x14, x30
	sbcs x24, x1, x13
	sbcs x11, x28, x22
	sbcs x8, x8, x13
	csel x12, x6, x12, hs
	csel x14, x23, x14, hs
	csel x1, x24, x1, hs
	csel x28, x11, x28, hs
	subs x27, x12, x27
	sbcs x14, x14, x17
	mul x9, x25, x7
	sbcs x1, x1, x16
	ldr x10, [x0, #7120]
	mul x4, x25, x10
	sbcs x5, x28, x5
	umulh x20, x25, x10
	sbc x15, x13, x13
	adds x4, x4, x2
	lsr x3, x15, #32
	lsl x8, x15, #32
	sub x8, x8, x15
	ldr x6, [x0, #7112]
	mul x23, x25, x6
	adcs x20, x23, x20
	ldr x24, [x0, #7104]
	mul x11, x25, x24
	umulh x12, x25, x6
	adcs x12, x11, x12
	umulh x25, x25, x24
	adcs x25, x13, x25
	adds x15, x27, x15
	adcs x3, x14, x3
	str x15, [x0, #736]
	str x3, [x0, #744]
	lsl x17, x9, #32
	adcs x1, x1, x13
	adc x5, x5, x8
	ldr x16, [x0, #5408]
	mul x28, x16, x7
	adds x4, x4, x17
	str x1, [x0, #752]
	lsr x2, x9, #32
	adcs x20, x20, x2
	mul x23, x9, x21
	adcs x12, x12, x23
	umulh x9, x9, x21
	mul x11, x16, x10
	adcs x25, x25, x9
	umulh x27, x16, x7
	str x5, [x0, #760]
	mul x14, x16, x6
	adcs x15, x13, x13
	adds x28, x4, x28
	adcs x11, x20, x11
	umulh x3, x16, x10
	adcs x12, x12, x14
	mul x8, x16, x24
	adcs x8, x25, x8
	umulh x17, x16, x24
	adcs x17, x15, x17
	umulh x16, x16, x6
	adds x11, x11, x27
	lsl x1, x28, #32
	ldr x2, [x0, #5416]
	mul x23, x2, x7
	adcs x12, x12, x3
	adcs x8, x8, x16
	lsr x9, x28, #32
	adcs x17, x17, x13
	adds x11, x11, x1
	mul x5, x28, x21
	adcs x9, x12, x9
	umulh x28, x28, x21
	mul x4, x2, x10
	adcs x8, x8, x5
	umulh x20, x2, x7
	adcs x17, x17, x28
	mul x14, x2, x6
	adcs x25, x13, x13
	adds x23, x11, x23
	adcs x4, x9, x4
	umulh x15, x2, x10
	adcs x14, x8, x14
	mul x27, x2, x24
	adcs x27, x17, x27
	umulh x3, x2, x24
	adcs x3, x25, x3
	umulh x2, x2, x6
	adds x4, x4, x20
	lsl x16, x23, #32
	ldr x1, [x0, #5424]
	mul x12, x1, x7
	adcs x14, x14, x15
	adcs x27, x27, x2
	lsr x5, x23, #32
	umulh x7, x1, x7
	adcs x3, x3, x13
	adds x4, x4, x16
	mul x28, x23, x21
	adcs x14, x14, x5
	umulh x23, x23, x21
	mul x11, x1, x10
	adcs x27, x27, x28
	mul x9, x1, x6
	adcs x3, x3, x23
	umulh x10, x1, x10
	mul x8, x1, x24
	umulh x24, x1, x24
	umulh x6, x1, x6
	adcs x17, x13, x13
	adds x12, x4, x12
	adcs x11, x14, x11
	lsl x25, x12, #32
	lsr x20, x12, #32
	adcs x9, x27, x9
	mul x15, x12, x21
	adcs x3, x3, x8
	umulh x12, x12, x21
	adcs x24, x17, x24
	adds x11, x11, x7
	adcs x9, x9, x10
	adcs x3, x3, x6
	adcs x24, x24, x13
	adds x11, x11, x25
	adcs x9, x9, x20
	adcs x15, x3, x15
	adcs x24, x24, x12
	adcs x2, x13, x13
	adds x16, x11, x26
	sbcs x5, x9, x30
	sbcs x28, x15, x13
	sbcs x23, x24, x22
	sbcs x2, x2, x13
	csel x16, x16, x11, hs
	csel x9, x5, x9, hs
	csel x28, x28, x15, hs
	csel x23, x23, x24, hs
	ldr x1, [x0, #768]
	umulh x4, x16, x1
	mul x14, x16, x1
	ldr x27, [x0, #776]
	mul x8, x16, x27
	umulh x17, x16, x27
	ldr x7, [x0, #784]
	mul x10, x16, x7
	umulh x6, x16, x7
	ldr x25, [x0, #792]
	mul x20, x16, x25
	umulh x3, x16, x25
	mul x12, x9, x1
	str x16, [x0, #5400]
	mul x2, x9, x27
	adds x8, x8, x4
	umulh x11, x9, x1
	adcs x10, x10, x17
	mul x5, x9, x7
	adcs x6, x20, x6
	umulh x15, x9, x27
	str x9, [x0, #5408]
	str x28, [x0, #5416]
	str x23, [x0, #5424]
	adcs x3, x13, x3
	lsl x24, x14, #32
	adds x8, x8, x24
	lsr x16, x14, #32
	adcs x10, x10, x16
	mul x4, x14, x21
	adcs x6, x6, x4
	umulh x14, x14, x21
	adcs x14, x3, x14
	mul x17, x9, x25
	adcs x20, x13, x13
	adds x8, x8, x12
	adcs x10, x10, x2
	umulh x24, x9, x25
	adcs x6, x6, x5
	umulh x9, x9, x7
	mul x16, x28, x1
	adcs x17, x14, x17
	mul x4, x28, x27
	adcs x24, x20, x24
	lsl x3, x8, #32
	adds x10, x10, x11
	lsr x12, x8, #32
	adcs x6, x6, x15
	mul x2, x8, x21
	adcs x17, x17, x9
	umulh x8, x8, x21
	umulh x5, x28, x1
	adcs x24, x24, x13
	adds x10, x10, x3
	mul x14, x28, x7
	adcs x6, x6, x12
	umulh x20, x28, x27
	adcs x2, x17, x2
	mul x11, x28, x25
	adcs x24, x24, x8
	umulh x15, x28, x25
	umulh x28, x28, x7
	adcs x9, x13, x13
	adds x10, x10, x16
	adcs x6, x6, x4
	mul x3, x23, x1
	adcs x14, x2, x14
	lsl x12, x10, #32
	adcs x24, x24, x11
	lsr x17, x10, #32
	adcs x15, x9, x15
	adds x6, x6, x5
	mul x8, x10, x21
	umulh x10, x10, x21
	mul x16, x23, x27
	adcs x14, x14, x20
	umulh x1, x23, x1
	mul x4, x23, x7
	adcs x24, x24, x28
	umulh x27, x23, x27
	mul x2, x23, x25
	umulh x25, x23, x25
	umulh x23, x23, x7
	adcs x15, x15, x13
	adds x6, x6, x12
	adcs x17, x14, x17
	adcs x24, x24, x8
	adcs x15, x15, x10
	adcs x11, x13, x13
	adds x3, x6, x3
	adcs x16, x17, x16
	lsl x9, x3, #32
	lsr x5, x3, #32
	mul x20, x3, x21
	umulh x3, x3, x21
	adcs x4, x24, x4
	adcs x2, x15, x2
	adcs x25, x11, x25
	adds x16, x16, x1
	adcs x4, x4, x27
	adcs x2, x2, x23
	adcs x25, x25, x13
	adds x9, x16, x9
	adcs x4, x4, x5
	adcs x2, x2, x20
	adcs x25, x25, x3
	adcs x28, x13, x13
	adds x26, x9, x26
	sbcs x30, x4, x30
	sbcs x7, x2, x13
	sbcs x22, x25, x22
	sbcs x28, x28, x13
	csel x9, x26, x9, hs
	csel x4, x30, x4, hs
	csel x2, x7, x2, hs
	csel x25, x22, x25, hs
	str x9, [x0, #5432]
	str x4, [x0, #5440]
	str x2, [x0, #5448]
	str x25, [x0, #5456]
	sub x1, x19, #1
	movz x2, #96, lsl #0
	mul x1, x1, x2
	add x16, x0, #2848
	add x16, x16, x1
	ldr x1, [x0, #704]
	str x1, [x16, #0]
	ldr x1, [x0, #712]
	str x1, [x16, #8]
	ldr x1, [x0, #720]
	str x1, [x16, #16]
	ldr x1, [x0, #728]
	str x1, [x16, #24]
	ldr x1, [x0, #736]
	str x1, [x16, #32]
	ldr x1, [x0, #744]
	str x1, [x16, #40]
	ldr x1, [x0, #752]
	str x1, [x16, #48]
	ldr x1, [x0, #760]
	str x1, [x16, #56]
	ldr x1, [x0, #768]
	str x1, [x16, #64]
	ldr x1, [x0, #776]
	str x1, [x16, #72]
	ldr x1, [x0, #784]
	str x1, [x16, #80]
	ldr x1, [x0, #792]
	str x1, [x16, #88]
	sub x1, x19, #1
	lsl x1, x1, #6
	movz x2, #6000, lsl #0
	add x16, x0, x2
	add x16, x16, x1
	ldr x1, [x0, #5400]
	str x1, [x16, #0]
	ldr x1, [x0, #5408]
	str x1, [x16, #8]
	ldr x1, [x0, #5416]
	str x1, [x16, #16]
	ldr x1, [x0, #5424]
	str x1, [x16, #24]
	ldr x1, [x0, #5432]
	str x1, [x16, #32]
	ldr x1, [x0, #5440]
	str x1, [x16, #40]
	ldr x1, [x0, #5448]
	str x1, [x16, #48]
	ldr x1, [x0, #5456]
	str x1, [x16, #56]
	sub x4, x19, #8
	cbnz x4, 215b
	ldr x1, [x0, #608]
	str x1, [x0, #3616]
	ldr x1, [x0, #616]
	str x1, [x0, #3624]
	ldr x1, [x0, #624]
	str x1, [x0, #3632]
	ldr x1, [x0, #632]
	str x1, [x0, #3640]
	ldr x1, [x0, #640]
	str x1, [x0, #3648]
	ldr x1, [x0, #648]
	str x1, [x0, #3656]
	ldr x1, [x0, #656]
	str x1, [x0, #3664]
	ldr x1, [x0, #664]
	str x1, [x0, #3672]
	ldr x1, [x0, #768]
	str x1, [x0, #3680]
	ldr x1, [x0, #776]
	str x1, [x0, #3688]
	ldr x1, [x0, #784]
	str x1, [x0, #3696]
	ldr x1, [x0, #792]
	str x1, [x0, #3704]
	ldr x1, [x0, #768]
	str x1, [x0, #672]
	ldr x1, [x0, #776]
	str x1, [x0, #680]
	ldr x1, [x0, #784]
	str x1, [x0, #688]
	ldr x1, [x0, #792]
	str x1, [x0, #696]
	ldr x1, [x0, #704]
	str x1, [x0, #512]
	ldr x1, [x0, #712]
	str x1, [x0, #520]
	ldr x1, [x0, #720]
	str x1, [x0, #528]
	ldr x1, [x0, #728]
	str x1, [x0, #536]
	ldr x1, [x0, #736]
	str x1, [x0, #544]
	ldr x1, [x0, #744]
	str x1, [x0, #552]
	ldr x1, [x0, #752]
	str x1, [x0, #560]
	ldr x1, [x0, #760]
	str x1, [x0, #568]
	ldr x1, [x0, #768]
	str x1, [x0, #576]
	ldr x1, [x0, #776]
	str x1, [x0, #584]
	ldr x1, [x0, #784]
	str x1, [x0, #592]
	ldr x1, [x0, #792]
	str x1, [x0, #600]
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #544]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #552]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #560]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
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
	movz x19, #256, lsl #0
	bl {vg_p256_verify_cached_digit}
	add x16, x0, x19
	add x16, x16, x19
	ldrb w2, [x16, #2112]
	ldrb w3, [x16, #2113]
	cbnz x2, 216f
	b 217f
216:
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
	lsl x2, x2, #7
	adrp x16, {VG_P256_GTAB}
	add x16, x16, {VG_P256_GTAB}
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #704]
	ldr x4, [x16, #8]
	str x4, [x0, #712]
	ldr x4, [x16, #16]
	str x4, [x0, #720]
	ldr x4, [x16, #24]
	str x4, [x0, #728]
	ldr x4, [x16, #32]
	str x4, [x0, #736]
	ldr x4, [x16, #40]
	str x4, [x0, #744]
	ldr x4, [x16, #48]
	str x4, [x0, #752]
	ldr x4, [x16, #56]
	str x4, [x0, #760]
	ldr x1, [x0, #224]
	str x1, [x0, #768]
	ldr x1, [x0, #232]
	str x1, [x0, #776]
	ldr x1, [x0, #240]
	str x1, [x0, #784]
	ldr x1, [x0, #248]
	str x1, [x0, #792]
	add x16, x0, x19
	add x16, x16, x19
	ldrb w3, [x16, #2113]
	lsr x3, x3, #7
	cbnz x3, 218f
	b 219f
218:
	movz x7, #0, lsl #0
	ldr x8, [x0, #160]
	ldr x9, [x0, #168]
	ldr x10, [x0, #176]
	ldr x11, [x0, #184]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
219:
	bl {vg_p256_verify_mixed_add}
	ldr x1, [x0, #608]
	str x1, [x0, #512]
	ldr x1, [x0, #616]
	str x1, [x0, #520]
	ldr x1, [x0, #624]
	str x1, [x0, #528]
	ldr x1, [x0, #632]
	str x1, [x0, #536]
	ldr x1, [x0, #640]
	str x1, [x0, #544]
	ldr x1, [x0, #648]
	str x1, [x0, #552]
	ldr x1, [x0, #656]
	str x1, [x0, #560]
	ldr x1, [x0, #664]
	str x1, [x0, #568]
	ldr x1, [x0, #672]
	str x1, [x0, #576]
	ldr x1, [x0, #680]
	str x1, [x0, #584]
	ldr x1, [x0, #688]
	str x1, [x0, #592]
	ldr x1, [x0, #696]
	str x1, [x0, #600]
217:
220:
	sub x19, x19, #1
	ldr x1, [x0, #576]
	umulh x2, x1, x1
	ldr x3, [x0, #584]
	mul x4, x1, x3
	mul x5, x1, x1
	umulh x6, x1, x3
	ldr x7, [x0, #592]
	mul x8, x1, x7
	umulh x9, x1, x7
	mul x10, x3, x3
	ldr x11, [x0, #600]
	mul x12, x1, x11
	umulh x13, x3, x3
	mul x14, x3, x7
	lsl x15, x5, #32
	mul x16, x3, x11
	umulh x17, x1, x11
	umulh x20, x3, x11
	umulh x21, x3, x7
	adds x8, x6, x8
	mul x22, x7, x11
	umulh x23, x7, x11
	sub x24, x5, x15
	adcs x12, x12, x9
	mul x25, x7, x7
	umulh x26, x7, x7
	umulh x27, x11, x11
	mul x28, x11, x11
	adcs x16, x17, x16
	movz x30, #1, lsl #0
	orr x6, x30, x30
	movk x6, #0, lsl #16
	adcs x22, x22, x20
	movk x6, #65535, lsl #32
	movz x9, #0, lsl #0
	adc x23, x23, x9
	adds x14, x12, x14
	adcs x21, x16, x21
	movk x6, #65535, lsl #48
	adcs x22, x22, x9
	adc x23, x23, x9
	adds x4, x4, x4
	adcs x8, x8, x8
	adcs x14, x14, x14
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adc x17, x9, x9
	adds x2, x4, x2
	extr x20, x2, x5, #32
	adcs x8, x8, x10
	adcs x13, x14, x13
	adcs x21, x21, x25
	adcs x22, x22, x26
	adcs x23, x23, x28
	adc x27, x17, x27
	adds x2, x2, x15
	adcs x8, x8, x20
	extr x12, x8, x2, #32
	adcs x13, x13, x12
	add x16, x13, x24
	extr x4, x16, x8, #32
	lsr x10, x16, #32
	adcs x21, x21, x4
	adcs x22, x22, x10
	adcs x23, x23, x9
	adc x27, x27, x9
	subs x15, x5, x15
	sbcs x20, x5, x20
	sbcs x12, x2, x12
	sbcs x4, x8, x4
	sbc x10, x16, x10
	ldr x14, [x0, #544]
	adds x14, x14, x14
	ldr x25, [x0, #552]
	adcs x25, x25, x25
	ldr x26, [x0, #560]
	adcs x26, x26, x26
	ldr x28, [x0, #568]
	adcs x28, x28, x28
	adc x17, x9, x9
	adds x15, x14, x30
	ldr x5, [x0, #72]
	sbcs x11, x25, x5
	sbcs x7, x26, x9
	ldr x1, [x0, #88]
	sbcs x3, x28, x1
	sbcs x17, x17, x9
	csel x25, x11, x25, hs
	csel x14, x15, x14, hs
	csel x26, x7, x26, hs
	csel x3, x3, x28, hs
	adds x13, x13, x24
	adcs x20, x20, x2
	adcs x8, x12, x8
	adcs x16, x4, x16
	adc x10, x10, x9
	adds x20, x21, x20
	adcs x8, x22, x8
	adcs x16, x23, x16
	adcs x10, x27, x10
	adc x17, x9, x9
	adds x11, x20, x30
	sbcs x15, x8, x5
	sbcs x7, x16, x9
	sbcs x28, x10, x1
	sbcs x17, x17, x9
	csel x11, x11, x20, hs
	csel x8, x15, x8, hs
	csel x28, x28, x10, hs
	csel x16, x7, x16, hs
	mul x24, x14, x25
	mul x13, x14, x26
	umulh x2, x14, x25
	umulh x12, x14, x26
	mul x4, x14, x3
	mul x21, x25, x26
	umulh x22, x14, x3
	mul x23, x25, x3
	umulh x27, x25, x3
	adds x13, x2, x13
	umulh x17, x26, x3
	adcs x4, x4, x12
	umulh x20, x25, x26
	adcs x23, x22, x23
	mul x15, x26, x3
	adcs x15, x15, x27
	adc x17, x17, x9
	adds x21, x4, x21
	adcs x20, x23, x20
	adcs x15, x15, x9
	adc x17, x17, x9
	adds x24, x24, x24
	adcs x13, x13, x13
	adcs x21, x21, x21
	adcs x20, x20, x20
	adcs x15, x15, x15
	adcs x17, x17, x17
	adc x10, x9, x9
	ldr x7, [x0, #512]
	adds x2, x7, x11
	ldr x12, [x0, #520]
	adcs x22, x12, x8
	ldr x27, [x0, #528]
	adcs x4, x27, x16
	ldr x23, [x0, #536]
	str x10, [x0, #7104]
	adcs x10, x23, x28
	str x17, [x0, #7112]
	adc x17, x9, x9
	subs x11, x7, x11
	sbcs x8, x12, x8
	sbcs x16, x27, x16
	sbcs x28, x23, x28
	sbc x23, x9, x9
	adds x11, x11, x23
	lsr x27, x23, #32
	adcs x27, x8, x27
	adcs x16, x16, x9
	lsl x8, x23, #32
	sub x8, x8, x23
	adc x8, x28, x8
	adds x23, x2, x30
	sbcs x28, x22, x5
	sbcs x12, x4, x9
	sbcs x7, x10, x1
	sbcs x17, x17, x9
	csel x22, x28, x22, hs
	csel x2, x23, x2, hs
	csel x4, x12, x4, hs
	csel x10, x7, x10, hs
	mul x17, x11, x2
	mul x28, x11, x22
	mul x23, x11, x4
	mul x12, x11, x10
	umulh x7, x11, x2
	adds x28, x28, x7
	umulh x7, x11, x22
	adcs x23, x23, x7
	umulh x7, x11, x4
	adcs x12, x12, x7
	umulh x11, x11, x10
	adcs x11, x9, x11
	lsl x7, x17, #32
	adds x28, x28, x7
	lsr x7, x17, #32
	adcs x23, x23, x7
	mul x7, x17, x6
	adcs x12, x12, x7
	umulh x17, x17, x6
	adcs x11, x11, x17
	adcs x7, x9, x9
	mul x17, x27, x2
	adds x17, x28, x17
	mul x28, x27, x22
	adcs x28, x23, x28
	mul x23, x27, x4
	adcs x23, x12, x23
	mul x12, x27, x10
	adcs x11, x11, x12
	umulh x12, x27, x10
	adcs x12, x7, x12
	umulh x7, x27, x2
	adds x28, x28, x7
	umulh x7, x27, x22
	adcs x23, x23, x7
	umulh x27, x27, x4
	adcs x27, x11, x27
	adcs x12, x12, x9
	lsl x7, x17, #32
	adds x28, x28, x7
	lsr x11, x17, #32
	adcs x23, x23, x11
	mul x7, x17, x6
	adcs x7, x27, x7
	umulh x17, x17, x6
	adcs x12, x12, x17
	adcs x11, x9, x9
	mul x27, x16, x2
	adds x27, x28, x27
	mul x17, x16, x22
	adcs x17, x23, x17
	mul x28, x16, x4
	adcs x7, x7, x28
	mul x23, x16, x10
	adcs x23, x12, x23
	umulh x28, x16, x10
	adcs x28, x11, x28
	umulh x12, x16, x2
	adds x17, x17, x12
	umulh x11, x16, x22
	adcs x11, x7, x11
	umulh x16, x16, x4
	adcs x23, x23, x16
	adcs x28, x28, x9
	lsl x12, x27, #32
	adds x17, x17, x12
	lsr x7, x27, #32
	adcs x7, x11, x7
	mul x16, x27, x6
	adcs x23, x23, x16
	umulh x27, x27, x6
	adcs x28, x28, x27
	adcs x12, x9, x9
	mul x11, x8, x2
	adds x17, x17, x11
	umulh x2, x8, x2
	mul x16, x8, x22
	adcs x7, x7, x16
	umulh x22, x8, x22
	mul x27, x8, x4
	adcs x27, x23, x27
	umulh x4, x8, x4
	mul x11, x8, x10
	umulh x8, x8, x10
	adcs x11, x28, x11
	adcs x8, x12, x8
	adds x2, x7, x2
	adcs x27, x27, x22
	adcs x11, x11, x4
	adcs x8, x8, x9
	lsl x16, x17, #32
	adds x16, x2, x16
	lsr x23, x17, #32
	adcs x27, x27, x23
	mul x10, x17, x6
	adcs x11, x11, x10
	umulh x17, x17, x6
	adcs x8, x8, x17
	adcs x28, x9, x9
	adds x12, x16, x30
	sbcs x7, x27, x5
	sbcs x22, x11, x9
	sbcs x4, x8, x1
	sbcs x28, x28, x9
	csel x27, x7, x27, hs
	csel x11, x22, x11, hs
	csel x12, x12, x16, hs
	csel x8, x4, x8, hs
	lsl x2, x12, #1
	adds x2, x12, x2
	extr x12, x27, x12, #63
	adcs x12, x27, x12
	extr x27, x11, x27, #63
	adcs x27, x11, x27
	extr x11, x8, x11, #63
	adcs x11, x8, x11
	lsr x8, x8, #63
	adc x8, x8, x9
	add x8, x8, x30
	sub x23, x9, x8
	subs x2, x2, x23
	lsl x10, x8, #32
	sub x8, x8, x10
	sub x10, x10, x30
	sbcs x10, x12, x10
	sbcs x27, x27, x9
	sbcs x8, x11, x8
	sbc x17, x9, x9
	adds x2, x2, x17
	lsr x28, x17, #32
	adcs x28, x10, x28
	adcs x27, x27, x9
	lsl x7, x17, #32
	sub x7, x7, x17
	adcs x7, x8, x7
	mul x22, x14, x14
	umulh x16, x14, x14
	adds x16, x24, x16
	mul x4, x25, x25
	adcs x4, x13, x4
	umulh x23, x25, x25
	adcs x23, x21, x23
	mul x12, x26, x26
	adcs x20, x20, x12
	umulh x11, x26, x26
	adcs x11, x15, x11
	mul x10, x3, x3
	ldr x17, [x0, #7112]
	adcs x17, x17, x10
	umulh x8, x3, x3
	ldr x24, [x0, #7104]
	adc x24, x24, x8
	lsl x13, x22, #32
	sub x21, x22, x13
	extr x12, x16, x22, #32
	adds x16, x16, x13
	adcs x4, x4, x12
	extr x15, x4, x16, #32
	adcs x23, x23, x15
	add x10, x23, x21
	extr x8, x10, x4, #32
	adcs x20, x20, x8
	str x7, [x0, #7104]
	lsr x7, x10, #32
	adcs x11, x11, x7
	adcs x17, x17, x9
	adc x24, x24, x9
	subs x13, x22, x13
	sbcs x22, x22, x12
	sbcs x15, x16, x15
	sbcs x8, x4, x8
	sbc x7, x10, x7
	adds x21, x23, x21
	adcs x22, x22, x16
	adcs x15, x15, x4
	adcs x8, x8, x10
	adc x7, x7, x9
	adds x22, x20, x22
	adcs x15, x11, x15
	adcs x8, x17, x8
	adcs x7, x24, x7
	ldr x13, [x0, #584]
	umulh x12, x14, x13
	adc x23, x9, x9
	adds x21, x22, x30
	sbcs x16, x15, x5
	sbcs x4, x8, x9
	sbcs x10, x7, x1
	sbcs x23, x23, x9
	csel x22, x21, x22, hs
	csel x15, x16, x15, hs
	csel x4, x4, x8, hs
	csel x10, x10, x7, hs
	ldr x20, [x0, #512]
	mul x11, x20, x22
	mul x17, x20, x15
	mul x24, x20, x4
	mul x23, x20, x10
	umulh x21, x20, x22
	adds x17, x17, x21
	umulh x16, x20, x15
	adcs x24, x24, x16
	umulh x8, x20, x4
	adcs x23, x23, x8
	umulh x20, x20, x10
	adcs x20, x9, x20
	lsl x7, x11, #32
	adds x17, x17, x7
	lsr x21, x11, #32
	adcs x24, x24, x21
	mul x16, x11, x6
	adcs x23, x23, x16
	umulh x11, x11, x6
	adcs x20, x20, x11
	adcs x8, x9, x9
	ldr x7, [x0, #520]
	mul x21, x7, x22
	adds x21, x17, x21
	mul x16, x7, x15
	adcs x24, x24, x16
	mul x11, x7, x4
	adcs x23, x23, x11
	mul x17, x7, x10
	adcs x20, x20, x17
	umulh x16, x7, x10
	adcs x16, x8, x16
	umulh x11, x7, x22
	adds x24, x24, x11
	umulh x17, x7, x15
	adcs x23, x23, x17
	umulh x7, x7, x4
	adcs x7, x20, x7
	adcs x16, x16, x9
	lsl x8, x21, #32
	adds x24, x24, x8
	lsr x11, x21, #32
	adcs x23, x23, x11
	mul x17, x21, x6
	adcs x17, x7, x17
	umulh x21, x21, x6
	adcs x16, x16, x21
	adcs x20, x9, x9
	ldr x8, [x0, #528]
	mul x11, x8, x22
	adds x11, x24, x11
	mul x7, x8, x15
	adcs x7, x23, x7
	mul x21, x8, x4
	adcs x17, x17, x21
	mul x24, x8, x10
	adcs x24, x16, x24
	umulh x23, x8, x10
	adcs x23, x20, x23
	umulh x21, x8, x22
	adds x7, x7, x21
	umulh x16, x8, x15
	adcs x16, x17, x16
	umulh x8, x8, x4
	adcs x24, x24, x8
	adcs x23, x23, x9
	lsl x20, x11, #32
	adds x7, x7, x20
	lsr x21, x11, #32
	adcs x21, x16, x21
	mul x17, x11, x6
	adcs x24, x24, x17
	umulh x11, x11, x6
	adcs x23, x23, x11
	adcs x8, x9, x9
	ldr x20, [x0, #536]
	mul x16, x20, x22
	adds x16, x7, x16
	mul x17, x20, x15
	adcs x21, x21, x17
	mul x11, x20, x4
	adcs x11, x24, x11
	mul x7, x20, x10
	adcs x7, x23, x7
	umulh x17, x20, x10
	adcs x17, x8, x17
	umulh x24, x20, x22
	adds x24, x21, x24
	umulh x23, x20, x15
	adcs x11, x11, x23
	umulh x20, x20, x4
	adcs x7, x7, x20
	adcs x17, x17, x9
	lsl x8, x16, #32
	adds x8, x24, x8
	lsr x21, x16, #32
	adcs x11, x11, x21
	mul x23, x16, x6
	adcs x7, x7, x23
	umulh x16, x16, x6
	adcs x17, x17, x16
	adcs x20, x9, x9
	adds x24, x8, x30
	sbcs x21, x11, x5
	sbcs x23, x7, x9
	sbcs x16, x17, x1
	sbcs x20, x20, x9
	csel x24, x24, x8, hs
	csel x11, x21, x11, hs
	csel x7, x23, x7, hs
	csel x17, x16, x17, hs
	ldr x20, [x0, #576]
	mul x8, x14, x20
	mul x21, x14, x13
	ldr x23, [x0, #592]
	mul x16, x14, x23
	ldr x1, [x0, #600]
	mul x5, x14, x1
	umulh x30, x14, x20
	adds x30, x21, x30
	adcs x12, x16, x12
	umulh x21, x14, x23
	adcs x5, x5, x21
	umulh x14, x14, x1
	adcs x14, x9, x14
	lsl x16, x8, #32
	adds x30, x30, x16
	lsr x21, x8, #32
	adcs x12, x12, x21
	mul x16, x8, x6
	adcs x5, x5, x16
	umulh x8, x8, x6
	adcs x14, x14, x8
	adcs x21, x9, x9
	mul x16, x25, x20
	adds x30, x30, x16
	mul x8, x25, x13
	adcs x12, x12, x8
	mul x16, x25, x23
	adcs x16, x5, x16
	mul x8, x25, x1
	adcs x8, x14, x8
	umulh x5, x25, x1
	adcs x5, x21, x5
	umulh x14, x25, x20
	adds x14, x12, x14
	umulh x21, x25, x13
	adcs x16, x16, x21
	umulh x25, x25, x23
	adcs x8, x8, x25
	adcs x5, x5, x9
	lsl x12, x30, #32
	adds x12, x14, x12
	lsr x21, x30, #32
	adcs x16, x16, x21
	mul x25, x30, x6
	adcs x8, x8, x25
	umulh x30, x30, x6
	adcs x5, x5, x30
	adcs x14, x9, x9
	mul x21, x26, x20
	adds x12, x12, x21
	mul x25, x26, x13
	adcs x25, x16, x25
	mul x30, x26, x23
	adcs x8, x8, x30
	mul x21, x26, x1
	adcs x5, x5, x21
	umulh x16, x26, x1
	adcs x16, x14, x16
	umulh x30, x26, x20
	adds x25, x25, x30
	umulh x21, x26, x13
	adcs x8, x8, x21
	umulh x26, x26, x23
	adcs x5, x5, x26
	adcs x16, x16, x9
	lsl x14, x12, #32
	adds x25, x25, x14
	lsr x30, x12, #32
	adcs x8, x8, x30
	mul x21, x12, x6
	adcs x5, x5, x21
	umulh x12, x12, x6
	adcs x16, x16, x12
	adcs x26, x9, x9
	mul x14, x3, x20
	adds x14, x25, x14
	umulh x20, x3, x20
	mul x30, x3, x13
	adcs x8, x8, x30
	umulh x13, x3, x13
	mul x21, x3, x23
	adcs x5, x5, x21
	umulh x23, x3, x23
	mul x12, x3, x1
	umulh x1, x3, x1
	adcs x16, x16, x12
	adcs x1, x26, x1
	mul x25, x2, x28
	adds x8, x8, x20
	umulh x30, x2, x2
	adcs x5, x5, x13
	mul x21, x2, x2
	adcs x23, x16, x23
	umulh x3, x2, x28
	adcs x1, x1, x9
	lsl x12, x14, #32
	adds x8, x8, x12
	lsr x26, x14, #32
	adcs x5, x5, x26
	mul x20, x14, x6
	adcs x20, x23, x20
	umulh x14, x14, x6
	adcs x1, x1, x14
	mul x13, x2, x27
	adcs x16, x9, x9
	adds x13, x3, x13
	umulh x12, x2, x27
	ldr x26, [x0, #7104]
	mul x23, x2, x26
	adcs x12, x23, x12
	umulh x14, x2, x26
	mul x3, x28, x27
	umulh x23, x28, x27
	str x6, [x0, #7112]
	mul x6, x28, x26
	adcs x6, x14, x6
	umulh x14, x28, x26
	str x2, [x0, #7120]
	mul x2, x27, x26
	adcs x2, x2, x14
	umulh x14, x27, x26
	adc x14, x14, x9
	adds x3, x12, x3
	adcs x23, x6, x23
	adcs x2, x2, x9
	adc x14, x14, x9
	adds x25, x25, x25
	adcs x13, x13, x13
	adcs x3, x3, x3
	adcs x23, x23, x23
	adcs x2, x2, x2
	adcs x14, x14, x14
	adc x12, x9, x9
	adds x25, x25, x30
	mul x6, x28, x28
	adcs x6, x13, x6
	umulh x30, x28, x28
	adcs x3, x3, x30
	mul x13, x27, x27
	adcs x13, x23, x13
	umulh x30, x27, x27
	adcs x2, x2, x30
	mul x23, x26, x26
	adcs x14, x14, x23
	umulh x30, x26, x26
	adc x12, x12, x30
	movz x23, #1, lsl #0
	adds x30, x8, x23
	ldr x26, [x0, #72]
	str x27, [x0, #7128]
	sbcs x27, x5, x26
	str x28, [x0, #7136]
	sbcs x28, x20, x9
	ldr x26, [x0, #88]
	sbcs x23, x1, x26
	sbcs x16, x16, x9
	csel x23, x23, x1, hs
	csel x5, x27, x5, hs
	csel x20, x28, x20, hs
	csel x30, x30, x8, hs
	str x5, [x0, #584]
	str x30, [x0, #576]
	str x23, [x0, #600]
	str x20, [x0, #592]
	extr x16, x25, x21, #32
	lsl x1, x21, #32
	adds x25, x25, x1
	adcs x6, x6, x16
	sub x27, x21, x1
	extr x28, x6, x25, #32
	adcs x3, x3, x28
	add x8, x3, x27
	extr x5, x8, x6, #32
	adcs x13, x13, x5
	lsr x30, x8, #32
	adcs x2, x2, x30
	adcs x14, x14, x9
	adc x12, x12, x9
	subs x1, x21, x1
	sbcs x16, x21, x16
	sbcs x28, x25, x28
	sbcs x5, x6, x5
	sbc x30, x8, x30
	adds x3, x3, x27
	adcs x16, x16, x25
	adcs x28, x28, x6
	adcs x8, x5, x8
	mul x23, x22, x15
	adc x30, x30, x9
	adds x16, x13, x16
	umulh x20, x22, x15
	adcs x28, x2, x28
	mul x1, x22, x4
	adcs x8, x14, x8
	umulh x21, x22, x4
	adcs x30, x12, x30
	mul x27, x22, x10
	adc x3, x9, x9
	adds x1, x20, x1
	adcs x27, x27, x21
	mul x25, x15, x4
	umulh x6, x22, x10
	umulh x5, x15, x4
	mul x13, x15, x10
	adcs x13, x6, x13
	umulh x2, x15, x10
	mul x14, x4, x10
	adcs x14, x14, x2
	umulh x12, x4, x10
	adc x12, x12, x9
	adds x25, x27, x25
	adcs x5, x13, x5
	adcs x14, x14, x9
	adc x12, x12, x9
	adds x23, x23, x23
	adcs x1, x1, x1
	adcs x25, x25, x25
	adcs x5, x5, x5
	adcs x14, x14, x14
	adcs x12, x12, x12
	adc x20, x9, x9
	movz x21, #1, lsl #0
	adds x6, x16, x21
	ldr x2, [x0, #72]
	sbcs x27, x28, x2
	sbcs x13, x8, x9
	sbcs x2, x30, x26
	sbcs x3, x3, x9
	csel x27, x27, x28, hs
	csel x16, x6, x16, hs
	csel x13, x13, x8, hs
	csel x2, x2, x30, hs
	subs x16, x16, x24
	sbcs x27, x27, x11
	sbcs x13, x13, x7
	sbcs x2, x2, x17
	sbc x3, x9, x9
	adds x16, x16, x3
	lsr x28, x3, #32
	adcs x27, x27, x28
	adcs x13, x13, x9
	lsl x6, x3, #32
	sub x6, x6, x3
	adc x6, x2, x6
	subs x16, x16, x24
	sbcs x27, x27, x11
	sbcs x13, x13, x7
	sbcs x6, x6, x17
	sbc x8, x9, x9
	adds x16, x16, x8
	str x16, [x0, #512]
	lsr x30, x8, #32
	adcs x30, x27, x30
	adcs x13, x13, x9
	str x30, [x0, #520]
	str x13, [x0, #528]
	lsl x28, x8, #32
	sub x28, x28, x8
	adc x6, x6, x28
	subs x24, x24, x16
	sbcs x11, x11, x30
	sbcs x7, x7, x13
	umulh x3, x22, x22
	mul x22, x22, x22
	sbcs x17, x17, x6
	str x6, [x0, #536]
	mul x2, x15, x15
	umulh x15, x15, x15
	sbc x27, x9, x9
	adds x3, x23, x3
	adcs x1, x1, x2
	lsl x8, x22, #32
	adcs x15, x25, x15
	umulh x28, x4, x4
	mul x4, x4, x4
	adcs x5, x5, x4
	sub x16, x22, x8
	adcs x14, x14, x28
	extr x30, x3, x22, #32
	lsr x13, x27, #32
	lsl x6, x27, #32
	sub x6, x6, x27
	mul x23, x10, x10
	adcs x12, x12, x23
	umulh x10, x10, x10
	adc x10, x20, x10
	adds x24, x24, x27
	adcs x11, x11, x13
	ldr x2, [x0, #7120]
	umulh x25, x2, x24
	adcs x7, x7, x9
	adc x6, x17, x6
	adds x3, x3, x8
	adcs x1, x1, x30
	extr x4, x1, x3, #32
	adcs x15, x15, x4
	mul x28, x2, x24
	mul x23, x2, x11
	mul x20, x2, x7
	mul x27, x2, x6
	umulh x13, x2, x11
	umulh x17, x2, x7
	umulh x2, x2, x6
	lsl x26, x28, #32
	lsr x21, x28, #32
	ldr x9, [x0, #7112]
	str x21, [x0, #7120]
	mul x21, x28, x9
	umulh x28, x28, x9
	ldr x9, [x0, #7136]
	str x28, [x0, #7144]
	mul x28, x9, x24
	str x28, [x0, #7152]
	mul x28, x9, x11
	str x28, [x0, #7160]
	mul x28, x9, x7
	str x28, [x0, #7168]
	mul x28, x9, x6
	str x28, [x0, #7176]
	umulh x28, x9, x6
	str x28, [x0, #7184]
	umulh x28, x9, x24
	str x28, [x0, #7192]
	umulh x28, x9, x11
	umulh x9, x9, x7
	str x9, [x0, #7136]
	ldr x9, [x0, #7128]
	str x28, [x0, #7200]
	mul x28, x9, x24
	str x28, [x0, #7208]
	mul x28, x9, x11
	str x28, [x0, #7216]
	mul x28, x9, x7
	str x28, [x0, #7224]
	mul x28, x9, x6
	str x28, [x0, #7232]
	umulh x28, x9, x6
	str x28, [x0, #7240]
	umulh x28, x9, x24
	str x28, [x0, #7248]
	umulh x28, x9, x11
	umulh x9, x9, x7
	str x9, [x0, #7128]
	ldr x9, [x0, #7104]
	str x28, [x0, #7256]
	mul x28, x9, x24
	umulh x24, x9, x24
	str x24, [x0, #7264]
	mul x24, x9, x11
	umulh x11, x9, x11
	str x11, [x0, #7272]
	mul x11, x9, x7
	umulh x7, x9, x7
	str x7, [x0, #7280]
	mul x7, x9, x6
	umulh x9, x9, x6
	add x6, x15, x16
	str x9, [x0, #7104]
	extr x9, x6, x1, #32
	adcs x5, x5, x9
	str x7, [x0, #7288]
	lsr x7, x6, #32
	adcs x14, x14, x7
	str x11, [x0, #7296]
	movz x11, #0, lsl #0
	adcs x12, x12, x11
	adc x10, x10, x11
	adds x25, x23, x25
	adcs x13, x20, x13
	adcs x27, x27, x17
	adcs x2, x11, x2
	subs x8, x22, x8
	sbcs x30, x22, x30
	sbcs x4, x3, x4
	sbcs x9, x1, x9
	sbc x7, x6, x7
	adds x15, x15, x16
	adcs x30, x30, x3
	adcs x1, x4, x1
	adcs x6, x9, x6
	adc x7, x7, x11
	adds x25, x25, x26
	ldr x23, [x0, #7120]
	adcs x23, x13, x23
	adcs x27, x27, x21
	ldr x20, [x0, #7144]
	adcs x2, x2, x20
	adcs x17, x11, x11
	ldr x8, [x0, #7152]
	adds x25, x25, x8
	ldr x22, [x0, #7160]
	adcs x22, x23, x22
	ldr x16, [x0, #7168]
	adcs x27, x27, x16
	ldr x15, [x0, #7176]
	adcs x2, x2, x15
	ldr x3, [x0, #7184]
	adcs x3, x17, x3
	adds x30, x5, x30
	adcs x1, x14, x1
	adcs x6, x12, x6
	adcs x7, x10, x7
	lsl x4, x25, #32
	lsr x9, x25, #32
	ldr x26, [x0, #7112]
	mul x13, x25, x26
	umulh x25, x25, x26
	adc x21, x11, x11
	ldr x20, [x0, #7192]
	adds x22, x22, x20
	ldr x8, [x0, #7200]
	adcs x27, x27, x8
	ldr x23, [x0, #7136]
	adcs x2, x2, x23
	adcs x3, x3, x11
	adds x4, x22, x4
	adcs x27, x27, x9
	adcs x2, x2, x13
	adcs x3, x3, x25
	adcs x16, x11, x11
	ldr x15, [x0, #7208]
	adds x15, x4, x15
	ldr x17, [x0, #7216]
	adcs x17, x27, x17
	ldr x5, [x0, #7224]
	adcs x5, x2, x5
	ldr x14, [x0, #7232]
	adcs x14, x3, x14
	ldr x12, [x0, #7240]
	adcs x16, x16, x12
	ldr x10, [x0, #7248]
	adds x17, x17, x10
	lsl x20, x15, #32
	ldr x8, [x0, #7256]
	adcs x5, x5, x8
	lsr x23, x15, #32
	ldr x22, [x0, #7128]
	adcs x14, x14, x22
	umulh x9, x15, x26
	mul x15, x15, x26
	adcs x16, x16, x11
	adds x17, x17, x20
	adcs x5, x5, x23
	adcs x14, x14, x15
	adcs x9, x16, x9
	adcs x13, x11, x11
	movz x25, #1, lsl #0
	adds x4, x30, x25
	ldr x27, [x0, #72]
	sbcs x2, x1, x27
	sbcs x3, x6, x11
	ldr x12, [x0, #88]
	sbcs x10, x7, x12
	sbcs x21, x21, x11
	csel x4, x4, x30, hs
	csel x2, x2, x1, hs
	csel x3, x3, x6, hs
	csel x7, x10, x7, hs
	adds x28, x17, x28
	adcs x24, x5, x24
	lsl x8, x28, #32
	mul x22, x28, x26
	umulh x26, x28, x26
	lsr x28, x28, #32
	ldr x20, [x0, #7296]
	adcs x20, x14, x20
	ldr x23, [x0, #7288]
	adcs x23, x9, x23
	lsl x15, x4, #63
	ldr x16, [x0, #7104]
	adcs x16, x13, x16
	ldr x21, [x0, #7264]
	adds x24, x24, x21
	ldr x30, [x0, #7272]
	adcs x20, x20, x30
	ldr x1, [x0, #7280]
	adcs x23, x23, x1
	lsr x15, x15, #63
	adcs x16, x16, x11
	adds x24, x24, x8
	adcs x20, x20, x28
	sub x15, x11, x15
	adcs x22, x23, x22
	adcs x16, x16, x26
	lsr x6, x15, #32
	lsl x10, x15, #32
	sub x10, x10, x15
	adcs x17, x11, x11
	adds x25, x24, x25
	sbcs x27, x20, x27
	sbcs x5, x22, x11
	sbcs x12, x16, x12
	sbcs x17, x17, x11
	csel x24, x25, x24, hs
	csel x20, x27, x20, hs
	csel x5, x5, x22, hs
	csel x12, x12, x16, hs
	adds x4, x4, x15
	adcs x2, x2, x6
	adcs x3, x3, x11
	extr x4, x2, x4, #1
	extr x2, x3, x2, #1
	adcs x7, x7, x10
	adc x14, x11, x11
	extr x3, x7, x3, #1
	extr x7, x14, x7, #1
	subs x4, x24, x4
	sbcs x2, x20, x2
	sbcs x5, x5, x3
	sbcs x12, x12, x7
	sbc x9, x11, x11
	lsr x13, x9, #32
	adds x4, x4, x9
	lsl x21, x9, #32
	sub x21, x21, x9
	adcs x2, x2, x13
	str x4, [x0, #544]
	adcs x5, x5, x11
	str x2, [x0, #552]
	adc x21, x12, x21
	str x5, [x0, #560]
	str x21, [x0, #568]
	bl {vg_p256_verify_cached_digit}
	add x16, x0, x19
	add x16, x16, x19
	ldrb w2, [x16, #2112]
	ldrb w3, [x16, #2113]
	cbnz x2, 221f
	b 222f
221:
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
	lsl x2, x2, #7
	adrp x16, {VG_P256_GTAB}
	add x16, x16, {VG_P256_GTAB}
	add x16, x16, x2
	ldr x4, [x16, #0]
	str x4, [x0, #704]
	ldr x4, [x16, #8]
	str x4, [x0, #712]
	ldr x4, [x16, #16]
	str x4, [x0, #720]
	ldr x4, [x16, #24]
	str x4, [x0, #728]
	ldr x4, [x16, #32]
	str x4, [x0, #736]
	ldr x4, [x16, #40]
	str x4, [x0, #744]
	ldr x4, [x16, #48]
	str x4, [x0, #752]
	ldr x4, [x16, #56]
	str x4, [x0, #760]
	ldr x1, [x0, #224]
	str x1, [x0, #768]
	ldr x1, [x0, #232]
	str x1, [x0, #776]
	ldr x1, [x0, #240]
	str x1, [x0, #784]
	ldr x1, [x0, #248]
	str x1, [x0, #792]
	add x16, x0, x19
	add x16, x16, x19
	ldrb w3, [x16, #2113]
	lsr x3, x3, #7
	cbnz x3, 223f
	b 224f
223:
	movz x7, #0, lsl #0
	ldr x8, [x0, #160]
	ldr x9, [x0, #168]
	ldr x10, [x0, #176]
	ldr x11, [x0, #184]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
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
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
224:
	bl {vg_p256_verify_mixed_add}
	ldr x1, [x0, #608]
	str x1, [x0, #512]
	ldr x1, [x0, #616]
	str x1, [x0, #520]
	ldr x1, [x0, #624]
	str x1, [x0, #528]
	ldr x1, [x0, #632]
	str x1, [x0, #536]
	ldr x1, [x0, #640]
	str x1, [x0, #544]
	ldr x1, [x0, #648]
	str x1, [x0, #552]
	ldr x1, [x0, #656]
	str x1, [x0, #560]
	ldr x1, [x0, #664]
	str x1, [x0, #568]
	ldr x1, [x0, #672]
	str x1, [x0, #576]
	ldr x1, [x0, #680]
	str x1, [x0, #584]
	ldr x1, [x0, #688]
	str x1, [x0, #592]
	ldr x1, [x0, #696]
	str x1, [x0, #600]
222:
	cbnz x19, 220b
	movz x7, #0, lsl #0
	ldr x4, [x0, #576]
	ldr x5, [x0, #584]
	ldr x16, [x0, #592]
	ldr x17, [x0, #600]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #704]
	str x13, [x0, #712]
	str x8, [x0, #720]
	str x9, [x0, #728]
	movz x7, #0, lsl #0
	ldr x3, [x0, #576]
	ldr x4, [x0, #584]
	ldr x5, [x0, #592]
	ldr x6, [x0, #600]
	mul x8, x3, x4
	umulh x9, x3, x4
	mul x1, x3, x5
	umulh x2, x3, x5
	mul x10, x3, x6
	umulh x11, x3, x6
	mul x16, x4, x5
	umulh x17, x4, x5
	mul x14, x4, x6
	umulh x15, x4, x6
	mul x12, x5, x6
	umulh x13, x5, x6
	adds x9, x9, x1
	adcs x10, x10, x2
	adcs x11, x11, x14
	adcs x12, x12, x15
	adc x13, x13, x7
	adds x10, x10, x16
	adcs x11, x11, x17
	adcs x12, x12, x7
	adc x13, x13, x7
	adds x8, x8, x8
	adcs x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adc x14, x7, x7
	mul x15, x3, x3
	umulh x1, x3, x3
	mul x2, x4, x4
	umulh x16, x4, x4
	mul x17, x5, x5
	umulh x3, x5, x5
	mul x4, x6, x6
	umulh x6, x6, x6
	adds x8, x8, x1
	adcs x9, x9, x2
	adcs x10, x10, x16
	adcs x11, x11, x17
	adcs x12, x12, x3
	adcs x13, x13, x4
	adc x14, x14, x6
	lsl x1, x15, #32
	sub x4, x15, x1
	extr x2, x8, x15, #32
	adds x8, x8, x1
	adcs x9, x9, x2
	extr x3, x9, x8, #32
	adcs x10, x10, x3
	add x5, x10, x4
	extr x6, x5, x9, #32
	lsr x16, x5, #32
	adcs x11, x11, x6
	adcs x12, x12, x16
	adcs x13, x13, x7
	adc x14, x14, x7
	subs x1, x15, x1
	sbcs x15, x15, x2
	sbcs x2, x8, x3
	sbcs x3, x9, x6
	sbc x1, x5, x16
	adds x4, x10, x4
	adcs x15, x15, x8
	adcs x2, x2, x9
	adcs x3, x3, x5
	adc x1, x1, x7
	adds x8, x11, x15
	adcs x9, x12, x2
	adcs x10, x13, x3
	adcs x11, x14, x1
	adc x12, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	str x8, [x0, #800]
	str x9, [x0, #808]
	str x10, [x0, #816]
	str x11, [x0, #824]
	movz x7, #0, lsl #0
	ldr x4, [x0, #576]
	ldr x5, [x0, #584]
	ldr x16, [x0, #592]
	ldr x17, [x0, #600]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #800]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #808]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #816]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #824]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #768]
	str x13, [x0, #776]
	str x8, [x0, #784]
	str x9, [x0, #792]
	movz x7, #0, lsl #0
	ldr x8, [x0, #544]
	ldr x9, [x0, #552]
	ldr x10, [x0, #560]
	ldr x11, [x0, #568]
	ldr x2, [x0, #160]
	adds x8, x8, x2
	ldr x2, [x0, #168]
	adcs x9, x9, x2
	ldr x2, [x0, #176]
	adcs x10, x10, x2
	ldr x2, [x0, #184]
	adcs x11, x11, x2
	adc x12, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	str x8, [x0, #736]
	str x9, [x0, #744]
	str x10, [x0, #752]
	str x11, [x0, #760]
	ldr x1, [x0, #704]
	str x1, [x0, #512]
	ldr x1, [x0, #712]
	str x1, [x0, #520]
	ldr x1, [x0, #720]
	str x1, [x0, #528]
	ldr x1, [x0, #728]
	str x1, [x0, #536]
	ldr x1, [x0, #736]
	str x1, [x0, #544]
	ldr x1, [x0, #744]
	str x1, [x0, #552]
	ldr x1, [x0, #752]
	str x1, [x0, #560]
	ldr x1, [x0, #760]
	str x1, [x0, #568]
	ldr x1, [x0, #768]
	str x1, [x0, #576]
	ldr x1, [x0, #776]
	str x1, [x0, #584]
	ldr x1, [x0, #784]
	str x1, [x0, #592]
	ldr x1, [x0, #792]
	str x1, [x0, #600]
	movz x7, #0, lsl #0
	ldr x1, [x0, #576]
	ldr x2, [x0, #584]
	orr x1, x1, x2
	ldr x2, [x0, #592]
	orr x1, x1, x2
	ldr x2, [x0, #600]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x9, [x0, #544]
	bic x9, x9, x2, ror #0
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #544]
	ldr x9, [x0, #552]
	bic x9, x9, x2, ror #0
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #65535, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #552]
	ldr x9, [x0, #560]
	bic x9, x9, x2, ror #0
	movz x4, #65535, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #65535, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #560]
	ldr x9, [x0, #568]
	bic x9, x9, x2, ror #0
	movz x4, #65534, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	and x4, x4, x2
	orr x4, x4, x9
	str x4, [x0, #568]
	ldr x26, [x0, #7800]
	ldr x27, [x0, #7808]
	ldr x28, [x0, #7816]
	ldr x30, [x0, #7824]
	movz x1, #3, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1152]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65531, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1160]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1168]
	movz x1, #65533, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #4, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1176]
	movz x1, #62824, lsl #0
	movk x1, #13109, lsl #16
	movk x1, #26952, lsl #32
	movk x1, #39633, lsl #48
	str x1, [x0, #992]
	movz x1, #39217, lsl #0
	movk x1, #25598, lsl #16
	movk x1, #1348, lsl #32
	movk x1, #35249, lsl #48
	str x1, [x0, #1000]
	movz x1, #38583, lsl #0
	movk x1, #25902, lsl #16
	movk x1, #26318, lsl #32
	movk x1, #39937, lsl #48
	str x1, [x0, #1008]
	movz x1, #4075, lsl #0
	movk x1, #4067, lsl #16
	movk x1, #35872, lsl #32
	movk x1, #39012, lsl #48
	str x1, [x0, #1016]
	movz x1, #55982, lsl #0
	movk x1, #924, lsl #16
	movk x1, #13629, lsl #32
	movk x1, #3142, lsl #48
	str x1, [x0, #96]
	movz x1, #24955, lsl #0
	movk x1, #22760, lsl #16
	movk x1, #1363, lsl #32
	movk x1, #17177, lsl #48
	str x1, [x0, #104]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #112]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #120]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1152]
	ldr x5, [x0, #1160]
	ldr x16, [x0, #1168]
	ldr x17, [x0, #1176]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1056]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #1064]
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #1072]
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #1080]
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	ldr x4, [x0, #576]
	ldr x5, [x0, #584]
	ldr x16, [x0, #592]
	ldr x17, [x0, #600]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	ldr x8, [x0, #512]
	ldr x9, [x0, #520]
	ldr x10, [x0, #528]
	ldr x11, [x0, #536]
	ldr x2, [x0, #1184]
	subs x8, x8, x2
	ldr x2, [x0, #1192]
	sbcs x9, x9, x2
	ldr x2, [x0, #1200]
	sbcs x10, x10, x2
	ldr x2, [x0, #1208]
	sbcs x11, x11, x2
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
	str x8, [x0, #1344]
	str x9, [x0, #1352]
	str x10, [x0, #1360]
	str x11, [x0, #1368]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1152]
	ldr x9, [x0, #1160]
	ldr x10, [x0, #1168]
	ldr x11, [x0, #1176]
	ldr x2, [x0, #992]
	adds x8, x8, x2
	ldr x2, [x0, #1000]
	adcs x9, x9, x2
	ldr x2, [x0, #1008]
	adcs x10, x10, x2
	ldr x2, [x0, #1016]
	adcs x11, x11, x2
	adc x12, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	str x8, [x0, #1152]
	str x9, [x0, #1160]
	str x10, [x0, #1168]
	str x11, [x0, #1176]
	movz x7, #0, lsl #0
	ldr x4, [x0, #576]
	ldr x5, [x0, #584]
	ldr x16, [x0, #592]
	ldr x17, [x0, #600]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	ldr x8, [x0, #512]
	ldr x9, [x0, #520]
	ldr x10, [x0, #528]
	ldr x11, [x0, #536]
	ldr x2, [x0, #1184]
	subs x8, x8, x2
	ldr x2, [x0, #1192]
	sbcs x9, x9, x2
	ldr x2, [x0, #1200]
	sbcs x10, x10, x2
	ldr x2, [x0, #1208]
	sbcs x11, x11, x2
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1344]
	ldr x2, [x0, #1352]
	orr x1, x1, x2
	ldr x2, [x0, #1360]
	orr x1, x1, x2
	ldr x2, [x0, #1368]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1056]
	ldr x2, [x0, #96]
	subs x16, x1, x2
	ldr x1, [x0, #1064]
	ldr x2, [x0, #104]
	sbcs x16, x1, x2
	ldr x1, [x0, #1072]
	ldr x2, [x0, #112]
	sbcs x16, x1, x2
	ldr x1, [x0, #1080]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x6, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1280]
	ldr x2, [x0, #1288]
	orr x1, x1, x2
	ldr x2, [x0, #1296]
	orr x1, x1, x2
	ldr x2, [x0, #1304]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	and x2, x2, x6
	orr x2, x2, x4
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
	add sp, sp, #80
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
	movi v28.2d, #0
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #80
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	add sp, sp, #80
	ret
	.p2align 6

vg_ecdsa_p256_sign:
	ldr x6, [x5, #32]
	ldr x7, [x5, #40]
	str x30, [sp, #-16]!
	sub sp, sp, #608
	add x15, sp, #0
	str x0, [x15, #208]
	str x1, [x15, #200]
	str x2, [x15, #192]
	str x4, [x15, #184]
	str x6, [x15, #216]
	str x7, [x15, #224]
	str x5, [x15, #600]
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #320]
	str x14, [x15, #328]
	str x14, [x15, #336]
	str x14, [x15, #344]
	str x14, [x15, #352]
	str x14, [x15, #360]
	str x14, [x15, #368]
	str x14, [x15, #376]
	str x14, [x15, #384]
	ldr x13, [sp, #216]
	movz x9, #32, lsl #0
	subs x10, x13, x9
	csel x13, x9, x13, hs
	add x12, sp, #352
	sub x12, x12, x13
	ldr x11, [sp, #192]
20:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 20b
	add x1, sp, #320
	movz x7, #0, lsl #0
	add x15, sp, #0
	ldr x8, [x1, #24]
	rev x8, x8
	str x8, [x15, #64]
	movz x12, #9553, lsl #0
	movk x12, #64611, lsl #16
	movk x12, #51906, lsl #32
	movk x12, #62393, lsl #48
	subs x2, x8, x12
	str x2, [x15, #0]
	ldr x8, [x1, #16]
	rev x8, x8
	str x8, [x15, #72]
	movz x12, #40580, lsl #0
	movk x12, #42775, lsl #16
	movk x12, #64173, lsl #32
	movk x12, #48358, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #8]
	ldr x8, [x1, #8]
	rev x8, x8
	str x8, [x15, #80]
	movz x12, #65535, lsl #0
	movk x12, #65535, lsl #16
	movk x12, #65535, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #16]
	ldr x8, [x1, #0]
	rev x8, x8
	str x8, [x15, #88]
	movz x12, #0, lsl #0
	movk x12, #0, lsl #16
	movk x12, #65535, lsl #32
	movk x12, #65535, lsl #48
	sbcs x2, x8, x12
	str x2, [x15, #24]
	sbc x6, x7, x7
	ldr x8, [x15, #64]
	ldr x2, [x15, #0]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #272]
	ldr x8, [x15, #72]
	ldr x2, [x15, #8]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #264]
	ldr x8, [x15, #80]
	ldr x2, [x15, #16]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #256]
	ldr x8, [x15, #88]
	ldr x2, [x15, #24]
	eor x8, x8, x2
	and x8, x8, x6
	eor x8, x8, x2
	rev x8, x8
	str x8, [x15, #248]
	movz x9, #257, lsl #0
	movk x9, #257, lsl #16
	movk x9, #257, lsl #32
	movk x9, #257, lsl #48
	movz x10, #0, lsl #0
	add x15, sp, #0
	str x9, [x15, #64]
	str x10, [x15, #0]
	str x9, [x15, #72]
	str x10, [x15, #8]
	str x9, [x15, #80]
	str x10, [x15, #16]
	str x9, [x15, #88]
	str x10, [x15, #24]
	str x9, [x15, #96]
	str x10, [x15, #32]
	str x9, [x15, #104]
	str x10, [x15, #40]
	str x9, [x15, #112]
	str x10, [x15, #48]
	str x9, [x15, #120]
	str x10, [x15, #56]
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	movz x11, #0, lsl #0
	strb w11, [x9, #16]
	add x12, x9, #17
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	add x13, x15, #248
	add x14, x12, #32
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	ldr x11, [x13, #24]
	str x11, [x14, #24]
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	ldr x9, [sp, #216]
	add x1, x1, x9
	ldr x2, [sp, #184]
	add x2, x2, #16
	movz x3, #65, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #65
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x9, [sp, #184]
	add x11, x9, #1216
	add x12, x9, #832
	movz x13, #384, lsl #0
21:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 21b
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	movz x11, #1, lsl #0
	strb w11, [x9, #16]
	add x12, x9, #17
	ldr x11, [x10, #0]
	str x11, [x12, #0]
	ldr x11, [x10, #8]
	str x11, [x12, #8]
	ldr x11, [x10, #16]
	str x11, [x12, #16]
	ldr x11, [x10, #24]
	str x11, [x12, #24]
	add x13, x15, #248
	add x14, x12, #32
	ldr x11, [x13, #0]
	str x11, [x14, #0]
	ldr x11, [x13, #8]
	str x11, [x14, #8]
	ldr x11, [x13, #16]
	str x11, [x14, #16]
	ldr x11, [x13, #24]
	str x11, [x14, #24]
	ldr x9, [sp, #184]
	add x11, x9, #832
	add x12, x9, #1216
	movz x13, #384, lsl #0
22:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 22b
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	ldr x9, [sp, #216]
	add x1, x1, x9
	ldr x2, [sp, #184]
	add x2, x2, #16
	movz x3, #65, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #65
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x9, [sp, #184]
	add x11, x9, #1216
	add x12, x9, #832
	movz x13, #384, lsl #0
23:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 23b
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	movz x9, #8, lsl #0
	add x15, sp, #0
	str x9, [x15, #176]
24:
	movz x9, #0, lsl #0
	add x15, sp, #0
	str x9, [x15, #128]
25:
	ldr x9, [sp, #184]
	add x11, x9, #832
	add x12, x9, #1216
	movz x13, #384, lsl #0
26:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 26b
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	add x11, sp, #64
	add x12, sp, #464
	ldr x9, [sp, #128]
	add x12, x12, x9
	ldr x13, [sp, #216]
27:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 27b
	ldr x9, [sp, #128]
	ldr x10, [sp, #216]
	add x9, x9, x10
	add x15, sp, #0
	str x9, [x15, #128]
	movz x10, #32, lsl #0
	subs x12, x9, x10
	sbc x12, x12, x12
	cbnz x12, 25b
	ldr x0, [sp, #208]
	ldr x1, [sp, #200]
	add x2, sp, #320
	add x3, sp, #464
	ldr x4, [sp, #184]
	bl {vg_ecdsa_p256_sign_k}
	ldr x9, [sp, #176]
	sub x9, x9, #1
	add x15, sp, #0
	str x9, [x15, #176]
	movz x7, #0, lsl #0
	movz x10, #1, lsl #0
	subs w16, w0, w10
	sbc x11, x7, x7
	and x12, x11, x9
	cbnz x12, 28f
	movz x12, #0, lsl #0
	b 29f
28:
	ldr x9, [sp, #184]
	ldr x10, [sp, #200]
	add x15, sp, #0
	movz x11, #0, lsl #0
	strb w11, [x9, #16]
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	ldr x9, [sp, #216]
	add x1, x1, x9
	ldr x2, [sp, #184]
	add x2, x2, #16
	movz x3, #1, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #1
	add x3, sp, #0
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	add x2, sp, #0
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #0]
	blr x16
	ldr x9, [sp, #184]
	add x11, x9, #1216
	add x12, x9, #832
	movz x13, #384, lsl #0
210:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 210b
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #224]
	add x2, sp, #64
	ldr x3, [sp, #216]
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #8]
	blr x16
	ldr x0, [sp, #184]
	add x0, x0, #1216
	ldr x1, [sp, #184]
	add x1, x1, #1408
	ldr x2, [sp, #224]
	ldr x9, [sp, #216]
	add x2, x2, x9
	add x2, x2, #0
	add x3, sp, #64
	ldr x4, [sp, #184]
	add x4, x4, #1600
	ldr x16, [sp, #600]
	ldr x16, [x16, #16]
	blr x16
	movz x12, #1, lsl #0
29:
	cbnz x12, 24b
	add x15, sp, #0
	movz x14, #0, lsl #0
	str x14, [x15, #0]
	str x14, [x15, #8]
	str x14, [x15, #16]
	str x14, [x15, #24]
	str x14, [x15, #32]
	str x14, [x15, #40]
	str x14, [x15, #48]
	str x14, [x15, #56]
	str x14, [x15, #64]
	str x14, [x15, #72]
	str x14, [x15, #80]
	str x14, [x15, #88]
	str x14, [x15, #96]
	str x14, [x15, #104]
	str x14, [x15, #112]
	str x14, [x15, #120]
	str x14, [x15, #232]
	str x14, [x15, #240]
	str x14, [x15, #248]
	str x14, [x15, #256]
	str x14, [x15, #264]
	str x14, [x15, #272]
	str x14, [x15, #280]
	str x14, [x15, #288]
	str x14, [x15, #296]
	str x14, [x15, #304]
	str x14, [x15, #312]
	str x14, [x15, #320]
	str x14, [x15, #328]
	str x14, [x15, #336]
	str x14, [x15, #344]
	str x14, [x15, #352]
	str x14, [x15, #360]
	str x14, [x15, #368]
	str x14, [x15, #376]
	str x14, [x15, #384]
	str x14, [x15, #392]
	str x14, [x15, #400]
	str x14, [x15, #408]
	str x14, [x15, #416]
	str x14, [x15, #424]
	str x14, [x15, #432]
	str x14, [x15, #440]
	str x14, [x15, #448]
	str x14, [x15, #456]
	str x14, [x15, #464]
	str x14, [x15, #472]
	str x14, [x15, #480]
	str x14, [x15, #488]
	str x14, [x15, #496]
	str x14, [x15, #504]
	str x14, [x15, #512]
	str x14, [x15, #520]
	str x14, [x15, #528]
	str x14, [x15, #536]
	str x14, [x15, #544]
	str x14, [x15, #552]
	str x14, [x15, #560]
	str x14, [x15, #568]
	str x14, [x15, #576]
	str x14, [x15, #584]
	str x14, [x15, #592]
	add sp, sp, #608
	ldr x30, [sp], #16
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
	sub sp, sp, #640
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
211:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 211b
	add sp, sp, #640
	ret
	.p2align 6
