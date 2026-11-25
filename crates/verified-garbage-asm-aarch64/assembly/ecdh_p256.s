// The functions of `src/ecdh_p256.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_p256:
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
	movz x1, #16912, lsl #0
	movk x1, #8456, lsl #16
	movk x1, #4228, lsl #32
	movk x1, #2114, lsl #48
	str x1, [x0, #1760]
	movz x1, #33825, lsl #0
	movk x1, #16912, lsl #16
	movk x1, #8456, lsl #32
	movk x1, #4228, lsl #48
	str x1, [x0, #1768]
	movz x1, #2114, lsl #0
	movk x1, #33825, lsl #16
	movk x1, #16912, lsl #32
	movk x1, #8456, lsl #48
	str x1, [x0, #1776]
	movz x1, #4228, lsl #0
	movk x1, #2114, lsl #16
	movk x1, #33825, lsl #32
	movk x1, #16912, lsl #48
	str x1, [x0, #1784]
	movz x1, #8, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1792]
	ldr x8, [x0, #1056]
	ldr x9, [x0, #1064]
	ldr x10, [x0, #1072]
	ldr x11, [x0, #1080]
	movz x12, #0, lsl #0
	ldr x2, [x0, #1760]
	adds x8, x8, x2
	ldr x2, [x0, #1768]
	adcs x9, x9, x2
	ldr x2, [x0, #1776]
	adcs x10, x10, x2
	ldr x2, [x0, #1784]
	adcs x11, x11, x2
	ldr x2, [x0, #1792]
	adcs x12, x12, x2
	str x8, [x0, #1760]
	str x9, [x0, #1768]
	str x10, [x0, #1776]
	str x11, [x0, #1784]
	str x12, [x0, #1792]
	movz x19, #40, lsl #0
	movz x5, #1, lsl #0
20:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #1760]
	lsl x17, x19, #3
	add x17, x0, x17
	and x2, x1, x5
	strb w2, [x17, #1824]
	lsr x2, x1, #1
	and x2, x2, x5
	strb w2, [x17, #1825]
	lsr x2, x1, #2
	and x2, x2, x5
	strb w2, [x17, #1826]
	lsr x2, x1, #3
	and x2, x2, x5
	strb w2, [x17, #1827]
	lsr x2, x1, #4
	and x2, x2, x5
	strb w2, [x17, #1828]
	lsr x2, x1, #5
	and x2, x2, x5
	strb w2, [x17, #1829]
	lsr x2, x1, #6
	and x2, x2, x5
	strb w2, [x17, #1830]
	lsr x2, x1, #7
	and x2, x2, x5
	strb w2, [x17, #1831]
	cbnz x19, 20b
	str x26, [x0, #7800]
	str x27, [x0, #7808]
	str x28, [x0, #7816]
	str x30, [x0, #7824]
	str x20, [x0, #7832]
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
	movz x2, #160, lsl #0
	mul x1, x1, x2
	add x16, x0, #2816
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
	ldr x1, [x0, #5400]
	str x1, [x16, #96]
	ldr x1, [x0, #5408]
	str x1, [x16, #104]
	ldr x1, [x0, #5416]
	str x1, [x16, #112]
	ldr x1, [x0, #5424]
	str x1, [x16, #120]
	ldr x1, [x0, #5432]
	str x1, [x16, #128]
	ldr x1, [x0, #5440]
	str x1, [x16, #136]
	ldr x1, [x0, #5448]
	str x1, [x16, #144]
	ldr x1, [x0, #5456]
	str x1, [x16, #152]
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
	ldr x1, [x0, #896]
	str x1, [x0, #608]
	ldr x1, [x0, #904]
	str x1, [x0, #616]
	ldr x1, [x0, #912]
	str x1, [x0, #624]
	ldr x1, [x0, #920]
	str x1, [x0, #632]
	ldr x1, [x0, #864]
	str x1, [x0, #640]
	ldr x1, [x0, #872]
	str x1, [x0, #648]
	ldr x1, [x0, #880]
	str x1, [x0, #656]
	ldr x1, [x0, #888]
	str x1, [x0, #664]
	movz x19, #2, lsl #0
	sub x1, x19, #1
	movz x2, #160, lsl #0
	mul x1, x1, x2
	add x16, x0, #2816
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
	ldr x1, [x0, #5400]
	str x1, [x16, #96]
	ldr x1, [x0, #5408]
	str x1, [x16, #104]
	ldr x1, [x0, #5416]
	str x1, [x16, #112]
	ldr x1, [x0, #5424]
	str x1, [x16, #120]
	ldr x1, [x0, #5432]
	str x1, [x16, #128]
	ldr x1, [x0, #5440]
	str x1, [x16, #136]
	ldr x1, [x0, #5448]
	str x1, [x16, #144]
	ldr x1, [x0, #5456]
	str x1, [x16, #152]
21:
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
	movz x2, #160, lsl #0
	mul x1, x1, x2
	add x16, x0, #2816
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
	ldr x1, [x0, #5400]
	str x1, [x16, #96]
	ldr x1, [x0, #5408]
	str x1, [x16, #104]
	ldr x1, [x0, #5416]
	str x1, [x16, #112]
	ldr x1, [x0, #5424]
	str x1, [x16, #120]
	ldr x1, [x0, #5432]
	str x1, [x16, #128]
	ldr x1, [x0, #5440]
	str x1, [x16, #136]
	ldr x1, [x0, #5448]
	str x1, [x16, #144]
	ldr x1, [x0, #5456]
	str x1, [x16, #152]
	sub x4, x19, #16
	cbnz x4, 21b
	movz x19, #51, lsl #0
	movz x16, #5, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	movz x2, #0, lsl #0
	add x2, x2, x2
	ldrb w4, [x16, #1828]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1827]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1826]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1825]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1824]
	add x2, x2, x4
	sub x3, x2, #16
	lsr x4, x3, #63
	movz x9, #0, lsl #0
	sub x4, x9, x4
	eor x2, x3, x4
	sub x2, x2, x4
	movz x5, #1, lsl #0
	dup v31.2d, x5
	dup v30.2d, x2
	movi v28.2d, #0
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
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #2816]
	ldr q19, [x0, #2832]
	ldr q20, [x0, #2848]
	ldr q21, [x0, #2864]
	ldr q22, [x0, #2880]
	ldr q23, [x0, #2896]
	ldr q24, [x0, #2912]
	ldr q25, [x0, #2928]
	ldr q26, [x0, #2944]
	ldr q27, [x0, #2960]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #2976]
	ldr q19, [x0, #2992]
	ldr q20, [x0, #3008]
	ldr q21, [x0, #3024]
	ldr q22, [x0, #3040]
	ldr q23, [x0, #3056]
	ldr q24, [x0, #3072]
	ldr q25, [x0, #3088]
	ldr q26, [x0, #3104]
	ldr q27, [x0, #3120]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #3136]
	ldr q19, [x0, #3152]
	ldr q20, [x0, #3168]
	ldr q21, [x0, #3184]
	ldr q22, [x0, #3200]
	ldr q23, [x0, #3216]
	ldr q24, [x0, #3232]
	ldr q25, [x0, #3248]
	ldr q26, [x0, #3264]
	ldr q27, [x0, #3280]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #3296]
	ldr q19, [x0, #3312]
	ldr q20, [x0, #3328]
	ldr q21, [x0, #3344]
	ldr q22, [x0, #3360]
	ldr q23, [x0, #3376]
	ldr q24, [x0, #3392]
	ldr q25, [x0, #3408]
	ldr q26, [x0, #3424]
	ldr q27, [x0, #3440]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #3456]
	ldr q19, [x0, #3472]
	ldr q20, [x0, #3488]
	ldr q21, [x0, #3504]
	ldr q22, [x0, #3520]
	ldr q23, [x0, #3536]
	ldr q24, [x0, #3552]
	ldr q25, [x0, #3568]
	ldr q26, [x0, #3584]
	ldr q27, [x0, #3600]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #3616]
	ldr q19, [x0, #3632]
	ldr q20, [x0, #3648]
	ldr q21, [x0, #3664]
	ldr q22, [x0, #3680]
	ldr q23, [x0, #3696]
	ldr q24, [x0, #3712]
	ldr q25, [x0, #3728]
	ldr q26, [x0, #3744]
	ldr q27, [x0, #3760]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #3776]
	ldr q19, [x0, #3792]
	ldr q20, [x0, #3808]
	ldr q21, [x0, #3824]
	ldr q22, [x0, #3840]
	ldr q23, [x0, #3856]
	ldr q24, [x0, #3872]
	ldr q25, [x0, #3888]
	ldr q26, [x0, #3904]
	ldr q27, [x0, #3920]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #3936]
	ldr q19, [x0, #3952]
	ldr q20, [x0, #3968]
	ldr q21, [x0, #3984]
	ldr q22, [x0, #4000]
	ldr q23, [x0, #4016]
	ldr q24, [x0, #4032]
	ldr q25, [x0, #4048]
	ldr q26, [x0, #4064]
	ldr q27, [x0, #4080]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #4096]
	ldr q19, [x0, #4112]
	ldr q20, [x0, #4128]
	ldr q21, [x0, #4144]
	ldr q22, [x0, #4160]
	ldr q23, [x0, #4176]
	ldr q24, [x0, #4192]
	ldr q25, [x0, #4208]
	ldr q26, [x0, #4224]
	ldr q27, [x0, #4240]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #4256]
	ldr q19, [x0, #4272]
	ldr q20, [x0, #4288]
	ldr q21, [x0, #4304]
	ldr q22, [x0, #4320]
	ldr q23, [x0, #4336]
	ldr q24, [x0, #4352]
	ldr q25, [x0, #4368]
	ldr q26, [x0, #4384]
	ldr q27, [x0, #4400]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #4416]
	ldr q19, [x0, #4432]
	ldr q20, [x0, #4448]
	ldr q21, [x0, #4464]
	ldr q22, [x0, #4480]
	ldr q23, [x0, #4496]
	ldr q24, [x0, #4512]
	ldr q25, [x0, #4528]
	ldr q26, [x0, #4544]
	ldr q27, [x0, #4560]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #4576]
	ldr q19, [x0, #4592]
	ldr q20, [x0, #4608]
	ldr q21, [x0, #4624]
	ldr q22, [x0, #4640]
	ldr q23, [x0, #4656]
	ldr q24, [x0, #4672]
	ldr q25, [x0, #4688]
	ldr q26, [x0, #4704]
	ldr q27, [x0, #4720]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #4736]
	ldr q19, [x0, #4752]
	ldr q20, [x0, #4768]
	ldr q21, [x0, #4784]
	ldr q22, [x0, #4800]
	ldr q23, [x0, #4816]
	ldr q24, [x0, #4832]
	ldr q25, [x0, #4848]
	ldr q26, [x0, #4864]
	ldr q27, [x0, #4880]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #4896]
	ldr q19, [x0, #4912]
	ldr q20, [x0, #4928]
	ldr q21, [x0, #4944]
	ldr q22, [x0, #4960]
	ldr q23, [x0, #4976]
	ldr q24, [x0, #4992]
	ldr q25, [x0, #5008]
	ldr q26, [x0, #5024]
	ldr q27, [x0, #5040]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #5056]
	ldr q19, [x0, #5072]
	ldr q20, [x0, #5088]
	ldr q21, [x0, #5104]
	ldr q22, [x0, #5120]
	ldr q23, [x0, #5136]
	ldr q24, [x0, #5152]
	ldr q25, [x0, #5168]
	ldr q26, [x0, #5184]
	ldr q27, [x0, #5200]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	add v28.2d, v28.2d, v31.2d
	cmeq v29.2d, v28.2d, v30.2d
	ldr q18, [x0, #5216]
	ldr q19, [x0, #5232]
	ldr q20, [x0, #5248]
	ldr q21, [x0, #5264]
	ldr q22, [x0, #5280]
	ldr q23, [x0, #5296]
	ldr q24, [x0, #5312]
	ldr q25, [x0, #5328]
	ldr q26, [x0, #5344]
	ldr q27, [x0, #5360]
	bit v0.16b, v18.16b, v29.16b
	bit v1.16b, v19.16b, v29.16b
	bit v2.16b, v20.16b, v29.16b
	bit v3.16b, v21.16b, v29.16b
	bit v4.16b, v22.16b, v29.16b
	bit v5.16b, v23.16b, v29.16b
	bit v6.16b, v24.16b, v29.16b
	bit v7.16b, v25.16b, v29.16b
	bit v16.16b, v26.16b, v29.16b
	bit v17.16b, v27.16b, v29.16b
	str q0, [x0, #704]
	str q1, [x0, #720]
	str q2, [x0, #736]
	str q3, [x0, #752]
	str q4, [x0, #768]
	str q5, [x0, #784]
	movz x17, #5400, lsl #0
	add x17, x0, x17
	str q6, [x17, #0]
	str q7, [x17, #16]
	str q16, [x17, #32]
	str q17, [x17, #48]
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
	str x8, [x0, #1024]
	str x9, [x0, #1032]
	str x10, [x0, #1040]
	str x11, [x0, #1048]
	movz x16, #5, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	ldrb w3, [x16, #1828]
	sub x3, x3, #1
	ldr x1, [x0, #736]
	ldr x2, [x0, #1024]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #736]
	ldr x1, [x0, #744]
	ldr x2, [x0, #1032]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #744]
	ldr x1, [x0, #752]
	ldr x2, [x0, #1040]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #752]
	ldr x1, [x0, #760]
	ldr x2, [x0, #1048]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #760]
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
22:
	sub x19, x19, #1
	movz x4, #8192, lsl #0
	add x19, x19, x4
23:
	ldr x1, [x0, #576]
	ldr x2, [x0, #584]
	mul x3, x1, x2
	umulh x4, x1, x1
	umulh x5, x1, x2
	ldr x6, [x0, #592]
	mul x7, x1, x6
	mul x8, x1, x1
	umulh x9, x1, x6
	mul x10, x2, x2
	ldr x11, [x0, #600]
	mul x12, x1, x11
	mul x13, x2, x6
	umulh x14, x2, x2
	lsl x15, x8, #32
	adds x7, x5, x7
	umulh x16, x1, x11
	umulh x17, x2, x6
	mul x20, x2, x11
	adcs x12, x12, x9
	umulh x21, x2, x11
	mul x22, x6, x11
	umulh x23, x6, x11
	sub x24, x8, x15
	mul x25, x6, x6
	adcs x20, x16, x20
	umulh x26, x6, x6
	adcs x22, x22, x21
	mul x27, x11, x11
	movz x28, #0, lsl #0
	adc x23, x23, x28
	adds x13, x12, x13
	umulh x30, x11, x11
	adcs x17, x20, x17
	movz x5, #1, lsl #0
	sub x9, x28, x5
	adcs x22, x22, x28
	adc x23, x23, x28
	adds x3, x3, x3
	adcs x7, x7, x7
	adcs x13, x13, x13
	adcs x17, x17, x17
	adcs x22, x22, x22
	adcs x23, x23, x23
	adc x16, x28, x28
	adds x4, x3, x4
	adcs x7, x7, x10
	ldr x21, [x0, #544]
	ldr x12, [x0, #552]
	mul x20, x21, x12
	adcs x14, x13, x14
	adcs x17, x17, x25
	adcs x22, x22, x26
	extr x3, x4, x8, #32
	adcs x23, x23, x27
	umulh x10, x21, x21
	adc x30, x16, x30
	adds x4, x4, x15
	umulh x13, x21, x12
	adcs x7, x7, x3
	extr x25, x7, x4, #32
	adcs x14, x14, x25
	add x26, x14, x24
	extr x27, x26, x7, #32
	adcs x17, x17, x27
	lsr x16, x26, #32
	adcs x22, x22, x16
	adcs x23, x23, x28
	adc x30, x30, x28
	subs x15, x8, x15
	sbcs x3, x8, x3
	sbcs x25, x4, x25
	sbcs x27, x7, x27
	sbc x16, x26, x16
	adds x14, x14, x24
	adcs x3, x3, x4
	orr x15, x5, x5
	movk x15, #0, lsl #16
	adcs x7, x25, x7
	ldr x8, [x0, #560]
	mul x24, x21, x8
	adcs x26, x27, x26
	movk x15, #65535, lsl #32
	movk x15, #65535, lsl #48
	adc x16, x16, x28
	adds x24, x13, x24
	mul x14, x21, x21
	umulh x4, x21, x8
	ldr x25, [x0, #568]
	mul x27, x21, x25
	adcs x27, x27, x4
	umulh x13, x21, x25
	mul x4, x12, x8
	str x15, [x0, #7104]
	umulh x15, x12, x8
	str x9, [x0, #7112]
	mul x9, x12, x25
	adcs x9, x13, x9
	umulh x13, x12, x25
	mul x11, x8, x25
	adcs x11, x11, x13
	umulh x13, x8, x25
	adc x13, x13, x28
	adds x3, x17, x3
	adcs x7, x22, x7
	adcs x26, x23, x26
	adcs x16, x30, x16
	adc x17, x28, x28
	adds x4, x27, x4
	adcs x15, x9, x15
	adcs x11, x11, x28
	adc x13, x13, x28
	adds x20, x20, x20
	adcs x24, x24, x24
	adcs x4, x4, x4
	adcs x15, x15, x15
	adcs x11, x11, x11
	adcs x13, x13, x13
	adc x22, x28, x28
	adds x10, x20, x10
	mul x23, x12, x12
	adcs x24, x24, x23
	umulh x30, x12, x12
	adcs x4, x4, x30
	mul x27, x8, x8
	adcs x15, x15, x27
	umulh x9, x8, x8
	adcs x11, x11, x9
	mul x20, x25, x25
	adcs x13, x13, x20
	umulh x23, x25, x25
	adc x23, x22, x23
	adds x30, x3, x5
	ldr x27, [x0, #72]
	sbcs x9, x7, x27
	sbcs x20, x26, x28
	ldr x22, [x0, #88]
	sbcs x27, x16, x22
	sbcs x17, x17, x28
	csel x30, x30, x3, hs
	csel x7, x9, x7, hs
	csel x26, x20, x26, hs
	csel x27, x27, x16, hs
	adds x1, x21, x1
	adcs x2, x12, x2
	adcs x8, x8, x6
	ldr x17, [x0, #600]
	adcs x17, x25, x17
	extr x3, x10, x14, #32
	lsl x9, x14, #32
	sub x20, x14, x9
	adc x16, x28, x28
	adds x10, x10, x9
	adcs x24, x24, x3
	extr x21, x24, x10, #32
	adcs x4, x4, x21
	add x12, x4, x20
	extr x6, x12, x24, #32
	adcs x15, x15, x6
	lsr x25, x12, #32
	adcs x11, x11, x25
	adcs x13, x13, x28
	adc x23, x23, x28
	subs x9, x14, x9
	sbcs x3, x14, x3
	sbcs x21, x10, x21
	sbcs x6, x24, x6
	sbc x25, x12, x25
	adds x4, x4, x20
	adcs x3, x3, x10
	adcs x24, x21, x24
	adcs x12, x6, x12
	adc x25, x25, x28
	adds x3, x15, x3
	adcs x24, x11, x24
	adcs x12, x13, x12
	adcs x25, x23, x25
	adc x9, x28, x28
	ldr x14, [x0, #512]
	subs x20, x14, x30
	ldr x4, [x0, #520]
	sbcs x10, x4, x7
	ldr x21, [x0, #528]
	sbcs x6, x21, x26
	ldr x15, [x0, #536]
	sbcs x11, x15, x27
	sbc x13, x28, x28
	adds x20, x20, x13
	lsr x23, x13, #32
	adcs x23, x10, x23
	adcs x6, x6, x28
	lsl x10, x13, #32
	sub x13, x10, x13
	adc x11, x11, x13
	adds x10, x3, x5
	ldr x13, [x0, #72]
	sbcs x5, x24, x13
	sbcs x13, x12, x28
	str x16, [x0, #7120]
	sbcs x16, x25, x22
	sbcs x9, x9, x28
	csel x10, x10, x3, hs
	csel x5, x5, x24, hs
	csel x13, x13, x12, hs
	csel x25, x16, x25, hs
	adds x9, x14, x30
	adcs x3, x4, x7
	adcs x24, x21, x26
	adcs x12, x15, x27
	ldr x16, [x0, #7112]
	csel x16, x16, x28, hs
	subs x9, x9, x16
	str x27, [x0, #7112]
	lsl x27, x16, #32
	sub x16, x27, x16
	lsr x27, x27, #32
	sbcs x3, x3, x27
	sbcs x24, x24, x28
	sbc x16, x12, x16
	mul x27, x9, x20
	mul x12, x9, x23
	str x26, [x0, #7128]
	mul x26, x9, x6
	str x7, [x0, #7136]
	mul x7, x9, x11
	str x30, [x0, #7144]
	umulh x30, x9, x20
	adds x12, x12, x30
	umulh x30, x9, x23
	adcs x30, x26, x30
	umulh x26, x9, x6
	adcs x26, x7, x26
	umulh x9, x9, x11
	adcs x9, x28, x9
	lsl x7, x27, #32
	adds x12, x12, x7
	lsr x7, x27, #32
	adcs x30, x30, x7
	ldr x7, [x0, #7104]
	mul x15, x27, x7
	adcs x26, x26, x15
	umulh x27, x27, x7
	adcs x9, x9, x27
	adcs x15, x28, x28
	mul x27, x3, x20
	adds x27, x12, x27
	mul x12, x3, x23
	adcs x30, x30, x12
	mul x12, x3, x6
	adcs x26, x26, x12
	mul x12, x3, x11
	adcs x12, x9, x12
	umulh x9, x3, x11
	adcs x9, x15, x9
	umulh x15, x3, x20
	adds x30, x30, x15
	umulh x15, x3, x23
	adcs x15, x26, x15
	umulh x3, x3, x6
	adcs x12, x12, x3
	adcs x9, x9, x28
	lsl x26, x27, #32
	adds x30, x30, x26
	lsr x3, x27, #32
	adcs x3, x15, x3
	mul x26, x27, x7
	adcs x12, x12, x26
	umulh x27, x27, x7
	adcs x9, x9, x27
	adcs x15, x28, x28
	mul x26, x24, x20
	adds x30, x30, x26
	mul x27, x24, x23
	adcs x3, x3, x27
	mul x26, x24, x6
	adcs x26, x12, x26
	mul x27, x24, x11
	adcs x9, x9, x27
	umulh x12, x24, x11
	adcs x12, x15, x12
	umulh x27, x24, x20
	adds x27, x3, x27
	umulh x15, x24, x23
	adcs x26, x26, x15
	umulh x24, x24, x6
	adcs x9, x9, x24
	adcs x12, x12, x28
	lsl x3, x30, #32
	adds x3, x27, x3
	lsr x15, x30, #32
	adcs x26, x26, x15
	mul x24, x30, x7
	adcs x9, x9, x24
	umulh x30, x30, x7
	adcs x12, x12, x30
	adcs x27, x28, x28
	mul x15, x16, x20
	adds x3, x3, x15
	umulh x20, x16, x20
	mul x24, x16, x23
	adcs x24, x26, x24
	umulh x23, x16, x23
	mul x30, x16, x6
	adcs x9, x9, x30
	umulh x6, x16, x6
	mul x15, x16, x11
	umulh x11, x16, x11
	adcs x12, x12, x15
	adcs x11, x27, x11
	adds x24, x24, x20
	adcs x9, x9, x23
	adcs x12, x12, x6
	adcs x11, x11, x28
	lsl x26, x3, #32
	adds x24, x24, x26
	lsr x30, x3, #32
	adcs x9, x9, x30
	mul x16, x3, x7
	adcs x12, x12, x16
	umulh x3, x3, x7
	adcs x11, x11, x3
	adcs x15, x28, x28
	movz x27, #1, lsl #0
	adds x20, x24, x27
	ldr x23, [x0, #72]
	sbcs x6, x9, x23
	sbcs x26, x12, x28
	sbcs x30, x11, x22
	sbcs x15, x15, x28
	csel x24, x20, x24, hs
	csel x9, x6, x9, hs
	csel x12, x26, x12, hs
	csel x11, x30, x11, hs
	adds x16, x1, x27
	sbcs x3, x2, x23
	sbcs x15, x8, x28
	sbcs x20, x17, x22
	ldr x6, [x0, #7120]
	sbcs x6, x6, x28
	csel x16, x16, x1, hs
	csel x2, x3, x2, hs
	csel x8, x15, x8, hs
	csel x17, x20, x17, hs
	mul x26, x14, x10
	mul x30, x14, x5
	mul x6, x14, x13
	mul x1, x14, x25
	umulh x3, x14, x10
	adds x3, x30, x3
	umulh x15, x14, x5
	adcs x15, x6, x15
	umulh x20, x14, x13
	adcs x1, x1, x20
	umulh x14, x14, x25
	adcs x14, x28, x14
	lsl x30, x26, #32
	adds x3, x3, x30
	lsr x6, x26, #32
	adcs x15, x15, x6
	mul x20, x26, x7
	adcs x1, x1, x20
	umulh x26, x26, x7
	adcs x14, x14, x26
	adcs x30, x28, x28
	mul x6, x4, x10
	adds x3, x3, x6
	mul x20, x4, x5
	adcs x15, x15, x20
	mul x26, x4, x13
	adcs x26, x1, x26
	mul x6, x4, x25
	adcs x14, x14, x6
	umulh x20, x4, x25
	adcs x20, x30, x20
	umulh x1, x4, x10
	adds x1, x15, x1
	umulh x6, x4, x5
	adcs x26, x26, x6
	umulh x4, x4, x13
	adcs x14, x14, x4
	adcs x20, x20, x28
	lsl x30, x3, #32
	adds x30, x1, x30
	lsr x15, x3, #32
	adcs x26, x26, x15
	mul x6, x3, x7
	adcs x14, x14, x6
	umulh x3, x3, x7
	adcs x20, x20, x3
	adcs x4, x28, x28
	mul x1, x21, x10
	adds x30, x30, x1
	mul x15, x21, x5
	adcs x15, x26, x15
	mul x6, x21, x13
	adcs x14, x14, x6
	mul x3, x21, x25
	adcs x20, x20, x3
	umulh x1, x21, x25
	adcs x1, x4, x1
	umulh x26, x21, x10
	adds x15, x15, x26
	umulh x6, x21, x5
	adcs x14, x14, x6
	umulh x21, x21, x13
	adcs x20, x20, x21
	adcs x1, x1, x28
	lsl x3, x30, #32
	adds x15, x15, x3
	lsr x4, x30, #32
	adcs x14, x14, x4
	mul x26, x30, x7
	adcs x20, x20, x26
	umulh x30, x30, x7
	adcs x1, x1, x30
	adcs x6, x28, x28
	ldr x21, [x0, #536]
	mul x3, x21, x10
	adds x3, x15, x3
	mul x4, x21, x5
	adcs x4, x14, x4
	mul x26, x21, x13
	adcs x26, x20, x26
	mul x30, x21, x25
	adcs x1, x1, x30
	umulh x15, x21, x25
	adcs x15, x6, x15
	umulh x14, x21, x10
	adds x4, x4, x14
	umulh x20, x21, x5
	adcs x26, x26, x20
	umulh x21, x21, x13
	adcs x21, x1, x21
	adcs x15, x15, x28
	lsl x30, x3, #32
	adds x4, x4, x30
	lsr x6, x3, #32
	adcs x26, x26, x6
	mul x14, x3, x7
	adcs x14, x21, x14
	umulh x3, x3, x7
	adcs x15, x15, x3
	adcs x20, x28, x28
	adds x1, x4, x27
	sbcs x30, x26, x23
	sbcs x6, x14, x28
	sbcs x21, x15, x22
	sbcs x20, x20, x28
	csel x4, x1, x4, hs
	csel x26, x30, x26, hs
	csel x14, x6, x14, hs
	csel x21, x21, x15, hs
	mul x3, x24, x9
	umulh x20, x24, x9
	mul x1, x24, x12
	adds x1, x20, x1
	umulh x30, x24, x12
	mul x6, x24, x11
	adcs x30, x6, x30
	umulh x15, x24, x11
	mul x20, x9, x12
	umulh x6, x9, x12
	mul x7, x9, x11
	adcs x7, x15, x7
	umulh x15, x9, x11
	str x25, [x0, #7120]
	mul x25, x12, x11
	adcs x25, x25, x15
	umulh x15, x12, x11
	adc x15, x15, x28
	adds x20, x30, x20
	adcs x6, x7, x6
	adcs x25, x25, x28
	adc x15, x15, x28
	adds x3, x3, x3
	adcs x1, x1, x1
	adcs x20, x20, x20
	adcs x6, x6, x6
	adcs x25, x25, x25
	adcs x15, x15, x15
	adc x30, x28, x28
	mul x7, x24, x24
	str x13, [x0, #7152]
	umulh x13, x24, x24
	adds x13, x3, x13
	mul x3, x9, x9
	adcs x1, x1, x3
	umulh x3, x9, x9
	adcs x3, x20, x3
	mul x20, x12, x12
	adcs x6, x6, x20
	umulh x20, x12, x12
	adcs x25, x25, x20
	mul x20, x11, x11
	adcs x15, x15, x20
	umulh x20, x11, x11
	adc x30, x30, x20
	lsl x20, x7, #32
	str x11, [x0, #7160]
	sub x11, x7, x20
	str x12, [x0, #7168]
	extr x12, x13, x7, #32
	adds x13, x13, x20
	adcs x1, x1, x12
	str x9, [x0, #7176]
	extr x9, x1, x13, #32
	adcs x3, x3, x9
	str x24, [x0, #7184]
	add x24, x3, x11
	str x5, [x0, #7192]
	extr x5, x24, x1, #32
	adcs x6, x6, x5
	str x10, [x0, #7200]
	lsr x10, x24, #32
	adcs x25, x25, x10
	adcs x15, x15, x28
	adc x30, x30, x28
	subs x20, x7, x20
	sbcs x12, x7, x12
	sbcs x9, x13, x9
	sbcs x5, x1, x5
	sbc x10, x24, x10
	adds x3, x3, x11
	adcs x12, x12, x13
	adcs x9, x9, x1
	adcs x24, x5, x24
	adc x10, x10, x28
	adds x12, x6, x12
	adcs x9, x25, x9
	adcs x24, x15, x24
	adcs x10, x30, x10
	adc x20, x28, x28
	adds x7, x12, x27
	sbcs x11, x9, x23
	sbcs x3, x24, x28
	sbcs x13, x10, x22
	sbcs x20, x20, x28
	csel x12, x7, x12, hs
	csel x11, x11, x9, hs
	csel x3, x3, x24, hs
	csel x13, x13, x10, hs
	mul x1, x16, x2
	umulh x5, x16, x2
	mul x6, x16, x8
	adds x6, x5, x6
	umulh x25, x16, x8
	mul x15, x16, x17
	adcs x15, x15, x25
	umulh x30, x16, x17
	mul x20, x2, x8
	umulh x7, x2, x8
	mul x9, x2, x17
	adcs x9, x30, x9
	umulh x24, x2, x17
	mul x10, x8, x17
	adcs x10, x10, x24
	umulh x5, x8, x17
	adc x5, x5, x28
	adds x20, x15, x20
	adcs x7, x9, x7
	adcs x10, x10, x28
	adc x5, x5, x28
	adds x1, x1, x1
	adcs x6, x6, x6
	adcs x20, x20, x20
	adcs x7, x7, x7
	adcs x10, x10, x10
	adcs x5, x5, x5
	adc x25, x28, x28
	mul x30, x16, x16
	umulh x16, x16, x16
	adds x16, x1, x16
	mul x24, x2, x2
	adcs x6, x6, x24
	umulh x2, x2, x2
	adcs x2, x20, x2
	mul x15, x8, x8
	adcs x7, x7, x15
	umulh x8, x8, x8
	adcs x10, x10, x8
	mul x9, x17, x17
	adcs x5, x5, x9
	umulh x17, x17, x17
	adc x17, x25, x17
	lsl x1, x30, #32
	sub x24, x30, x1
	extr x20, x16, x30, #32
	adds x16, x16, x1
	adcs x6, x6, x20
	extr x15, x6, x16, #32
	adcs x2, x2, x15
	add x8, x2, x24
	extr x9, x8, x6, #32
	adcs x7, x7, x9
	lsr x25, x8, #32
	adcs x10, x10, x25
	adcs x5, x5, x28
	adc x17, x17, x28
	subs x1, x30, x1
	sbcs x20, x30, x20
	sbcs x15, x16, x15
	sbcs x9, x6, x9
	sbc x25, x8, x25
	adds x2, x2, x24
	adcs x20, x20, x16
	adcs x6, x15, x6
	adcs x8, x9, x8
	adc x25, x25, x28
	adds x20, x7, x20
	adcs x6, x10, x6
	adcs x8, x5, x8
	adcs x25, x17, x25
	adc x1, x28, x28
	adds x30, x20, x27
	sbcs x24, x6, x23
	sbcs x2, x8, x28
	sbcs x16, x25, x22
	sbcs x1, x1, x28
	csel x30, x30, x20, hs
	csel x24, x24, x6, hs
	csel x2, x2, x8, hs
	csel x25, x16, x25, hs
	ldr x15, [x0, #7144]
	subs x15, x30, x15
	ldr x9, [x0, #7136]
	sbcs x9, x24, x9
	ldr x7, [x0, #7128]
	sbcs x7, x2, x7
	ldr x10, [x0, #7112]
	sbcs x25, x25, x10
	movz x5, #65535, lsl #0
	movk x5, #65535, lsl #16
	orr x17, x5, x5
	movk x17, #65535, lsl #32
	movk x17, #65535, lsl #48
	orr x1, x27, x27
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	lsl x20, x4, #1
	extr x6, x26, x4, #63
	extr x8, x14, x26, #63
	extr x16, x21, x14, #63
	lsr x30, x21, #63
	sbc x24, x28, x28
	subs x12, x17, x12
	sbcs x11, x5, x11
	sbcs x3, x28, x3
	sbc x13, x1, x13
	adds x20, x4, x20
	adcs x6, x26, x6
	adcs x8, x14, x8
	adcs x16, x21, x16
	adc x30, x30, x28
	extr x30, x30, x16, #62
	extr x16, x16, x8, #62
	extr x8, x8, x6, #62
	extr x6, x6, x20, #62
	lsl x20, x20, #2
	adds x15, x15, x24
	lsl x2, x12, #3
	extr x10, x11, x12, #61
	extr x22, x3, x11, #61
	extr x23, x13, x3, #61
	str x1, [x0, #7112]
	lsr x1, x13, #61
	str x5, [x0, #7128]
	lsr x5, x24, #32
	adcs x5, x9, x5
	adcs x7, x7, x28
	lsl x9, x24, #32
	sub x9, x9, x24
	adc x9, x25, x9
	adds x12, x2, x12
	adcs x11, x10, x11
	adcs x3, x22, x3
	adcs x13, x23, x13
	adc x1, x1, x28
	adds x12, x12, x20
	adcs x6, x11, x6
	adcs x3, x3, x8
	adcs x16, x13, x16
	adc x30, x1, x30
	ldr x24, [x0, #7200]
	subs x15, x15, x24
	ldr x25, [x0, #7192]
	sbcs x5, x5, x25
	ldr x2, [x0, #7152]
	sbcs x7, x7, x2
	ldr x10, [x0, #7120]
	sbcs x9, x9, x10
	add x22, x30, x27
	lsl x23, x22, #32
	sub x20, x28, x22
	sub x11, x23, x27
	sbc x8, x28, x28
	adds x23, x16, x23
	adc x30, x30, x28
	subs x20, x12, x20
	sbcs x11, x6, x11
	sbcs x3, x3, x28
	sbcs x23, x23, x22
	sbc x22, x30, x22
	adds x15, x15, x8
	str x15, [x0, #576]
	lsl x13, x22, #32
	lsr x13, x13, #32
	sub x1, x28, x13
	lsr x16, x8, #32
	adcs x5, x5, x16
	str x5, [x0, #584]
	adcs x7, x7, x28
	str x7, [x0, #592]
	lsl x12, x8, #32
	sub x12, x12, x8
	adc x9, x9, x12
	adds x20, x20, x22
	str x9, [x0, #600]
	adcs x11, x11, x13
	adcs x3, x3, x28
	adc x23, x23, x1
	lsl x6, x4, #2
	extr x4, x26, x4, #62
	extr x26, x14, x26, #62
	subs x6, x6, x20
	extr x14, x21, x14, #62
	lsr x21, x21, #62
	sbcs x4, x4, x11
	sbcs x26, x26, x3
	sbcs x14, x14, x23
	sbc x21, x21, x28
	add x21, x21, x27
	lsl x30, x21, #32
	subs x15, x28, x30
	sbcs x16, x28, x28
	sbc x30, x30, x21
	adds x21, x6, x21
	adcs x15, x4, x15
	adcs x16, x26, x16
	adcs x14, x14, x30
	sbc x5, x28, x28
	adds x21, x21, x5
	str x21, [x0, #512]
	lsl x5, x5, #32
	lsr x5, x5, #32
	adcs x15, x15, x5
	str x15, [x0, #520]
	sub x5, x28, x5
	adcs x16, x16, x28
	adc x14, x14, x5
	mul x7, x24, x25
	str x16, [x0, #528]
	umulh x8, x24, x24
	str x14, [x0, #536]
	umulh x12, x24, x25
	ldr x22, [x0, #7184]
	mul x9, x20, x22
	ldr x13, [x0, #7176]
	mul x1, x20, x13
	ldr x6, [x0, #7168]
	mul x4, x20, x6
	ldr x26, [x0, #7160]
	mul x30, x20, x26
	umulh x21, x20, x22
	adds x21, x1, x21
	umulh x15, x20, x13
	adcs x4, x4, x15
	umulh x5, x20, x6
	adcs x30, x30, x5
	umulh x20, x20, x26
	adcs x20, x28, x20
	lsl x16, x9, #32
	adds x16, x21, x16
	lsr x14, x9, #32
	adcs x4, x4, x14
	ldr x1, [x0, #7104]
	mul x15, x9, x1
	adcs x30, x30, x15
	umulh x9, x9, x1
	adcs x20, x20, x9
	adcs x5, x28, x28
	mul x21, x11, x22
	adds x21, x16, x21
	mul x14, x11, x13
	adcs x4, x4, x14
	mul x15, x11, x6
	adcs x30, x30, x15
	mul x9, x11, x26
	adcs x20, x20, x9
	umulh x16, x11, x26
	adcs x5, x5, x16
	umulh x14, x11, x22
	adds x4, x4, x14
	umulh x15, x11, x13
	adcs x30, x30, x15
	umulh x11, x11, x6
	adcs x20, x20, x11
	adcs x5, x5, x28
	lsl x9, x21, #32
	adds x4, x4, x9
	lsr x16, x21, #32
	adcs x30, x30, x16
	mul x14, x21, x1
	adcs x20, x20, x14
	umulh x21, x21, x1
	adcs x21, x5, x21
	adcs x15, x28, x28
	mul x11, x3, x22
	adds x11, x4, x11
	mul x9, x3, x13
	adcs x9, x30, x9
	mul x16, x3, x6
	adcs x16, x20, x16
	mul x14, x3, x26
	adcs x14, x21, x14
	umulh x5, x3, x26
	adcs x5, x15, x5
	umulh x4, x3, x22
	adds x9, x9, x4
	umulh x30, x3, x13
	adcs x16, x16, x30
	umulh x3, x3, x6
	adcs x14, x14, x3
	adcs x5, x5, x28
	lsl x20, x11, #32
	adds x9, x9, x20
	lsr x21, x11, #32
	adcs x16, x16, x21
	mul x15, x11, x1
	adcs x15, x14, x15
	umulh x11, x11, x1
	adcs x5, x5, x11
	adcs x4, x28, x28
	mul x30, x23, x22
	adds x30, x9, x30
	umulh x22, x23, x22
	mul x3, x23, x13
	adcs x3, x16, x3
	umulh x13, x23, x13
	mul x20, x23, x6
	adcs x20, x15, x20
	umulh x6, x23, x6
	mul x21, x23, x26
	umulh x23, x23, x26
	adcs x21, x5, x21
	adcs x23, x4, x23
	adds x3, x3, x22
	mul x14, x24, x2
	adcs x20, x20, x13
	mul x11, x24, x24
	adcs x21, x21, x6
	umulh x9, x24, x2
	adcs x23, x23, x28
	adds x14, x12, x14
	mul x16, x25, x25
	lsl x15, x30, #32
	lsr x26, x30, #32
	mul x5, x30, x1
	umulh x30, x30, x1
	mul x4, x24, x10
	adcs x4, x4, x9
	umulh x24, x24, x10
	mul x22, x25, x2
	umulh x13, x25, x2
	mul x6, x25, x10
	adcs x6, x24, x6
	umulh x12, x25, x10
	umulh x25, x25, x25
	mul x1, x2, x10
	adcs x1, x1, x12
	umulh x9, x2, x10
	adc x9, x9, x28
	adds x22, x4, x22
	adcs x13, x6, x13
	adcs x1, x1, x28
	adc x9, x9, x28
	adds x3, x3, x15
	adcs x26, x20, x26
	adcs x21, x21, x5
	adcs x23, x23, x30
	adcs x24, x28, x28
	adds x7, x7, x7
	adcs x14, x14, x14
	adcs x22, x22, x22
	adcs x13, x13, x13
	adcs x1, x1, x1
	adcs x9, x9, x9
	adc x12, x28, x28
	adds x8, x7, x8
	adcs x14, x14, x16
	adcs x22, x22, x25
	lsl x4, x11, #32
	mul x6, x2, x2
	adcs x13, x13, x6
	umulh x2, x2, x2
	adcs x2, x1, x2
	extr x15, x8, x11, #32
	mul x20, x10, x10
	adcs x9, x9, x20
	umulh x10, x10, x10
	adc x10, x12, x10
	adds x8, x8, x4
	sub x5, x11, x4
	adcs x14, x14, x15
	extr x30, x14, x8, #32
	adcs x22, x22, x30
	add x7, x22, x5
	extr x16, x7, x14, #32
	adcs x13, x13, x16
	lsr x25, x7, #32
	adcs x2, x2, x25
	adcs x9, x9, x28
	adc x10, x10, x28
	subs x4, x11, x4
	sbcs x15, x11, x15
	sbcs x30, x8, x30
	sbcs x16, x14, x16
	sbc x25, x7, x25
	adds x5, x22, x5
	adcs x8, x15, x8
	adcs x14, x30, x14
	adcs x16, x16, x7
	adc x25, x25, x28
	adds x6, x3, x27
	ldr x1, [x0, #72]
	sbcs x20, x26, x1
	sbcs x12, x21, x28
	ldr x4, [x0, #88]
	sbcs x11, x23, x4
	sbcs x24, x24, x28
	csel x20, x20, x26, hs
	csel x3, x6, x3, hs
	csel x21, x12, x21, hs
	csel x23, x11, x23, hs
	adds x8, x13, x8
	adcs x14, x2, x14
	extr x22, x20, x3, #63
	extr x5, x21, x20, #63
	lsl x15, x3, #1
	extr x30, x23, x21, #63
	lsr x7, x23, #63
	adcs x9, x9, x16
	adcs x10, x10, x25
	adc x24, x28, x28
	adds x26, x8, x27
	sbcs x1, x14, x1
	sbcs x6, x9, x28
	sbcs x4, x10, x4
	sbcs x24, x24, x28
	csel x26, x26, x8, hs
	csel x14, x1, x14, hs
	csel x9, x6, x9, hs
	csel x10, x4, x10, hs
	adds x3, x3, x15
	adcs x20, x20, x22
	adcs x21, x21, x5
	adcs x23, x23, x30
	adc x7, x7, x28
	subs x26, x17, x26
	ldr x12, [x0, #7128]
	sbcs x12, x12, x14
	lsl x11, x26, #3
	sbcs x9, x28, x9
	extr x26, x12, x26, #61
	ldr x13, [x0, #7112]
	sbc x10, x13, x10
	adds x3, x11, x3
	extr x12, x9, x12, #61
	extr x9, x10, x9, #61
	lsr x10, x10, #61
	adcs x20, x26, x20
	adcs x12, x12, x21
	adcs x9, x9, x23
	adc x7, x10, x7
	add x2, x7, x27
	lsl x16, x2, #32
	sub x25, x28, x2
	sub x27, x16, x27
	adds x9, x9, x16
	adc x7, x7, x28
	subs x25, x3, x25
	sbcs x27, x20, x27
	sbcs x12, x12, x28
	sbcs x9, x9, x2
	sbc x7, x7, x2
	lsl x24, x7, #32
	adds x25, x25, x7
	lsr x24, x24, #32
	str x25, [x0, #544]
	adcs x27, x27, x24
	sub x24, x28, x24
	adcs x28, x12, x28
	str x27, [x0, #552]
	adc x9, x9, x24
	str x28, [x0, #560]
	str x9, [x0, #568]
	sub x19, x19, #2048
	lsr x4, x19, #11
	cbnz x4, 23b
	movz x16, #5, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	movz x2, #0, lsl #0
	add x2, x2, x2
	ldrb w4, [x16, #1828]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1827]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1826]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1825]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1824]
	add x2, x2, x4
	sub x3, x2, #16
	lsr x4, x3, #63
	movz x9, #0, lsl #0
	sub x4, x9, x4
	eor x2, x3, x4
	sub x2, x2, x4
	movz x5, #1, lsl #0
	dup v31.2d, x5
	dup v30.2d, x2
	movi v28.2d, #0
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
	ldr x1, [x0, #576]
	add v28.2d, v28.2d, v31.2d
	ldr x2, [x0, #584]
	mul x3, x1, x2
	cmeq v29.2d, v28.2d, v30.2d
	umulh x4, x1, x1
	umulh x5, x1, x2
	ldr x6, [x0, #592]
	ldr q18, [x0, #2816]
	mul x7, x1, x6
	mul x8, x1, x1
	umulh x9, x1, x6
	ldr q19, [x0, #2832]
	mul x10, x2, x2
	ldr x11, [x0, #600]
	mul x12, x1, x11
	ldr q20, [x0, #2848]
	mul x13, x2, x6
	umulh x14, x2, x2
	lsl x15, x8, #32
	ldr q21, [x0, #2864]
	adds x7, x5, x7
	umulh x16, x1, x11
	ldr q22, [x0, #2880]
	umulh x17, x2, x6
	mul x20, x2, x11
	adcs x12, x12, x9
	ldr q23, [x0, #2896]
	umulh x21, x2, x11
	mul x22, x6, x11
	umulh x23, x6, x11
	ldr q24, [x0, #2912]
	sub x24, x8, x15
	mul x25, x6, x6
	adcs x20, x16, x20
	ldr q25, [x0, #2928]
	umulh x26, x6, x6
	adcs x22, x22, x21
	mul x27, x11, x11
	ldr q26, [x0, #2944]
	movz x28, #0, lsl #0
	adc x23, x23, x28
	adds x13, x12, x13
	ldr q27, [x0, #2960]
	umulh x30, x11, x11
	adcs x17, x20, x17
	bit v0.16b, v18.16b, v29.16b
	movz x5, #1, lsl #0
	sub x9, x28, x5
	adcs x22, x22, x28
	bit v1.16b, v19.16b, v29.16b
	adc x23, x23, x28
	adds x3, x3, x3
	adcs x7, x7, x7
	bit v2.16b, v20.16b, v29.16b
	adcs x13, x13, x13
	adcs x17, x17, x17
	adcs x22, x22, x22
	bit v3.16b, v21.16b, v29.16b
	adcs x23, x23, x23
	adc x16, x28, x28
	adds x4, x3, x4
	bit v4.16b, v22.16b, v29.16b
	adcs x7, x7, x10
	ldr x21, [x0, #544]
	ldr x12, [x0, #552]
	bit v5.16b, v23.16b, v29.16b
	mul x20, x21, x12
	adcs x14, x13, x14
	bit v6.16b, v24.16b, v29.16b
	adcs x17, x17, x25
	adcs x22, x22, x26
	extr x3, x4, x8, #32
	bit v7.16b, v25.16b, v29.16b
	adcs x23, x23, x27
	umulh x10, x21, x21
	adc x30, x16, x30
	bit v16.16b, v26.16b, v29.16b
	adds x4, x4, x15
	umulh x13, x21, x12
	adcs x7, x7, x3
	bit v17.16b, v27.16b, v29.16b
	extr x25, x7, x4, #32
	adcs x14, x14, x25
	add x26, x14, x24
	add v28.2d, v28.2d, v31.2d
	extr x27, x26, x7, #32
	adcs x17, x17, x27
	lsr x16, x26, #32
	cmeq v29.2d, v28.2d, v30.2d
	adcs x22, x22, x16
	adcs x23, x23, x28
	ldr q18, [x0, #2976]
	adc x30, x30, x28
	subs x15, x8, x15
	sbcs x3, x8, x3
	ldr q19, [x0, #2992]
	sbcs x25, x4, x25
	sbcs x27, x7, x27
	sbc x16, x26, x16
	ldr q20, [x0, #3008]
	adds x14, x14, x24
	adcs x3, x3, x4
	orr x15, x5, x5
	ldr q21, [x0, #3024]
	movk x15, #0, lsl #16
	adcs x7, x25, x7
	ldr x8, [x0, #560]
	ldr q22, [x0, #3040]
	mul x24, x21, x8
	adcs x26, x27, x26
	ldr q23, [x0, #3056]
	movk x15, #65535, lsl #32
	movk x15, #65535, lsl #48
	adc x16, x16, x28
	ldr q24, [x0, #3072]
	adds x24, x13, x24
	mul x14, x21, x21
	umulh x4, x21, x8
	ldr q25, [x0, #3088]
	ldr x25, [x0, #568]
	mul x27, x21, x25
	adcs x27, x27, x4
	ldr q26, [x0, #3104]
	umulh x13, x21, x25
	mul x4, x12, x8
	str x15, [x0, #7104]
	ldr q27, [x0, #3120]
	umulh x15, x12, x8
	str x9, [x0, #7112]
	mul x9, x12, x25
	bit v0.16b, v18.16b, v29.16b
	adcs x9, x13, x9
	umulh x13, x12, x25
	bit v1.16b, v19.16b, v29.16b
	mul x11, x8, x25
	adcs x11, x11, x13
	umulh x13, x8, x25
	bit v2.16b, v20.16b, v29.16b
	adc x13, x13, x28
	adds x3, x17, x3
	adcs x7, x22, x7
	bit v3.16b, v21.16b, v29.16b
	adcs x26, x23, x26
	adcs x16, x30, x16
	adc x17, x28, x28
	bit v4.16b, v22.16b, v29.16b
	adds x4, x27, x4
	adcs x15, x9, x15
	adcs x11, x11, x28
	bit v5.16b, v23.16b, v29.16b
	adc x13, x13, x28
	adds x20, x20, x20
	adcs x24, x24, x24
	bit v6.16b, v24.16b, v29.16b
	adcs x4, x4, x4
	adcs x15, x15, x15
	bit v7.16b, v25.16b, v29.16b
	adcs x11, x11, x11
	adcs x13, x13, x13
	adc x22, x28, x28
	bit v16.16b, v26.16b, v29.16b
	adds x10, x20, x10
	mul x23, x12, x12
	adcs x24, x24, x23
	bit v17.16b, v27.16b, v29.16b
	umulh x30, x12, x12
	adcs x4, x4, x30
	mul x27, x8, x8
	add v28.2d, v28.2d, v31.2d
	adcs x15, x15, x27
	umulh x9, x8, x8
	adcs x11, x11, x9
	cmeq v29.2d, v28.2d, v30.2d
	mul x20, x25, x25
	adcs x13, x13, x20
	umulh x23, x25, x25
	ldr q18, [x0, #3136]
	adc x23, x22, x23
	adds x30, x3, x5
	ldr q19, [x0, #3152]
	ldr x27, [x0, #72]
	sbcs x9, x7, x27
	sbcs x20, x26, x28
	ldr q20, [x0, #3168]
	ldr x22, [x0, #88]
	sbcs x27, x16, x22
	sbcs x17, x17, x28
	ldr q21, [x0, #3184]
	csel x30, x30, x3, hs
	csel x7, x9, x7, hs
	csel x26, x20, x26, hs
	ldr q22, [x0, #3200]
	csel x27, x27, x16, hs
	adds x1, x21, x1
	adcs x2, x12, x2
	ldr q23, [x0, #3216]
	adcs x8, x8, x6
	ldr x17, [x0, #600]
	ldr q24, [x0, #3232]
	adcs x17, x25, x17
	extr x3, x10, x14, #32
	lsl x9, x14, #32
	ldr q25, [x0, #3248]
	sub x20, x14, x9
	adc x16, x28, x28
	adds x10, x10, x9
	ldr q26, [x0, #3264]
	adcs x24, x24, x3
	extr x21, x24, x10, #32
	adcs x4, x4, x21
	ldr q27, [x0, #3280]
	add x12, x4, x20
	extr x6, x12, x24, #32
	adcs x15, x15, x6
	bit v0.16b, v18.16b, v29.16b
	lsr x25, x12, #32
	adcs x11, x11, x25
	adcs x13, x13, x28
	bit v1.16b, v19.16b, v29.16b
	adc x23, x23, x28
	subs x9, x14, x9
	bit v2.16b, v20.16b, v29.16b
	sbcs x3, x14, x3
	sbcs x21, x10, x21
	sbcs x6, x24, x6
	bit v3.16b, v21.16b, v29.16b
	sbc x25, x12, x25
	adds x4, x4, x20
	adcs x3, x3, x10
	bit v4.16b, v22.16b, v29.16b
	adcs x24, x21, x24
	adcs x12, x6, x12
	adc x25, x25, x28
	bit v5.16b, v23.16b, v29.16b
	adds x3, x15, x3
	adcs x24, x11, x24
	adcs x12, x13, x12
	bit v6.16b, v24.16b, v29.16b
	adcs x25, x23, x25
	adc x9, x28, x28
	ldr x14, [x0, #512]
	bit v7.16b, v25.16b, v29.16b
	subs x20, x14, x30
	ldr x4, [x0, #520]
	bit v16.16b, v26.16b, v29.16b
	sbcs x10, x4, x7
	ldr x21, [x0, #528]
	sbcs x6, x21, x26
	bit v17.16b, v27.16b, v29.16b
	ldr x15, [x0, #536]
	sbcs x11, x15, x27
	sbc x13, x28, x28
	add v28.2d, v28.2d, v31.2d
	adds x20, x20, x13
	lsr x23, x13, #32
	adcs x23, x10, x23
	cmeq v29.2d, v28.2d, v30.2d
	adcs x6, x6, x28
	lsl x10, x13, #32
	sub x13, x10, x13
	ldr q18, [x0, #3296]
	adc x11, x11, x13
	adds x10, x3, x5
	ldr x13, [x0, #72]
	ldr q19, [x0, #3312]
	sbcs x5, x24, x13
	sbcs x13, x12, x28
	ldr q20, [x0, #3328]
	str x16, [x0, #7120]
	sbcs x16, x25, x22
	sbcs x9, x9, x28
	ldr q21, [x0, #3344]
	csel x10, x10, x3, hs
	csel x5, x5, x24, hs
	csel x13, x13, x12, hs
	ldr q22, [x0, #3360]
	csel x25, x16, x25, hs
	adds x9, x14, x30
	adcs x3, x4, x7
	ldr q23, [x0, #3376]
	adcs x24, x21, x26
	adcs x12, x15, x27
	ldr x16, [x0, #7112]
	ldr q24, [x0, #3392]
	csel x16, x16, x28, hs
	subs x9, x9, x16
	str x27, [x0, #7112]
	ldr q25, [x0, #3408]
	lsl x27, x16, #32
	sub x16, x27, x16
	ldr q26, [x0, #3424]
	lsr x27, x27, #32
	sbcs x3, x3, x27
	sbcs x24, x24, x28
	ldr q27, [x0, #3440]
	sbc x16, x12, x16
	mul x27, x9, x20
	mul x12, x9, x23
	bit v0.16b, v18.16b, v29.16b
	str x26, [x0, #7128]
	mul x26, x9, x6
	str x7, [x0, #7136]
	bit v1.16b, v19.16b, v29.16b
	mul x7, x9, x11
	str x30, [x0, #7144]
	umulh x30, x9, x20
	bit v2.16b, v20.16b, v29.16b
	adds x12, x12, x30
	umulh x30, x9, x23
	bit v3.16b, v21.16b, v29.16b
	adcs x30, x26, x30
	umulh x26, x9, x6
	adcs x26, x7, x26
	bit v4.16b, v22.16b, v29.16b
	umulh x9, x9, x11
	adcs x9, x28, x9
	lsl x7, x27, #32
	bit v5.16b, v23.16b, v29.16b
	adds x12, x12, x7
	lsr x7, x27, #32
	adcs x30, x30, x7
	bit v6.16b, v24.16b, v29.16b
	ldr x7, [x0, #7104]
	mul x15, x27, x7
	adcs x26, x26, x15
	bit v7.16b, v25.16b, v29.16b
	umulh x27, x27, x7
	adcs x9, x9, x27
	adcs x15, x28, x28
	bit v16.16b, v26.16b, v29.16b
	mul x27, x3, x20
	adds x27, x12, x27
	bit v17.16b, v27.16b, v29.16b
	mul x12, x3, x23
	adcs x30, x30, x12
	mul x12, x3, x6
	add v28.2d, v28.2d, v31.2d
	adcs x26, x26, x12
	mul x12, x3, x11
	adcs x12, x9, x12
	cmeq v29.2d, v28.2d, v30.2d
	umulh x9, x3, x11
	adcs x9, x15, x9
	umulh x15, x3, x20
	ldr q18, [x0, #3456]
	adds x30, x30, x15
	umulh x15, x3, x23
	adcs x15, x26, x15
	ldr q19, [x0, #3472]
	umulh x3, x3, x6
	adcs x12, x12, x3
	adcs x9, x9, x28
	ldr q20, [x0, #3488]
	lsl x26, x27, #32
	adds x30, x30, x26
	ldr q21, [x0, #3504]
	lsr x3, x27, #32
	adcs x3, x15, x3
	mul x26, x27, x7
	ldr q22, [x0, #3520]
	adcs x12, x12, x26
	umulh x27, x27, x7
	adcs x9, x9, x27
	ldr q23, [x0, #3536]
	adcs x15, x28, x28
	mul x26, x24, x20
	adds x30, x30, x26
	ldr q24, [x0, #3552]
	mul x27, x24, x23
	adcs x3, x3, x27
	mul x26, x24, x6
	ldr q25, [x0, #3568]
	adcs x26, x12, x26
	mul x27, x24, x11
	adcs x9, x9, x27
	ldr q26, [x0, #3584]
	umulh x12, x24, x11
	adcs x12, x15, x12
	ldr q27, [x0, #3600]
	umulh x27, x24, x20
	adds x27, x3, x27
	umulh x15, x24, x23
	bit v0.16b, v18.16b, v29.16b
	adcs x26, x26, x15
	umulh x24, x24, x6
	adcs x9, x9, x24
	bit v1.16b, v19.16b, v29.16b
	adcs x12, x12, x28
	lsl x3, x30, #32
	adds x3, x27, x3
	bit v2.16b, v20.16b, v29.16b
	lsr x15, x30, #32
	adcs x26, x26, x15
	mul x24, x30, x7
	bit v3.16b, v21.16b, v29.16b
	adcs x9, x9, x24
	umulh x30, x30, x7
	bit v4.16b, v22.16b, v29.16b
	adcs x12, x12, x30
	adcs x27, x28, x28
	mul x15, x16, x20
	bit v5.16b, v23.16b, v29.16b
	adds x3, x3, x15
	umulh x20, x16, x20
	mul x24, x16, x23
	bit v6.16b, v24.16b, v29.16b
	adcs x24, x26, x24
	umulh x23, x16, x23
	mul x30, x16, x6
	bit v7.16b, v25.16b, v29.16b
	adcs x9, x9, x30
	umulh x6, x16, x6
	mul x15, x16, x11
	bit v16.16b, v26.16b, v29.16b
	umulh x11, x16, x11
	adcs x12, x12, x15
	adcs x11, x27, x11
	bit v17.16b, v27.16b, v29.16b
	adds x24, x24, x20
	adcs x9, x9, x23
	add v28.2d, v28.2d, v31.2d
	adcs x12, x12, x6
	adcs x11, x11, x28
	lsl x26, x3, #32
	cmeq v29.2d, v28.2d, v30.2d
	adds x24, x24, x26
	lsr x30, x3, #32
	adcs x9, x9, x30
	ldr q18, [x0, #3616]
	mul x16, x3, x7
	adcs x12, x12, x16
	umulh x3, x3, x7
	ldr q19, [x0, #3632]
	adcs x11, x11, x3
	adcs x15, x28, x28
	movz x27, #1, lsl #0
	ldr q20, [x0, #3648]
	adds x20, x24, x27
	ldr x23, [x0, #72]
	sbcs x6, x9, x23
	ldr q21, [x0, #3664]
	sbcs x26, x12, x28
	sbcs x30, x11, x22
	ldr q22, [x0, #3680]
	sbcs x15, x15, x28
	csel x24, x20, x24, hs
	csel x9, x6, x9, hs
	ldr q23, [x0, #3696]
	csel x12, x26, x12, hs
	csel x11, x30, x11, hs
	adds x16, x1, x27
	ldr q24, [x0, #3712]
	sbcs x3, x2, x23
	sbcs x15, x8, x28
	sbcs x20, x17, x22
	ldr q25, [x0, #3728]
	ldr x6, [x0, #7120]
	sbcs x6, x6, x28
	csel x16, x16, x1, hs
	ldr q26, [x0, #3744]
	csel x2, x3, x2, hs
	csel x8, x15, x8, hs
	csel x17, x20, x17, hs
	ldr q27, [x0, #3760]
	mul x26, x14, x10
	mul x30, x14, x5
	bit v0.16b, v18.16b, v29.16b
	mul x6, x14, x13
	mul x1, x14, x25
	umulh x3, x14, x10
	bit v1.16b, v19.16b, v29.16b
	adds x3, x30, x3
	umulh x15, x14, x5
	adcs x15, x6, x15
	bit v2.16b, v20.16b, v29.16b
	umulh x20, x14, x13
	adcs x1, x1, x20
	umulh x14, x14, x25
	bit v3.16b, v21.16b, v29.16b
	adcs x14, x28, x14
	lsl x30, x26, #32
	adds x3, x3, x30
	bit v4.16b, v22.16b, v29.16b
	lsr x6, x26, #32
	adcs x15, x15, x6
	bit v5.16b, v23.16b, v29.16b
	mul x20, x26, x7
	adcs x1, x1, x20
	umulh x26, x26, x7
	bit v6.16b, v24.16b, v29.16b
	adcs x14, x14, x26
	adcs x30, x28, x28
	mul x6, x4, x10
	bit v7.16b, v25.16b, v29.16b
	adds x3, x3, x6
	mul x20, x4, x5
	adcs x15, x15, x20
	bit v16.16b, v26.16b, v29.16b
	mul x26, x4, x13
	adcs x26, x1, x26
	mul x6, x4, x25
	bit v17.16b, v27.16b, v29.16b
	adcs x14, x14, x6
	umulh x20, x4, x25
	adcs x20, x30, x20
	add v28.2d, v28.2d, v31.2d
	umulh x1, x4, x10
	adds x1, x15, x1
	cmeq v29.2d, v28.2d, v30.2d
	umulh x6, x4, x5
	adcs x26, x26, x6
	umulh x4, x4, x13
	ldr q18, [x0, #3776]
	adcs x14, x14, x4
	adcs x20, x20, x28
	lsl x30, x3, #32
	ldr q19, [x0, #3792]
	adds x30, x1, x30
	lsr x15, x3, #32
	adcs x26, x26, x15
	ldr q20, [x0, #3808]
	mul x6, x3, x7
	adcs x14, x14, x6
	umulh x3, x3, x7
	ldr q21, [x0, #3824]
	adcs x20, x20, x3
	adcs x4, x28, x28
	mul x1, x21, x10
	ldr q22, [x0, #3840]
	adds x30, x30, x1
	mul x15, x21, x5
	ldr q23, [x0, #3856]
	adcs x15, x26, x15
	mul x6, x21, x13
	adcs x14, x14, x6
	ldr q24, [x0, #3872]
	mul x3, x21, x25
	adcs x20, x20, x3
	umulh x1, x21, x25
	ldr q25, [x0, #3888]
	adcs x1, x4, x1
	umulh x26, x21, x10
	adds x15, x15, x26
	ldr q26, [x0, #3904]
	umulh x6, x21, x5
	adcs x14, x14, x6
	umulh x21, x21, x13
	ldr q27, [x0, #3920]
	adcs x20, x20, x21
	adcs x1, x1, x28
	lsl x3, x30, #32
	bit v0.16b, v18.16b, v29.16b
	adds x15, x15, x3
	lsr x4, x30, #32
	bit v1.16b, v19.16b, v29.16b
	adcs x14, x14, x4
	mul x26, x30, x7
	adcs x20, x20, x26
	bit v2.16b, v20.16b, v29.16b
	umulh x30, x30, x7
	adcs x1, x1, x30
	adcs x6, x28, x28
	bit v3.16b, v21.16b, v29.16b
	ldr x21, [x0, #536]
	mul x3, x21, x10
	adds x3, x15, x3
	bit v4.16b, v22.16b, v29.16b
	mul x4, x21, x5
	adcs x4, x14, x4
	mul x26, x21, x13
	bit v5.16b, v23.16b, v29.16b
	adcs x26, x20, x26
	mul x30, x21, x25
	adcs x1, x1, x30
	bit v6.16b, v24.16b, v29.16b
	umulh x15, x21, x25
	adcs x15, x6, x15
	bit v7.16b, v25.16b, v29.16b
	umulh x14, x21, x10
	adds x4, x4, x14
	umulh x20, x21, x5
	bit v16.16b, v26.16b, v29.16b
	adcs x26, x26, x20
	umulh x21, x21, x13
	adcs x21, x1, x21
	bit v17.16b, v27.16b, v29.16b
	adcs x15, x15, x28
	lsl x30, x3, #32
	adds x4, x4, x30
	add v28.2d, v28.2d, v31.2d
	lsr x6, x3, #32
	adcs x26, x26, x6
	mul x14, x3, x7
	cmeq v29.2d, v28.2d, v30.2d
	adcs x14, x21, x14
	umulh x3, x3, x7
	ldr q18, [x0, #3936]
	adcs x15, x15, x3
	adcs x20, x28, x28
	adds x1, x4, x27
	ldr q19, [x0, #3952]
	sbcs x30, x26, x23
	sbcs x6, x14, x28
	sbcs x21, x15, x22
	ldr q20, [x0, #3968]
	sbcs x20, x20, x28
	csel x4, x1, x4, hs
	csel x26, x30, x26, hs
	ldr q21, [x0, #3984]
	csel x14, x6, x14, hs
	csel x21, x21, x15, hs
	mul x3, x24, x9
	ldr q22, [x0, #4000]
	umulh x20, x24, x9
	mul x1, x24, x12
	adds x1, x20, x1
	ldr q23, [x0, #4016]
	umulh x30, x24, x12
	mul x6, x24, x11
	ldr q24, [x0, #4032]
	adcs x30, x6, x30
	umulh x15, x24, x11
	mul x20, x9, x12
	ldr q25, [x0, #4048]
	umulh x6, x9, x12
	mul x7, x9, x11
	adcs x7, x15, x7
	ldr q26, [x0, #4064]
	umulh x15, x9, x11
	str x25, [x0, #7120]
	mul x25, x12, x11
	ldr q27, [x0, #4080]
	adcs x25, x25, x15
	umulh x15, x12, x11
	adc x15, x15, x28
	bit v0.16b, v18.16b, v29.16b
	adds x20, x30, x20
	adcs x6, x7, x6
	adcs x25, x25, x28
	bit v1.16b, v19.16b, v29.16b
	adc x15, x15, x28
	adds x3, x3, x3
	bit v2.16b, v20.16b, v29.16b
	adcs x1, x1, x1
	adcs x20, x20, x20
	adcs x6, x6, x6
	bit v3.16b, v21.16b, v29.16b
	adcs x25, x25, x25
	adcs x15, x15, x15
	adc x30, x28, x28
	bit v4.16b, v22.16b, v29.16b
	mul x7, x24, x24
	str x13, [x0, #7152]
	umulh x13, x24, x24
	bit v5.16b, v23.16b, v29.16b
	adds x13, x3, x13
	mul x3, x9, x9
	adcs x1, x1, x3
	bit v6.16b, v24.16b, v29.16b
	umulh x3, x9, x9
	adcs x3, x20, x3
	mul x20, x12, x12
	bit v7.16b, v25.16b, v29.16b
	adcs x6, x6, x20
	umulh x20, x12, x12
	bit v16.16b, v26.16b, v29.16b
	adcs x25, x25, x20
	mul x20, x11, x11
	adcs x15, x15, x20
	bit v17.16b, v27.16b, v29.16b
	umulh x20, x11, x11
	adc x30, x30, x20
	lsl x20, x7, #32
	add v28.2d, v28.2d, v31.2d
	str x11, [x0, #7160]
	sub x11, x7, x20
	str x12, [x0, #7168]
	cmeq v29.2d, v28.2d, v30.2d
	extr x12, x13, x7, #32
	adds x13, x13, x20
	adcs x1, x1, x12
	ldr q18, [x0, #4096]
	str x9, [x0, #7176]
	extr x9, x1, x13, #32
	ldr q19, [x0, #4112]
	adcs x3, x3, x9
	str x24, [x0, #7184]
	add x24, x3, x11
	ldr q20, [x0, #4128]
	str x5, [x0, #7192]
	extr x5, x24, x1, #32
	adcs x6, x6, x5
	ldr q21, [x0, #4144]
	str x10, [x0, #7200]
	lsr x10, x24, #32
	adcs x25, x25, x10
	ldr q22, [x0, #4160]
	adcs x15, x15, x28
	adc x30, x30, x28
	subs x20, x7, x20
	ldr q23, [x0, #4176]
	sbcs x12, x7, x12
	sbcs x9, x13, x9
	sbcs x5, x1, x5
	ldr q24, [x0, #4192]
	sbc x10, x24, x10
	adds x3, x3, x11
	ldr q25, [x0, #4208]
	adcs x12, x12, x13
	adcs x9, x9, x1
	adcs x24, x5, x24
	ldr q26, [x0, #4224]
	adc x10, x10, x28
	adds x12, x6, x12
	adcs x9, x25, x9
	ldr q27, [x0, #4240]
	adcs x24, x15, x24
	adcs x10, x30, x10
	adc x20, x28, x28
	bit v0.16b, v18.16b, v29.16b
	adds x7, x12, x27
	sbcs x11, x9, x23
	sbcs x3, x24, x28
	bit v1.16b, v19.16b, v29.16b
	sbcs x13, x10, x22
	sbcs x20, x20, x28
	csel x12, x7, x12, hs
	bit v2.16b, v20.16b, v29.16b
	csel x11, x11, x9, hs
	csel x3, x3, x24, hs
	bit v3.16b, v21.16b, v29.16b
	csel x13, x13, x10, hs
	mul x1, x16, x2
	umulh x5, x16, x2
	bit v4.16b, v22.16b, v29.16b
	mul x6, x16, x8
	adds x6, x5, x6
	umulh x25, x16, x8
	bit v5.16b, v23.16b, v29.16b
	mul x15, x16, x17
	adcs x15, x15, x25
	umulh x30, x16, x17
	bit v6.16b, v24.16b, v29.16b
	mul x20, x2, x8
	umulh x7, x2, x8
	mul x9, x2, x17
	bit v7.16b, v25.16b, v29.16b
	adcs x9, x30, x9
	umulh x24, x2, x17
	mul x10, x8, x17
	bit v16.16b, v26.16b, v29.16b
	adcs x10, x10, x24
	umulh x5, x8, x17
	bit v17.16b, v27.16b, v29.16b
	adc x5, x5, x28
	adds x20, x15, x20
	adcs x7, x9, x7
	add v28.2d, v28.2d, v31.2d
	adcs x10, x10, x28
	adc x5, x5, x28
	adds x1, x1, x1
	cmeq v29.2d, v28.2d, v30.2d
	adcs x6, x6, x6
	adcs x20, x20, x20
	adcs x7, x7, x7
	ldr q18, [x0, #4256]
	adcs x10, x10, x10
	adcs x5, x5, x5
	adc x25, x28, x28
	ldr q19, [x0, #4272]
	mul x30, x16, x16
	umulh x16, x16, x16
	ldr q20, [x0, #4288]
	adds x16, x1, x16
	mul x24, x2, x2
	adcs x6, x6, x24
	ldr q21, [x0, #4304]
	umulh x2, x2, x2
	adcs x2, x20, x2
	mul x15, x8, x8
	ldr q22, [x0, #4320]
	adcs x7, x7, x15
	umulh x8, x8, x8
	adcs x10, x10, x8
	ldr q23, [x0, #4336]
	mul x9, x17, x17
	adcs x5, x5, x9
	umulh x17, x17, x17
	ldr q24, [x0, #4352]
	adc x17, x25, x17
	lsl x1, x30, #32
	sub x24, x30, x1
	ldr q25, [x0, #4368]
	extr x20, x16, x30, #32
	adds x16, x16, x1
	ldr q26, [x0, #4384]
	adcs x6, x6, x20
	extr x15, x6, x16, #32
	adcs x2, x2, x15
	ldr q27, [x0, #4400]
	add x8, x2, x24
	extr x9, x8, x6, #32
	adcs x7, x7, x9
	bit v0.16b, v18.16b, v29.16b
	lsr x25, x8, #32
	adcs x10, x10, x25
	adcs x5, x5, x28
	bit v1.16b, v19.16b, v29.16b
	adc x17, x17, x28
	subs x1, x30, x1
	sbcs x20, x30, x20
	bit v2.16b, v20.16b, v29.16b
	sbcs x15, x16, x15
	sbcs x9, x6, x9
	sbc x25, x8, x25
	bit v3.16b, v21.16b, v29.16b
	adds x2, x2, x24
	adcs x20, x20, x16
	bit v4.16b, v22.16b, v29.16b
	adcs x6, x15, x6
	adcs x8, x9, x8
	adc x25, x25, x28
	bit v5.16b, v23.16b, v29.16b
	adds x20, x7, x20
	adcs x6, x10, x6
	adcs x8, x5, x8
	bit v6.16b, v24.16b, v29.16b
	adcs x25, x17, x25
	adc x1, x28, x28
	adds x30, x20, x27
	bit v7.16b, v25.16b, v29.16b
	sbcs x24, x6, x23
	sbcs x2, x8, x28
	sbcs x16, x25, x22
	bit v16.16b, v26.16b, v29.16b
	sbcs x1, x1, x28
	csel x30, x30, x20, hs
	csel x24, x24, x6, hs
	bit v17.16b, v27.16b, v29.16b
	csel x2, x2, x8, hs
	csel x25, x16, x25, hs
	add v28.2d, v28.2d, v31.2d
	ldr x15, [x0, #7144]
	subs x15, x30, x15
	ldr x9, [x0, #7136]
	cmeq v29.2d, v28.2d, v30.2d
	sbcs x9, x24, x9
	ldr x7, [x0, #7128]
	sbcs x7, x2, x7
	ldr q18, [x0, #4416]
	ldr x10, [x0, #7112]
	sbcs x25, x25, x10
	movz x5, #65535, lsl #0
	ldr q19, [x0, #4432]
	movk x5, #65535, lsl #16
	orr x17, x5, x5
	movk x17, #65535, lsl #32
	ldr q20, [x0, #4448]
	movk x17, #65535, lsl #48
	orr x1, x27, x27
	movk x1, #65535, lsl #32
	ldr q21, [x0, #4464]
	movk x1, #65535, lsl #48
	lsl x20, x4, #1
	ldr q22, [x0, #4480]
	extr x6, x26, x4, #63
	extr x8, x14, x26, #63
	extr x16, x21, x14, #63
	ldr q23, [x0, #4496]
	lsr x30, x21, #63
	sbc x24, x28, x28
	subs x12, x17, x12
	ldr q24, [x0, #4512]
	sbcs x11, x5, x11
	sbcs x3, x28, x3
	sbc x13, x1, x13
	ldr q25, [x0, #4528]
	adds x20, x4, x20
	adcs x6, x26, x6
	adcs x8, x14, x8
	ldr q26, [x0, #4544]
	adcs x16, x21, x16
	adc x30, x30, x28
	ldr q27, [x0, #4560]
	extr x30, x30, x16, #62
	extr x16, x16, x8, #62
	extr x8, x8, x6, #62
	bit v0.16b, v18.16b, v29.16b
	extr x6, x6, x20, #62
	lsl x20, x20, #2
	adds x15, x15, x24
	bit v1.16b, v19.16b, v29.16b
	lsl x2, x12, #3
	extr x10, x11, x12, #61
	extr x22, x3, x11, #61
	bit v2.16b, v20.16b, v29.16b
	extr x23, x13, x3, #61
	str x1, [x0, #7112]
	lsr x1, x13, #61
	bit v3.16b, v21.16b, v29.16b
	str x5, [x0, #7128]
	lsr x5, x24, #32
	adcs x5, x9, x5
	bit v4.16b, v22.16b, v29.16b
	adcs x7, x7, x28
	lsl x9, x24, #32
	bit v5.16b, v23.16b, v29.16b
	sub x9, x9, x24
	adc x9, x25, x9
	adds x12, x2, x12
	bit v6.16b, v24.16b, v29.16b
	adcs x11, x10, x11
	adcs x3, x22, x3
	adcs x13, x23, x13
	bit v7.16b, v25.16b, v29.16b
	adc x1, x1, x28
	adds x12, x12, x20
	adcs x6, x11, x6
	bit v16.16b, v26.16b, v29.16b
	adcs x3, x3, x8
	adcs x16, x13, x16
	adc x30, x1, x30
	bit v17.16b, v27.16b, v29.16b
	ldr x24, [x0, #7200]
	subs x15, x15, x24
	ldr x25, [x0, #7192]
	add v28.2d, v28.2d, v31.2d
	sbcs x5, x5, x25
	ldr x2, [x0, #7152]
	cmeq v29.2d, v28.2d, v30.2d
	sbcs x7, x7, x2
	ldr x10, [x0, #7120]
	sbcs x9, x9, x10
	ldr q18, [x0, #4576]
	add x22, x30, x27
	lsl x23, x22, #32
	sub x20, x28, x22
	ldr q19, [x0, #4592]
	sub x11, x23, x27
	sbc x8, x28, x28
	adds x23, x16, x23
	ldr q20, [x0, #4608]
	adc x30, x30, x28
	subs x20, x12, x20
	sbcs x11, x6, x11
	ldr q21, [x0, #4624]
	sbcs x3, x3, x28
	sbcs x23, x23, x22
	sbc x22, x30, x22
	ldr q22, [x0, #4640]
	adds x15, x15, x8
	str x15, [x0, #576]
	ldr q23, [x0, #4656]
	lsl x13, x22, #32
	lsr x13, x13, #32
	sub x1, x28, x13
	ldr q24, [x0, #4672]
	lsr x16, x8, #32
	adcs x5, x5, x16
	str x5, [x0, #584]
	ldr q25, [x0, #4688]
	adcs x7, x7, x28
	str x7, [x0, #592]
	lsl x12, x8, #32
	ldr q26, [x0, #4704]
	sub x12, x12, x8
	adc x9, x9, x12
	adds x20, x20, x22
	ldr q27, [x0, #4720]
	str x9, [x0, #600]
	adcs x11, x11, x13
	bit v0.16b, v18.16b, v29.16b
	adcs x3, x3, x28
	adc x23, x23, x1
	lsl x6, x4, #2
	bit v1.16b, v19.16b, v29.16b
	extr x4, x26, x4, #62
	extr x26, x14, x26, #62
	subs x6, x6, x20
	bit v2.16b, v20.16b, v29.16b
	extr x14, x21, x14, #62
	lsr x21, x21, #62
	sbcs x4, x4, x11
	bit v3.16b, v21.16b, v29.16b
	sbcs x26, x26, x3
	sbcs x14, x14, x23
	sbc x21, x21, x28
	bit v4.16b, v22.16b, v29.16b
	add x21, x21, x27
	lsl x30, x21, #32
	subs x15, x28, x30
	bit v5.16b, v23.16b, v29.16b
	sbcs x16, x28, x28
	sbc x30, x30, x21
	bit v6.16b, v24.16b, v29.16b
	adds x21, x6, x21
	adcs x15, x4, x15
	adcs x16, x26, x16
	bit v7.16b, v25.16b, v29.16b
	adcs x14, x14, x30
	sbc x5, x28, x28
	adds x21, x21, x5
	bit v16.16b, v26.16b, v29.16b
	str x21, [x0, #512]
	lsl x5, x5, #32
	lsr x5, x5, #32
	bit v17.16b, v27.16b, v29.16b
	adcs x15, x15, x5
	str x15, [x0, #520]
	sub x5, x28, x5
	add v28.2d, v28.2d, v31.2d
	adcs x16, x16, x28
	adc x14, x14, x5
	mul x7, x24, x25
	cmeq v29.2d, v28.2d, v30.2d
	str x16, [x0, #528]
	umulh x8, x24, x24
	ldr q18, [x0, #4736]
	str x14, [x0, #536]
	umulh x12, x24, x25
	ldr x22, [x0, #7184]
	ldr q19, [x0, #4752]
	mul x9, x20, x22
	ldr x13, [x0, #7176]
	mul x1, x20, x13
	ldr q20, [x0, #4768]
	ldr x6, [x0, #7168]
	mul x4, x20, x6
	ldr x26, [x0, #7160]
	ldr q21, [x0, #4784]
	mul x30, x20, x26
	umulh x21, x20, x22
	adds x21, x1, x21
	ldr q22, [x0, #4800]
	umulh x15, x20, x13
	adcs x4, x4, x15
	umulh x5, x20, x6
	ldr q23, [x0, #4816]
	adcs x30, x30, x5
	umulh x20, x20, x26
	ldr q24, [x0, #4832]
	adcs x20, x28, x20
	lsl x16, x9, #32
	adds x16, x21, x16
	ldr q25, [x0, #4848]
	lsr x14, x9, #32
	adcs x4, x4, x14
	ldr x1, [x0, #7104]
	ldr q26, [x0, #4864]
	mul x15, x9, x1
	adcs x30, x30, x15
	umulh x9, x9, x1
	ldr q27, [x0, #4880]
	adcs x20, x20, x9
	adcs x5, x28, x28
	mul x21, x11, x22
	bit v0.16b, v18.16b, v29.16b
	adds x21, x16, x21
	mul x14, x11, x13
	bit v1.16b, v19.16b, v29.16b
	adcs x4, x4, x14
	mul x15, x11, x6
	adcs x30, x30, x15
	bit v2.16b, v20.16b, v29.16b
	mul x9, x11, x26
	adcs x20, x20, x9
	umulh x16, x11, x26
	bit v3.16b, v21.16b, v29.16b
	adcs x5, x5, x16
	umulh x14, x11, x22
	adds x4, x4, x14
	bit v4.16b, v22.16b, v29.16b
	umulh x15, x11, x13
	adcs x30, x30, x15
	umulh x11, x11, x6
	bit v5.16b, v23.16b, v29.16b
	adcs x20, x20, x11
	adcs x5, x5, x28
	lsl x9, x21, #32
	bit v6.16b, v24.16b, v29.16b
	adds x4, x4, x9
	lsr x16, x21, #32
	bit v7.16b, v25.16b, v29.16b
	adcs x30, x30, x16
	mul x14, x21, x1
	adcs x20, x20, x14
	bit v16.16b, v26.16b, v29.16b
	umulh x21, x21, x1
	adcs x21, x5, x21
	adcs x15, x28, x28
	bit v17.16b, v27.16b, v29.16b
	mul x11, x3, x22
	adds x11, x4, x11
	mul x9, x3, x13
	add v28.2d, v28.2d, v31.2d
	adcs x9, x30, x9
	mul x16, x3, x6
	adcs x16, x20, x16
	cmeq v29.2d, v28.2d, v30.2d
	mul x14, x3, x26
	adcs x14, x21, x14
	umulh x5, x3, x26
	ldr q18, [x0, #4896]
	adcs x5, x15, x5
	umulh x4, x3, x22
	ldr q19, [x0, #4912]
	adds x9, x9, x4
	umulh x30, x3, x13
	adcs x16, x16, x30
	ldr q20, [x0, #4928]
	umulh x3, x3, x6
	adcs x14, x14, x3
	adcs x5, x5, x28
	ldr q21, [x0, #4944]
	lsl x20, x11, #32
	adds x9, x9, x20
	lsr x21, x11, #32
	ldr q22, [x0, #4960]
	adcs x16, x16, x21
	mul x15, x11, x1
	adcs x15, x14, x15
	ldr q23, [x0, #4976]
	umulh x11, x11, x1
	adcs x5, x5, x11
	adcs x4, x28, x28
	ldr q24, [x0, #4992]
	mul x30, x23, x22
	adds x30, x9, x30
	ldr q25, [x0, #5008]
	umulh x22, x23, x22
	mul x3, x23, x13
	adcs x3, x16, x3
	ldr q26, [x0, #5024]
	umulh x13, x23, x13
	mul x20, x23, x6
	adcs x20, x15, x20
	ldr q27, [x0, #5040]
	umulh x6, x23, x6
	mul x21, x23, x26
	umulh x23, x23, x26
	bit v0.16b, v18.16b, v29.16b
	adcs x21, x5, x21
	adcs x23, x4, x23
	adds x3, x3, x22
	bit v1.16b, v19.16b, v29.16b
	mul x14, x24, x2
	adcs x20, x20, x13
	mul x11, x24, x24
	bit v2.16b, v20.16b, v29.16b
	adcs x21, x21, x6
	umulh x9, x24, x2
	bit v3.16b, v21.16b, v29.16b
	adcs x23, x23, x28
	adds x14, x12, x14
	mul x16, x25, x25
	bit v4.16b, v22.16b, v29.16b
	lsl x15, x30, #32
	lsr x26, x30, #32
	mul x5, x30, x1
	bit v5.16b, v23.16b, v29.16b
	umulh x30, x30, x1
	mul x4, x24, x10
	adcs x4, x4, x9
	bit v6.16b, v24.16b, v29.16b
	umulh x24, x24, x10
	mul x22, x25, x2
	umulh x13, x25, x2
	bit v7.16b, v25.16b, v29.16b
	mul x6, x25, x10
	adcs x6, x24, x6
	bit v16.16b, v26.16b, v29.16b
	umulh x12, x25, x10
	umulh x25, x25, x25
	mul x1, x2, x10
	bit v17.16b, v27.16b, v29.16b
	adcs x1, x1, x12
	umulh x9, x2, x10
	adc x9, x9, x28
	add v28.2d, v28.2d, v31.2d
	adds x22, x4, x22
	adcs x13, x6, x13
	adcs x1, x1, x28
	cmeq v29.2d, v28.2d, v30.2d
	adc x9, x9, x28
	adds x3, x3, x15
	adcs x26, x20, x26
	ldr q18, [x0, #5056]
	adcs x21, x21, x5
	adcs x23, x23, x30
	adcs x24, x28, x28
	ldr q19, [x0, #5072]
	adds x7, x7, x7
	adcs x14, x14, x14
	ldr q20, [x0, #5088]
	adcs x22, x22, x22
	adcs x13, x13, x13
	adcs x1, x1, x1
	ldr q21, [x0, #5104]
	adcs x9, x9, x9
	adc x12, x28, x28
	adds x8, x7, x8
	ldr q22, [x0, #5120]
	adcs x14, x14, x16
	adcs x22, x22, x25
	lsl x4, x11, #32
	ldr q23, [x0, #5136]
	mul x6, x2, x2
	adcs x13, x13, x6
	umulh x2, x2, x2
	ldr q24, [x0, #5152]
	adcs x2, x1, x2
	extr x15, x8, x11, #32
	mul x20, x10, x10
	ldr q25, [x0, #5168]
	adcs x9, x9, x20
	umulh x10, x10, x10
	ldr q26, [x0, #5184]
	adc x10, x12, x10
	adds x8, x8, x4
	sub x5, x11, x4
	ldr q27, [x0, #5200]
	adcs x14, x14, x15
	extr x30, x14, x8, #32
	adcs x22, x22, x30
	bit v0.16b, v18.16b, v29.16b
	add x7, x22, x5
	extr x16, x7, x14, #32
	adcs x13, x13, x16
	bit v1.16b, v19.16b, v29.16b
	lsr x25, x7, #32
	adcs x2, x2, x25
	adcs x9, x9, x28
	bit v2.16b, v20.16b, v29.16b
	adc x10, x10, x28
	subs x4, x11, x4
	sbcs x15, x11, x15
	bit v3.16b, v21.16b, v29.16b
	sbcs x30, x8, x30
	sbcs x16, x14, x16
	bit v4.16b, v22.16b, v29.16b
	sbc x25, x7, x25
	adds x5, x22, x5
	adcs x8, x15, x8
	bit v5.16b, v23.16b, v29.16b
	adcs x14, x30, x14
	adcs x16, x16, x7
	adc x25, x25, x28
	bit v6.16b, v24.16b, v29.16b
	adds x6, x3, x27
	ldr x1, [x0, #72]
	sbcs x20, x26, x1
	bit v7.16b, v25.16b, v29.16b
	sbcs x12, x21, x28
	ldr x4, [x0, #88]
	sbcs x11, x23, x4
	bit v16.16b, v26.16b, v29.16b
	sbcs x24, x24, x28
	csel x20, x20, x26, hs
	bit v17.16b, v27.16b, v29.16b
	csel x3, x6, x3, hs
	csel x21, x12, x21, hs
	csel x23, x11, x23, hs
	add v28.2d, v28.2d, v31.2d
	adds x8, x13, x8
	adcs x14, x2, x14
	extr x22, x20, x3, #63
	cmeq v29.2d, v28.2d, v30.2d
	extr x5, x21, x20, #63
	lsl x15, x3, #1
	extr x30, x23, x21, #63
	ldr q18, [x0, #5216]
	lsr x7, x23, #63
	adcs x9, x9, x16
	adcs x10, x10, x25
	ldr q19, [x0, #5232]
	adc x24, x28, x28
	adds x26, x8, x27
	sbcs x1, x14, x1
	ldr q20, [x0, #5248]
	sbcs x6, x9, x28
	sbcs x4, x10, x4
	ldr q21, [x0, #5264]
	sbcs x24, x24, x28
	csel x26, x26, x8, hs
	csel x14, x1, x14, hs
	ldr q22, [x0, #5280]
	csel x9, x6, x9, hs
	csel x10, x4, x10, hs
	adds x3, x3, x15
	ldr q23, [x0, #5296]
	adcs x20, x20, x22
	adcs x21, x21, x5
	adcs x23, x23, x30
	ldr q24, [x0, #5312]
	adc x7, x7, x28
	subs x26, x17, x26
	ldr x12, [x0, #7128]
	ldr q25, [x0, #5328]
	sbcs x12, x12, x14
	lsl x11, x26, #3
	sbcs x9, x28, x9
	ldr q26, [x0, #5344]
	extr x26, x12, x26, #61
	ldr x13, [x0, #7112]
	ldr q27, [x0, #5360]
	sbc x10, x13, x10
	adds x3, x11, x3
	extr x12, x9, x12, #61
	bit v0.16b, v18.16b, v29.16b
	extr x9, x10, x9, #61
	lsr x10, x10, #61
	adcs x20, x26, x20
	bit v1.16b, v19.16b, v29.16b
	adcs x12, x12, x21
	adcs x9, x9, x23
	adc x7, x10, x7
	bit v2.16b, v20.16b, v29.16b
	add x2, x7, x27
	lsl x16, x2, #32
	sub x25, x28, x2
	bit v3.16b, v21.16b, v29.16b
	sub x27, x16, x27
	adds x9, x9, x16
	adc x7, x7, x28
	bit v4.16b, v22.16b, v29.16b
	subs x25, x3, x25
	sbcs x27, x20, x27
	bit v5.16b, v23.16b, v29.16b
	sbcs x12, x12, x28
	sbcs x9, x9, x2
	sbc x7, x7, x2
	bit v6.16b, v24.16b, v29.16b
	lsl x24, x7, #32
	adds x25, x25, x7
	lsr x24, x24, #32
	bit v7.16b, v25.16b, v29.16b
	str x25, [x0, #544]
	adcs x27, x27, x24
	sub x24, x28, x24
	bit v16.16b, v26.16b, v29.16b
	adcs x28, x12, x28
	str x27, [x0, #552]
	adc x9, x9, x24
	bit v17.16b, v27.16b, v29.16b
	str x28, [x0, #560]
	str x9, [x0, #568]
	str q0, [x0, #704]
	str q1, [x0, #720]
	str q2, [x0, #736]
	str q3, [x0, #752]
	str q4, [x0, #768]
	str q5, [x0, #784]
	movz x17, #5400, lsl #0
	add x17, x0, x17
	str q6, [x17, #0]
	str q7, [x17, #16]
	str q16, [x17, #32]
	str q17, [x17, #48]
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
	str x8, [x0, #1024]
	str x9, [x0, #1032]
	str x10, [x0, #1040]
	str x11, [x0, #1048]
	movz x16, #5, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	ldrb w3, [x16, #1828]
	sub x3, x3, #1
	ldr x1, [x0, #736]
	ldr x2, [x0, #1024]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #736]
	ldr x1, [x0, #744]
	ldr x2, [x0, #1032]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #744]
	ldr x1, [x0, #752]
	ldr x2, [x0, #1040]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #752]
	ldr x1, [x0, #760]
	ldr x2, [x0, #1048]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #760]
	ldr x1, [x0, #576]
	ldr x2, [x0, #584]
	mul x3, x1, x2
	umulh x4, x1, x1
	umulh x5, x1, x2
	mul x6, x1, x1
	ldr x7, [x0, #592]
	mul x8, x1, x7
	umulh x9, x1, x7
	mul x10, x2, x2
	ldr x11, [x0, #600]
	mul x12, x1, x11
	mul x13, x2, x7
	lsl x14, x6, #32
	umulh x15, x2, x2
	adds x8, x5, x8
	umulh x16, x1, x11
	mul x17, x2, x11
	umulh x20, x2, x7
	adcs x12, x12, x9
	umulh x21, x2, x11
	umulh x22, x7, x11
	mul x23, x7, x11
	sub x24, x6, x14
	umulh x25, x7, x7
	mul x26, x7, x7
	adcs x17, x16, x17
	umulh x27, x11, x11
	mul x28, x11, x11
	adcs x23, x23, x21
	movz x30, #0, lsl #0
	adc x22, x22, x30
	adds x13, x12, x13
	adcs x20, x17, x20
	adcs x23, x23, x30
	adc x22, x22, x30
	adds x3, x3, x3
	adcs x8, x8, x8
	adcs x13, x13, x13
	adcs x20, x20, x20
	adcs x23, x23, x23
	adcs x22, x22, x22
	adc x5, x30, x30
	movz x9, #1, lsl #0
	orr x16, x9, x9
	movk x16, #0, lsl #16
	adds x4, x3, x4
	movk x16, #65535, lsl #32
	extr x21, x4, x6, #32
	adcs x8, x8, x10
	movk x16, #65535, lsl #48
	adcs x15, x13, x15
	adcs x20, x20, x26
	ldr x12, [x0, #512]
	ldr x17, [x0, #5400]
	mul x3, x12, x17
	adcs x23, x23, x25
	ldr x10, [x0, #5408]
	mul x13, x12, x10
	adcs x22, x22, x28
	ldr x26, [x0, #5416]
	mul x25, x12, x26
	adc x27, x5, x27
	adds x4, x4, x14
	umulh x28, x12, x17
	adcs x8, x8, x21
	extr x5, x8, x4, #32
	adcs x15, x15, x5
	add x11, x15, x24
	extr x7, x11, x8, #32
	adcs x20, x20, x7
	lsr x2, x11, #32
	adcs x23, x23, x2
	adcs x22, x22, x30
	adc x27, x27, x30
	subs x14, x6, x14
	sbcs x21, x6, x21
	sbcs x5, x4, x5
	sbcs x7, x8, x7
	sbc x2, x11, x2
	adds x15, x15, x24
	adcs x21, x21, x4
	umulh x14, x12, x10
	adcs x8, x5, x8
	umulh x6, x12, x26
	adcs x11, x7, x11
	ldr x24, [x0, #5424]
	mul x15, x12, x24
	umulh x12, x12, x24
	adc x2, x2, x30
	adds x28, x13, x28
	adcs x14, x25, x14
	ldr x4, [x0, #520]
	mul x5, x4, x17
	adcs x15, x15, x6
	adcs x12, x30, x12
	adds x21, x20, x21
	lsl x7, x3, #32
	adcs x8, x23, x8
	mul x13, x4, x10
	adcs x11, x22, x11
	lsr x25, x3, #32
	adcs x2, x27, x2
	umulh x6, x3, x16
	mul x3, x3, x16
	adc x20, x30, x30
	adds x28, x28, x7
	adcs x25, x14, x25
	umulh x23, x4, x17
	adcs x15, x15, x3
	mul x22, x4, x26
	adcs x12, x12, x6
	umulh x27, x4, x24
	adcs x7, x30, x30
	adds x5, x28, x5
	adcs x13, x25, x13
	mul x14, x4, x24
	adcs x22, x15, x22
	adcs x14, x12, x14
	adcs x27, x7, x27
	adds x3, x21, x9
	umulh x6, x4, x10
	ldr x28, [x0, #72]
	sbcs x25, x8, x28
	sbcs x15, x11, x30
	umulh x4, x4, x26
	ldr x12, [x0, #88]
	sbcs x7, x2, x12
	sbcs x20, x20, x30
	csel x3, x3, x21, hs
	csel x8, x25, x8, hs
	csel x11, x15, x11, hs
	csel x7, x7, x2, hs
	adds x13, x13, x23
	lsl x20, x5, #32
	adcs x22, x22, x6
	adcs x14, x14, x4
	str x11, [x0, #816]
	str x3, [x0, #800]
	str x8, [x0, #808]
	lsr x21, x5, #32
	str x7, [x0, #824]
	ldr x25, [x0, #528]
	mul x15, x25, x17
	adcs x27, x27, x30
	adds x13, x13, x20
	mul x2, x5, x16
	adcs x22, x22, x21
	mul x23, x25, x10
	adcs x14, x14, x2
	umulh x5, x5, x16
	umulh x6, x25, x17
	adcs x27, x27, x5
	mul x4, x25, x26
	adcs x20, x30, x30
	adds x15, x13, x15
	adcs x23, x22, x23
	umulh x21, x25, x10
	adcs x4, x14, x4
	umulh x2, x25, x24
	mul x5, x25, x24
	adcs x27, x27, x5
	adcs x2, x20, x2
	umulh x25, x25, x26
	lsl x13, x15, #32
	adds x23, x23, x6
	ldr x22, [x0, #536]
	mul x14, x22, x17
	adcs x4, x4, x21
	adcs x27, x27, x25
	mul x5, x22, x10
	umulh x17, x22, x17
	umulh x10, x22, x10
	adcs x2, x2, x30
	adds x23, x23, x13
	umulh x20, x15, x16
	lsr x6, x15, #32
	adcs x4, x4, x6
	mul x15, x15, x16
	adcs x15, x27, x15
	ldr x21, [x0, #704]
	mul x25, x21, x8
	adcs x2, x2, x20
	adcs x13, x30, x30
	adds x14, x23, x14
	adcs x5, x4, x5
	umulh x6, x21, x3
	mul x27, x22, x26
	adcs x27, x15, x27
	umulh x26, x22, x26
	mul x20, x22, x24
	umulh x24, x22, x24
	adcs x20, x2, x20
	mul x23, x21, x3
	adcs x24, x13, x24
	umulh x4, x21, x8
	adds x6, x25, x6
	umulh x15, x21, x11
	lsl x22, x14, #32
	lsr x2, x14, #32
	mul x13, x14, x16
	umulh x14, x14, x16
	mul x25, x21, x11
	adcs x4, x25, x4
	mul x25, x21, x7
	adcs x25, x25, x15
	umulh x21, x21, x7
	adcs x21, x30, x21
	adds x17, x5, x17
	adcs x27, x27, x10
	adcs x20, x20, x26
	adcs x24, x24, x30
	adds x22, x17, x22
	lsl x15, x23, #32
	adcs x27, x27, x2
	ldr x5, [x0, #712]
	mul x10, x5, x3
	adcs x20, x20, x13
	adcs x24, x24, x14
	mul x26, x23, x16
	adcs x17, x30, x30
	adds x6, x6, x15
	lsr x2, x23, #32
	adcs x2, x4, x2
	adcs x25, x25, x26
	umulh x13, x5, x3
	umulh x23, x23, x16
	adcs x21, x21, x23
	mul x14, x5, x8
	adcs x15, x30, x30
	adds x10, x6, x10
	adcs x14, x2, x14
	mul x4, x5, x11
	adcs x4, x25, x4
	umulh x26, x5, x7
	mul x23, x5, x7
	adcs x23, x21, x23
	adcs x26, x15, x26
	adds x6, x22, x9
	sbcs x2, x27, x28
	sbcs x25, x20, x30
	sbcs x21, x24, x12
	sbcs x17, x17, x30
	csel x6, x6, x22, hs
	csel x27, x2, x27, hs
	csel x20, x25, x20, hs
	umulh x15, x5, x8
	csel x24, x21, x24, hs
	umulh x5, x5, x11
	adds x14, x14, x13
	lsl x17, x10, #32
	adcs x4, x4, x15
	str x20, [x0, #880]
	str x27, [x0, #872]
	str x24, [x0, #888]
	str x6, [x0, #864]
	ldr x22, [x0, #720]
	mul x2, x22, x3
	adcs x23, x23, x5
	lsr x25, x10, #32
	adcs x26, x26, x30
	adds x14, x14, x17
	mul x21, x22, x8
	adcs x4, x4, x25
	umulh x13, x22, x3
	mul x15, x10, x16
	adcs x23, x23, x15
	umulh x10, x10, x16
	adcs x26, x26, x10
	umulh x5, x22, x8
	adcs x17, x30, x30
	adds x2, x14, x2
	adcs x21, x4, x21
	mul x25, x22, x11
	adcs x25, x23, x25
	umulh x15, x22, x7
	mul x10, x22, x7
	adcs x26, x26, x10
	adcs x15, x17, x15
	umulh x22, x22, x11
	adds x21, x21, x13
	ldr x14, [x0, #728]
	mul x4, x14, x3
	adcs x25, x25, x5
	lsl x23, x2, #32
	adcs x26, x26, x22
	mul x10, x2, x16
	adcs x15, x15, x30
	adds x21, x21, x23
	mul x17, x14, x8
	lsr x13, x2, #32
	adcs x25, x25, x13
	adcs x10, x26, x10
	ldr x5, [x0, #544]
	ldr x22, [x0, #5432]
	mul x23, x5, x22
	umulh x2, x2, x16
	adcs x15, x15, x2
	adcs x13, x30, x30
	adds x4, x21, x4
	adcs x17, x25, x17
	mul x26, x14, x11
	adcs x26, x10, x26
	mul x2, x14, x7
	adcs x2, x15, x2
	umulh x21, x14, x7
	adcs x21, x13, x21
	umulh x25, x14, x3
	adds x25, x17, x25
	umulh x10, x14, x8
	adcs x26, x26, x10
	umulh x14, x14, x11
	adcs x2, x2, x14
	umulh x15, x5, x22
	adcs x21, x21, x30
	lsl x13, x4, #32
	adds x13, x25, x13
	lsr x17, x4, #32
	adcs x26, x26, x17
	mul x10, x4, x16
	adcs x2, x2, x10
	umulh x4, x4, x16
	adcs x21, x21, x4
	ldr x14, [x0, #5440]
	umulh x25, x5, x14
	adcs x17, x30, x30
	adds x10, x13, x9
	sbcs x4, x26, x28
	sbcs x24, x2, x30
	sbcs x20, x21, x12
	sbcs x17, x17, x30
	csel x10, x10, x13, hs
	csel x26, x4, x26, hs
	csel x2, x24, x2, hs
	csel x21, x20, x21, hs
	mul x17, x5, x14
	adds x17, x17, x15
	ldr x13, [x0, #5448]
	mul x4, x5, x13
	adcs x4, x4, x25
	ldr x24, [x0, #5456]
	mul x20, x5, x24
	umulh x15, x5, x13
	adcs x15, x20, x15
	umulh x5, x5, x24
	adcs x5, x30, x5
	lsl x25, x23, #32
	adds x17, x17, x25
	lsr x20, x23, #32
	adcs x4, x4, x20
	mul x25, x23, x16
	adcs x15, x15, x25
	umulh x23, x23, x16
	adcs x23, x5, x23
	adcs x20, x30, x30
	ldr x25, [x0, #552]
	mul x5, x25, x22
	adds x5, x17, x5
	mul x17, x25, x14
	adcs x17, x4, x17
	mul x4, x25, x13
	adcs x4, x15, x4
	mul x15, x25, x24
	adcs x15, x23, x15
	umulh x23, x25, x24
	adcs x23, x20, x23
	umulh x20, x25, x22
	adds x17, x17, x20
	umulh x20, x25, x14
	adcs x20, x4, x20
	umulh x25, x25, x13
	adcs x15, x15, x25
	adcs x23, x23, x30
	lsl x4, x5, #32
	adds x17, x17, x4
	lsr x25, x5, #32
	adcs x25, x20, x25
	mul x4, x5, x16
	adcs x15, x15, x4
	umulh x5, x5, x16
	adcs x23, x23, x5
	adcs x20, x30, x30
	ldr x4, [x0, #560]
	mul x5, x4, x22
	adds x5, x17, x5
	mul x17, x4, x14
	adcs x25, x25, x17
	mul x17, x4, x13
	adcs x17, x15, x17
	mul x15, x4, x24
	adcs x15, x23, x15
	umulh x23, x4, x24
	adcs x23, x20, x23
	umulh x20, x4, x22
	adds x25, x25, x20
	umulh x20, x4, x14
	adcs x17, x17, x20
	umulh x4, x4, x13
	adcs x15, x15, x4
	adcs x23, x23, x30
	lsl x20, x5, #32
	adds x20, x25, x20
	lsr x4, x5, #32
	adcs x17, x17, x4
	mul x25, x5, x16
	adcs x15, x15, x25
	umulh x5, x5, x16
	adcs x23, x23, x5
	adcs x4, x30, x30
	ldr x25, [x0, #568]
	mul x5, x25, x22
	adds x5, x20, x5
	umulh x22, x25, x22
	mul x20, x25, x14
	adcs x20, x17, x20
	umulh x14, x25, x14
	mul x17, x25, x13
	adcs x17, x15, x17
	umulh x13, x25, x13
	mul x15, x25, x24
	umulh x24, x25, x24
	adcs x15, x23, x15
	adcs x4, x4, x24
	adds x20, x20, x22
	adcs x17, x17, x14
	adcs x13, x15, x13
	adcs x4, x4, x30
	lsl x25, x5, #32
	adds x20, x20, x25
	lsr x23, x5, #32
	adcs x17, x17, x23
	mul x24, x5, x16
	adcs x24, x13, x24
	umulh x5, x5, x16
	adcs x4, x4, x5
	ldr x22, [x0, #736]
	umulh x14, x22, x1
	adcs x15, x30, x30
	adds x25, x20, x9
	sbcs x23, x17, x28
	sbcs x13, x24, x30
	sbcs x5, x4, x12
	sbcs x15, x15, x30
	csel x20, x25, x20, hs
	csel x17, x23, x17, hs
	csel x24, x13, x24, hs
	csel x5, x5, x4, hs
	str x5, [x0, #952]
	str x24, [x0, #944]
	str x17, [x0, #936]
	str x20, [x0, #928]
	mul x15, x22, x1
	ldr x25, [x0, #584]
	mul x23, x22, x25
	adds x23, x23, x14
	ldr x13, [x0, #592]
	mul x4, x22, x13
	ldr x14, [x0, #600]
	mul x5, x22, x14
	umulh x24, x22, x25
	adcs x4, x4, x24
	umulh x24, x22, x13
	adcs x24, x5, x24
	umulh x22, x22, x14
	adcs x22, x30, x22
	lsl x5, x15, #32
	adds x23, x23, x5
	lsr x5, x15, #32
	adcs x4, x4, x5
	mul x5, x15, x16
	adcs x24, x24, x5
	umulh x15, x15, x16
	adcs x15, x22, x15
	adcs x5, x30, x30
	ldr x22, [x0, #744]
	mul x17, x22, x1
	adds x17, x23, x17
	mul x23, x22, x25
	adcs x23, x4, x23
	mul x4, x22, x13
	adcs x4, x24, x4
	mul x24, x22, x14
	adcs x24, x15, x24
	umulh x15, x22, x14
	adcs x15, x5, x15
	umulh x5, x22, x1
	adds x23, x23, x5
	umulh x5, x22, x25
	adcs x5, x4, x5
	umulh x22, x22, x13
	adcs x24, x24, x22
	adcs x15, x15, x30
	lsl x4, x17, #32
	adds x23, x23, x4
	lsr x22, x17, #32
	adcs x22, x5, x22
	mul x4, x17, x16
	adcs x24, x24, x4
	umulh x17, x17, x16
	adcs x15, x15, x17
	adcs x5, x30, x30
	ldr x4, [x0, #752]
	mul x17, x4, x1
	adds x17, x23, x17
	mul x23, x4, x25
	adcs x22, x22, x23
	mul x23, x4, x13
	adcs x23, x24, x23
	mul x24, x4, x14
	adcs x24, x15, x24
	umulh x15, x4, x14
	adcs x15, x5, x15
	umulh x5, x4, x1
	adds x22, x22, x5
	umulh x5, x4, x25
	adcs x23, x23, x5
	umulh x4, x4, x13
	adcs x24, x24, x4
	adcs x15, x15, x30
	lsl x5, x17, #32
	adds x5, x22, x5
	lsr x4, x17, #32
	adcs x23, x23, x4
	mul x22, x17, x16
	adcs x24, x24, x22
	umulh x17, x17, x16
	adcs x15, x15, x17
	adcs x4, x30, x30
	ldr x22, [x0, #760]
	mul x17, x22, x1
	adds x17, x5, x17
	umulh x1, x22, x1
	mul x5, x22, x25
	adcs x5, x23, x5
	umulh x25, x22, x25
	mul x23, x22, x13
	adcs x23, x24, x23
	umulh x13, x22, x13
	mul x24, x22, x14
	umulh x14, x22, x14
	adcs x24, x15, x24
	adcs x4, x4, x14
	adds x5, x5, x1
	adcs x23, x23, x25
	adcs x13, x24, x13
	adcs x4, x4, x30
	lsl x22, x17, #32
	adds x5, x5, x22
	lsr x15, x17, #32
	adcs x23, x23, x15
	mul x14, x17, x16
	adcs x14, x13, x14
	umulh x17, x17, x16
	adcs x4, x4, x17
	adcs x1, x30, x30
	adds x25, x5, x9
	sbcs x24, x23, x28
	sbcs x22, x14, x30
	sbcs x15, x4, x12
	sbcs x1, x1, x30
	csel x25, x25, x5, hs
	csel x23, x24, x23, hs
	csel x14, x22, x14, hs
	csel x15, x15, x4, hs
	umulh x13, x25, x3
	mul x17, x25, x3
	mul x1, x25, x8
	adds x1, x1, x13
	mul x5, x25, x11
	mul x24, x25, x7
	umulh x22, x25, x8
	adcs x5, x5, x22
	umulh x4, x25, x11
	adcs x24, x24, x4
	umulh x25, x25, x7
	adcs x25, x30, x25
	lsl x13, x17, #32
	adds x1, x1, x13
	lsr x22, x17, #32
	adcs x5, x5, x22
	mul x4, x17, x16
	adcs x24, x24, x4
	umulh x17, x17, x16
	adcs x25, x25, x17
	adcs x13, x30, x30
	mul x22, x23, x3
	adds x22, x1, x22
	mul x4, x23, x8
	adcs x5, x5, x4
	mul x17, x23, x11
	adcs x24, x24, x17
	mul x1, x23, x7
	adcs x25, x25, x1
	umulh x4, x23, x7
	adcs x4, x13, x4
	umulh x17, x23, x3
	adds x5, x5, x17
	umulh x1, x23, x8
	adcs x24, x24, x1
	umulh x23, x23, x11
	adcs x23, x25, x23
	adcs x4, x4, x30
	lsl x13, x22, #32
	adds x5, x5, x13
	lsr x17, x22, #32
	adcs x24, x24, x17
	mul x1, x22, x16
	adcs x1, x23, x1
	umulh x22, x22, x16
	adcs x4, x4, x22
	adcs x25, x30, x30
	mul x13, x14, x3
	adds x5, x5, x13
	mul x17, x14, x8
	adcs x24, x24, x17
	mul x23, x14, x11
	adcs x1, x1, x23
	mul x22, x14, x7
	adcs x4, x4, x22
	umulh x13, x14, x7
	adcs x13, x25, x13
	umulh x17, x14, x3
	adds x24, x24, x17
	umulh x23, x14, x8
	adcs x23, x1, x23
	umulh x14, x14, x11
	adcs x4, x4, x14
	adcs x13, x13, x30
	subs x10, x10, x6
	sbcs x26, x26, x27
	lsl x22, x5, #32
	ldr x25, [x0, #880]
	sbcs x2, x2, x25
	mul x17, x15, x3
	ldr x1, [x0, #888]
	sbcs x21, x21, x1
	umulh x3, x15, x3
	mul x14, x15, x8
	umulh x8, x15, x8
	lsr x6, x5, #32
	mul x27, x5, x16
	umulh x5, x5, x16
	mul x25, x15, x11
	umulh x11, x15, x11
	mul x1, x15, x7
	umulh x15, x15, x7
	sbc x7, x30, x30
	adds x24, x24, x22
	adcs x6, x23, x6
	adcs x4, x4, x27
	adcs x13, x13, x5
	adcs x22, x30, x30
	adds x24, x24, x17
	adcs x6, x6, x14
	lsr x23, x7, #32
	adcs x25, x4, x25
	lsl x27, x24, #32
	adcs x13, x13, x1
	mul x5, x24, x16
	adcs x15, x22, x15
	adds x3, x6, x3
	lsr x17, x24, #32
	umulh x16, x24, x16
	adcs x25, x25, x8
	lsl x14, x7, #32
	adcs x13, x13, x11
	sub x14, x14, x7
	adcs x15, x15, x30
	adds x27, x3, x27
	adcs x25, x25, x17
	adcs x13, x13, x5
	adcs x15, x15, x16
	adcs x4, x30, x30
	adds x9, x27, x9
	sbcs x28, x25, x28
	sbcs x1, x13, x30
	sbcs x12, x15, x12
	sbcs x4, x4, x30
	csel x9, x9, x27, hs
	csel x25, x28, x25, hs
	csel x13, x1, x13, hs
	csel x15, x12, x15, hs
	adds x7, x10, x7
	adcs x23, x26, x23
	str x7, [x0, #896]
	adcs x2, x2, x30
	str x23, [x0, #904]
	adc x14, x21, x14
	subs x9, x9, x20
	str x2, [x0, #912]
	ldr x22, [x0, #936]
	sbcs x25, x25, x22
	str x14, [x0, #920]
	ldr x6, [x0, #944]
	sbcs x13, x13, x6
	ldr x24, [x0, #952]
	sbcs x15, x15, x24
	sbc x8, x30, x30
	lsr x11, x8, #32
	adds x9, x9, x8
	lsl x3, x8, #32
	adcs x25, x25, x11
	sub x3, x3, x8
	str x9, [x0, #960]
	adcs x13, x13, x30
	str x25, [x0, #968]
	adc x15, x15, x3
	str x13, [x0, #976]
	str x15, [x0, #984]
	ldr x1, [x0, #896]
	ldr x2, [x0, #904]
	mul x3, x1, x2
	umulh x4, x1, x2
	ldr x5, [x0, #912]
	mul x6, x1, x5
	umulh x7, x1, x5
	ldr x8, [x0, #920]
	mul x9, x1, x8
	mul x10, x2, x5
	umulh x11, x1, x8
	umulh x12, x2, x8
	mul x13, x2, x8
	umulh x14, x2, x5
	umulh x15, x1, x1
	mul x16, x1, x1
	mul x17, x2, x2
	umulh x20, x5, x8
	mul x21, x5, x8
	umulh x22, x2, x2
	adds x6, x4, x6
	mul x23, x5, x5
	umulh x24, x5, x5
	adcs x9, x9, x7
	mul x25, x8, x8
	adcs x13, x11, x13
	umulh x26, x8, x8
	adcs x21, x21, x12
	movz x27, #0, lsl #0
	adc x20, x20, x27
	adds x10, x9, x10
	adcs x14, x13, x14
	adcs x21, x21, x27
	adc x20, x20, x27
	adds x3, x3, x3
	adcs x6, x6, x6
	lsl x28, x16, #32
	adcs x10, x10, x10
	sub x30, x16, x28
	adcs x14, x14, x14
	adcs x21, x21, x21
	adcs x20, x20, x20
	adc x4, x27, x27
	adds x15, x3, x15
	extr x7, x15, x16, #32
	adcs x6, x6, x17
	adcs x22, x10, x22
	adcs x14, x14, x23
	adcs x21, x21, x24
	adcs x20, x20, x25
	adc x26, x4, x26
	adds x15, x15, x28
	adcs x6, x6, x7
	extr x11, x6, x15, #32
	adcs x22, x22, x11
	add x12, x22, x30
	extr x9, x12, x6, #32
	lsr x13, x12, #32
	adcs x14, x14, x9
	adcs x21, x21, x13
	adcs x20, x20, x27
	adc x26, x26, x27
	subs x28, x16, x28
	sbcs x7, x16, x7
	sbcs x11, x15, x11
	sbcs x9, x6, x9
	sbc x13, x12, x13
	adds x22, x22, x30
	adcs x7, x7, x15
	adcs x6, x11, x6
	adcs x12, x9, x12
	adc x13, x13, x27
	adds x7, x14, x7
	adcs x6, x21, x6
	adcs x12, x20, x12
	adcs x13, x26, x13
	adc x3, x27, x27
	movz x17, #1, lsl #0
	adds x10, x7, x17
	orr x23, x17, x17
	movk x23, #0, lsl #16
	movk x23, #65535, lsl #32
	ldr x24, [x0, #72]
	sbcs x25, x6, x24
	movk x23, #65535, lsl #48
	sbcs x4, x12, x27
	ldr x28, [x0, #88]
	sbcs x16, x13, x28
	sbcs x3, x3, x27
	csel x10, x10, x7, hs
	csel x6, x25, x6, hs
	csel x12, x4, x12, hs
	csel x16, x16, x13, hs
	mul x30, x10, x1
	str x16, [x0, #824]
	str x6, [x0, #808]
	str x12, [x0, #816]
	str x10, [x0, #800]
	umulh x22, x10, x1
	umulh x15, x10, x2
	mul x11, x10, x2
	mul x9, x10, x5
	umulh x14, x10, x5
	mul x21, x6, x1
	umulh x20, x10, x8
	mul x26, x10, x8
	mul x3, x6, x2
	lsl x7, x30, #32
	umulh x25, x30, x23
	mul x4, x30, x23
	lsr x30, x30, #32
	adds x11, x11, x22
	mul x13, x6, x5
	adcs x9, x9, x15
	mul x22, x6, x8
	adcs x26, x26, x14
	umulh x15, x6, x8
	adcs x20, x27, x20
	umulh x14, x6, x1
	adds x11, x11, x7
	umulh x7, x6, x2
	adcs x9, x9, x30
	umulh x30, x6, x5
	adcs x26, x26, x4
	adcs x20, x20, x25
	adcs x4, x27, x27
	adds x21, x11, x21
	adcs x9, x9, x3
	lsl x25, x21, #32
	umulh x11, x21, x23
	mul x3, x21, x23
	lsr x21, x21, #32
	adcs x26, x26, x13
	adcs x20, x20, x22
	mul x13, x12, x1
	adcs x15, x4, x15
	mul x22, x12, x2
	adds x9, x9, x14
	mul x4, x12, x5
	adcs x26, x26, x7
	mul x14, x12, x8
	adcs x30, x20, x30
	umulh x7, x12, x8
	adcs x15, x15, x27
	umulh x20, x12, x1
	adds x9, x9, x25
	umulh x25, x12, x2
	adcs x26, x26, x21
	umulh x21, x12, x5
	adcs x3, x30, x3
	adcs x15, x15, x11
	adcs x30, x27, x27
	adds x13, x9, x13
	adcs x22, x26, x22
	lsl x11, x13, #32
	mul x9, x13, x23
	umulh x26, x13, x23
	lsr x13, x13, #32
	adcs x3, x3, x4
	adcs x14, x15, x14
	mul x4, x16, x1
	adcs x7, x30, x7
	mul x15, x16, x2
	adds x22, x22, x20
	mul x30, x16, x5
	adcs x25, x3, x25
	mul x20, x16, x8
	adcs x14, x14, x21
	umulh x3, x16, x8
	adcs x7, x7, x27
	umulh x21, x16, x1
	adds x22, x22, x11
	umulh x11, x16, x2
	adcs x13, x25, x13
	umulh x25, x16, x5
	adcs x14, x14, x9
	adcs x7, x7, x26
	adcs x9, x27, x27
	adds x4, x22, x4
	adcs x13, x13, x15
	lsl x26, x4, #32
	umulh x22, x4, x23
	mul x15, x4, x23
	lsr x4, x4, #32
	adcs x30, x14, x30
	adcs x20, x7, x20
	adcs x3, x9, x3
	adds x21, x13, x21
	adcs x30, x30, x11
	adcs x20, x20, x25
	adcs x3, x3, x27
	adds x26, x21, x26
	adcs x30, x30, x4
	adcs x20, x20, x15
	adcs x3, x3, x22
	adcs x14, x27, x27
	adds x7, x26, x17
	sbcs x9, x30, x24
	sbcs x13, x20, x27
	sbcs x11, x3, x28
	sbcs x14, x14, x27
	ldr x25, [x0, #864]
	mul x21, x25, x10
	csel x7, x7, x26, hs
	csel x30, x9, x30, hs
	csel x20, x13, x20, hs
	csel x3, x11, x3, hs
	str x3, [x0, #856]
	str x20, [x0, #848]
	str x7, [x0, #832]
	mul x4, x25, x6
	str x30, [x0, #840]
	umulh x15, x25, x10
	umulh x22, x25, x6
	umulh x14, x25, x12
	mul x26, x25, x12
	mul x9, x25, x16
	umulh x25, x25, x16
	ldr x13, [x0, #872]
	mul x11, x13, x10
	lsl x8, x21, #32
	mul x5, x21, x23
	mul x2, x13, x6
	umulh x1, x21, x23
	lsr x21, x21, #32
	adds x15, x4, x15
	mul x4, x13, x12
	adcs x22, x26, x22
	mul x26, x13, x16
	adcs x9, x9, x14
	umulh x14, x13, x16
	adcs x25, x27, x25
	umulh x3, x13, x10
	adds x15, x15, x8
	umulh x8, x13, x6
	adcs x21, x22, x21
	umulh x13, x13, x12
	adcs x9, x9, x5
	adcs x25, x25, x1
	adcs x22, x27, x27
	adds x11, x15, x11
	adcs x2, x21, x2
	lsl x5, x11, #32
	mul x1, x11, x23
	lsr x15, x11, #32
	umulh x11, x11, x23
	adcs x4, x9, x4
	adcs x26, x25, x26
	ldr x21, [x0, #880]
	mul x9, x21, x10
	adcs x14, x22, x14
	adds x2, x2, x3
	mul x25, x21, x6
	mul x22, x21, x12
	adcs x4, x4, x8
	mul x3, x21, x16
	adcs x26, x26, x13
	umulh x8, x21, x16
	adcs x14, x14, x27
	umulh x13, x21, x10
	adds x2, x2, x5
	umulh x5, x21, x6
	adcs x4, x4, x15
	umulh x21, x21, x12
	adcs x26, x26, x1
	adcs x14, x14, x11
	adcs x15, x27, x27
	adds x9, x2, x9
	adcs x25, x4, x25
	lsl x1, x9, #32
	lsr x11, x9, #32
	umulh x2, x9, x23
	mul x9, x9, x23
	adcs x22, x26, x22
	adcs x14, x14, x3
	ldr x4, [x0, #888]
	mul x26, x4, x10
	adcs x8, x15, x8
	adds x25, x25, x13
	mul x3, x4, x6
	mul x15, x4, x12
	adcs x22, x22, x5
	mul x13, x4, x16
	adcs x14, x14, x21
	umulh x16, x4, x16
	adcs x8, x8, x27
	umulh x10, x4, x10
	adds x25, x25, x1
	umulh x6, x4, x6
	adcs x22, x22, x11
	umulh x12, x4, x12
	adcs x9, x14, x9
	adcs x8, x8, x2
	adcs x5, x27, x27
	adds x26, x25, x26
	adcs x3, x22, x3
	lsl x21, x26, #32
	umulh x1, x26, x23
	lsr x11, x26, #32
	mul x26, x26, x23
	adcs x15, x9, x15
	adcs x13, x8, x13
	adcs x16, x5, x16
	adds x10, x3, x10
	adcs x15, x15, x6
	adcs x13, x13, x12
	adcs x16, x16, x27
	adds x21, x10, x21
	adcs x15, x15, x11
	adcs x13, x13, x26
	adcs x16, x16, x1
	adcs x4, x27, x27
	ldr x14, [x0, #960]
	ldr x2, [x0, #968]
	mul x25, x14, x2
	adds x22, x21, x17
	umulh x9, x14, x2
	ldr x8, [x0, #976]
	mul x5, x14, x8
	sbcs x3, x15, x24
	umulh x6, x14, x8
	sbcs x12, x13, x27
	ldr x10, [x0, #984]
	mul x11, x14, x10
	umulh x26, x14, x10
	sbcs x1, x16, x28
	str x23, [x0, #7104]
	mul x23, x2, x8
	sbcs x4, x4, x27
	umulh x4, x2, x8
	csel x22, x22, x21, hs
	csel x15, x3, x15, hs
	csel x13, x12, x13, hs
	csel x16, x1, x16, hs
	str x22, [x0, #864]
	mul x21, x2, x10
	str x16, [x0, #888]
	str x13, [x0, #880]
	str x15, [x0, #872]
	umulh x3, x14, x14
	mul x12, x14, x14
	adds x5, x9, x5
	umulh x1, x2, x10
	mul x9, x2, x2
	umulh x14, x8, x10
	mul x16, x8, x10
	adcs x6, x11, x6
	umulh x11, x2, x2
	umulh x2, x8, x8
	mul x13, x8, x8
	mul x8, x10, x10
	adcs x21, x26, x21
	umulh x26, x10, x10
	adcs x16, x16, x1
	adc x14, x14, x27
	adds x23, x6, x23
	adcs x4, x21, x4
	adcs x16, x16, x27
	adc x14, x14, x27
	adds x25, x25, x25
	adcs x5, x5, x5
	lsl x1, x12, #32
	adcs x23, x23, x23
	sub x6, x12, x1
	adcs x4, x4, x4
	adcs x16, x16, x16
	adcs x14, x14, x14
	adc x21, x27, x27
	adds x25, x25, x3
	extr x3, x25, x12, #32
	adcs x9, x5, x9
	adcs x23, x23, x11
	adcs x13, x4, x13
	adcs x16, x16, x2
	adcs x14, x14, x8
	adc x21, x21, x26
	adds x25, x25, x1
	adcs x9, x9, x3
	extr x5, x9, x25, #32
	adcs x23, x23, x5
	add x11, x23, x6
	extr x4, x11, x9, #32
	lsr x2, x11, #32
	adcs x13, x13, x4
	adcs x16, x16, x2
	adcs x14, x14, x27
	adc x21, x21, x27
	subs x1, x12, x1
	sbcs x3, x12, x3
	sbcs x5, x25, x5
	sbcs x4, x9, x4
	sbc x2, x11, x2
	adds x23, x23, x6
	adcs x3, x3, x25
	adcs x5, x5, x9
	adcs x11, x4, x11
	adc x2, x2, x27
	adds x3, x13, x3
	adcs x5, x16, x5
	adcs x11, x14, x11
	adcs x2, x21, x2
	adc x8, x27, x27
	adds x26, x3, x17
	sbcs x1, x5, x24
	sbcs x12, x11, x27
	sbcs x6, x2, x28
	sbcs x8, x8, x27
	csel x3, x26, x3, hs
	csel x1, x1, x5, hs
	csel x12, x12, x11, hs
	csel x6, x6, x2, hs
	subs x3, x3, x7
	sbcs x1, x1, x30
	sbcs x12, x12, x20
	ldr x23, [x0, #856]
	sbcs x6, x6, x23
	sbc x25, x27, x27
	adds x3, x3, x25
	lsr x9, x25, #32
	lsl x4, x25, #32
	adcs x1, x1, x9
	sub x4, x4, x25
	adcs x12, x12, x27
	adc x4, x6, x4
	subs x3, x3, x22
	sbcs x1, x1, x15
	ldr x13, [x0, #880]
	sbcs x12, x12, x13
	ldr x16, [x0, #888]
	sbcs x4, x4, x16
	sbc x14, x27, x27
	adds x3, x3, x14
	lsr x21, x14, #32
	lsl x8, x14, #32
	adcs x21, x1, x21
	sub x8, x8, x14
	adcs x12, x12, x27
	adc x4, x4, x8
	subs x3, x3, x22
	sbcs x21, x21, x15
	sbcs x12, x12, x13
	sbcs x4, x4, x16
	sbc x26, x27, x27
	lsr x5, x26, #32
	adds x3, x3, x26
	lsl x11, x26, #32
	adcs x21, x21, x5
	sub x11, x11, x26
	str x3, [x0, #608]
	adcs x12, x12, x27
	str x21, [x0, #616]
	adc x11, x4, x11
	subs x3, x22, x3
	sbcs x21, x15, x21
	sbcs x13, x13, x12
	str x12, [x0, #624]
	sbcs x16, x16, x11
	str x11, [x0, #632]
	sbc x2, x27, x27
	lsr x9, x2, #32
	adds x3, x3, x2
	lsl x25, x2, #32
	adcs x9, x21, x9
	sub x25, x25, x2
	ldr x6, [x0, #960]
	mul x1, x6, x3
	mul x14, x6, x9
	adcs x13, x13, x27
	mul x8, x6, x13
	adc x16, x16, x25
	umulh x5, x6, x3
	ldr x26, [x0, #968]
	mul x4, x26, x3
	umulh x22, x6, x9
	umulh x15, x6, x13
	lsl x12, x1, #32
	ldr x11, [x0, #7104]
	umulh x21, x1, x11
	lsr x2, x1, #32
	mul x1, x1, x11
	adds x14, x14, x5
	mul x25, x6, x16
	mul x5, x26, x9
	mul x23, x26, x13
	umulh x6, x6, x16
	adcs x8, x8, x22
	mul x22, x26, x16
	adcs x15, x25, x15
	umulh x25, x26, x16
	adcs x6, x27, x6
	umulh x20, x26, x3
	adds x14, x14, x12
	umulh x12, x26, x9
	adcs x8, x8, x2
	umulh x26, x26, x13
	adcs x15, x15, x1
	adcs x21, x6, x21
	adcs x2, x27, x27
	adds x14, x14, x4
	adcs x8, x8, x5
	lsl x1, x14, #32
	umulh x6, x14, x11
	mul x4, x14, x11
	lsr x14, x14, #32
	adcs x15, x15, x23
	adcs x22, x21, x22
	ldr x5, [x0, #976]
	mul x23, x5, x3
	adcs x25, x2, x25
	mul x21, x5, x9
	adds x8, x8, x20
	mul x2, x5, x13
	adcs x15, x15, x12
	mul x20, x5, x16
	adcs x22, x22, x26
	umulh x12, x5, x16
	adcs x25, x25, x27
	umulh x26, x5, x3
	adds x8, x8, x1
	umulh x1, x5, x9
	adcs x15, x15, x14
	umulh x5, x5, x13
	adcs x4, x22, x4
	adcs x25, x25, x6
	adcs x14, x27, x27
	adds x23, x8, x23
	adcs x21, x15, x21
	lsl x22, x23, #32
	umulh x6, x23, x11
	lsr x8, x23, #32
	mul x23, x23, x11
	adcs x2, x4, x2
	adcs x20, x25, x20
	mul x15, x10, x3
	adcs x12, x14, x12
	mul x4, x10, x9
	adds x21, x21, x26
	mul x25, x10, x13
	adcs x2, x2, x1
	mul x14, x10, x16
	adcs x20, x20, x5
	umulh x16, x10, x16
	adcs x12, x12, x27
	umulh x3, x10, x3
	adds x21, x21, x22
	umulh x9, x10, x9
	adcs x8, x2, x8
	umulh x13, x10, x13
	adcs x20, x20, x23
	adcs x12, x12, x6
	adcs x26, x27, x27
	adds x15, x21, x15
	adcs x4, x8, x4
	lsl x1, x15, #32
	mul x5, x15, x11
	umulh x22, x15, x11
	lsr x15, x15, #32
	adcs x25, x20, x25
	adcs x14, x12, x14
	adcs x16, x26, x16
	adds x4, x4, x3
	adcs x25, x25, x9
	adcs x14, x14, x13
	adcs x16, x16, x27
	adds x1, x4, x1
	adcs x25, x25, x15
	adcs x14, x14, x5
	adcs x16, x16, x22
	adcs x2, x27, x27
	adds x10, x1, x17
	sbcs x23, x25, x24
	sbcs x6, x14, x27
	sbcs x21, x16, x28
	sbcs x2, x2, x27
	ldr x8, [x0, #928]
	mul x20, x8, x7
	csel x1, x10, x1, hs
	mul x12, x8, x30
	csel x25, x23, x25, hs
	ldr x26, [x0, #848]
	mul x3, x8, x26
	csel x14, x6, x14, hs
	ldr x9, [x0, #856]
	mul x13, x8, x9
	csel x16, x21, x16, hs
	umulh x4, x8, x7
	umulh x15, x8, x30
	umulh x5, x8, x26
	lsl x22, x20, #32
	umulh x8, x8, x9
	ldr x2, [x0, #936]
	mul x10, x2, x7
	lsr x23, x20, #32
	umulh x6, x20, x11
	mul x21, x2, x30
	mul x20, x20, x11
	adds x4, x12, x4
	mul x12, x2, x26
	adcs x3, x3, x15
	mul x15, x2, x9
	adcs x13, x13, x5
	umulh x5, x2, x9
	adcs x8, x27, x8
	umulh x28, x2, x7
	adds x4, x4, x22
	umulh x22, x2, x30
	adcs x3, x3, x23
	umulh x2, x2, x26
	adcs x13, x13, x20
	adcs x8, x8, x6
	adcs x23, x27, x27
	adds x4, x4, x10
	adcs x21, x3, x21
	lsl x20, x4, #32
	mul x6, x4, x11
	lsr x10, x4, #32
	umulh x4, x4, x11
	adcs x12, x13, x12
	adcs x15, x8, x15
	ldr x3, [x0, #944]
	mul x13, x3, x7
	adcs x23, x23, x5
	adds x21, x21, x28
	mul x8, x3, x30
	mul x5, x3, x26
	adcs x12, x12, x22
	mul x28, x3, x9
	adcs x15, x15, x2
	umulh x22, x3, x9
	adcs x23, x23, x27
	adds x21, x21, x20
	umulh x2, x3, x7
	umulh x20, x3, x30
	adcs x12, x12, x10
	umulh x3, x3, x26
	adcs x15, x15, x6
	adcs x4, x23, x4
	adcs x10, x27, x27
	adds x13, x21, x13
	adcs x8, x12, x8
	lsl x6, x13, #32
	lsr x23, x13, #32
	umulh x21, x13, x11
	mul x13, x13, x11
	adcs x5, x15, x5
	adcs x28, x4, x28
	ldr x12, [x0, #952]
	mul x15, x12, x7
	adcs x22, x10, x22
	adds x8, x8, x2
	mul x4, x12, x30
	mul x10, x12, x26
	adcs x20, x5, x20
	mul x2, x12, x9
	adcs x28, x28, x3
	umulh x9, x12, x9
	adcs x22, x22, x27
	umulh x7, x12, x7
	adds x8, x8, x6
	umulh x30, x12, x30
	adcs x23, x20, x23
	umulh x26, x12, x26
	adcs x28, x28, x13
	adcs x22, x22, x21
	adcs x5, x27, x27
	adds x15, x8, x15
	adcs x23, x23, x4
	lsl x3, x15, #32
	umulh x6, x15, x11
	mul x20, x15, x11
	lsr x15, x15, #32
	adcs x10, x28, x10
	adcs x2, x22, x2
	adcs x9, x5, x9
	adds x23, x23, x7
	adcs x10, x10, x30
	adcs x2, x2, x26
	adcs x9, x9, x27
	adds x3, x23, x3
	adcs x10, x10, x15
	adcs x2, x2, x20
	adcs x9, x9, x6
	adcs x12, x27, x27
	adds x13, x3, x17
	sbcs x21, x10, x24
	sbcs x8, x2, x27
	ldr x4, [x0, #88]
	sbcs x28, x9, x4
	sbcs x12, x12, x27
	csel x3, x13, x3, hs
	csel x10, x21, x10, hs
	csel x2, x8, x2, hs
	csel x9, x28, x9, hs
	str x3, [x0, #928]
	str x2, [x0, #944]
	str x9, [x0, #952]
	str x10, [x0, #936]
	subs x3, x1, x3
	sbcs x25, x25, x10
	sbcs x14, x14, x2
	sbcs x9, x16, x9
	sbc x22, x27, x27
	lsr x5, x22, #32
	adds x3, x3, x22
	lsl x7, x22, #32
	adcs x5, x25, x5
	sub x7, x7, x22
	ldr x30, [x0, #576]
	ldr x26, [x0, #768]
	mul x23, x30, x26
	str x3, [x0, #640]
	ldr x15, [x0, #776]
	mul x20, x30, x15
	adcs x14, x14, x27
	str x5, [x0, #648]
	ldr x6, [x0, #784]
	mul x12, x30, x6
	adc x9, x9, x7
	str x14, [x0, #656]
	ldr x13, [x0, #792]
	mul x21, x30, x13
	str x9, [x0, #664]
	umulh x8, x30, x26
	umulh x28, x30, x15
	umulh x1, x30, x6
	ldr x10, [x0, #584]
	mul x2, x10, x26
	lsl x16, x23, #32
	umulh x30, x30, x13
	mul x25, x23, x11
	lsr x22, x23, #32
	mul x3, x10, x15
	umulh x23, x23, x11
	adds x8, x20, x8
	mul x5, x10, x6
	adcs x12, x12, x28
	mul x7, x10, x13
	adcs x21, x21, x1
	umulh x14, x10, x13
	adcs x30, x27, x30
	umulh x9, x10, x26
	adds x8, x8, x16
	umulh x20, x10, x15
	adcs x12, x12, x22
	umulh x10, x10, x6
	adcs x21, x21, x25
	adcs x30, x30, x23
	adcs x28, x27, x27
	adds x8, x8, x2
	adcs x3, x12, x3
	lsl x1, x8, #32
	lsr x16, x8, #32
	mul x22, x8, x11
	umulh x8, x8, x11
	adcs x5, x21, x5
	adcs x7, x30, x7
	ldr x25, [x0, #592]
	mul x23, x25, x26
	adcs x28, x28, x14
	mul x2, x25, x15
	adds x3, x3, x9
	mul x12, x25, x6
	adcs x5, x5, x20
	mul x21, x25, x13
	adcs x7, x7, x10
	umulh x30, x25, x13
	adcs x28, x28, x27
	umulh x14, x25, x26
	adds x3, x3, x1
	umulh x9, x25, x15
	adcs x5, x5, x16
	umulh x25, x25, x6
	adcs x7, x7, x22
	adcs x8, x28, x8
	adcs x20, x27, x27
	adds x23, x3, x23
	adcs x2, x5, x2
	lsl x10, x23, #32
	mul x1, x23, x11
	lsr x16, x23, #32
	umulh x23, x23, x11
	adcs x12, x7, x12
	adcs x21, x8, x21
	ldr x22, [x0, #600]
	mul x28, x22, x26
	adcs x30, x20, x30
	mul x3, x22, x15
	adds x2, x2, x14
	mul x5, x22, x6
	adcs x9, x12, x9
	mul x7, x22, x13
	adcs x21, x21, x25
	umulh x13, x22, x13
	adcs x30, x30, x27
	adds x2, x2, x10
	umulh x26, x22, x26
	umulh x15, x22, x15
	adcs x16, x9, x16
	umulh x6, x22, x6
	adcs x21, x21, x1
	adcs x30, x30, x23
	adcs x8, x27, x27
	adds x28, x2, x28
	adcs x16, x16, x3
	lsl x20, x28, #32
	lsr x14, x28, #32
	mul x12, x28, x11
	umulh x28, x28, x11
	adcs x5, x21, x5
	adcs x7, x30, x7
	adcs x13, x8, x13
	adds x16, x16, x26
	adcs x5, x5, x15
	adcs x7, x7, x6
	adcs x13, x13, x27
	adds x20, x16, x20
	adcs x5, x5, x14
	adcs x7, x7, x12
	adcs x13, x13, x28
	adcs x25, x27, x27
	adds x10, x20, x17
	sbcs x9, x5, x24
	sbcs x22, x7, x27
	sbcs x1, x13, x4
	sbcs x25, x25, x27
	csel x20, x10, x20, hs
	csel x5, x9, x5, hs
	csel x7, x22, x7, hs
	csel x13, x1, x13, hs
	ldr x23, [x0, #896]
	umulh x2, x20, x23
	ldr x3, [x0, #904]
	mul x21, x20, x3
	mul x30, x20, x23
	umulh x8, x20, x3
	ldr x26, [x0, #912]
	mul x15, x20, x26
	umulh x6, x20, x26
	ldr x16, [x0, #920]
	umulh x14, x20, x16
	mul x12, x5, x23
	mul x20, x20, x16
	mul x28, x5, x3
	lsl x25, x30, #32
	umulh x10, x30, x11
	lsr x9, x30, #32
	mul x30, x30, x11
	adds x2, x21, x2
	mul x22, x5, x26
	adcs x8, x15, x8
	mul x1, x5, x16
	adcs x20, x20, x6
	umulh x21, x5, x16
	adcs x14, x27, x14
	umulh x15, x5, x23
	adds x2, x2, x25
	umulh x6, x5, x3
	adcs x9, x8, x9
	umulh x5, x5, x26
	adcs x20, x20, x30
	adcs x14, x14, x10
	adcs x25, x27, x27
	adds x2, x2, x12
	adcs x28, x9, x28
	lsl x8, x2, #32
	umulh x30, x2, x11
	lsr x10, x2, #32
	mul x2, x2, x11
	adcs x22, x20, x22
	adcs x1, x14, x1
	mul x12, x7, x23
	adcs x21, x25, x21
	mul x9, x7, x3
	adds x28, x28, x15
	mul x20, x7, x26
	adcs x22, x22, x6
	mul x14, x7, x16
	adcs x1, x1, x5
	umulh x25, x7, x16
	adcs x21, x21, x27
	umulh x15, x7, x23
	adds x8, x28, x8
	umulh x6, x7, x3
	adcs x22, x22, x10
	umulh x7, x7, x26
	adcs x1, x1, x2
	adcs x21, x21, x30
	adcs x5, x27, x27
	adds x12, x8, x12
	adcs x9, x22, x9
	lsl x28, x12, #32
	mul x10, x12, x11
	umulh x2, x12, x11
	lsr x12, x12, #32
	adcs x20, x1, x20
	adcs x21, x21, x14
	mul x30, x13, x23
	adcs x5, x5, x25
	mul x8, x13, x3
	adds x9, x9, x15
	mul x22, x13, x26
	adcs x20, x20, x6
	mul x1, x13, x16
	adcs x21, x21, x7
	umulh x16, x13, x16
	adcs x5, x5, x27
	umulh x23, x13, x23
	adds x9, x9, x28
	umulh x3, x13, x3
	adcs x20, x20, x12
	umulh x26, x13, x26
	adcs x21, x21, x10
	adcs x2, x5, x2
	adcs x14, x27, x27
	adds x30, x9, x30
	adcs x20, x20, x8
	lsl x25, x30, #32
	lsr x15, x30, #32
	mul x6, x30, x11
	umulh x30, x30, x11
	adcs x21, x21, x22
	adcs x1, x2, x1
	adcs x16, x14, x16
	adds x20, x20, x23
	adcs x21, x21, x3
	adcs x1, x1, x26
	adcs x16, x16, x27
	adds x20, x20, x25
	adcs x21, x21, x15
	adcs x6, x1, x6
	adcs x16, x16, x30
	adcs x7, x27, x27
	adds x17, x20, x17
	sbcs x24, x21, x24
	sbcs x28, x6, x27
	sbcs x4, x16, x4
	sbcs x7, x7, x27
	csel x28, x28, x6, hs
	csel x17, x17, x20, hs
	csel x4, x4, x16, hs
	csel x21, x24, x21, hs
	str x28, [x0, #688]
	str x21, [x0, #680]
	str x4, [x0, #696]
	str x17, [x0, #672]
	movz x7, #0, lsl #0
	ldr x1, [x0, #576]
	ldr x2, [x0, #584]
	orr x1, x1, x2
	ldr x2, [x0, #592]
	orr x1, x1, x2
	ldr x2, [x0, #600]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x3, x7, x7
	ldr x1, [x0, #704]
	ldr x2, [x0, #608]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #608]
	ldr x1, [x0, #712]
	ldr x2, [x0, #616]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #616]
	ldr x1, [x0, #720]
	ldr x2, [x0, #624]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #624]
	ldr x1, [x0, #728]
	ldr x2, [x0, #632]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #632]
	ldr x1, [x0, #736]
	ldr x2, [x0, #640]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #640]
	ldr x1, [x0, #744]
	ldr x2, [x0, #648]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #648]
	ldr x1, [x0, #752]
	ldr x2, [x0, #656]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #656]
	ldr x1, [x0, #760]
	ldr x2, [x0, #664]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #664]
	ldr x1, [x0, #768]
	ldr x2, [x0, #672]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #672]
	ldr x1, [x0, #776]
	ldr x2, [x0, #680]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #680]
	ldr x1, [x0, #784]
	ldr x2, [x0, #688]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #688]
	ldr x1, [x0, #792]
	ldr x2, [x0, #696]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #696]
	movz x16, #5, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	movz x2, #0, lsl #0
	add x2, x2, x2
	ldrb w4, [x16, #1828]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1827]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1826]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1825]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1824]
	add x2, x2, x4
	sub x3, x2, #16
	lsr x4, x3, #63
	movz x9, #0, lsl #0
	sub x4, x9, x4
	eor x2, x3, x4
	sub x2, x2, x4
	movz x7, #0, lsl #0
	movz x5, #1, lsl #0
	subs x16, x2, x5
	sbc x3, x7, x7
	ldr x1, [x0, #608]
	ldr x2, [x0, #512]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #512]
	ldr x1, [x0, #616]
	ldr x2, [x0, #520]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #520]
	ldr x1, [x0, #624]
	ldr x2, [x0, #528]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #528]
	ldr x1, [x0, #632]
	ldr x2, [x0, #536]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #536]
	ldr x1, [x0, #640]
	ldr x2, [x0, #544]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #544]
	ldr x1, [x0, #648]
	ldr x2, [x0, #552]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #552]
	ldr x1, [x0, #656]
	ldr x2, [x0, #560]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #560]
	ldr x1, [x0, #664]
	ldr x2, [x0, #568]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #568]
	ldr x1, [x0, #672]
	ldr x2, [x0, #576]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #576]
	ldr x1, [x0, #680]
	ldr x2, [x0, #584]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #584]
	ldr x1, [x0, #688]
	ldr x2, [x0, #592]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #592]
	ldr x1, [x0, #696]
	ldr x2, [x0, #600]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #600]
	cbnz x19, 22b
	movz x7, #0, lsl #0
	ldr x1, [x0, #576]
	ldr x2, [x0, #584]
	orr x1, x1, x2
	ldr x2, [x0, #592]
	orr x1, x1, x2
	ldr x2, [x0, #600]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x3, x7, x7
	ldr x1, [x0, #160]
	ldr x2, [x0, #544]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #544]
	ldr x1, [x0, #168]
	ldr x2, [x0, #552]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #552]
	ldr x1, [x0, #176]
	ldr x2, [x0, #560]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #560]
	ldr x1, [x0, #184]
	ldr x2, [x0, #568]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #568]
	sub x4, x7, #1
	eor x3, x3, x4
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #544]
	orr x1, x1, x2
	str x1, [x0, #544]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #552]
	orr x1, x1, x2
	str x1, [x0, #552]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #560]
	orr x1, x1, x2
	str x1, [x0, #560]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #568]
	orr x1, x1, x2
	str x1, [x0, #568]
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
	str x12, [x0, #512]
	str x13, [x0, #520]
	str x8, [x0, #528]
	str x9, [x0, #536]
	ldr x3, [x0, #576]
	ldr x4, [x0, #584]
	orr x5, x16, x16
	orr x6, x17, x17
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
	orr x1, x8, x8
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
	str x12, [x0, #576]
	str x13, [x0, #584]
	str x8, [x0, #592]
	str x9, [x0, #600]
	ldr x26, [x0, #7800]
	ldr x27, [x0, #7808]
	ldr x28, [x0, #7816]
	ldr x30, [x0, #7824]
	ldr x20, [x0, #7832]
	str x21, [x0, #7800]
	str x22, [x0, #7808]
	str x23, [x0, #7816]
	str x24, [x0, #7824]
	str x25, [x0, #7832]
	str x26, [x0, #7840]
	str x27, [x0, #7848]
	str x28, [x0, #7856]
	str x30, [x0, #7864]
	movz x27, #0, lsl #0
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #10, lsl #0
	ldr x2, [x0, #64]
	str x2, [x0, #2272]
	ldr x2, [x0, #72]
	str x2, [x0, #2280]
	ldr x2, [x0, #80]
	str x2, [x0, #2288]
	ldr x2, [x0, #88]
	str x2, [x0, #2296]
	str x12, [x0, #2304]
	ldr x2, [x0, #576]
	str x2, [x0, #2312]
	ldr x2, [x0, #584]
	str x2, [x0, #2320]
	ldr x2, [x0, #592]
	str x2, [x0, #2328]
	ldr x2, [x0, #600]
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
24:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #2272]
	ldr x3, [x0, #2312]
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #1, lsl #0
	movz x28, #65535, lsl #0
	movk x28, #15, lsl #16
	and x4, x2, x28
	movz x28, #0, lsl #0
	movk x28, #65024, lsl #32
	movk x28, #65535, lsl #48
	orr x4, x4, x28
	movz x28, #65535, lsl #0
	movk x28, #15, lsl #16
	and x5, x3, x28
	movz x28, #0, lsl #0
	movk x28, #49152, lsl #48
	orr x5, x5, x28
	movz x28, #1, lsl #0
	tst x5, x28
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	movz x28, #0, lsl #0
	movk x28, #16, lsl #16
	add x8, x4, x28
	lsl x8, x8, #22
	lsr x26, x8, #63
	sub x26, x27, x26
	extr x8, x26, x8, #43
	movz x11, #0, lsl #0
	movk x11, #16, lsl #16
	lsl x28, x11, #21
	add x11, x11, x28
	add x9, x4, x11
	lsr x26, x9, #63
	sub x26, x27, x26
	extr x9, x26, x9, #42
	movz x28, #0, lsl #0
	movk x28, #16, lsl #16
	add x10, x5, x28
	lsl x10, x10, #22
	lsr x26, x10, #63
	sub x26, x27, x26
	extr x10, x26, x10, #43
	add x11, x5, x11
	lsr x26, x11, #63
	sub x26, x27, x26
	extr x11, x26, x11, #42
	mul x6, x8, x2
	mul x7, x9, x3
	mul x2, x10, x2
	mul x3, x11, x3
	add x4, x6, x7
	add x5, x2, x3
	lsr x26, x4, #63
	sub x26, x27, x26
	extr x2, x26, x4, #20
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x3, x26, x5, #20
	movz x28, #65535, lsl #0
	movk x28, #15, lsl #16
	and x4, x2, x28
	movz x28, #0, lsl #0
	movk x28, #65024, lsl #32
	movk x28, #65535, lsl #48
	orr x4, x4, x28
	movz x28, #65535, lsl #0
	movk x28, #15, lsl #16
	and x5, x3, x28
	movz x28, #0, lsl #0
	movk x28, #49152, lsl #48
	orr x5, x5, x28
	movz x28, #1, lsl #0
	tst x5, x28
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	movz x28, #0, lsl #0
	movk x28, #16, lsl #16
	add x12, x4, x28
	lsl x12, x12, #22
	lsr x26, x12, #63
	sub x26, x27, x26
	extr x12, x26, x12, #43
	movz x15, #0, lsl #0
	movk x15, #16, lsl #16
	lsl x28, x15, #21
	add x15, x15, x28
	add x13, x4, x15
	lsr x26, x13, #63
	sub x26, x27, x26
	extr x13, x26, x13, #42
	movz x28, #0, lsl #0
	movk x28, #16, lsl #16
	add x14, x5, x28
	lsl x14, x14, #22
	lsr x26, x14, #63
	sub x26, x27, x26
	extr x14, x26, x14, #43
	add x15, x5, x15
	lsr x26, x15, #63
	sub x26, x27, x26
	extr x15, x26, x15, #42
	mul x6, x12, x2
	mul x7, x13, x3
	mul x2, x14, x2
	mul x3, x15, x3
	add x4, x6, x7
	add x5, x2, x3
	lsr x26, x4, #63
	sub x26, x27, x26
	extr x2, x26, x4, #20
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x3, x26, x5, #20
	movz x28, #65535, lsl #0
	movk x28, #15, lsl #16
	and x4, x2, x28
	movz x28, #0, lsl #0
	movk x28, #65024, lsl #32
	movk x28, #65535, lsl #48
	orr x4, x4, x28
	movz x28, #65535, lsl #0
	movk x28, #15, lsl #16
	and x5, x3, x28
	movz x28, #0, lsl #0
	movk x28, #49152, lsl #48
	orr x5, x5, x28
	movz x28, #1, lsl #0
	tst x5, x28
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	mul x2, x12, x8
	mul x3, x12, x9
	mul x6, x14, x8
	mul x7, x14, x9
	madd x8, x13, x10, x2
	madd x9, x13, x11, x3
	madd x16, x15, x10, x6
	madd x17, x15, x11, x7
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	movz x28, #2, lsl #0
	tst x5, x28
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	csel x6, x4, x27, ne
	ccmp x1, #0, #8, ne
	csneg x1, x1, x1, lt
	csneg x6, x6, x6, lt
	csel x4, x5, x4, ge
	add x5, x5, x6
	add x1, x1, #2
	lsr x26, x5, #63
	sub x26, x27, x26
	extr x5, x26, x5, #1
	movz x28, #0, lsl #0
	movk x28, #16, lsl #16
	add x12, x4, x28
	lsl x12, x12, #21
	lsr x26, x12, #63
	sub x26, x27, x26
	extr x12, x26, x12, #43
	movz x15, #0, lsl #0
	movk x15, #16, lsl #16
	lsl x28, x15, #21
	add x15, x15, x28
	add x13, x4, x15
	lsr x26, x13, #63
	sub x26, x27, x26
	extr x13, x26, x13, #43
	movz x28, #0, lsl #0
	movk x28, #16, lsl #16
	add x14, x5, x28
	lsl x14, x14, #21
	lsr x26, x14, #63
	sub x26, x27, x26
	extr x14, x26, x14, #43
	add x15, x5, x15
	lsr x26, x15, #63
	sub x26, x27, x26
	extr x15, x26, x15, #43
	mul x2, x12, x8
	sub x2, x27, x2
	mul x3, x12, x9
	sub x3, x27, x3
	mul x4, x14, x8
	sub x4, x27, x4
	mul x5, x14, x9
	sub x5, x27, x5
	mul x26, x13, x16
	sub x10, x2, x26
	mul x26, x13, x17
	sub x11, x3, x26
	mul x26, x15, x16
	sub x12, x4, x26
	mul x26, x15, x17
	sub x13, x5, x26
	orr x4, x10, x10
	orr x5, x11, x11
	orr x6, x12, x12
	orr x7, x13, x13
	ldr x2, [x0, #2272]
	ldr x3, [x0, #2280]
	ldr x8, [x0, #2288]
	umulh x9, x4, x2
	mul x10, x4, x3
	ldr x11, [x0, #2296]
	umulh x12, x4, x3
	mul x13, x4, x8
	ldr x14, [x0, #2304]
	umulh x15, x4, x8
	movz x16, #0, lsl #0
	adds x9, x10, x9
	mul x10, x4, x11
	ldr x17, [x0, #2312]
	adc x12, x12, x16
	umulh x21, x4, x11
	adds x12, x13, x12
	mul x13, x4, x14
	adc x15, x15, x16
	umulh x22, x4, x14
	adds x10, x10, x15
	mul x15, x5, x17
	ldr x23, [x0, #2320]
	adc x21, x21, x16
	umulh x24, x5, x17
	mul x25, x4, x2
	adds x13, x13, x21
	adc x21, x22, x16
	adds x15, x15, x16
	mul x21, x5, x23
	ldr x22, [x0, #2328]
	adc x24, x24, x16
	umulh x26, x5, x23
	adds x15, x25, x15
	adc x24, x24, x16
	adds x21, x21, x24
	mul x24, x5, x22
	ldr x25, [x0, #2336]
	adc x26, x26, x16
	umulh x28, x5, x22
	adds x9, x9, x21
	adc x21, x26, x16
	adds x21, x24, x21
	mul x24, x5, x25
	ldr x26, [x0, #2344]
	adc x28, x28, x16
	umulh x30, x5, x25
	adds x12, x12, x21
	adc x21, x28, x16
	adds x21, x24, x21
	mul x24, x5, x26
	adc x28, x30, x16
	umulh x30, x5, x26
	adds x10, x10, x21
	adc x21, x28, x16
	adds x21, x24, x21
	lsr x24, x4, #63
	adc x28, x30, x16
	sub x24, x16, x24
	adds x13, x13, x21
	adc x21, x28, x16
	and x21, x2, x24
	subs x9, x9, x21
	and x21, x3, x24
	lsr x28, x5, #63
	sbcs x12, x12, x21
	and x21, x8, x24
	sub x28, x16, x28
	sbcs x10, x10, x21
	and x21, x11, x24
	sbcs x13, x13, x21
	and x21, x17, x28
	subs x9, x9, x21
	and x21, x23, x28
	umulh x24, x6, x2
	mul x30, x6, x3
	sbcs x12, x12, x21
	and x21, x22, x28
	str x12, [x0, #7104]
	umulh x12, x6, x3
	sbcs x10, x10, x21
	and x21, x25, x28
	mul x28, x6, x8
	sbcs x13, x13, x21
	umulh x21, x6, x8
	adds x24, x30, x24
	mul x30, x6, x11
	adc x12, x12, x16
	str x13, [x0, #7112]
	umulh x13, x6, x11
	adds x12, x28, x12
	mul x28, x6, x14
	adc x21, x21, x16
	umulh x14, x6, x14
	adds x21, x30, x21
	mul x30, x7, x17
	adc x13, x13, x16
	str x10, [x0, #7120]
	umulh x10, x7, x17
	str x9, [x0, #7128]
	mul x9, x6, x2
	adds x13, x28, x13
	adc x14, x14, x16
	adds x14, x30, x16
	mul x28, x7, x23
	adc x10, x10, x16
	umulh x30, x7, x23
	adds x9, x9, x14
	adc x10, x10, x16
	adds x10, x28, x10
	mul x14, x7, x22
	adc x28, x30, x16
	umulh x30, x7, x22
	adds x10, x24, x10
	adc x24, x28, x16
	adds x14, x14, x24
	mul x24, x7, x25
	adc x28, x30, x16
	umulh x30, x7, x25
	adds x12, x12, x14
	adc x14, x28, x16
	adds x14, x24, x14
	mul x24, x7, x26
	adc x28, x30, x16
	umulh x26, x7, x26
	adds x14, x21, x14
	adc x21, x28, x16
	adds x21, x24, x21
	lsr x24, x6, #63
	adc x26, x26, x16
	sub x24, x16, x24
	adds x13, x13, x21
	adc x21, x26, x16
	and x2, x2, x24
	subs x2, x10, x2
	and x3, x3, x24
	ldr x10, [x0, #2352]
	ldr x21, [x0, #2360]
	lsr x26, x7, #63
	sbcs x3, x12, x3
	and x8, x8, x24
	sub x12, x16, x26
	sbcs x8, x14, x8
	and x11, x11, x24
	ldr x14, [x0, #2368]
	sbcs x11, x13, x11
	and x13, x17, x12
	subs x2, x2, x13
	and x13, x23, x12
	umulh x17, x4, x10
	mul x23, x4, x21
	ldr x24, [x0, #2376]
	sbcs x3, x3, x13
	and x13, x22, x12
	umulh x22, x4, x21
	sbcs x8, x8, x13
	and x12, x25, x12
	mul x13, x4, x14
	ldr x25, [x0, #2384]
	sbcs x11, x11, x12
	umulh x12, x4, x14
	adds x17, x23, x17
	mul x23, x4, x24
	adc x22, x22, x16
	umulh x26, x4, x24
	adds x13, x13, x22
	mul x22, x5, x25
	ldr x28, [x0, #2392]
	adc x12, x12, x16
	umulh x30, x5, x25
	str x7, [x0, #7136]
	mul x7, x4, x10
	adds x12, x23, x12
	adc x23, x26, x16
	adds x22, x22, x16
	mul x26, x5, x28
	str x6, [x0, #7144]
	ldr x6, [x0, #2400]
	adc x30, x30, x16
	str x25, [x0, #7152]
	umulh x25, x5, x28
	adds x7, x7, x22
	adc x22, x30, x16
	adds x22, x26, x22
	mul x26, x5, x6
	ldr x30, [x0, #2408]
	adc x25, x25, x16
	adds x17, x17, x22
	umulh x22, x5, x6
	adc x25, x25, x16
	adds x25, x26, x25
	mul x26, x5, x30
	adc x22, x22, x16
	adds x13, x13, x25
	umulh x25, x5, x30
	adc x22, x22, x16
	adds x22, x26, x22
	adc x25, x25, x16
	movz x26, #1, lsl #0
	lsr x4, x4, #63
	adds x12, x12, x22
	sub x4, x16, x4
	adc x22, x25, x16
	adds x22, x23, x22
	orr x23, x26, x26
	movk x23, #0, lsl #16
	movk x23, #0, lsl #32
	movk x23, #0, lsl #48
	mul x23, x7, x23
	lsr x5, x5, #63
	sub x5, x16, x5
	movk x26, #0, lsl #16
	movk x26, #0, lsl #32
	movk x26, #0, lsl #48
	ldr x25, [x0, #7128]
	extr x15, x25, x15, #59
	str x15, [x0, #2272]
	ldr x15, [x0, #7104]
	extr x25, x15, x25, #59
	str x26, [x0, #7128]
	ldr x26, [x0, #7120]
	extr x15, x26, x15, #59
	str x7, [x0, #7104]
	ldr x7, [x0, #7112]
	extr x26, x7, x26, #59
	extr x9, x2, x9, #59
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x11, x8, #59
	str x25, [x0, #2280]
	and x25, x10, x4
	subs x17, x17, x25
	and x25, x21, x4
	sbcs x13, x13, x25
	ldr x25, [x0, #64]
	str x15, [x0, #2288]
	and x15, x14, x4
	sbcs x12, x12, x15
	and x4, x24, x4
	sbcs x4, x22, x4
	ldr x15, [x0, #7152]
	and x22, x15, x5
	subs x17, x17, x22
	and x22, x28, x5
	str x11, [x0, #7120]
	mul x11, x23, x25
	sbcs x13, x13, x22
	ldr x22, [x0, #72]
	str x26, [x0, #2296]
	and x26, x6, x5
	sbcs x12, x12, x26
	umulh x26, x23, x25
	and x5, x30, x5
	sbcs x4, x4, x5
	adds x5, x11, x16
	mul x11, x23, x22
	adc x26, x26, x16
	ldr x7, [x0, #7104]
	adds x5, x7, x5
	ldr x5, [x0, #80]
	umulh x7, x23, x22
	adc x26, x26, x16
	adds x11, x11, x26
	mul x26, x23, x5
	adc x7, x7, x16
	adds x11, x17, x11
	ldr x17, [x0, #88]
	adc x7, x7, x16
	adds x7, x26, x7
	umulh x26, x23, x5
	adc x26, x26, x16
	adds x7, x13, x7
	mul x13, x23, x17
	umulh x23, x23, x17
	adc x26, x26, x16
	adds x13, x13, x26
	adc x23, x23, x16
	adds x12, x12, x13
	lsr x13, x4, #63
	adc x23, x23, x16
	sub x13, x16, x13
	adds x4, x4, x23
	adcs x13, x13, x16
	lsr x23, x13, #63
	sub x23, x16, x23
	and x26, x25, x23
	adds x11, x11, x26
	and x26, x22, x23
	adcs x7, x7, x26
	and x26, x5, x23
	adcs x12, x12, x26
	and x23, x17, x23
	adcs x4, x4, x23
	add x23, x16, x16
	adcs x13, x13, x23
	subs x11, x11, x25
	sbcs x7, x7, x22
	sbcs x12, x12, x5
	sbcs x4, x4, x17
	add x23, x16, x16
	sbcs x13, x13, x23
	lsr x23, x13, #63
	sub x23, x16, x23
	and x26, x25, x23
	adds x11, x11, x26
	and x26, x22, x23
	adcs x7, x7, x26
	and x26, x5, x23
	adcs x12, x12, x26
	ldr x26, [x0, #7144]
	str x12, [x0, #7104]
	umulh x12, x26, x10
	and x23, x17, x23
	adcs x4, x4, x23
	mul x23, x26, x21
	str x9, [x0, #2312]
	umulh x9, x26, x21
	str x2, [x0, #2320]
	add x2, x16, x16
	adcs x2, x13, x2
	mul x2, x26, x14
	umulh x13, x26, x14
	adds x12, x23, x12
	mul x23, x26, x24
	adc x9, x9, x16
	adds x2, x2, x9
	umulh x9, x26, x24
	adc x13, x13, x16
	adds x13, x23, x13
	ldr x23, [x0, #7136]
	str x4, [x0, #7160]
	mul x4, x23, x15
	adc x9, x9, x16
	adds x4, x4, x16
	str x3, [x0, #2328]
	umulh x3, x23, x15
	adc x3, x3, x16
	str x8, [x0, #2336]
	mul x8, x26, x10
	adds x4, x8, x4
	mul x8, x23, x28
	adc x3, x3, x16
	adds x3, x8, x3
	umulh x8, x23, x28
	adc x8, x8, x16
	adds x3, x12, x3
	mul x12, x23, x6
	adc x8, x8, x16
	adds x8, x12, x8
	umulh x12, x23, x6
	adc x12, x12, x16
	adds x2, x2, x8
	mul x8, x23, x30
	adc x12, x12, x16
	adds x8, x8, x12
	umulh x12, x23, x30
	adc x12, x12, x16
	lsr x26, x26, #63
	adds x8, x13, x8
	sub x13, x16, x26
	adc x12, x12, x16
	adds x9, x9, x12
	and x10, x10, x13
	subs x3, x3, x10
	and x10, x21, x13
	ldr x12, [x0, #7128]
	mul x12, x4, x12
	lsr x21, x23, #63
	sbcs x2, x2, x10
	and x10, x14, x13
	sub x14, x16, x21
	sbcs x8, x8, x10
	and x10, x24, x13
	sbcs x9, x9, x10
	and x10, x15, x14
	subs x3, x3, x10
	and x10, x28, x14
	mul x13, x12, x25
	sbcs x2, x2, x10
	and x6, x6, x14
	umulh x10, x12, x25
	sbcs x6, x8, x6
	and x8, x30, x14
	sbcs x8, x9, x8
	adds x9, x13, x16
	mul x13, x12, x22
	adc x10, x10, x16
	umulh x14, x12, x22
	adds x4, x4, x9
	adc x4, x10, x16
	adds x4, x13, x4
	mul x9, x12, x5
	adc x10, x14, x16
	umulh x13, x12, x5
	adds x3, x3, x4
	adc x4, x10, x16
	adds x4, x9, x4
	mul x9, x12, x17
	adc x10, x13, x16
	umulh x12, x12, x17
	adds x2, x2, x4
	adc x4, x10, x16
	adds x4, x9, x4
	adc x9, x12, x16
	adds x4, x6, x4
	lsr x6, x8, #63
	adc x9, x9, x16
	sub x6, x16, x6
	adds x8, x8, x9
	adcs x6, x6, x16
	lsr x9, x6, #63
	sub x9, x16, x9
	and x10, x25, x9
	adds x3, x3, x10
	and x10, x22, x9
	adcs x2, x2, x10
	and x10, x5, x9
	adcs x4, x4, x10
	and x9, x17, x9
	adcs x8, x8, x9
	add x9, x16, x16
	adcs x6, x6, x9
	subs x3, x3, x25
	sbcs x2, x2, x22
	sbcs x4, x4, x5
	sbcs x8, x8, x17
	add x9, x16, x16
	sbcs x6, x6, x9
	lsr x9, x6, #63
	sub x9, x16, x9
	and x10, x25, x9
	adds x3, x3, x10
	and x10, x22, x9
	ldr x12, [x0, #7112]
	lsr x13, x12, #63
	ldr x14, [x0, #7120]
	lsr x15, x14, #63
	adcs x2, x2, x10
	and x5, x5, x9
	sub x10, x16, x13
	sub x13, x16, x15
	adcs x4, x4, x5
	and x5, x17, x9
	extr x9, x10, x12, #59
	extr x10, x13, x14, #59
	adcs x5, x8, x5
	add x8, x16, x16
	str x9, [x0, #2304]
	str x10, [x0, #2344]
	adcs x6, x6, x8
	str x3, [x0, #2384]
	str x2, [x0, #2392]
	str x4, [x0, #2400]
	str x5, [x0, #2408]
	str x11, [x0, #2352]
	str x7, [x0, #2360]
	ldr x2, [x0, #7104]
	str x2, [x0, #2368]
	ldr x2, [x0, #7160]
	str x2, [x0, #2376]
	cbnz x19, 24b
	movz x12, #0, lsl #0
	ldr x3, [x0, #2272]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #0, lsl #0
	movk x2, #96, lsl #16
	movk x2, #0, lsl #32
	movk x2, #40, lsl #48
	movz x3, #65535, lsl #0
	movk x3, #65439, lsl #16
	movk x3, #65535, lsl #32
	movk x3, #65495, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2416]
	movz x2, #0, lsl #0
	movk x2, #65524, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65407, lsl #48
	movz x3, #65535, lsl #0
	movk x3, #11, lsl #16
	movk x3, #1, lsl #32
	movk x3, #128, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2424]
	movz x2, #65535, lsl #0
	movk x2, #65463, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65523, lsl #48
	movz x3, #0, lsl #0
	movk x3, #72, lsl #16
	movk x3, #0, lsl #32
	movk x3, #12, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2432]
	movz x2, #65535, lsl #0
	movk x2, #65463, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #99, lsl #48
	movz x3, #1, lsl #0
	movk x3, #72, lsl #16
	movk x3, #65535, lsl #32
	movk x3, #65435, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2440]
	movz x7, #0, lsl #0
	ldr x4, [x0, #2416]
	ldr x5, [x0, #2424]
	ldr x16, [x0, #2432]
	ldr x17, [x0, #2440]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	str x12, [x0, #992]
	str x13, [x0, #1000]
	str x8, [x0, #1008]
	str x9, [x0, #1016]
	ldr x21, [x0, #7800]
	ldr x22, [x0, #7808]
	ldr x23, [x0, #7816]
	ldr x24, [x0, #7824]
	ldr x25, [x0, #7832]
	ldr x26, [x0, #7840]
	ldr x27, [x0, #7848]
	ldr x28, [x0, #7856]
	ldr x30, [x0, #7864]
	movz x7, #0, lsl #0
	ldr x4, [x0, #992]
	ldr x5, [x0, #1000]
	ldr x16, [x0, #1008]
	ldr x17, [x0, #1016]
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
	str x12, [x0, #1152]
	str x13, [x0, #1160]
	str x8, [x0, #1168]
	str x9, [x0, #1176]
	movz x7, #0, lsl #0
	ldr x4, [x0, #192]
	ldr x5, [x0, #200]
	ldr x16, [x0, #208]
	ldr x17, [x0, #216]
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
