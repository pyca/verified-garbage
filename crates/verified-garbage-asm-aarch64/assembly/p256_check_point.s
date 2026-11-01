// The functions of `src/p256_check_point.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p256_check_point:
	movz x7, #0, lsl #0
	ldr x1, [x0, #1120]
	ldr x2, [x0, #64]
	subs x16, x1, x2
	ldr x1, [x0, #1128]
	ldr x2, [x0, #72]
	sbcs x16, x1, x2
	ldr x1, [x0, #1136]
	ldr x2, [x0, #80]
	sbcs x16, x1, x2
	ldr x1, [x0, #1144]
	ldr x2, [x0, #88]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1216]
	ldr x2, [x0, #64]
	subs x16, x1, x2
	ldr x1, [x0, #1224]
	ldr x2, [x0, #72]
	sbcs x16, x1, x2
	ldr x1, [x0, #1232]
	ldr x2, [x0, #80]
	sbcs x16, x1, x2
	ldr x1, [x0, #1240]
	ldr x2, [x0, #88]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1120]
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
	ldr x1, [x0, #1128]
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
	ldr x1, [x0, #1136]
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
	ldr x1, [x0, #1144]
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
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1216]
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
	ldr x1, [x0, #1224]
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
	ldr x1, [x0, #1232]
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
	ldr x1, [x0, #1240]
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
	ldr x4, [x0, #1184]
	ldr x5, [x0, #1192]
	ldr x16, [x0, #1200]
	ldr x17, [x0, #1208]
	mul x9, x5, x4
	umulh x2, x5, x4
	mul x10, x16, x4
	umulh x3, x16, x4
	mul x11, x17, x4
	umulh x12, x17, x4
	adds x10, x10, x2
	mul x1, x16, x5
	umulh x2, x16, x5
	adcs x11, x11, x3
	mul x3, x17, x5
	umulh x6, x17, x5
	adc x12, x12, x7
	mul x13, x17, x16
	umulh x14, x17, x16
	adds x2, x2, x3
	mul x8, x4, x4
	adc x3, x6, x7
	adds x11, x11, x1
	umulh x4, x4, x4
	adcs x12, x12, x2
	mul x2, x5, x5
	adcs x13, x13, x3
	umulh x5, x5, x5
	adc x14, x14, x7
	adds x9, x9, x9
	mul x3, x16, x16
	adcs x10, x10, x10
	umulh x16, x16, x16
	adcs x11, x11, x11
	mul x6, x17, x17
	adcs x12, x12, x12
	umulh x17, x17, x17
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x15, x7, x7
	adds x9, x9, x4
	adcs x10, x10, x2
	adcs x11, x11, x5
	adcs x12, x12, x3
	adcs x13, x13, x16
	lsl x1, x8, #32
	adcs x14, x14, x6
	lsr x2, x8, #32
	adc x15, x15, x17
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	adcs x10, x11, x3
	adc x11, x6, x7
	adds x8, x8, x12
	adcs x9, x9, x13
	adcs x10, x10, x14
	adcs x11, x11, x15
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
	str x8, [x0, #1248]
	str x9, [x0, #1256]
	str x10, [x0, #1264]
	str x11, [x0, #1272]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1152]
	ldr x5, [x0, #1160]
	ldr x16, [x0, #1168]
	ldr x17, [x0, #1176]
	mul x9, x5, x4
	umulh x2, x5, x4
	mul x10, x16, x4
	umulh x3, x16, x4
	mul x11, x17, x4
	umulh x12, x17, x4
	adds x10, x10, x2
	mul x1, x16, x5
	umulh x2, x16, x5
	adcs x11, x11, x3
	mul x3, x17, x5
	umulh x6, x17, x5
	adc x12, x12, x7
	mul x13, x17, x16
	umulh x14, x17, x16
	adds x2, x2, x3
	mul x8, x4, x4
	adc x3, x6, x7
	adds x11, x11, x1
	umulh x4, x4, x4
	adcs x12, x12, x2
	mul x2, x5, x5
	adcs x13, x13, x3
	umulh x5, x5, x5
	adc x14, x14, x7
	adds x9, x9, x9
	mul x3, x16, x16
	adcs x10, x10, x10
	umulh x16, x16, x16
	adcs x11, x11, x11
	mul x6, x17, x17
	adcs x12, x12, x12
	umulh x17, x17, x17
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x15, x7, x7
	adds x9, x9, x4
	adcs x10, x10, x2
	adcs x11, x11, x5
	adcs x12, x12, x3
	adcs x13, x13, x16
	lsl x1, x8, #32
	adcs x14, x14, x6
	lsr x2, x8, #32
	adc x15, x15, x17
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	adcs x10, x11, x3
	adc x11, x6, x7
	adds x8, x8, x12
	adcs x9, x9, x13
	adcs x10, x10, x14
	adcs x11, x11, x15
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
	str x8, [x0, #1376]
	str x9, [x0, #1384]
	str x10, [x0, #1392]
	str x11, [x0, #1400]
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
	str x12, [x0, #1408]
	str x13, [x0, #1416]
	str x8, [x0, #1424]
	str x9, [x0, #1432]
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
	ldr x1, [x0, #256]
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
	ldr x1, [x0, #264]
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
	ldr x1, [x0, #272]
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
	ldr x1, [x0, #280]
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
	str x12, [x0, #1376]
	str x13, [x0, #1384]
	str x8, [x0, #1392]
	str x9, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1408]
	ldr x9, [x0, #1416]
	ldr x10, [x0, #1424]
	ldr x11, [x0, #1432]
	ldr x2, [x0, #1376]
	adds x8, x8, x2
	ldr x2, [x0, #1384]
	adcs x9, x9, x2
	ldr x2, [x0, #1392]
	adcs x10, x10, x2
	ldr x2, [x0, #1400]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1280]
	ldr x9, [x0, #1288]
	ldr x10, [x0, #1296]
	ldr x11, [x0, #1304]
	ldr x2, [x0, #1344]
	adds x8, x8, x2
	ldr x2, [x0, #1352]
	adcs x9, x9, x2
	ldr x2, [x0, #1360]
	adcs x10, x10, x2
	ldr x2, [x0, #1368]
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
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1248]
	ldr x9, [x0, #1256]
	ldr x10, [x0, #1264]
	ldr x11, [x0, #1272]
	ldr x2, [x0, #1408]
	subs x8, x8, x2
	ldr x2, [x0, #1416]
	sbcs x9, x9, x2
	ldr x2, [x0, #1424]
	sbcs x10, x10, x2
	ldr x2, [x0, #1432]
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
	str x8, [x0, #1376]
	str x9, [x0, #1384]
	str x10, [x0, #1392]
	str x11, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1376]
	ldr x2, [x0, #1384]
	orr x1, x1, x2
	ldr x2, [x0, #1392]
	orr x1, x1, x2
	ldr x2, [x0, #1400]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	ldr x3, [x0, #1472]
	ldr x1, [x0, #320]
	ldr x2, [x0, #1152]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1280]
	ldr x1, [x0, #328]
	ldr x2, [x0, #1160]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1288]
	ldr x1, [x0, #336]
	ldr x2, [x0, #1168]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1296]
	ldr x1, [x0, #344]
	ldr x2, [x0, #1176]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1304]
	ldr x1, [x0, #352]
	ldr x2, [x0, #1184]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1440]
	ldr x1, [x0, #360]
	ldr x2, [x0, #1192]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1448]
	ldr x1, [x0, #368]
	ldr x2, [x0, #1200]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1456]
	ldr x1, [x0, #376]
	ldr x2, [x0, #1208]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1464]
	ret
	.p2align 6
