// The functions of `src/internal/vg_ecdsa_p384_verify_digits.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p384_verify_digits:
	add x16, x0, x19
	ldrb w2, [x16, #2704]
	cbnz x2, 20f
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
	b 21f
20:
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
	cbnz x3, 22f
	b 23f
22:
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
23:
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
	cbnz x2, 24f
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
	cbnz x2, 26f
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
	cbnz x2, 28f
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
	b 29f
28:
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
	cbnz x2, 210f
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
	b 211f
210:
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
211:
29:
	b 27f
26:
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
27:
	b 25f
24:
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
25:
21:
	add x16, x0, x19
	add x16, x16, x19
	ldrb w2, [x16, #3152]
	ldrb w3, [x16, #3153]
	cbnz x2, 212f
	b 213f
212:
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
	cbnz x3, 214f
	b 215f
214:
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
215:
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
	cbnz x2, 216f
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
	cbnz x2, 218f
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
	b 219f
218:
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
	cbnz x2, 220f
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
	b 221f
220:
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
221:
219:
	b 217f
216:
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
217:
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
213:
	ret
	.p2align 6
