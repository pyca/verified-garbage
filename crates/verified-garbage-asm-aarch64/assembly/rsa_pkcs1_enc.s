// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_decrypt_precomputed_sha256_sha2:
	str x30, [sp, #-16]!
	sub sp, sp, #224
	add x9, sp, #0
	str x0, [x9, #112]
	str x2, [x9, #120]
	str x3, [x9, #128]
	str x4, [x9, #136]
	str x5, [x9, #144]
	str x6, [x9, #152]
	str x7, [x9, #160]
	ldr x10, [sp, #240]
	str x10, [x9, #168]
	ldr x10, [sp, #248]
	str x10, [x9, #176]
	ldr x10, [sp, #344]
	str x10, [x9, #184]
	ldr x10, [sp, #264]
	str x10, [x9, #0]
	ldr x10, [sp, #272]
	str x10, [x9, #8]
	ldr x10, [sp, #280]
	str x10, [x9, #16]
	ldr x10, [sp, #288]
	str x10, [x9, #24]
	ldr x10, [sp, #296]
	str x10, [x9, #32]
	ldr x10, [sp, #304]
	str x10, [x9, #40]
	ldr x10, [sp, #312]
	str x10, [x9, #48]
	ldr x10, [sp, #320]
	str x10, [x9, #56]
	ldr x10, [sp, #328]
	str x10, [x9, #64]
	ldr x10, [sp, #336]
	str x10, [x9, #72]
	ldr x10, [sp, #344]
	str x10, [x9, #80]
	ldr x10, [sp, #352]
	str x10, [x9, #88]
	orr x1, x4, x4
	orr x2, x3, x3
	orr x3, x4, x4
	orr x4, x5, x5
	orr x5, x6, x6
	ldr x6, [sp, #248]
	orr x7, x1, x1
	add x9, sp, #0
	ldr x10, [sp, #360]
	str x10, [x9, #96]
	ldr x10, [sp, #368]
	str x10, [x9, #104]
	bl {vg_rsa_private_checked_precomputed}
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #192]
	ldr x11, [sp, #184]
	add x11, x11, #2416
	ldr x12, [sp, #136]
	movz x13, #0, lsl #0
20:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 20b
	ldr x14, [sp, #160]
	ldr x12, [sp, #168]
	ldr x11, [sp, #184]
	add x11, x11, #2416
	ldr x15, [sp, #136]
	add x11, x11, x15
	sub x11, x11, x12
21:
	ldrb w10, [x14, #0]
	strb w10, [x11, #0]
	add x14, x14, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 21b
	ldr x0, [sp, #184]
	add x0, x0, #0
	bl {vg_sha256_init}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2416
	ldr x3, [sp, #136]
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #136]
	ldr x2, [sp, #184]
	add x2, x2, #1040
	ldr x3, [sp, #184]
	add x3, x3, #192
	bl {vg_sha256_finalize_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	ldr x2, [sp, #184]
	add x2, x2, #1040
	movz x3, #32, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #176]
	ldr x3, [sp, #136]
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	ldr x2, [sp, #136]
	add x2, x2, #64
	ldr x3, [sp, #184]
	add x3, x3, #1104
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch_sha2}
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #200]
	ldr x10, [sp, #136]
	add x10, x10, #31
	lsr x10, x10, #5
	str x10, [x9, #208]
22:
	ldr x9, [sp, #184]
	add x9, x9, #1024
	ldr x11, [sp, #200]
	ldr x12, [sp, #136]
	movz x10, #0, lsl #0
	strb w10, [x9, #0]
	strb w11, [x9, #1]
	movz x10, #108, lsl #0
	strb w10, [x9, #2]
	movz x10, #101, lsl #0
	strb w10, [x9, #3]
	movz x10, #110, lsl #0
	strb w10, [x9, #4]
	movz x10, #103, lsl #0
	strb w10, [x9, #5]
	movz x10, #116, lsl #0
	strb w10, [x9, #6]
	movz x10, #104, lsl #0
	strb w10, [x9, #7]
	movz x10, #8, lsl #0
	strb w10, [x9, #8]
	movz x10, #0, lsl #0
	strb w10, [x9, #9]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	ldr x2, [sp, #184]
	add x2, x2, #1104
	movz x3, #32, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #1024
	movz x3, #10, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	movz x2, #74, lsl #0
	ldr x3, [sp, #200]
	lsl x3, x3, #5
	ldr x10, [sp, #184]
	add x10, x10, #1136
	add x3, x3, x10
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch_sha2}
	ldr x11, [sp, #200]
	add x11, x11, #1
	add x9, sp, #0
	str x11, [x9, #200]
	movz x12, #8, lsl #0
	sub x12, x12, x11
	cbnz x12, 22b
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #200]
23:
	ldr x9, [sp, #184]
	add x9, x9, #1024
	ldr x11, [sp, #200]
	ldr x12, [sp, #136]
	movz x10, #0, lsl #0
	strb w10, [x9, #0]
	strb w11, [x9, #1]
	movz x10, #109, lsl #0
	strb w10, [x9, #2]
	movz x10, #101, lsl #0
	strb w10, [x9, #3]
	movz x10, #115, lsl #0
	strb w10, [x9, #4]
	movz x10, #115, lsl #0
	strb w10, [x9, #5]
	movz x10, #97, lsl #0
	strb w10, [x9, #6]
	movz x10, #103, lsl #0
	strb w10, [x9, #7]
	movz x10, #101, lsl #0
	strb w10, [x9, #8]
	lsl x10, x12, #3
	strb w10, [x9, #10]
	lsr x10, x10, #8
	strb w10, [x9, #9]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	ldr x2, [sp, #184]
	add x2, x2, #1104
	movz x3, #32, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #1024
	movz x3, #11, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_sha256_update_scratch_sha2}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	movz x2, #75, lsl #0
	ldr x3, [sp, #200]
	lsl x3, x3, #5
	ldr x10, [sp, #184]
	add x10, x10, #1392
	add x3, x3, x10
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch_sha2}
	ldr x11, [sp, #200]
	add x11, x11, #1
	add x9, sp, #0
	str x11, [x9, #200]
	ldr x12, [sp, #208]
	sub x12, x12, x11
	cbnz x12, 23b
	ldr x9, [sp, #136]
	sub x9, x9, #11
	movz x8, #0, lsl #0
24:
	add x8, x8, x8
	add x8, x8, #1
	subs x10, x8, x9
	sbc x10, x10, x10
	cbnz x10, 24b
	ldr x11, [sp, #184]
	add x11, x11, #1136
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
25:
	ldrb w10, [x11, #0]
	lsl x10, x10, #8
	ldrb w14, [x11, #1]
	add x10, x10, x14
	and x10, x10, x8
	subs x14, x9, x10
	csel x13, x10, x13, hs
	add x11, x11, #2
	sub x12, x12, #1
	cbnz x12, 25b
	ldr x11, [sp, #112]
	add x11, x11, #2
	ldr x12, [sp, #136]
	sub x12, x12, #2
	movz x14, #2, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #1, lsl #0
26:
	ldrb w10, [x11, #0]
	subs x10, x10, x17
	sbc x10, x10, x10
	bic x9, x10, x15, ror #0
	and x9, x9, x14
	orr x16, x16, x9
	orr x15, x15, x10
	add x14, x14, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 26b
	ldr x11, [sp, #112]
	ldr x12, [sp, #136]
	ldrb w10, [x11, #0]
	subs x10, x10, x17
	sbc x10, x10, x10
	ldrb w9, [x11, #1]
	movz x14, #2, lsl #0
	eor x9, x9, x14
	subs x9, x9, x17
	sbc x9, x9, x9
	and x10, x10, x9
	and x15, x15, x10
	movz x14, #10, lsl #0
	subs x9, x16, x14
	sbc x9, x9, x9
	bic x15, x15, x9, ror #0
	sub x9, x12, x16
	sub x9, x9, #1
	eor x9, x9, x13
	and x9, x9, x15
	eor x13, x13, x9
	ldr x14, [sp, #192]
	eor x14, x14, x17
	subs x14, x14, x17
	sbc x14, x14, x14
	sub x16, x12, x13
	and x13, x13, x14
	ldr x10, [sp, #120]
	str x13, [x10, #0]
	ldr x10, [sp, #184]
	add x10, x10, #1392
	movz x9, #0, lsl #0
27:
	ldrb w13, [x11, #0]
	ldrb w8, [x10, #0]
	eor x13, x13, x8
	and x13, x13, x15
	eor x13, x13, x8
	subs x8, x9, x16
	sbc x8, x8, x8
	bic x8, x14, x8, ror #0
	and x13, x13, x8
	strb w13, [x11, #0]
	add x9, x9, #1
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 27b
	ldr x0, [sp, #192]
	add sp, sp, #224
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
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #3488
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	str q31, [x9, #2144]
	str q31, [x9, #2160]
	str q31, [x9, #2176]
	str q31, [x9, #2192]
	str q31, [x9, #2208]
	str q31, [x9, #2224]
	str q31, [x9, #2240]
	str q31, [x9, #2256]
	str q31, [x9, #2272]
	str q31, [x9, #2288]
	str q31, [x9, #2304]
	str q31, [x9, #2320]
	str q31, [x9, #2336]
	str q31, [x9, #2352]
	str q31, [x9, #2368]
	str q31, [x9, #2384]
	str q31, [x9, #2400]
	str q31, [x9, #2416]
	str q31, [x9, #2432]
	str q31, [x9, #2448]
	str q31, [x9, #2464]
	str q31, [x9, #2480]
	str q31, [x9, #2496]
	str q31, [x9, #2512]
	str q31, [x9, #2528]
	str q31, [x9, #2544]
	str q31, [x9, #2560]
	str q31, [x9, #2576]
	str q31, [x9, #2592]
	str q31, [x9, #2608]
	str q31, [x9, #2624]
	str q31, [x9, #2640]
	str q31, [x9, #2656]
	str q31, [x9, #2672]
	str q31, [x9, #2688]
	str q31, [x9, #2704]
	str q31, [x9, #2720]
	str q31, [x9, #2736]
	str q31, [x9, #2752]
	str q31, [x9, #2768]
	str q31, [x9, #2784]
	str q31, [x9, #2800]
	str q31, [x9, #2816]
	str q31, [x9, #2832]
	str q31, [x9, #2848]
	str q31, [x9, #2864]
	str q31, [x9, #2880]
	str q31, [x9, #2896]
	str q31, [x9, #2912]
	str q31, [x9, #2928]
	str q31, [x9, #2944]
	str q31, [x9, #2960]
	str q31, [x9, #2976]
	str q31, [x9, #2992]
	str q31, [x9, #3008]
	str q31, [x9, #3024]
	str q31, [x9, #3040]
	str q31, [x9, #3056]
	str q31, [x9, #3072]
	str q31, [x9, #3088]
	str q31, [x9, #3104]
	str q31, [x9, #3120]
	str q31, [x9, #3136]
	str q31, [x9, #3152]
	str q31, [x9, #3168]
	str q31, [x9, #3184]
	str q31, [x9, #3200]
	str q31, [x9, #3216]
	str q31, [x9, #3232]
	str q31, [x9, #3248]
	str q31, [x9, #3264]
	str q31, [x9, #3280]
	str q31, [x9, #3296]
	str q31, [x9, #3312]
	str q31, [x9, #3328]
	str q31, [x9, #3344]
	str q31, [x9, #3360]
	str q31, [x9, #3376]
	str q31, [x9, #3392]
	str q31, [x9, #3408]
	str q31, [x9, #3424]
	str q31, [x9, #3440]
	str q31, [x9, #3456]
	str q31, [x9, #3472]
	add sp, sp, #3488
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_precomputed:
	str x30, [sp, #-16]!
	sub sp, sp, #224
	add x9, sp, #0
	str x0, [x9, #112]
	str x2, [x9, #120]
	str x3, [x9, #128]
	str x4, [x9, #136]
	str x5, [x9, #144]
	str x6, [x9, #152]
	str x7, [x9, #160]
	ldr x10, [sp, #240]
	str x10, [x9, #168]
	ldr x10, [sp, #248]
	str x10, [x9, #176]
	ldr x10, [sp, #344]
	str x10, [x9, #184]
	ldr x10, [sp, #264]
	str x10, [x9, #0]
	ldr x10, [sp, #272]
	str x10, [x9, #8]
	ldr x10, [sp, #280]
	str x10, [x9, #16]
	ldr x10, [sp, #288]
	str x10, [x9, #24]
	ldr x10, [sp, #296]
	str x10, [x9, #32]
	ldr x10, [sp, #304]
	str x10, [x9, #40]
	ldr x10, [sp, #312]
	str x10, [x9, #48]
	ldr x10, [sp, #320]
	str x10, [x9, #56]
	ldr x10, [sp, #328]
	str x10, [x9, #64]
	ldr x10, [sp, #336]
	str x10, [x9, #72]
	ldr x10, [sp, #344]
	str x10, [x9, #80]
	ldr x10, [sp, #352]
	str x10, [x9, #88]
	orr x1, x4, x4
	orr x2, x3, x3
	orr x3, x4, x4
	orr x4, x5, x5
	orr x5, x6, x6
	ldr x6, [sp, #248]
	orr x7, x1, x1
	add x9, sp, #0
	ldr x10, [sp, #360]
	str x10, [x9, #96]
	ldr x10, [sp, #368]
	str x10, [x9, #104]
	bl {vg_rsa_private_checked_precomputed}
	orr w0, w0, w0
	add x9, sp, #0
	str x0, [x9, #192]
	ldr x11, [sp, #184]
	add x11, x11, #2416
	ldr x12, [sp, #136]
	movz x13, #0, lsl #0
20:
	strb w13, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 20b
	ldr x14, [sp, #160]
	ldr x12, [sp, #168]
	ldr x11, [sp, #184]
	add x11, x11, #2416
	ldr x15, [sp, #136]
	add x11, x11, x15
	sub x11, x11, x12
21:
	ldrb w10, [x14, #0]
	strb w10, [x11, #0]
	add x14, x14, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 21b
	ldr x0, [sp, #184]
	add x0, x0, #0
	bl {vg_sha256_init}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #0, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #2416
	ldr x3, [sp, #136]
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #136]
	ldr x2, [sp, #184]
	add x2, x2, #1040
	ldr x3, [sp, #184]
	add x3, x3, #192
	bl {vg_sha256_finalize_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	ldr x2, [sp, #184]
	add x2, x2, #1040
	movz x3, #32, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #176]
	ldr x3, [sp, #136]
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	ldr x2, [sp, #136]
	add x2, x2, #64
	ldr x3, [sp, #184]
	add x3, x3, #1104
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch}
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #200]
	ldr x10, [sp, #136]
	add x10, x10, #31
	lsr x10, x10, #5
	str x10, [x9, #208]
22:
	ldr x9, [sp, #184]
	add x9, x9, #1024
	ldr x11, [sp, #200]
	ldr x12, [sp, #136]
	movz x10, #0, lsl #0
	strb w10, [x9, #0]
	strb w11, [x9, #1]
	movz x10, #108, lsl #0
	strb w10, [x9, #2]
	movz x10, #101, lsl #0
	strb w10, [x9, #3]
	movz x10, #110, lsl #0
	strb w10, [x9, #4]
	movz x10, #103, lsl #0
	strb w10, [x9, #5]
	movz x10, #116, lsl #0
	strb w10, [x9, #6]
	movz x10, #104, lsl #0
	strb w10, [x9, #7]
	movz x10, #8, lsl #0
	strb w10, [x9, #8]
	movz x10, #0, lsl #0
	strb w10, [x9, #9]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	ldr x2, [sp, #184]
	add x2, x2, #1104
	movz x3, #32, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #1024
	movz x3, #10, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	movz x2, #74, lsl #0
	ldr x3, [sp, #200]
	lsl x3, x3, #5
	ldr x10, [sp, #184]
	add x10, x10, #1136
	add x3, x3, x10
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch}
	ldr x11, [sp, #200]
	add x11, x11, #1
	add x9, sp, #0
	str x11, [x9, #200]
	movz x12, #8, lsl #0
	sub x12, x12, x11
	cbnz x12, 22b
	add x9, sp, #0
	movz x10, #0, lsl #0
	str x10, [x9, #200]
23:
	ldr x9, [sp, #184]
	add x9, x9, #1024
	ldr x11, [sp, #200]
	ldr x12, [sp, #136]
	movz x10, #0, lsl #0
	strb w10, [x9, #0]
	strb w11, [x9, #1]
	movz x10, #109, lsl #0
	strb w10, [x9, #2]
	movz x10, #101, lsl #0
	strb w10, [x9, #3]
	movz x10, #115, lsl #0
	strb w10, [x9, #4]
	movz x10, #115, lsl #0
	strb w10, [x9, #5]
	movz x10, #97, lsl #0
	strb w10, [x9, #6]
	movz x10, #103, lsl #0
	strb w10, [x9, #7]
	movz x10, #101, lsl #0
	strb w10, [x9, #8]
	lsl x10, x12, #3
	strb w10, [x9, #10]
	lsr x10, x10, #8
	strb w10, [x9, #9]
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	ldr x2, [sp, #184]
	add x2, x2, #1104
	movz x3, #32, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_init_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	movz x1, #64, lsl #0
	ldr x2, [sp, #184]
	add x2, x2, #1024
	movz x3, #11, lsl #0
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_sha256_update_scratch}
	ldr x0, [sp, #184]
	add x0, x0, #0
	ldr x1, [sp, #184]
	add x1, x1, #96
	movz x2, #75, lsl #0
	ldr x3, [sp, #200]
	lsl x3, x3, #5
	ldr x10, [sp, #184]
	add x10, x10, #1392
	add x3, x3, x10
	ldr x4, [sp, #184]
	add x4, x4, #192
	bl {vg_hmac_sha256_finalize_scratch}
	ldr x11, [sp, #200]
	add x11, x11, #1
	add x9, sp, #0
	str x11, [x9, #200]
	ldr x12, [sp, #208]
	sub x12, x12, x11
	cbnz x12, 23b
	ldr x9, [sp, #136]
	sub x9, x9, #11
	movz x8, #0, lsl #0
24:
	add x8, x8, x8
	add x8, x8, #1
	subs x10, x8, x9
	sbc x10, x10, x10
	cbnz x10, 24b
	ldr x11, [sp, #184]
	add x11, x11, #1136
	movz x12, #128, lsl #0
	movz x13, #0, lsl #0
25:
	ldrb w10, [x11, #0]
	lsl x10, x10, #8
	ldrb w14, [x11, #1]
	add x10, x10, x14
	and x10, x10, x8
	subs x14, x9, x10
	csel x13, x10, x13, hs
	add x11, x11, #2
	sub x12, x12, #1
	cbnz x12, 25b
	ldr x11, [sp, #112]
	add x11, x11, #2
	ldr x12, [sp, #136]
	sub x12, x12, #2
	movz x14, #2, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #1, lsl #0
26:
	ldrb w10, [x11, #0]
	subs x10, x10, x17
	sbc x10, x10, x10
	bic x9, x10, x15, ror #0
	and x9, x9, x14
	orr x16, x16, x9
	orr x15, x15, x10
	add x14, x14, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 26b
	ldr x11, [sp, #112]
	ldr x12, [sp, #136]
	ldrb w10, [x11, #0]
	subs x10, x10, x17
	sbc x10, x10, x10
	ldrb w9, [x11, #1]
	movz x14, #2, lsl #0
	eor x9, x9, x14
	subs x9, x9, x17
	sbc x9, x9, x9
	and x10, x10, x9
	and x15, x15, x10
	movz x14, #10, lsl #0
	subs x9, x16, x14
	sbc x9, x9, x9
	bic x15, x15, x9, ror #0
	sub x9, x12, x16
	sub x9, x9, #1
	eor x9, x9, x13
	and x9, x9, x15
	eor x13, x13, x9
	ldr x14, [sp, #192]
	eor x14, x14, x17
	subs x14, x14, x17
	sbc x14, x14, x14
	sub x16, x12, x13
	and x13, x13, x14
	ldr x10, [sp, #120]
	str x13, [x10, #0]
	ldr x10, [sp, #184]
	add x10, x10, #1392
	movz x9, #0, lsl #0
27:
	ldrb w13, [x11, #0]
	ldrb w8, [x10, #0]
	eor x13, x13, x8
	and x13, x13, x15
	eor x13, x13, x8
	subs x8, x9, x16
	sbc x8, x8, x8
	bic x8, x14, x8, ror #0
	and x13, x13, x8
	strb w13, [x11, #0]
	add x9, x9, #1
	add x11, x11, #1
	add x10, x10, #1
	sub x12, x12, #1
	cbnz x12, 27b
	ldr x0, [sp, #192]
	add sp, sp, #224
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
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	add w0, w0, #0
	sub sp, sp, #3488
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	str q31, [x9, #2144]
	str q31, [x9, #2160]
	str q31, [x9, #2176]
	str q31, [x9, #2192]
	str q31, [x9, #2208]
	str q31, [x9, #2224]
	str q31, [x9, #2240]
	str q31, [x9, #2256]
	str q31, [x9, #2272]
	str q31, [x9, #2288]
	str q31, [x9, #2304]
	str q31, [x9, #2320]
	str q31, [x9, #2336]
	str q31, [x9, #2352]
	str q31, [x9, #2368]
	str q31, [x9, #2384]
	str q31, [x9, #2400]
	str q31, [x9, #2416]
	str q31, [x9, #2432]
	str q31, [x9, #2448]
	str q31, [x9, #2464]
	str q31, [x9, #2480]
	str q31, [x9, #2496]
	str q31, [x9, #2512]
	str q31, [x9, #2528]
	str q31, [x9, #2544]
	str q31, [x9, #2560]
	str q31, [x9, #2576]
	str q31, [x9, #2592]
	str q31, [x9, #2608]
	str q31, [x9, #2624]
	str q31, [x9, #2640]
	str q31, [x9, #2656]
	str q31, [x9, #2672]
	str q31, [x9, #2688]
	str q31, [x9, #2704]
	str q31, [x9, #2720]
	str q31, [x9, #2736]
	str q31, [x9, #2752]
	str q31, [x9, #2768]
	str q31, [x9, #2784]
	str q31, [x9, #2800]
	str q31, [x9, #2816]
	str q31, [x9, #2832]
	str q31, [x9, #2848]
	str q31, [x9, #2864]
	str q31, [x9, #2880]
	str q31, [x9, #2896]
	str q31, [x9, #2912]
	str q31, [x9, #2928]
	str q31, [x9, #2944]
	str q31, [x9, #2960]
	str q31, [x9, #2976]
	str q31, [x9, #2992]
	str q31, [x9, #3008]
	str q31, [x9, #3024]
	str q31, [x9, #3040]
	str q31, [x9, #3056]
	str q31, [x9, #3072]
	str q31, [x9, #3088]
	str q31, [x9, #3104]
	str q31, [x9, #3120]
	str q31, [x9, #3136]
	str q31, [x9, #3152]
	str q31, [x9, #3168]
	str q31, [x9, #3184]
	str q31, [x9, #3200]
	str q31, [x9, #3216]
	str q31, [x9, #3232]
	str q31, [x9, #3248]
	str q31, [x9, #3264]
	str q31, [x9, #3280]
	str q31, [x9, #3296]
	str q31, [x9, #3312]
	str q31, [x9, #3328]
	str q31, [x9, #3344]
	str q31, [x9, #3360]
	str q31, [x9, #3376]
	str q31, [x9, #3392]
	str q31, [x9, #3408]
	str q31, [x9, #3424]
	str q31, [x9, #3440]
	str q31, [x9, #3456]
	str q31, [x9, #3472]
	add sp, sp, #3488
	ret
	.p2align 6

vg_rsa_pkcs1_encrypt_random:
	str x30, [sp, #-16]!
	sub sp, sp, #1088
	ldr x9, [sp, #1104]
	ldr x11, [sp, #1112]
	ldr x12, [sp, #1120]
	sub x15, x4, x9
	sub x15, x15, #3
	str x15, [sp, #48]
	add x14, sp, #64
	orr x16, x15, x15
	cbnz x12, 20f
	b 21f
20:
22:
	ldrb w17, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbz x17, 23f
	strb w17, [x14, #0]
	add x14, x14, #1
	sub x16, x16, #1
	b 24f
23:
24:
	mul x9, x12, x16
	cbnz x9, 22b
21:
	cbz x16, 25f
	orr x9, x0, x0
	orr x10, x4, x4
	movz x13, #0, lsl #0
27:
	strb w13, [x9, #0]
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 27b
	movz x10, #1024, lsl #0
	add x9, sp, #64
28:
	strb w13, [x9, #0]
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 28b
	add x11, x15, #128
	ldr x12, [sp, #1120]
	sub x10, x15, x16
	add x9, x15, x12
	sub x9, x9, x10
	subs x17, x11, x9
	csel x9, x11, x9, lo
	subs x17, x12, x11
	movz x13, #0, lsl #0
	csel x14, x12, x13, hs
	csel x9, x13, x9, hs
	movz x10, #3, lsl #0
	csel x0, x10, x13, hs
	str x14, [x2, #0]
	str x9, [x2, #8]
	b 26f
25:
	ldr x9, [sp, #1120]
	sub x9, x9, x12
	ldr x10, [sp, #1128]
	ldr x11, [sp, #1136]
	ldr x13, [sp, #1144]
	ldr x14, [sp, #1152]
	ldr x8, [sp, #1104]
	add x16, sp, #64
	movz x17, #0, lsl #0
	str x9, [x2, #0]
	str x17, [x2, #8]
	str x16, [sp, #0]
	str x15, [sp, #8]
	str x10, [sp, #16]
	str x11, [sp, #24]
	str x13, [sp, #32]
	str x14, [sp, #40]
	orr x2, x3, x3
	orr x3, x4, x4
	orr x4, x5, x5
	orr x5, x6, x6
	orr x6, x7, x7
	orr x7, x8, x8
	bl {vg_rsa_pkcs1_encrypt_precomputed}
	movz x9, #2, lsl #0
	sub w0, w9, w0
	movz x12, #1024, lsl #0
	add x13, sp, #64
	movz x14, #0, lsl #0
29:
	strb w14, [x13, #0]
	add x13, x13, #1
	sub x12, x12, #1
	cbnz x12, 29b
26:
	add sp, sp, #1088
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
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #2208
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #80]
	str q31, [x9, #96]
	str q31, [x9, #112]
	str q31, [x9, #128]
	str q31, [x9, #144]
	str q31, [x9, #160]
	str q31, [x9, #176]
	str q31, [x9, #192]
	str q31, [x9, #208]
	str q31, [x9, #224]
	str q31, [x9, #240]
	str q31, [x9, #256]
	str q31, [x9, #272]
	str q31, [x9, #288]
	str q31, [x9, #304]
	str q31, [x9, #320]
	str q31, [x9, #336]
	str q31, [x9, #352]
	str q31, [x9, #368]
	str q31, [x9, #384]
	str q31, [x9, #400]
	str q31, [x9, #416]
	str q31, [x9, #432]
	str q31, [x9, #448]
	str q31, [x9, #464]
	str q31, [x9, #480]
	str q31, [x9, #496]
	str q31, [x9, #512]
	str q31, [x9, #528]
	str q31, [x9, #544]
	str q31, [x9, #560]
	str q31, [x9, #576]
	str q31, [x9, #592]
	str q31, [x9, #608]
	str q31, [x9, #624]
	str q31, [x9, #640]
	str q31, [x9, #656]
	str q31, [x9, #672]
	str q31, [x9, #688]
	str q31, [x9, #704]
	str q31, [x9, #720]
	str q31, [x9, #736]
	str q31, [x9, #752]
	str q31, [x9, #768]
	str q31, [x9, #784]
	str q31, [x9, #800]
	str q31, [x9, #816]
	str q31, [x9, #832]
	str q31, [x9, #848]
	str q31, [x9, #864]
	str q31, [x9, #880]
	str q31, [x9, #896]
	str q31, [x9, #912]
	str q31, [x9, #928]
	str q31, [x9, #944]
	str q31, [x9, #960]
	str q31, [x9, #976]
	str q31, [x9, #992]
	str q31, [x9, #1008]
	str q31, [x9, #1024]
	str q31, [x9, #1040]
	str q31, [x9, #1056]
	str q31, [x9, #1072]
	str q31, [x9, #1088]
	str q31, [x9, #1104]
	str q31, [x9, #1120]
	str q31, [x9, #1136]
	str q31, [x9, #1152]
	str q31, [x9, #1168]
	str q31, [x9, #1184]
	str q31, [x9, #1200]
	str q31, [x9, #1216]
	str q31, [x9, #1232]
	str q31, [x9, #1248]
	str q31, [x9, #1264]
	str q31, [x9, #1280]
	str q31, [x9, #1296]
	str q31, [x9, #1312]
	str q31, [x9, #1328]
	str q31, [x9, #1344]
	str q31, [x9, #1360]
	str q31, [x9, #1376]
	str q31, [x9, #1392]
	str q31, [x9, #1408]
	str q31, [x9, #1424]
	str q31, [x9, #1440]
	str q31, [x9, #1456]
	str q31, [x9, #1472]
	str q31, [x9, #1488]
	str q31, [x9, #1504]
	str q31, [x9, #1520]
	str q31, [x9, #1536]
	str q31, [x9, #1552]
	str q31, [x9, #1568]
	str q31, [x9, #1584]
	str q31, [x9, #1600]
	str q31, [x9, #1616]
	str q31, [x9, #1632]
	str q31, [x9, #1648]
	str q31, [x9, #1664]
	str q31, [x9, #1680]
	str q31, [x9, #1696]
	str q31, [x9, #1712]
	str q31, [x9, #1728]
	str q31, [x9, #1744]
	str q31, [x9, #1760]
	str q31, [x9, #1776]
	str q31, [x9, #1792]
	str q31, [x9, #1808]
	str q31, [x9, #1824]
	str q31, [x9, #1840]
	str q31, [x9, #1856]
	str q31, [x9, #1872]
	str q31, [x9, #1888]
	str q31, [x9, #1904]
	str q31, [x9, #1920]
	str q31, [x9, #1936]
	str q31, [x9, #1952]
	str q31, [x9, #1968]
	str q31, [x9, #1984]
	str q31, [x9, #2000]
	str q31, [x9, #2016]
	str q31, [x9, #2032]
	str q31, [x9, #2048]
	str q31, [x9, #2064]
	str q31, [x9, #2080]
	str q31, [x9, #2096]
	str q31, [x9, #2112]
	str q31, [x9, #2128]
	str q31, [x9, #2144]
	str q31, [x9, #2160]
	str q31, [x9, #2176]
	str q31, [x9, #2192]
	add sp, sp, #2208
	ret
	.p2align 6
