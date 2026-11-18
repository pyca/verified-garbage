// The functions of `src/rsa_pss.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sign_precomputed:
	sub sp, sp, #336
	ldr x10, [sp, #448]
	add x16, sp, #0
	str x19, [x16, #96]
	str x20, [x16, #104]
	str x21, [x16, #112]
	str x22, [x16, #120]
	str x23, [x16, #128]
	str x24, [x16, #136]
	str x25, [x16, #144]
	str x26, [x16, #152]
	str x27, [x16, #160]
	str x28, [x16, #168]
	str x30, [x16, #176]
	str x0, [x16, #216]
	str x2, [x16, #184]
	str x4, [x16, #192]
	str x5, [x16, #200]
	str x6, [x16, #288]
	str x7, [x16, #296]
	add x23, x3, #0
	ldr x9, [sp, #400]
	str x9, [x16, #208]
	ldr x9, [sp, #416]
	str x9, [x16, #224]
	ldr x9, [sp, #424]
	str x9, [x16, #232]
	ldr x20, [sp, #432]
	ldr x9, [sp, #440]
	str x9, [x16, #240]
	ldr x27, [x10, #40]
	add x19, x20, #2048
	add x21, x20, #2304
	ldrb w10, [x2, #0]
	cbz x10, 20f
	clz x9, x10
	lsl x24, x23, #3
	add x24, x24, #55
	sub x24, x24, x9
	add x25, x24, #7
	lsr x25, x25, #3
	sub x26, x23, x25
	add x0, x20, #2560
	movz x9, #0, lsl #0
	strb w9, [x0, #0]
	add x0, x0, x26
	add x1, x25, #0
	ldr x2, [sp, #208]
	ldr x3, [sp, #224]
	ldr x4, [sp, #232]
	add x5, x24, #0
	add x6, x20, #3584
	ldr x7, [sp, #240]
	sub x7, x7, #448
	add x16, sp, #0
	ldr x9, [sp, #448]
	str x9, [x16, #0]
	ldr x9, [sp, #456]
	str x9, [x16, #8]
	sub x9, x27, #0
	cbz x9, 22f
	sub x9, x27, #1
	cbz x9, 24f
	sub x9, x27, #2
	cbz x9, 26f
	sub x9, x27, #3
	cbz x9, 28f
	sub x9, x27, #4
	cbz x9, 210f
	sub x9, x27, #5
	cbz x9, 212f
	sub x9, x27, #6
	cbz x9, 214f
	bl {vg_rsa_pss_sha512_256_encode}
	b 215f
214:
	bl {vg_rsa_pss_sha512_224_encode}
215:
	b 213f
212:
	bl {vg_rsa_pss_sha512_encode}
213:
	b 211f
210:
	bl {vg_rsa_pss_sha384_encode}
211:
	b 29f
28:
	bl {vg_rsa_pss_sha256_encode}
29:
	b 27f
26:
	bl {vg_rsa_pss_sha224_encode}
27:
	b 25f
24:
	bl {vg_rsa_pss_sha1_encode}
25:
	b 23f
22:
	bl {vg_rsa_pss_md5_encode}
23:
	cbz w0, 216f
	add x16, sp, #0
	ldr x9, [sp, #288]
	str x9, [x16, #0]
	ldr x9, [sp, #296]
	str x9, [x16, #8]
	ldr x9, [sp, #336]
	str x9, [x16, #16]
	ldr x9, [sp, #344]
	str x9, [x16, #24]
	ldr x9, [sp, #352]
	str x9, [x16, #32]
	ldr x9, [sp, #360]
	str x9, [x16, #40]
	ldr x9, [sp, #368]
	str x9, [x16, #48]
	ldr x9, [sp, #376]
	str x9, [x16, #56]
	ldr x9, [sp, #384]
	str x9, [x16, #64]
	ldr x9, [sp, #392]
	str x9, [x16, #72]
	movz x9, #8192, lsl #0
	add x9, x20, x9
	str x9, [x16, #80]
	ldr x9, [sp, #240]
	sub x9, x9, #1024
	str x9, [x16, #88]
	ldr x0, [sp, #216]
	add x1, x23, #0
	ldr x2, [sp, #184]
	add x3, x23, #0
	ldr x4, [sp, #192]
	ldr x5, [sp, #200]
	add x6, x20, #2560
	add x7, x23, #0
	ldr x19, [sp, #96]
	ldr x20, [sp, #104]
	ldr x9, [sp, #464]
	add x16, sp, #0
	str x9, [x16, #96]
	ldr x9, [sp, #472]
	add x16, sp, #0
	str x9, [x16, #104]
	bl {vg_rsa_private_checked_precomputed}
	b 217f
216:
	ldr x14, [sp, #216]
	add x13, x23, #0
	movz x15, #0, lsl #0
218:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 218b
	movz x0, #0, lsl #0
	ldr x19, [sp, #96]
	ldr x20, [sp, #104]
217:
	b 21f
20:
	ldr x14, [sp, #216]
	add x13, x23, #0
	movz x15, #0, lsl #0
219:
	strb w15, [x14, #0]
	add x14, x14, #1
	sub x13, x13, #1
	cbnz x13, 219b
	movz x0, #0, lsl #0
	ldr x19, [sp, #96]
	ldr x20, [sp, #104]
21:
	add x16, sp, #0
	ldr x21, [x16, #112]
	ldr x22, [x16, #120]
	ldr x23, [x16, #128]
	ldr x24, [x16, #136]
	ldr x25, [x16, #144]
	ldr x26, [x16, #152]
	ldr x27, [x16, #160]
	ldr x28, [x16, #168]
	ldr x30, [x16, #176]
	add sp, sp, #336
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
	sub sp, sp, #3584
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
	str q31, [x9, #3488]
	str q31, [x9, #3504]
	str q31, [x9, #3520]
	str q31, [x9, #3536]
	str q31, [x9, #3552]
	str q31, [x9, #3568]
	add sp, sp, #3584
	ret
	.p2align 6

vg_rsa_pss_verify_precomputed:
	sub sp, sp, #336
	ldr x10, [sp, #384]
	add x16, sp, #0
	str x19, [x16, #96]
	str x20, [x16, #104]
	str x21, [x16, #112]
	str x22, [x16, #120]
	str x23, [x16, #128]
	str x24, [x16, #136]
	str x25, [x16, #144]
	str x26, [x16, #152]
	str x27, [x16, #160]
	str x28, [x16, #168]
	str x30, [x16, #176]
	str x0, [x16, #184]
	str x2, [x16, #192]
	str x3, [x16, #200]
	str x4, [x16, #208]
	str x6, [x16, #216]
	add x23, x1, #0
	ldr x9, [sp, #336]
	str x9, [x16, #232]
	ldr x9, [sp, #344]
	add w9, w9, #0
	str x9, [x16, #264]
	ldr x20, [sp, #352]
	ldr x9, [sp, #360]
	str x9, [x16, #240]
	ldr x9, [sp, #368]
	str x9, [x16, #312]
	ldr x9, [sp, #376]
	str x9, [x16, #320]
	ldr x27, [x10, #40]
	add x19, x20, #2048
	add x21, x20, #2304
	ldrb w10, [x0, #0]
	cbz x10, 20f
	clz x9, x10
	lsl x24, x23, #3
	add x24, x24, #55
	sub x24, x24, x9
	add x25, x24, #7
	lsr x25, x25, #3
	sub x26, x23, x25
	add x16, sp, #0
	movz x9, #8192, lsl #0
	add x9, x20, x9
	str x9, [x16, #0]
	ldr x9, [sp, #240]
	sub x9, x9, #1024
	str x9, [x16, #8]
	add x0, x20, #0
	add x1, x23, #0
	ldr x2, [sp, #312]
	ldr x3, [sp, #320]
	ldr x4, [sp, #192]
	ldr x5, [sp, #200]
	ldr x6, [sp, #216]
	add x7, x23, #0
	bl {vg_rsa_public_precomputed_checked}
	add x1, x20, x26
	ldrb w9, [x20, #0]
	movz x10, #0, lsl #0
	sub x10, x10, x26
	and x9, x9, x10
	sub x26, x9, #1
	lsr x26, x26, #63
	ldr x0, [sp, #208]
	add x2, x25, #0
	add x3, x24, #0
	ldr x4, [sp, #232]
	ldr x5, [sp, #264]
	add x9, x23, #7
	lsr x9, x9, #3
	ldr x7, [sp, #240]
	sub x7, x7, x9
	lsl x9, x9, #3
	add x6, x20, x9
	add x16, sp, #0
	ldr x9, [sp, #384]
	str x9, [x16, #0]
	ldr x9, [sp, #392]
	str x9, [x16, #8]
	sub x9, x27, #0
	cbz x9, 22f
	sub x9, x27, #1
	cbz x9, 24f
	sub x9, x27, #2
	cbz x9, 26f
	sub x9, x27, #3
	cbz x9, 28f
	sub x9, x27, #4
	cbz x9, 210f
	sub x9, x27, #5
	cbz x9, 212f
	sub x9, x27, #6
	cbz x9, 214f
	bl {vg_rsa_pss_sha512_256_check_encoding}
	b 215f
214:
	bl {vg_rsa_pss_sha512_224_check_encoding}
215:
	b 213f
212:
	bl {vg_rsa_pss_sha512_check_encoding}
213:
	b 211f
210:
	bl {vg_rsa_pss_sha384_check_encoding}
211:
	b 29f
28:
	bl {vg_rsa_pss_sha256_check_encoding}
29:
	b 27f
26:
	bl {vg_rsa_pss_sha224_check_encoding}
27:
	b 25f
24:
	bl {vg_rsa_pss_sha1_check_encoding}
25:
	b 23f
22:
	bl {vg_rsa_pss_md5_check_encoding}
23:
	and x0, x0, x26
	b 21f
20:
	movz x0, #0, lsl #0
21:
	add x16, sp, #0
	ldr x19, [x16, #96]
	ldr x20, [x16, #104]
	ldr x21, [x16, #112]
	ldr x22, [x16, #120]
	ldr x23, [x16, #128]
	ldr x24, [x16, #136]
	ldr x25, [x16, #144]
	ldr x26, [x16, #152]
	ldr x27, [x16, #160]
	ldr x28, [x16, #168]
	ldr x30, [x16, #176]
	add sp, sp, #336
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
	sub sp, sp, #960
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
	add sp, sp, #960
	ret
	.p2align 6
