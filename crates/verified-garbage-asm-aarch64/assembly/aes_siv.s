// The functions of `src/aes_siv.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_siv_init_aes:
	sub sp, sp, #560
	add x3, sp, #0
	str x19, [x3, #0]
	str x20, [x3, #8]
	str x21, [x3, #16]
	str x22, [x3, #24]
	str x30, [x3, #32]
	add x19, x0, #0
	lsr x20, x1, #1
	add x21, x2, #0
	add x22, x3, #0
	add x1, x20, #0
	add x3, x3, #48
	bl {vg_aes_expand_key_scratch_aes}
	add x0, x21, #0
	lsr x1, x20, #2
	add x1, x1, #6
	add x2, x21, #240
	add x3, x22, #48
	bl {vg_cmac_aes_subkeys_aes}
	add x0, x19, x20
	add x1, x20, #0
	add x2, x21, #272
	add x3, x22, #48
	bl {vg_aes_expand_key_scratch_aes}
	ldr x19, [x22, #0]
	ldr x20, [x22, #8]
	ldr x21, [x22, #16]
	ldr x30, [x22, #32]
	ldr x22, [x22, #24]
	add sp, sp, #560
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
	movz x0, #0, lsl #0
	sub sp, sp, #560
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
	add sp, sp, #560
	ret
	.p2align 6

vg_aes_siv_init_neon:
	sub sp, sp, #2224
	add x3, sp, #0
	str x19, [x3, #0]
	str x20, [x3, #8]
	str x21, [x3, #16]
	str x22, [x3, #24]
	str x30, [x3, #32]
	add x19, x0, #0
	lsr x20, x1, #1
	add x21, x2, #0
	add x22, x3, #0
	add x1, x20, #0
	add x3, x3, #48
	bl {vg_aes_expand_key_scratch}
	add x0, x21, #0
	lsr x1, x20, #2
	add x1, x1, #6
	add x2, x21, #240
	add x3, x22, #48
	bl {vg_cmac_aes_subkeys_neon}
	add x0, x19, x20
	add x1, x20, #0
	add x2, x21, #272
	add x3, x22, #48
	bl {vg_aes_expand_key_scratch}
	ldr x19, [x22, #0]
	ldr x20, [x22, #8]
	ldr x21, [x22, #16]
	ldr x30, [x22, #32]
	ldr x22, [x22, #24]
	add sp, sp, #2224
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
	movz x0, #0, lsl #0
	sub sp, sp, #2224
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
	add sp, sp, #2224
	ret
	.p2align 6

vg_aes_siv_init:
	sub sp, sp, #2224
	add x3, sp, #0
	str x19, [x3, #0]
	str x20, [x3, #8]
	str x21, [x3, #16]
	str x22, [x3, #24]
	str x30, [x3, #32]
	add x19, x0, #0
	lsr x20, x1, #1
	add x21, x2, #0
	add x22, x3, #0
	add x1, x20, #0
	add x3, x3, #48
	bl {vg_aes_expand_key_scratch}
	add x0, x21, #0
	lsr x1, x20, #2
	add x1, x1, #6
	add x2, x21, #240
	add x3, x22, #48
	bl {vg_cmac_aes_subkeys}
	add x0, x19, x20
	add x1, x20, #0
	add x2, x21, #272
	add x3, x22, #48
	bl {vg_aes_expand_key_scratch}
	ldr x19, [x22, #0]
	ldr x20, [x22, #8]
	ldr x21, [x22, #16]
	ldr x30, [x22, #32]
	ldr x22, [x22, #24]
	add sp, sp, #2224
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
	movz x0, #0, lsl #0
	sub sp, sp, #2224
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
	add sp, sp, #2224
	ret
	.p2align 6

vg_aes_siv_encrypt_aes:
	sub sp, sp, #400
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #256]
	str x9, [x19, #264]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #256
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_aes}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update_aes}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_aes}
	ldr x9, [x19, #256]
	ldr x10, [x19, #264]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #256]
	str x10, [x19, #264]
	ldr x9, [x19, #256]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #256]
	ldr x9, [x19, #264]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #264]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 25f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 27f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 28f
27:
28:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 29f
211:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 211b
	b 210f
29:
210:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #256]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #264]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update_aes}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 212f
	movz x25, #1, lsl #0
	b 213f
212:
213:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	add x5, x19, #272
	bl {vg_cmac_aes_update_aes}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_aes}
	b 26f
25:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 214f
216:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 216b
	b 215f
214:
215:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #256]
	str x9, [x19, #144]
	ldr x9, [x19, #264]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_aes}
26:
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 217f
219:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #272
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 220f
	movz x8, #16, lsl #0
	b 221f
220:
221:
222:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 222b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 223f
	sub x23, x23, x10
	b 224f
223:
	movz x23, #0, lsl #0
224:
	cbnz x23, 219b
	b 218f
217:
218:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x19, #0]
	str x10, [x9, #0]
	ldr x10, [x19, #8]
	str x10, [x9, #8]
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #400
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
	movz x0, #0, lsl #0
	sub sp, sp, #400
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
	add sp, sp, #400
	ret
	.p2align 6

vg_aes_siv_decrypt_aes:
	sub sp, sp, #400
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #256]
	str x9, [x19, #264]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #256
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_aes}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update_aes}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_aes}
	ldr x9, [x19, #256]
	ldr x10, [x19, #264]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #256]
	str x10, [x19, #264]
	ldr x9, [x19, #256]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #256]
	ldr x9, [x19, #264]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #264]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x9, #0]
	str x10, [x19, #0]
	ldr x10, [x9, #8]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 25f
27:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #272
	bl {vg_aes_ctr32_aes}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 28f
	movz x8, #16, lsl #0
	b 29f
28:
29:
210:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 211f
	sub x23, x23, x10
	b 212f
211:
	movz x23, #0, lsl #0
212:
	cbnz x23, 27b
	b 26f
25:
26:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 213f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 215f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 216f
215:
216:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 217f
219:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 219b
	b 218f
217:
218:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #256]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #264]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update_aes}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 220f
	movz x25, #1, lsl #0
	b 221f
220:
221:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	add x5, x19, #272
	bl {vg_cmac_aes_update_aes}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_aes}
	b 214f
213:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 222f
224:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 224b
	b 223f
222:
223:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #256]
	str x9, [x19, #144]
	ldr x9, [x19, #264]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_aes}
214:
	ldr x9, [x19, #0]
	ldr x10, [x19, #112]
	eor x9, x9, x10
	ldr x10, [x19, #8]
	ldr x11, [x19, #120]
	eor x10, x10, x11
	orr x9, x9, x10
	sub x10, x9, #1
	bic x10, x10, x9, ror #0
	lsr x0, x10, #63
	movz x11, #0, lsl #0
	sub x11, x11, x0
	add x6, x26, #0
	lsr x8, x27, #3
	cbz x8, 225f
227:
	ldr x9, [x6, #0]
	and x9, x9, x11
	str x9, [x6, #0]
	add x6, x6, #8
	sub x8, x8, #1
	cbnz x8, 227b
	b 226f
225:
226:
	lsl x8, x27, #61
	lsr x8, x8, #61
	cbz x8, 228f
230:
	ldrb w9, [x6, #0]
	and x9, x9, x11
	strb w9, [x6, #0]
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 230b
	b 229f
228:
229:
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #400
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
	sub sp, sp, #400
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
	add sp, sp, #400
	ret
	.p2align 6

vg_aes_siv_encrypt_neon:
	sub sp, sp, #2448
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #256]
	str x9, [x19, #264]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #256
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_neon}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update_neon}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_neon}
	ldr x9, [x19, #256]
	ldr x10, [x19, #264]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #256]
	str x10, [x19, #264]
	ldr x9, [x19, #256]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #256]
	ldr x9, [x19, #264]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #264]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 25f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 27f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 28f
27:
28:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 29f
211:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 211b
	b 210f
29:
210:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #256]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #264]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update_neon}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 212f
	movz x25, #1, lsl #0
	b 213f
212:
213:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	add x5, x19, #272
	bl {vg_cmac_aes_update_neon}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_neon}
	b 26f
25:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 214f
216:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 216b
	b 215f
214:
215:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #256]
	str x9, [x19, #144]
	ldr x9, [x19, #264]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_neon}
26:
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_aes_ctr32_neon}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 217f
219:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #272
	bl {vg_aes_ctr32_neon}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 220f
	movz x8, #16, lsl #0
	b 221f
220:
221:
222:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 222b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 223f
	sub x23, x23, x10
	b 224f
223:
	movz x23, #0, lsl #0
224:
	cbnz x23, 219b
	b 218f
217:
218:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x19, #0]
	str x10, [x9, #0]
	ldr x10, [x19, #8]
	str x10, [x9, #8]
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #2448
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
	movz x0, #0, lsl #0
	sub sp, sp, #2448
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
	add sp, sp, #2448
	ret
	.p2align 6

vg_aes_siv_decrypt_neon:
	sub sp, sp, #2448
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #256]
	str x9, [x19, #264]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #256
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_neon}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update_neon}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_neon}
	ldr x9, [x19, #256]
	ldr x10, [x19, #264]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #256]
	str x10, [x19, #264]
	ldr x9, [x19, #256]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #256]
	ldr x9, [x19, #264]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #264]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x9, #0]
	str x10, [x19, #0]
	ldr x10, [x9, #8]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_aes_ctr32_neon}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 25f
27:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #272
	bl {vg_aes_ctr32_neon}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 28f
	movz x8, #16, lsl #0
	b 29f
28:
29:
210:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 211f
	sub x23, x23, x10
	b 212f
211:
	movz x23, #0, lsl #0
212:
	cbnz x23, 27b
	b 26f
25:
26:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 213f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 215f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 216f
215:
216:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 217f
219:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 219b
	b 218f
217:
218:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #256]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #264]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update_neon}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 220f
	movz x25, #1, lsl #0
	b 221f
220:
221:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	add x5, x19, #272
	bl {vg_cmac_aes_update_neon}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_neon}
	b 214f
213:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 222f
224:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 224b
	b 223f
222:
223:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #256]
	str x9, [x19, #144]
	ldr x9, [x19, #264]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize_neon}
214:
	ldr x9, [x19, #0]
	ldr x10, [x19, #112]
	eor x9, x9, x10
	ldr x10, [x19, #8]
	ldr x11, [x19, #120]
	eor x10, x10, x11
	orr x9, x9, x10
	sub x10, x9, #1
	bic x10, x10, x9, ror #0
	lsr x0, x10, #63
	movz x11, #0, lsl #0
	sub x11, x11, x0
	add x6, x26, #0
	lsr x8, x27, #3
	cbz x8, 225f
227:
	ldr x9, [x6, #0]
	and x9, x9, x11
	str x9, [x6, #0]
	add x6, x6, #8
	sub x8, x8, #1
	cbnz x8, 227b
	b 226f
225:
226:
	lsl x8, x27, #61
	lsr x8, x8, #61
	cbz x8, 228f
230:
	ldrb w9, [x6, #0]
	and x9, x9, x11
	strb w9, [x6, #0]
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 230b
	b 229f
228:
229:
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #2448
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
	sub sp, sp, #2448
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
	add sp, sp, #2448
	ret
	.p2align 6

vg_aes_siv_encrypt:
	sub sp, sp, #2448
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #256]
	str x9, [x19, #264]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #256
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #272
	bl {vg_cmac_aes_finalize}
	ldr x9, [x19, #256]
	ldr x10, [x19, #264]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #256]
	str x10, [x19, #264]
	ldr x9, [x19, #256]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #256]
	ldr x9, [x19, #264]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #264]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 25f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 27f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 28f
27:
28:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 29f
211:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 211b
	b 210f
29:
210:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #256]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #264]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 212f
	movz x25, #1, lsl #0
	b 213f
212:
213:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	add x5, x19, #272
	bl {vg_cmac_aes_update}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize}
	b 26f
25:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 214f
216:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 216b
	b 215f
214:
215:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #256]
	str x9, [x19, #144]
	ldr x9, [x19, #264]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #0
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize}
26:
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_aes_ctr32}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 217f
219:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #272
	bl {vg_aes_ctr32}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 220f
	movz x8, #16, lsl #0
	b 221f
220:
221:
222:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 222b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 223f
	sub x23, x23, x10
	b 224f
223:
	movz x23, #0, lsl #0
224:
	cbnz x23, 219b
	b 218f
217:
218:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x19, #0]
	str x10, [x9, #0]
	ldr x10, [x19, #8]
	str x10, [x9, #8]
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #2448
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
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
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
	movz x0, #0, lsl #0
	sub sp, sp, #2448
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
	add sp, sp, #2448
	ret
	.p2align 6

vg_aes_siv_decrypt:
	sub sp, sp, #2448
	add x7, sp, #0
	str x19, [x7, #160]
	str x20, [x7, #168]
	str x21, [x7, #176]
	str x22, [x7, #184]
	str x23, [x7, #192]
	str x24, [x7, #200]
	str x25, [x7, #208]
	str x26, [x7, #216]
	str x27, [x7, #224]
	str x28, [x7, #232]
	str x30, [x7, #240]
	str x6, [x7, #248]
	add x19, x7, #0
	add x20, x0, #0
	add x21, x1, #0
	add x24, x2, #0
	add x25, x3, #0
	add x26, x4, #0
	add x27, x5, #0
	movz x9, #0, lsl #0
	str x9, [x19, #16]
	str x9, [x19, #24]
	str x9, [x19, #256]
	str x9, [x19, #264]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #256
	add x3, x19, #16
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize}
	cbz x25, 20f
22:
	ldr x22, [x24, #0]
	ldr x23, [x24, #8]
	movz x9, #0, lsl #0
	str x9, [x19, #128]
	str x9, [x19, #136]
	movz x28, #0, lsl #0
	cbz x23, 23f
	sub x28, x23, #1
	movz x9, #15, lsl #0
	and x9, x28, x9
	sub x28, x28, x9
	b 24f
23:
24:
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update}
	add x3, x22, x28
	sub x4, x23, x28
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #128
	add x5, x19, #272
	bl {vg_cmac_aes_finalize}
	ldr x9, [x19, #256]
	ldr x10, [x19, #264]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #256]
	str x10, [x19, #264]
	ldr x9, [x19, #256]
	ldr x10, [x19, #128]
	eor x9, x9, x10
	str x9, [x19, #256]
	ldr x9, [x19, #264]
	ldr x10, [x19, #136]
	eor x9, x9, x10
	str x9, [x19, #264]
	add x24, x24, #16
	sub x25, x25, #1
	cbnz x25, 22b
	b 21f
20:
21:
	add x22, x26, #0
	add x23, x27, #0
	ldr x9, [x19, #248]
	ldr x10, [x9, #0]
	str x10, [x19, #0]
	ldr x10, [x9, #8]
	str x10, [x19, #8]
	ldr x9, [x19, #0]
	str x9, [x19, #64]
	ldr x9, [x19, #8]
	movz x10, #128, lsl #0
	movk x10, #128, lsl #32
	bic x9, x9, x10, ror #0
	str x9, [x19, #72]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	lsr x4, x23, #4
	lsl x4, x4, #33
	lsr x4, x4, #33
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_aes_ctr32}
	lsr x9, x23, #4
	lsl x9, x9, #33
	lsr x9, x9, #33
	ldr x10, [x19, #72]
	rev x10, x10
	ldr x11, [x19, #64]
	rev x11, x11
	adds x10, x10, x9
	movz x12, #0, lsl #0
	adc x11, x11, x12
	rev x10, x10
	rev x11, x11
	str x11, [x19, #64]
	str x10, [x19, #72]
	lsl x9, x9, #4
	add x22, x22, x9
	sub x23, x23, x9
	cbz x23, 25f
27:
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #64]
	str x9, [x19, #96]
	ldr x9, [x19, #72]
	str x9, [x19, #104]
	add x0, x20, #272
	add x1, x21, #0
	add x2, x19, #96
	add x3, x19, #80
	movz x4, #1, lsl #0
	add x5, x19, #272
	bl {vg_aes_ctr32}
	lsr x9, x23, #4
	add x8, x23, #0
	add x6, x22, #0
	add x7, x19, #80
	cbz x9, 28f
	movz x8, #16, lsl #0
	b 29f
28:
29:
210:
	ldrb w9, [x6, #0]
	ldrb w10, [x7, #0]
	eor x9, x9, x10
	strb w9, [x6, #0]
	add x6, x6, #1
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 210b
	ldr x9, [x19, #72]
	rev x9, x9
	ldr x10, [x19, #64]
	rev x10, x10
	movz x11, #1, lsl #0
	adds x9, x9, x11
	movz x11, #0, lsl #0
	adc x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x10, [x19, #64]
	str x9, [x19, #72]
	add x22, x22, #16
	lsr x9, x23, #4
	movz x10, #16, lsl #0
	cbz x9, 211f
	sub x23, x23, x10
	b 212f
211:
	movz x23, #0, lsl #0
212:
	cbnz x23, 27b
	b 26f
25:
26:
	add x22, x26, #0
	add x23, x27, #0
	lsr x9, x23, #4
	cbz x9, 213f
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x28, #0, lsl #0
	cbz x9, 215f
	sub x9, x9, #1
	lsl x28, x9, #4
	b 216f
215:
216:
	add x6, x19, #32
	add x7, x22, x28
	sub x8, x23, x28
	cbz x8, 217f
219:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 219b
	b 218f
217:
218:
	sub x6, x23, x28
	add x6, x19, x6
	ldr x9, [x6, #16]
	ldr x10, [x19, #256]
	eor x9, x9, x10
	str x9, [x6, #16]
	ldr x9, [x6, #24]
	ldr x10, [x19, #264]
	eor x9, x9, x10
	str x9, [x6, #24]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	lsr x4, x28, #4
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x22, #0
	add x5, x19, #272
	bl {vg_cmac_aes_update}
	sub x9, x23, #1
	lsr x9, x9, #4
	movz x25, #0, lsl #0
	cbz x9, 220f
	movz x25, #1, lsl #0
	b 221f
220:
221:
	add x4, x25, #0
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	add x5, x19, #272
	bl {vg_cmac_aes_update}
	lsl x9, x25, #4
	add x3, x19, #32
	add x3, x3, x9
	sub x4, x23, x28
	sub x4, x4, x9
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x5, x19, #272
	bl {vg_cmac_aes_finalize}
	b 214f
213:
	movz x9, #0, lsl #0
	str x9, [x19, #32]
	str x9, [x19, #40]
	add x6, x19, #32
	add x7, x22, #0
	add x8, x23, #0
	cbz x8, 222f
224:
	ldrb w9, [x7, #0]
	strb w9, [x6, #0]
	add x7, x7, #1
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 224b
	b 223f
222:
223:
	add x6, x19, x23
	add x6, x6, #32
	movz x9, #128, lsl #0
	strb w9, [x6, #0]
	ldr x9, [x19, #256]
	str x9, [x19, #144]
	ldr x9, [x19, #264]
	str x9, [x19, #152]
	ldr x9, [x19, #144]
	ldr x10, [x19, #152]
	rev x9, x9
	rev x10, x10
	lsr x11, x9, #63
	movz x12, #0, lsl #0
	sub x11, x12, x11
	movz x12, #135, lsl #0
	and x11, x11, x12
	lsr x12, x10, #63
	lsl x9, x9, #1
	orr x9, x9, x12
	lsl x10, x10, #1
	eor x10, x10, x11
	rev x9, x9
	rev x10, x10
	str x9, [x19, #144]
	str x10, [x19, #152]
	ldr x9, [x19, #32]
	ldr x10, [x19, #144]
	eor x9, x9, x10
	str x9, [x19, #32]
	ldr x9, [x19, #40]
	ldr x10, [x19, #152]
	eor x9, x9, x10
	str x9, [x19, #40]
	movz x9, #0, lsl #0
	str x9, [x19, #112]
	str x9, [x19, #120]
	add x0, x20, #0
	add x1, x21, #0
	add x2, x19, #112
	add x3, x19, #32
	movz x4, #16, lsl #0
	add x5, x19, #272
	bl {vg_cmac_aes_finalize}
214:
	ldr x9, [x19, #0]
	ldr x10, [x19, #112]
	eor x9, x9, x10
	ldr x10, [x19, #8]
	ldr x11, [x19, #120]
	eor x10, x10, x11
	orr x9, x9, x10
	sub x10, x9, #1
	bic x10, x10, x9, ror #0
	lsr x0, x10, #63
	movz x11, #0, lsl #0
	sub x11, x11, x0
	add x6, x26, #0
	lsr x8, x27, #3
	cbz x8, 225f
227:
	ldr x9, [x6, #0]
	and x9, x9, x11
	str x9, [x6, #0]
	add x6, x6, #8
	sub x8, x8, #1
	cbnz x8, 227b
	b 226f
225:
226:
	lsl x8, x27, #61
	lsr x8, x8, #61
	cbz x8, 228f
230:
	ldrb w9, [x6, #0]
	and x9, x9, x11
	strb w9, [x6, #0]
	add x6, x6, #1
	sub x8, x8, #1
	cbnz x8, 230b
	b 229f
228:
229:
	ldr x20, [x19, #168]
	ldr x21, [x19, #176]
	ldr x22, [x19, #184]
	ldr x23, [x19, #192]
	ldr x24, [x19, #200]
	ldr x25, [x19, #208]
	ldr x26, [x19, #216]
	ldr x27, [x19, #224]
	ldr x28, [x19, #232]
	ldr x30, [x19, #240]
	ldr x19, [x19, #160]
	add sp, sp, #2448
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
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
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
	sub sp, sp, #2448
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
	add sp, sp, #2448
	ret
	.p2align 6
