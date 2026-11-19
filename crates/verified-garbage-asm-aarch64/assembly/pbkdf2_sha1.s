// The functions of `src/pbkdf2_sha1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1_sha2:
	sub sp, sp, #1120
	add x7, sp, #0
	add x10, x4, #0
	add x4, x7, #0
	str x19, [x4, #448]
	str x20, [x4, #456]
	str x21, [x4, #464]
	str x22, [x4, #472]
	str x24, [x4, #480]
	str x30, [x4, #488]
	str x23, [x4, #496]
	add x23, x4, #0
	str x5, [x23, #504]
	sub w9, w10, #1
	str x9, [x23, #512]
	str x6, [x23, #520]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	lsr x9, x20, #6
	cbz x9, 20f
	sub x9, x20, #64
	cbz x9, 22f
	add x0, x23, #780
	bl {vg_sha1_init}
	add x0, x23, #780
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha1_update_scratch_sha2}
	add x0, x23, #780
	add x1, x20, #0
	add x2, x23, #904
	add x3, x23, #0
	bl {vg_sha1_finalize_scratch_sha2}
	add x2, x23, #904
	movz x3, #20, lsl #0
	b 23f
22:
	add x2, x19, #0
	add x3, x20, #0
23:
	b 21f
20:
	add x2, x19, #0
	add x3, x20, #0
21:
	add x0, x23, #528
	add x1, x23, #612
	add x4, x23, #0
	bl {vg_hmac_sha1_init_scratch_sha2}
	ldr w9, [x23, #528]
	str w9, [x23, #696]
	ldr w9, [x23, #532]
	str w9, [x23, #700]
	ldr w9, [x23, #536]
	str w9, [x23, #704]
	ldr w9, [x23, #540]
	str w9, [x23, #708]
	ldr w9, [x23, #544]
	str w9, [x23, #712]
	ldr w9, [x23, #548]
	str w9, [x23, #716]
	ldr w9, [x23, #552]
	str w9, [x23, #720]
	ldr w9, [x23, #556]
	str w9, [x23, #724]
	ldr w9, [x23, #560]
	str w9, [x23, #728]
	ldr w9, [x23, #564]
	str w9, [x23, #732]
	ldr w9, [x23, #568]
	str w9, [x23, #736]
	ldr w9, [x23, #572]
	str w9, [x23, #740]
	ldr w9, [x23, #576]
	str w9, [x23, #744]
	ldr w9, [x23, #580]
	str w9, [x23, #748]
	ldr w9, [x23, #584]
	str w9, [x23, #752]
	ldr w9, [x23, #588]
	str w9, [x23, #756]
	ldr w9, [x23, #592]
	str w9, [x23, #760]
	ldr w9, [x23, #596]
	str w9, [x23, #764]
	ldr w9, [x23, #600]
	str w9, [x23, #768]
	ldr w9, [x23, #604]
	str w9, [x23, #772]
	ldr w9, [x23, #608]
	str w9, [x23, #776]
	add x0, x23, #696
	movz x1, #64, lsl #0
	add x2, x21, #0
	add x3, x22, #0
	add x4, x23, #0
	bl {vg_sha1_update_scratch_sha2}
	add x20, x22, #0
	ldr x22, [x23, #504]
	ldr x21, [x23, #520]
	movz x19, #1, lsl #0
	cbz x21, 24f
26:
	ldr w9, [x23, #696]
	str w9, [x23, #780]
	ldr w9, [x23, #700]
	str w9, [x23, #784]
	ldr w9, [x23, #704]
	str w9, [x23, #788]
	ldr w9, [x23, #708]
	str w9, [x23, #792]
	ldr w9, [x23, #712]
	str w9, [x23, #796]
	ldr w9, [x23, #716]
	str w9, [x23, #800]
	ldr w9, [x23, #720]
	str w9, [x23, #804]
	ldr w9, [x23, #724]
	str w9, [x23, #808]
	ldr w9, [x23, #728]
	str w9, [x23, #812]
	ldr w9, [x23, #732]
	str w9, [x23, #816]
	ldr w9, [x23, #736]
	str w9, [x23, #820]
	ldr w9, [x23, #740]
	str w9, [x23, #824]
	ldr w9, [x23, #744]
	str w9, [x23, #828]
	ldr w9, [x23, #748]
	str w9, [x23, #832]
	ldr w9, [x23, #752]
	str w9, [x23, #836]
	ldr w9, [x23, #756]
	str w9, [x23, #840]
	ldr w9, [x23, #760]
	str w9, [x23, #844]
	ldr w9, [x23, #764]
	str w9, [x23, #848]
	ldr w9, [x23, #768]
	str w9, [x23, #852]
	ldr w9, [x23, #772]
	str w9, [x23, #856]
	ldr w9, [x23, #776]
	str w9, [x23, #860]
	rev w9, w19
	str w9, [x23, #924]
	add x0, x23, #780
	add x1, x20, #64
	add x2, x23, #924
	movz x3, #4, lsl #0
	add x4, x23, #0
	bl {vg_sha1_update_scratch_sha2}
	add x0, x23, #780
	add x1, x23, #612
	add x2, x20, #68
	add x3, x23, #864
	add x4, x23, #0
	bl {vg_hmac_sha1_finalize_scratch_sha2}
	ldr w9, [x23, #864]
	str w9, [x23, #884]
	ldr w9, [x23, #868]
	str w9, [x23, #888]
	ldr w9, [x23, #872]
	str w9, [x23, #892]
	ldr w9, [x23, #876]
	str w9, [x23, #896]
	ldr w9, [x23, #880]
	str w9, [x23, #900]
	add x0, x23, #528
	add x1, x23, #864
	ldr x2, [x23, #512]
	add x3, x23, #884
	add x4, x23, #0
	bl {vg_pbkdf2_hmac_sha1_iterate_sha2}
	movz x11, #20, lsl #0
	sub x9, x21, #20
	lsr x9, x9, #63
	cbz x9, 27f
	add x11, x21, #0
	b 28f
27:
28:
	movz x24, #0, lsl #0
29:
	add x12, x23, x24
	ldrb w9, [x12, #884]
	add x13, x22, x24
	strb w9, [x13, #0]
	add x24, x24, #1
	sub x11, x11, #1
	cbnz x11, 29b
	add x22, x22, x24
	add x19, x19, #1
	sub x21, x21, x24
	cbnz x21, 26b
	b 25f
24:
25:
	ldr x19, [x23, #448]
	ldr x20, [x23, #456]
	ldr x21, [x23, #464]
	ldr x22, [x23, #472]
	ldr x24, [x23, #480]
	ldr x30, [x23, #488]
	ldr x23, [x23, #496]
	add sp, sp, #1120
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x7, #0, lsl #0
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
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #1136
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
	add sp, sp, #1136
	ret
	.p2align 6

vg_pbkdf2_hmac_sha1:
	sub sp, sp, #1120
	add x7, sp, #0
	add x10, x4, #0
	add x4, x7, #0
	str x19, [x4, #448]
	str x20, [x4, #456]
	str x21, [x4, #464]
	str x22, [x4, #472]
	str x24, [x4, #480]
	str x30, [x4, #488]
	str x23, [x4, #496]
	add x23, x4, #0
	str x5, [x23, #504]
	sub w9, w10, #1
	str x9, [x23, #512]
	str x6, [x23, #520]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	lsr x9, x20, #6
	cbz x9, 20f
	sub x9, x20, #64
	cbz x9, 22f
	add x0, x23, #780
	bl {vg_sha1_init}
	add x0, x23, #780
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha1_update_scratch}
	add x0, x23, #780
	add x1, x20, #0
	add x2, x23, #904
	add x3, x23, #0
	bl {vg_sha1_finalize_scratch}
	add x2, x23, #904
	movz x3, #20, lsl #0
	b 23f
22:
	add x2, x19, #0
	add x3, x20, #0
23:
	b 21f
20:
	add x2, x19, #0
	add x3, x20, #0
21:
	add x0, x23, #528
	add x1, x23, #612
	add x4, x23, #0
	bl {vg_hmac_sha1_init_scratch}
	ldr w9, [x23, #528]
	str w9, [x23, #696]
	ldr w9, [x23, #532]
	str w9, [x23, #700]
	ldr w9, [x23, #536]
	str w9, [x23, #704]
	ldr w9, [x23, #540]
	str w9, [x23, #708]
	ldr w9, [x23, #544]
	str w9, [x23, #712]
	ldr w9, [x23, #548]
	str w9, [x23, #716]
	ldr w9, [x23, #552]
	str w9, [x23, #720]
	ldr w9, [x23, #556]
	str w9, [x23, #724]
	ldr w9, [x23, #560]
	str w9, [x23, #728]
	ldr w9, [x23, #564]
	str w9, [x23, #732]
	ldr w9, [x23, #568]
	str w9, [x23, #736]
	ldr w9, [x23, #572]
	str w9, [x23, #740]
	ldr w9, [x23, #576]
	str w9, [x23, #744]
	ldr w9, [x23, #580]
	str w9, [x23, #748]
	ldr w9, [x23, #584]
	str w9, [x23, #752]
	ldr w9, [x23, #588]
	str w9, [x23, #756]
	ldr w9, [x23, #592]
	str w9, [x23, #760]
	ldr w9, [x23, #596]
	str w9, [x23, #764]
	ldr w9, [x23, #600]
	str w9, [x23, #768]
	ldr w9, [x23, #604]
	str w9, [x23, #772]
	ldr w9, [x23, #608]
	str w9, [x23, #776]
	add x0, x23, #696
	movz x1, #64, lsl #0
	add x2, x21, #0
	add x3, x22, #0
	add x4, x23, #0
	bl {vg_sha1_update_scratch}
	add x20, x22, #0
	ldr x22, [x23, #504]
	ldr x21, [x23, #520]
	movz x19, #1, lsl #0
	cbz x21, 24f
26:
	ldr w9, [x23, #696]
	str w9, [x23, #780]
	ldr w9, [x23, #700]
	str w9, [x23, #784]
	ldr w9, [x23, #704]
	str w9, [x23, #788]
	ldr w9, [x23, #708]
	str w9, [x23, #792]
	ldr w9, [x23, #712]
	str w9, [x23, #796]
	ldr w9, [x23, #716]
	str w9, [x23, #800]
	ldr w9, [x23, #720]
	str w9, [x23, #804]
	ldr w9, [x23, #724]
	str w9, [x23, #808]
	ldr w9, [x23, #728]
	str w9, [x23, #812]
	ldr w9, [x23, #732]
	str w9, [x23, #816]
	ldr w9, [x23, #736]
	str w9, [x23, #820]
	ldr w9, [x23, #740]
	str w9, [x23, #824]
	ldr w9, [x23, #744]
	str w9, [x23, #828]
	ldr w9, [x23, #748]
	str w9, [x23, #832]
	ldr w9, [x23, #752]
	str w9, [x23, #836]
	ldr w9, [x23, #756]
	str w9, [x23, #840]
	ldr w9, [x23, #760]
	str w9, [x23, #844]
	ldr w9, [x23, #764]
	str w9, [x23, #848]
	ldr w9, [x23, #768]
	str w9, [x23, #852]
	ldr w9, [x23, #772]
	str w9, [x23, #856]
	ldr w9, [x23, #776]
	str w9, [x23, #860]
	rev w9, w19
	str w9, [x23, #924]
	add x0, x23, #780
	add x1, x20, #64
	add x2, x23, #924
	movz x3, #4, lsl #0
	add x4, x23, #0
	bl {vg_sha1_update_scratch}
	add x0, x23, #780
	add x1, x23, #612
	add x2, x20, #68
	add x3, x23, #864
	add x4, x23, #0
	bl {vg_hmac_sha1_finalize_scratch}
	ldr w9, [x23, #864]
	str w9, [x23, #884]
	ldr w9, [x23, #868]
	str w9, [x23, #888]
	ldr w9, [x23, #872]
	str w9, [x23, #892]
	ldr w9, [x23, #876]
	str w9, [x23, #896]
	ldr w9, [x23, #880]
	str w9, [x23, #900]
	add x0, x23, #528
	add x1, x23, #864
	ldr x2, [x23, #512]
	add x3, x23, #884
	add x4, x23, #0
	bl {vg_pbkdf2_hmac_sha1_iterate}
	movz x11, #20, lsl #0
	sub x9, x21, #20
	lsr x9, x9, #63
	cbz x9, 27f
	add x11, x21, #0
	b 28f
27:
28:
	movz x24, #0, lsl #0
29:
	add x12, x23, x24
	ldrb w9, [x12, #884]
	add x13, x22, x24
	strb w9, [x13, #0]
	add x24, x24, #1
	sub x11, x11, #1
	cbnz x11, 29b
	add x22, x22, x24
	add x19, x19, #1
	sub x21, x21, x24
	cbnz x21, 26b
	b 25f
24:
25:
	ldr x19, [x23, #448]
	ldr x20, [x23, #456]
	ldr x21, [x23, #464]
	ldr x22, [x23, #472]
	ldr x24, [x23, #480]
	ldr x30, [x23, #488]
	ldr x23, [x23, #496]
	add sp, sp, #1120
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
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #1136
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
	add sp, sp, #1136
	ret
	.p2align 6
