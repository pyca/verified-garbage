// The functions of `src/pbkdf2_sha224.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha224_sha2:
	sub sp, sp, #1600
	add x7, sp, #0
	add x10, x4, #0
	add x4, x7, #0
	str x19, [x4, #832]
	str x20, [x4, #840]
	str x21, [x4, #848]
	str x22, [x4, #856]
	str x24, [x4, #864]
	str x30, [x4, #872]
	str x23, [x4, #880]
	add x23, x4, #0
	str x5, [x23, #888]
	sub w9, w10, #1
	str x9, [x23, #896]
	str x6, [x23, #904]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	lsr x9, x20, #6
	cbz x9, 20f
	sub x9, x20, #64
	cbz x9, 22f
	add x0, x23, #1200
	bl {vg_sha224_init}
	add x0, x23, #1200
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha256_update_scratch_sha2}
	add x0, x23, #1200
	add x1, x20, #0
	add x2, x23, #1352
	add x3, x23, #0
	bl {vg_sha256_finalize_scratch_sha2}
	add x2, x23, #1352
	movz x3, #28, lsl #0
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
	add x0, x23, #912
	add x1, x23, #1008
	add x4, x23, #0
	bl {vg_hmac_sha224_init_scratch_sha2}
	ldr w9, [x23, #912]
	str w9, [x23, #1104]
	ldr w9, [x23, #916]
	str w9, [x23, #1108]
	ldr w9, [x23, #920]
	str w9, [x23, #1112]
	ldr w9, [x23, #924]
	str w9, [x23, #1116]
	ldr w9, [x23, #928]
	str w9, [x23, #1120]
	ldr w9, [x23, #932]
	str w9, [x23, #1124]
	ldr w9, [x23, #936]
	str w9, [x23, #1128]
	ldr w9, [x23, #940]
	str w9, [x23, #1132]
	ldr w9, [x23, #944]
	str w9, [x23, #1136]
	ldr w9, [x23, #948]
	str w9, [x23, #1140]
	ldr w9, [x23, #952]
	str w9, [x23, #1144]
	ldr w9, [x23, #956]
	str w9, [x23, #1148]
	ldr w9, [x23, #960]
	str w9, [x23, #1152]
	ldr w9, [x23, #964]
	str w9, [x23, #1156]
	ldr w9, [x23, #968]
	str w9, [x23, #1160]
	ldr w9, [x23, #972]
	str w9, [x23, #1164]
	ldr w9, [x23, #976]
	str w9, [x23, #1168]
	ldr w9, [x23, #980]
	str w9, [x23, #1172]
	ldr w9, [x23, #984]
	str w9, [x23, #1176]
	ldr w9, [x23, #988]
	str w9, [x23, #1180]
	ldr w9, [x23, #992]
	str w9, [x23, #1184]
	ldr w9, [x23, #996]
	str w9, [x23, #1188]
	ldr w9, [x23, #1000]
	str w9, [x23, #1192]
	ldr w9, [x23, #1004]
	str w9, [x23, #1196]
	add x0, x23, #1104
	movz x1, #64, lsl #0
	add x2, x21, #0
	add x3, x22, #0
	add x4, x23, #0
	bl {vg_sha256_update_scratch_sha2}
	add x20, x22, #0
	ldr x22, [x23, #888]
	ldr x21, [x23, #904]
	movz x19, #1, lsl #0
	cbz x21, 24f
26:
	ldr w9, [x23, #1104]
	str w9, [x23, #1200]
	ldr w9, [x23, #1108]
	str w9, [x23, #1204]
	ldr w9, [x23, #1112]
	str w9, [x23, #1208]
	ldr w9, [x23, #1116]
	str w9, [x23, #1212]
	ldr w9, [x23, #1120]
	str w9, [x23, #1216]
	ldr w9, [x23, #1124]
	str w9, [x23, #1220]
	ldr w9, [x23, #1128]
	str w9, [x23, #1224]
	ldr w9, [x23, #1132]
	str w9, [x23, #1228]
	ldr w9, [x23, #1136]
	str w9, [x23, #1232]
	ldr w9, [x23, #1140]
	str w9, [x23, #1236]
	ldr w9, [x23, #1144]
	str w9, [x23, #1240]
	ldr w9, [x23, #1148]
	str w9, [x23, #1244]
	ldr w9, [x23, #1152]
	str w9, [x23, #1248]
	ldr w9, [x23, #1156]
	str w9, [x23, #1252]
	ldr w9, [x23, #1160]
	str w9, [x23, #1256]
	ldr w9, [x23, #1164]
	str w9, [x23, #1260]
	ldr w9, [x23, #1168]
	str w9, [x23, #1264]
	ldr w9, [x23, #1172]
	str w9, [x23, #1268]
	ldr w9, [x23, #1176]
	str w9, [x23, #1272]
	ldr w9, [x23, #1180]
	str w9, [x23, #1276]
	ldr w9, [x23, #1184]
	str w9, [x23, #1280]
	ldr w9, [x23, #1188]
	str w9, [x23, #1284]
	ldr w9, [x23, #1192]
	str w9, [x23, #1288]
	ldr w9, [x23, #1196]
	str w9, [x23, #1292]
	rev w9, w19
	str w9, [x23, #1384]
	add x0, x23, #1200
	add x1, x20, #64
	add x2, x23, #1384
	movz x3, #4, lsl #0
	add x4, x23, #0
	bl {vg_sha256_update_scratch_sha2}
	add x0, x23, #1200
	add x1, x23, #1008
	add x2, x20, #68
	add x3, x23, #1296
	add x4, x23, #0
	bl {vg_hmac_sha224_finalize_scratch_sha2}
	ldr w9, [x23, #1296]
	str w9, [x23, #1324]
	ldr w9, [x23, #1300]
	str w9, [x23, #1328]
	ldr w9, [x23, #1304]
	str w9, [x23, #1332]
	ldr w9, [x23, #1308]
	str w9, [x23, #1336]
	ldr w9, [x23, #1312]
	str w9, [x23, #1340]
	ldr w9, [x23, #1316]
	str w9, [x23, #1344]
	ldr w9, [x23, #1320]
	str w9, [x23, #1348]
	add x0, x23, #912
	add x1, x23, #1296
	ldr x2, [x23, #896]
	add x3, x23, #1324
	add x4, x23, #0
	bl {vg_pbkdf2_hmac_sha224_iterate_sha2}
	movz x11, #28, lsl #0
	sub x9, x21, #28
	lsr x9, x9, #63
	cbz x9, 27f
	add x11, x21, #0
	b 28f
27:
28:
	movz x24, #0, lsl #0
29:
	add x12, x23, x24
	ldrb w9, [x12, #1324]
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
	ldr x19, [x23, #832]
	ldr x20, [x23, #840]
	ldr x21, [x23, #848]
	ldr x22, [x23, #856]
	ldr x24, [x23, #864]
	ldr x30, [x23, #872]
	ldr x23, [x23, #880]
	add sp, sp, #1600
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
	sub sp, sp, #1616
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
	add sp, sp, #1616
	ret
	.p2align 6

vg_pbkdf2_hmac_sha224:
	sub sp, sp, #1600
	add x7, sp, #0
	add x10, x4, #0
	add x4, x7, #0
	str x19, [x4, #832]
	str x20, [x4, #840]
	str x21, [x4, #848]
	str x22, [x4, #856]
	str x24, [x4, #864]
	str x30, [x4, #872]
	str x23, [x4, #880]
	add x23, x4, #0
	str x5, [x23, #888]
	sub w9, w10, #1
	str x9, [x23, #896]
	str x6, [x23, #904]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	lsr x9, x20, #6
	cbz x9, 20f
	sub x9, x20, #64
	cbz x9, 22f
	add x0, x23, #1200
	bl {vg_sha224_init}
	add x0, x23, #1200
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha256_update_scratch}
	add x0, x23, #1200
	add x1, x20, #0
	add x2, x23, #1352
	add x3, x23, #0
	bl {vg_sha256_finalize_scratch}
	add x2, x23, #1352
	movz x3, #28, lsl #0
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
	add x0, x23, #912
	add x1, x23, #1008
	add x4, x23, #0
	bl {vg_hmac_sha224_init_scratch}
	ldr w9, [x23, #912]
	str w9, [x23, #1104]
	ldr w9, [x23, #916]
	str w9, [x23, #1108]
	ldr w9, [x23, #920]
	str w9, [x23, #1112]
	ldr w9, [x23, #924]
	str w9, [x23, #1116]
	ldr w9, [x23, #928]
	str w9, [x23, #1120]
	ldr w9, [x23, #932]
	str w9, [x23, #1124]
	ldr w9, [x23, #936]
	str w9, [x23, #1128]
	ldr w9, [x23, #940]
	str w9, [x23, #1132]
	ldr w9, [x23, #944]
	str w9, [x23, #1136]
	ldr w9, [x23, #948]
	str w9, [x23, #1140]
	ldr w9, [x23, #952]
	str w9, [x23, #1144]
	ldr w9, [x23, #956]
	str w9, [x23, #1148]
	ldr w9, [x23, #960]
	str w9, [x23, #1152]
	ldr w9, [x23, #964]
	str w9, [x23, #1156]
	ldr w9, [x23, #968]
	str w9, [x23, #1160]
	ldr w9, [x23, #972]
	str w9, [x23, #1164]
	ldr w9, [x23, #976]
	str w9, [x23, #1168]
	ldr w9, [x23, #980]
	str w9, [x23, #1172]
	ldr w9, [x23, #984]
	str w9, [x23, #1176]
	ldr w9, [x23, #988]
	str w9, [x23, #1180]
	ldr w9, [x23, #992]
	str w9, [x23, #1184]
	ldr w9, [x23, #996]
	str w9, [x23, #1188]
	ldr w9, [x23, #1000]
	str w9, [x23, #1192]
	ldr w9, [x23, #1004]
	str w9, [x23, #1196]
	add x0, x23, #1104
	movz x1, #64, lsl #0
	add x2, x21, #0
	add x3, x22, #0
	add x4, x23, #0
	bl {vg_sha256_update_scratch}
	add x20, x22, #0
	ldr x22, [x23, #888]
	ldr x21, [x23, #904]
	movz x19, #1, lsl #0
	cbz x21, 24f
26:
	ldr w9, [x23, #1104]
	str w9, [x23, #1200]
	ldr w9, [x23, #1108]
	str w9, [x23, #1204]
	ldr w9, [x23, #1112]
	str w9, [x23, #1208]
	ldr w9, [x23, #1116]
	str w9, [x23, #1212]
	ldr w9, [x23, #1120]
	str w9, [x23, #1216]
	ldr w9, [x23, #1124]
	str w9, [x23, #1220]
	ldr w9, [x23, #1128]
	str w9, [x23, #1224]
	ldr w9, [x23, #1132]
	str w9, [x23, #1228]
	ldr w9, [x23, #1136]
	str w9, [x23, #1232]
	ldr w9, [x23, #1140]
	str w9, [x23, #1236]
	ldr w9, [x23, #1144]
	str w9, [x23, #1240]
	ldr w9, [x23, #1148]
	str w9, [x23, #1244]
	ldr w9, [x23, #1152]
	str w9, [x23, #1248]
	ldr w9, [x23, #1156]
	str w9, [x23, #1252]
	ldr w9, [x23, #1160]
	str w9, [x23, #1256]
	ldr w9, [x23, #1164]
	str w9, [x23, #1260]
	ldr w9, [x23, #1168]
	str w9, [x23, #1264]
	ldr w9, [x23, #1172]
	str w9, [x23, #1268]
	ldr w9, [x23, #1176]
	str w9, [x23, #1272]
	ldr w9, [x23, #1180]
	str w9, [x23, #1276]
	ldr w9, [x23, #1184]
	str w9, [x23, #1280]
	ldr w9, [x23, #1188]
	str w9, [x23, #1284]
	ldr w9, [x23, #1192]
	str w9, [x23, #1288]
	ldr w9, [x23, #1196]
	str w9, [x23, #1292]
	rev w9, w19
	str w9, [x23, #1384]
	add x0, x23, #1200
	add x1, x20, #64
	add x2, x23, #1384
	movz x3, #4, lsl #0
	add x4, x23, #0
	bl {vg_sha256_update_scratch}
	add x0, x23, #1200
	add x1, x23, #1008
	add x2, x20, #68
	add x3, x23, #1296
	add x4, x23, #0
	bl {vg_hmac_sha224_finalize_scratch}
	ldr w9, [x23, #1296]
	str w9, [x23, #1324]
	ldr w9, [x23, #1300]
	str w9, [x23, #1328]
	ldr w9, [x23, #1304]
	str w9, [x23, #1332]
	ldr w9, [x23, #1308]
	str w9, [x23, #1336]
	ldr w9, [x23, #1312]
	str w9, [x23, #1340]
	ldr w9, [x23, #1316]
	str w9, [x23, #1344]
	ldr w9, [x23, #1320]
	str w9, [x23, #1348]
	add x0, x23, #912
	add x1, x23, #1296
	ldr x2, [x23, #896]
	add x3, x23, #1324
	add x4, x23, #0
	bl {vg_pbkdf2_hmac_sha224_iterate}
	movz x11, #28, lsl #0
	sub x9, x21, #28
	lsr x9, x9, #63
	cbz x9, 27f
	add x11, x21, #0
	b 28f
27:
28:
	movz x24, #0, lsl #0
29:
	add x12, x23, x24
	ldrb w9, [x12, #1324]
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
	ldr x19, [x23, #832]
	ldr x20, [x23, #840]
	ldr x21, [x23, #848]
	ldr x22, [x23, #856]
	ldr x24, [x23, #864]
	ldr x30, [x23, #872]
	ldr x23, [x23, #880]
	add sp, sp, #1600
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
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #1616
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
	add sp, sp, #1616
	ret
	.p2align 6
