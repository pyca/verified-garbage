// The functions of `src/internal/vg_cast5_batch_decrypt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_batch_decrypt:
	add x16, x14, #0
	adrp x9, {VG_CAST5_PLANES}
	add x9, x9, {VG_CAST5_PLANES}
	ldr q20, [x4, #0]
	ldr q21, [x4, #16]
	rev32 v20.16b, v20.16b
	rev32 v21.16b, v21.16b
	uzp1 v4.4s, v20.4s, v21.4s
	uzp2 v8.4s, v20.4s, v21.4s
	ldr q20, [x4, #32]
	ldr q21, [x4, #48]
	rev32 v20.16b, v20.16b
	rev32 v21.16b, v21.16b
	uzp1 v5.4s, v20.4s, v21.4s
	uzp2 v9.4s, v20.4s, v21.4s
	ldr q20, [x4, #64]
	ldr q21, [x4, #80]
	rev32 v20.16b, v20.16b
	rev32 v21.16b, v21.16b
	uzp1 v6.4s, v20.4s, v21.4s
	uzp2 v10.4s, v20.4s, v21.4s
	ldr q20, [x4, #96]
	ldr q21, [x4, #112]
	rev32 v20.16b, v20.16b
	rev32 v21.16b, v21.16b
	uzp1 v7.4s, v20.4s, v21.4s
	uzp2 v11.4s, v20.4s, v21.4s
	add x17, x4, #0
	lsl x5, x16, #2
	add x5, x5, x0
	sub x5, x5, #4
	lsr x7, x16, #2
	add x7, x7, #1
	sub x8, x16, #16
	cbz x8, 20f
	b 21f
20:
	ldr w6, [x5, #0]
	dup v0.4s, w6
	ldr w13, [x5, #64]
	movz w4, #1, lsl #0
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	dup v27.4s, w4
	add v12.4s, v0.4s, v8.4s
	add v13.4s, v0.4s, v9.4s
	add v14.4s, v0.4s, v10.4s
	add v15.4s, v0.4s, v11.4s
	umull v0.2d, v12.2s, v27.2s
	umull2 v1.2d, v12.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v12.16b, v20.16b, v21.16b
	umull v0.2d, v13.2s, v27.2s
	umull2 v1.2d, v13.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v13.16b, v20.16b, v21.16b
	umull v0.2d, v14.2s, v27.2s
	umull2 v1.2d, v14.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v14.16b, v20.16b, v21.16b
	umull v0.2d, v15.2s, v27.2s
	umull2 v1.2d, v15.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v15.16b, v20.16b, v21.16b
	uzp1 v0.16b, v12.16b, v13.16b
	uzp2 v1.16b, v12.16b, v13.16b
	uzp1 v20.16b, v14.16b, v15.16b
	uzp2 v21.16b, v14.16b, v15.16b
	uzp1 v19.16b, v0.16b, v20.16b
	uzp2 v17.16b, v0.16b, v20.16b
	uzp1 v18.16b, v1.16b, v21.16b
	uzp2 v16.16b, v1.16b, v21.16b
	eor v24.16b, v16.16b, v2.16b
	eor v25.16b, v16.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #0]
	ldr q29, [x9, #16]
	ldr q30, [x9, #32]
	ldr q31, [x9, #48]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #64]
	ldr q29, [x9, #80]
	ldr q30, [x9, #96]
	ldr q31, [x9, #112]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #128]
	ldr q29, [x9, #144]
	ldr q30, [x9, #160]
	ldr q31, [x9, #176]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #192]
	ldr q29, [x9, #208]
	ldr q30, [x9, #224]
	ldr q31, [x9, #240]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #256]
	ldr q29, [x9, #272]
	ldr q30, [x9, #288]
	ldr q31, [x9, #304]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #320]
	ldr q29, [x9, #336]
	ldr q30, [x9, #352]
	ldr q31, [x9, #368]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #384]
	ldr q29, [x9, #400]
	ldr q30, [x9, #416]
	ldr q31, [x9, #432]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #448]
	ldr q29, [x9, #464]
	ldr q30, [x9, #480]
	ldr q31, [x9, #496]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #512]
	ldr q29, [x9, #528]
	ldr q30, [x9, #544]
	ldr q31, [x9, #560]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #576]
	ldr q29, [x9, #592]
	ldr q30, [x9, #608]
	ldr q31, [x9, #624]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #640]
	ldr q29, [x9, #656]
	ldr q30, [x9, #672]
	ldr q31, [x9, #688]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #704]
	ldr q29, [x9, #720]
	ldr q30, [x9, #736]
	ldr q31, [x9, #752]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #768]
	ldr q29, [x9, #784]
	ldr q30, [x9, #800]
	ldr q31, [x9, #816]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #832]
	ldr q29, [x9, #848]
	ldr q30, [x9, #864]
	ldr q31, [x9, #880]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #896]
	ldr q29, [x9, #912]
	ldr q30, [x9, #928]
	ldr q31, [x9, #944]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #960]
	ldr q29, [x9, #976]
	ldr q30, [x9, #992]
	ldr q31, [x9, #1008]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	mov v12.16b, v21.16b
	mov v13.16b, v23.16b
	mov v14.16b, v0.16b
	mov v15.16b, v1.16b
	eor v24.16b, v17.16b, v2.16b
	eor v25.16b, v17.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #1024]
	ldr q29, [x9, #1040]
	ldr q30, [x9, #1056]
	ldr q31, [x9, #1072]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1088]
	ldr q29, [x9, #1104]
	ldr q30, [x9, #1120]
	ldr q31, [x9, #1136]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1152]
	ldr q29, [x9, #1168]
	ldr q30, [x9, #1184]
	ldr q31, [x9, #1200]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1216]
	ldr q29, [x9, #1232]
	ldr q30, [x9, #1248]
	ldr q31, [x9, #1264]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1280]
	ldr q29, [x9, #1296]
	ldr q30, [x9, #1312]
	ldr q31, [x9, #1328]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1344]
	ldr q29, [x9, #1360]
	ldr q30, [x9, #1376]
	ldr q31, [x9, #1392]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1408]
	ldr q29, [x9, #1424]
	ldr q30, [x9, #1440]
	ldr q31, [x9, #1456]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1472]
	ldr q29, [x9, #1488]
	ldr q30, [x9, #1504]
	ldr q31, [x9, #1520]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1536]
	ldr q29, [x9, #1552]
	ldr q30, [x9, #1568]
	ldr q31, [x9, #1584]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1600]
	ldr q29, [x9, #1616]
	ldr q30, [x9, #1632]
	ldr q31, [x9, #1648]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1664]
	ldr q29, [x9, #1680]
	ldr q30, [x9, #1696]
	ldr q31, [x9, #1712]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1728]
	ldr q29, [x9, #1744]
	ldr q30, [x9, #1760]
	ldr q31, [x9, #1776]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1792]
	ldr q29, [x9, #1808]
	ldr q30, [x9, #1824]
	ldr q31, [x9, #1840]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1856]
	ldr q29, [x9, #1872]
	ldr q30, [x9, #1888]
	ldr q31, [x9, #1904]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1920]
	ldr q29, [x9, #1936]
	ldr q30, [x9, #1952]
	ldr q31, [x9, #1968]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1984]
	ldr q29, [x9, #2000]
	ldr q30, [x9, #2016]
	ldr q31, [x9, #2032]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	eor v12.16b, v12.16b, v21.16b
	eor v13.16b, v13.16b, v23.16b
	eor v14.16b, v14.16b, v0.16b
	eor v15.16b, v15.16b, v1.16b
	eor v24.16b, v18.16b, v2.16b
	eor v25.16b, v18.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #2048]
	ldr q29, [x9, #2064]
	ldr q30, [x9, #2080]
	ldr q31, [x9, #2096]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2112]
	ldr q29, [x9, #2128]
	ldr q30, [x9, #2144]
	ldr q31, [x9, #2160]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2176]
	ldr q29, [x9, #2192]
	ldr q30, [x9, #2208]
	ldr q31, [x9, #2224]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2240]
	ldr q29, [x9, #2256]
	ldr q30, [x9, #2272]
	ldr q31, [x9, #2288]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2304]
	ldr q29, [x9, #2320]
	ldr q30, [x9, #2336]
	ldr q31, [x9, #2352]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2368]
	ldr q29, [x9, #2384]
	ldr q30, [x9, #2400]
	ldr q31, [x9, #2416]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2432]
	ldr q29, [x9, #2448]
	ldr q30, [x9, #2464]
	ldr q31, [x9, #2480]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2496]
	ldr q29, [x9, #2512]
	ldr q30, [x9, #2528]
	ldr q31, [x9, #2544]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2560]
	ldr q29, [x9, #2576]
	ldr q30, [x9, #2592]
	ldr q31, [x9, #2608]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2624]
	ldr q29, [x9, #2640]
	ldr q30, [x9, #2656]
	ldr q31, [x9, #2672]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2688]
	ldr q29, [x9, #2704]
	ldr q30, [x9, #2720]
	ldr q31, [x9, #2736]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2752]
	ldr q29, [x9, #2768]
	ldr q30, [x9, #2784]
	ldr q31, [x9, #2800]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2816]
	ldr q29, [x9, #2832]
	ldr q30, [x9, #2848]
	ldr q31, [x9, #2864]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2880]
	ldr q29, [x9, #2896]
	ldr q30, [x9, #2912]
	ldr q31, [x9, #2928]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2944]
	ldr q29, [x9, #2960]
	ldr q30, [x9, #2976]
	ldr q31, [x9, #2992]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3008]
	ldr q29, [x9, #3024]
	ldr q30, [x9, #3040]
	ldr q31, [x9, #3056]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	sub v12.4s, v12.4s, v21.4s
	sub v13.4s, v13.4s, v23.4s
	sub v14.4s, v14.4s, v0.4s
	sub v15.4s, v15.4s, v1.4s
	eor v24.16b, v19.16b, v2.16b
	eor v25.16b, v19.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #3072]
	ldr q29, [x9, #3088]
	ldr q30, [x9, #3104]
	ldr q31, [x9, #3120]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3136]
	ldr q29, [x9, #3152]
	ldr q30, [x9, #3168]
	ldr q31, [x9, #3184]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3200]
	ldr q29, [x9, #3216]
	ldr q30, [x9, #3232]
	ldr q31, [x9, #3248]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3264]
	ldr q29, [x9, #3280]
	ldr q30, [x9, #3296]
	ldr q31, [x9, #3312]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3328]
	ldr q29, [x9, #3344]
	ldr q30, [x9, #3360]
	ldr q31, [x9, #3376]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3392]
	ldr q29, [x9, #3408]
	ldr q30, [x9, #3424]
	ldr q31, [x9, #3440]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3456]
	ldr q29, [x9, #3472]
	ldr q30, [x9, #3488]
	ldr q31, [x9, #3504]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3520]
	ldr q29, [x9, #3536]
	ldr q30, [x9, #3552]
	ldr q31, [x9, #3568]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3584]
	ldr q29, [x9, #3600]
	ldr q30, [x9, #3616]
	ldr q31, [x9, #3632]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3648]
	ldr q29, [x9, #3664]
	ldr q30, [x9, #3680]
	ldr q31, [x9, #3696]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3712]
	ldr q29, [x9, #3728]
	ldr q30, [x9, #3744]
	ldr q31, [x9, #3760]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3776]
	ldr q29, [x9, #3792]
	ldr q30, [x9, #3808]
	ldr q31, [x9, #3824]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3840]
	ldr q29, [x9, #3856]
	ldr q30, [x9, #3872]
	ldr q31, [x9, #3888]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3904]
	ldr q29, [x9, #3920]
	ldr q30, [x9, #3936]
	ldr q31, [x9, #3952]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3968]
	ldr q29, [x9, #3984]
	ldr q30, [x9, #4000]
	ldr q31, [x9, #4016]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #4032]
	ldr q29, [x9, #4048]
	ldr q30, [x9, #4064]
	ldr q31, [x9, #4080]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	add v12.4s, v12.4s, v21.4s
	add v13.4s, v13.4s, v23.4s
	add v14.4s, v14.4s, v0.4s
	add v15.4s, v15.4s, v1.4s
	eor v12.16b, v4.16b, v12.16b
	eor v13.16b, v5.16b, v13.16b
	eor v14.16b, v6.16b, v14.16b
	eor v15.16b, v7.16b, v15.16b
	mov v4.16b, v8.16b
	mov v5.16b, v9.16b
	mov v6.16b, v10.16b
	mov v7.16b, v11.16b
	mov v8.16b, v12.16b
	mov v9.16b, v13.16b
	mov v10.16b, v14.16b
	mov v11.16b, v15.16b
	sub x5, x5, #4
21:
22:
	ldr w6, [x5, #0]
	dup v0.4s, w6
	ldr w13, [x5, #64]
	movz w4, #1, lsl #0
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	dup v27.4s, w4
	sub v12.4s, v0.4s, v8.4s
	sub v13.4s, v0.4s, v9.4s
	sub v14.4s, v0.4s, v10.4s
	sub v15.4s, v0.4s, v11.4s
	umull v0.2d, v12.2s, v27.2s
	umull2 v1.2d, v12.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v12.16b, v20.16b, v21.16b
	umull v0.2d, v13.2s, v27.2s
	umull2 v1.2d, v13.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v13.16b, v20.16b, v21.16b
	umull v0.2d, v14.2s, v27.2s
	umull2 v1.2d, v14.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v14.16b, v20.16b, v21.16b
	umull v0.2d, v15.2s, v27.2s
	umull2 v1.2d, v15.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v15.16b, v20.16b, v21.16b
	uzp1 v0.16b, v12.16b, v13.16b
	uzp2 v1.16b, v12.16b, v13.16b
	uzp1 v20.16b, v14.16b, v15.16b
	uzp2 v21.16b, v14.16b, v15.16b
	uzp1 v19.16b, v0.16b, v20.16b
	uzp2 v17.16b, v0.16b, v20.16b
	uzp1 v18.16b, v1.16b, v21.16b
	uzp2 v16.16b, v1.16b, v21.16b
	eor v24.16b, v16.16b, v2.16b
	eor v25.16b, v16.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #0]
	ldr q29, [x9, #16]
	ldr q30, [x9, #32]
	ldr q31, [x9, #48]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #64]
	ldr q29, [x9, #80]
	ldr q30, [x9, #96]
	ldr q31, [x9, #112]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #128]
	ldr q29, [x9, #144]
	ldr q30, [x9, #160]
	ldr q31, [x9, #176]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #192]
	ldr q29, [x9, #208]
	ldr q30, [x9, #224]
	ldr q31, [x9, #240]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #256]
	ldr q29, [x9, #272]
	ldr q30, [x9, #288]
	ldr q31, [x9, #304]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #320]
	ldr q29, [x9, #336]
	ldr q30, [x9, #352]
	ldr q31, [x9, #368]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #384]
	ldr q29, [x9, #400]
	ldr q30, [x9, #416]
	ldr q31, [x9, #432]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #448]
	ldr q29, [x9, #464]
	ldr q30, [x9, #480]
	ldr q31, [x9, #496]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #512]
	ldr q29, [x9, #528]
	ldr q30, [x9, #544]
	ldr q31, [x9, #560]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #576]
	ldr q29, [x9, #592]
	ldr q30, [x9, #608]
	ldr q31, [x9, #624]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #640]
	ldr q29, [x9, #656]
	ldr q30, [x9, #672]
	ldr q31, [x9, #688]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #704]
	ldr q29, [x9, #720]
	ldr q30, [x9, #736]
	ldr q31, [x9, #752]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #768]
	ldr q29, [x9, #784]
	ldr q30, [x9, #800]
	ldr q31, [x9, #816]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #832]
	ldr q29, [x9, #848]
	ldr q30, [x9, #864]
	ldr q31, [x9, #880]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #896]
	ldr q29, [x9, #912]
	ldr q30, [x9, #928]
	ldr q31, [x9, #944]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #960]
	ldr q29, [x9, #976]
	ldr q30, [x9, #992]
	ldr q31, [x9, #1008]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	mov v12.16b, v21.16b
	mov v13.16b, v23.16b
	mov v14.16b, v0.16b
	mov v15.16b, v1.16b
	eor v24.16b, v17.16b, v2.16b
	eor v25.16b, v17.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #1024]
	ldr q29, [x9, #1040]
	ldr q30, [x9, #1056]
	ldr q31, [x9, #1072]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1088]
	ldr q29, [x9, #1104]
	ldr q30, [x9, #1120]
	ldr q31, [x9, #1136]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1152]
	ldr q29, [x9, #1168]
	ldr q30, [x9, #1184]
	ldr q31, [x9, #1200]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1216]
	ldr q29, [x9, #1232]
	ldr q30, [x9, #1248]
	ldr q31, [x9, #1264]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1280]
	ldr q29, [x9, #1296]
	ldr q30, [x9, #1312]
	ldr q31, [x9, #1328]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1344]
	ldr q29, [x9, #1360]
	ldr q30, [x9, #1376]
	ldr q31, [x9, #1392]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1408]
	ldr q29, [x9, #1424]
	ldr q30, [x9, #1440]
	ldr q31, [x9, #1456]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1472]
	ldr q29, [x9, #1488]
	ldr q30, [x9, #1504]
	ldr q31, [x9, #1520]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1536]
	ldr q29, [x9, #1552]
	ldr q30, [x9, #1568]
	ldr q31, [x9, #1584]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1600]
	ldr q29, [x9, #1616]
	ldr q30, [x9, #1632]
	ldr q31, [x9, #1648]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1664]
	ldr q29, [x9, #1680]
	ldr q30, [x9, #1696]
	ldr q31, [x9, #1712]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1728]
	ldr q29, [x9, #1744]
	ldr q30, [x9, #1760]
	ldr q31, [x9, #1776]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1792]
	ldr q29, [x9, #1808]
	ldr q30, [x9, #1824]
	ldr q31, [x9, #1840]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1856]
	ldr q29, [x9, #1872]
	ldr q30, [x9, #1888]
	ldr q31, [x9, #1904]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1920]
	ldr q29, [x9, #1936]
	ldr q30, [x9, #1952]
	ldr q31, [x9, #1968]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1984]
	ldr q29, [x9, #2000]
	ldr q30, [x9, #2016]
	ldr q31, [x9, #2032]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	add v12.4s, v12.4s, v21.4s
	add v13.4s, v13.4s, v23.4s
	add v14.4s, v14.4s, v0.4s
	add v15.4s, v15.4s, v1.4s
	eor v24.16b, v18.16b, v2.16b
	eor v25.16b, v18.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #2048]
	ldr q29, [x9, #2064]
	ldr q30, [x9, #2080]
	ldr q31, [x9, #2096]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2112]
	ldr q29, [x9, #2128]
	ldr q30, [x9, #2144]
	ldr q31, [x9, #2160]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2176]
	ldr q29, [x9, #2192]
	ldr q30, [x9, #2208]
	ldr q31, [x9, #2224]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2240]
	ldr q29, [x9, #2256]
	ldr q30, [x9, #2272]
	ldr q31, [x9, #2288]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2304]
	ldr q29, [x9, #2320]
	ldr q30, [x9, #2336]
	ldr q31, [x9, #2352]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2368]
	ldr q29, [x9, #2384]
	ldr q30, [x9, #2400]
	ldr q31, [x9, #2416]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2432]
	ldr q29, [x9, #2448]
	ldr q30, [x9, #2464]
	ldr q31, [x9, #2480]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2496]
	ldr q29, [x9, #2512]
	ldr q30, [x9, #2528]
	ldr q31, [x9, #2544]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2560]
	ldr q29, [x9, #2576]
	ldr q30, [x9, #2592]
	ldr q31, [x9, #2608]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2624]
	ldr q29, [x9, #2640]
	ldr q30, [x9, #2656]
	ldr q31, [x9, #2672]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2688]
	ldr q29, [x9, #2704]
	ldr q30, [x9, #2720]
	ldr q31, [x9, #2736]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2752]
	ldr q29, [x9, #2768]
	ldr q30, [x9, #2784]
	ldr q31, [x9, #2800]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2816]
	ldr q29, [x9, #2832]
	ldr q30, [x9, #2848]
	ldr q31, [x9, #2864]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2880]
	ldr q29, [x9, #2896]
	ldr q30, [x9, #2912]
	ldr q31, [x9, #2928]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2944]
	ldr q29, [x9, #2960]
	ldr q30, [x9, #2976]
	ldr q31, [x9, #2992]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3008]
	ldr q29, [x9, #3024]
	ldr q30, [x9, #3040]
	ldr q31, [x9, #3056]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	eor v12.16b, v12.16b, v21.16b
	eor v13.16b, v13.16b, v23.16b
	eor v14.16b, v14.16b, v0.16b
	eor v15.16b, v15.16b, v1.16b
	eor v24.16b, v19.16b, v2.16b
	eor v25.16b, v19.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #3072]
	ldr q29, [x9, #3088]
	ldr q30, [x9, #3104]
	ldr q31, [x9, #3120]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3136]
	ldr q29, [x9, #3152]
	ldr q30, [x9, #3168]
	ldr q31, [x9, #3184]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3200]
	ldr q29, [x9, #3216]
	ldr q30, [x9, #3232]
	ldr q31, [x9, #3248]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3264]
	ldr q29, [x9, #3280]
	ldr q30, [x9, #3296]
	ldr q31, [x9, #3312]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3328]
	ldr q29, [x9, #3344]
	ldr q30, [x9, #3360]
	ldr q31, [x9, #3376]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3392]
	ldr q29, [x9, #3408]
	ldr q30, [x9, #3424]
	ldr q31, [x9, #3440]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3456]
	ldr q29, [x9, #3472]
	ldr q30, [x9, #3488]
	ldr q31, [x9, #3504]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3520]
	ldr q29, [x9, #3536]
	ldr q30, [x9, #3552]
	ldr q31, [x9, #3568]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3584]
	ldr q29, [x9, #3600]
	ldr q30, [x9, #3616]
	ldr q31, [x9, #3632]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3648]
	ldr q29, [x9, #3664]
	ldr q30, [x9, #3680]
	ldr q31, [x9, #3696]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3712]
	ldr q29, [x9, #3728]
	ldr q30, [x9, #3744]
	ldr q31, [x9, #3760]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3776]
	ldr q29, [x9, #3792]
	ldr q30, [x9, #3808]
	ldr q31, [x9, #3824]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3840]
	ldr q29, [x9, #3856]
	ldr q30, [x9, #3872]
	ldr q31, [x9, #3888]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3904]
	ldr q29, [x9, #3920]
	ldr q30, [x9, #3936]
	ldr q31, [x9, #3952]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3968]
	ldr q29, [x9, #3984]
	ldr q30, [x9, #4000]
	ldr q31, [x9, #4016]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #4032]
	ldr q29, [x9, #4048]
	ldr q30, [x9, #4064]
	ldr q31, [x9, #4080]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	sub v12.4s, v12.4s, v21.4s
	sub v13.4s, v13.4s, v23.4s
	sub v14.4s, v14.4s, v0.4s
	sub v15.4s, v15.4s, v1.4s
	eor v12.16b, v4.16b, v12.16b
	eor v13.16b, v5.16b, v13.16b
	eor v14.16b, v6.16b, v14.16b
	eor v15.16b, v7.16b, v15.16b
	mov v4.16b, v8.16b
	mov v5.16b, v9.16b
	mov v6.16b, v10.16b
	mov v7.16b, v11.16b
	mov v8.16b, v12.16b
	mov v9.16b, v13.16b
	mov v10.16b, v14.16b
	mov v11.16b, v15.16b
	sub x5, x5, #4
	ldr w6, [x5, #0]
	dup v0.4s, w6
	ldr w13, [x5, #64]
	movz w4, #1, lsl #0
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	dup v27.4s, w4
	eor v12.16b, v0.16b, v8.16b
	eor v13.16b, v0.16b, v9.16b
	eor v14.16b, v0.16b, v10.16b
	eor v15.16b, v0.16b, v11.16b
	umull v0.2d, v12.2s, v27.2s
	umull2 v1.2d, v12.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v12.16b, v20.16b, v21.16b
	umull v0.2d, v13.2s, v27.2s
	umull2 v1.2d, v13.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v13.16b, v20.16b, v21.16b
	umull v0.2d, v14.2s, v27.2s
	umull2 v1.2d, v14.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v14.16b, v20.16b, v21.16b
	umull v0.2d, v15.2s, v27.2s
	umull2 v1.2d, v15.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v15.16b, v20.16b, v21.16b
	uzp1 v0.16b, v12.16b, v13.16b
	uzp2 v1.16b, v12.16b, v13.16b
	uzp1 v20.16b, v14.16b, v15.16b
	uzp2 v21.16b, v14.16b, v15.16b
	uzp1 v19.16b, v0.16b, v20.16b
	uzp2 v17.16b, v0.16b, v20.16b
	uzp1 v18.16b, v1.16b, v21.16b
	uzp2 v16.16b, v1.16b, v21.16b
	eor v24.16b, v16.16b, v2.16b
	eor v25.16b, v16.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #0]
	ldr q29, [x9, #16]
	ldr q30, [x9, #32]
	ldr q31, [x9, #48]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #64]
	ldr q29, [x9, #80]
	ldr q30, [x9, #96]
	ldr q31, [x9, #112]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #128]
	ldr q29, [x9, #144]
	ldr q30, [x9, #160]
	ldr q31, [x9, #176]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #192]
	ldr q29, [x9, #208]
	ldr q30, [x9, #224]
	ldr q31, [x9, #240]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #256]
	ldr q29, [x9, #272]
	ldr q30, [x9, #288]
	ldr q31, [x9, #304]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #320]
	ldr q29, [x9, #336]
	ldr q30, [x9, #352]
	ldr q31, [x9, #368]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #384]
	ldr q29, [x9, #400]
	ldr q30, [x9, #416]
	ldr q31, [x9, #432]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #448]
	ldr q29, [x9, #464]
	ldr q30, [x9, #480]
	ldr q31, [x9, #496]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #512]
	ldr q29, [x9, #528]
	ldr q30, [x9, #544]
	ldr q31, [x9, #560]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #576]
	ldr q29, [x9, #592]
	ldr q30, [x9, #608]
	ldr q31, [x9, #624]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #640]
	ldr q29, [x9, #656]
	ldr q30, [x9, #672]
	ldr q31, [x9, #688]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #704]
	ldr q29, [x9, #720]
	ldr q30, [x9, #736]
	ldr q31, [x9, #752]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #768]
	ldr q29, [x9, #784]
	ldr q30, [x9, #800]
	ldr q31, [x9, #816]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #832]
	ldr q29, [x9, #848]
	ldr q30, [x9, #864]
	ldr q31, [x9, #880]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #896]
	ldr q29, [x9, #912]
	ldr q30, [x9, #928]
	ldr q31, [x9, #944]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #960]
	ldr q29, [x9, #976]
	ldr q30, [x9, #992]
	ldr q31, [x9, #1008]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	mov v12.16b, v21.16b
	mov v13.16b, v23.16b
	mov v14.16b, v0.16b
	mov v15.16b, v1.16b
	eor v24.16b, v17.16b, v2.16b
	eor v25.16b, v17.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #1024]
	ldr q29, [x9, #1040]
	ldr q30, [x9, #1056]
	ldr q31, [x9, #1072]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1088]
	ldr q29, [x9, #1104]
	ldr q30, [x9, #1120]
	ldr q31, [x9, #1136]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1152]
	ldr q29, [x9, #1168]
	ldr q30, [x9, #1184]
	ldr q31, [x9, #1200]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1216]
	ldr q29, [x9, #1232]
	ldr q30, [x9, #1248]
	ldr q31, [x9, #1264]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1280]
	ldr q29, [x9, #1296]
	ldr q30, [x9, #1312]
	ldr q31, [x9, #1328]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1344]
	ldr q29, [x9, #1360]
	ldr q30, [x9, #1376]
	ldr q31, [x9, #1392]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1408]
	ldr q29, [x9, #1424]
	ldr q30, [x9, #1440]
	ldr q31, [x9, #1456]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1472]
	ldr q29, [x9, #1488]
	ldr q30, [x9, #1504]
	ldr q31, [x9, #1520]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1536]
	ldr q29, [x9, #1552]
	ldr q30, [x9, #1568]
	ldr q31, [x9, #1584]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1600]
	ldr q29, [x9, #1616]
	ldr q30, [x9, #1632]
	ldr q31, [x9, #1648]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1664]
	ldr q29, [x9, #1680]
	ldr q30, [x9, #1696]
	ldr q31, [x9, #1712]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1728]
	ldr q29, [x9, #1744]
	ldr q30, [x9, #1760]
	ldr q31, [x9, #1776]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1792]
	ldr q29, [x9, #1808]
	ldr q30, [x9, #1824]
	ldr q31, [x9, #1840]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1856]
	ldr q29, [x9, #1872]
	ldr q30, [x9, #1888]
	ldr q31, [x9, #1904]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1920]
	ldr q29, [x9, #1936]
	ldr q30, [x9, #1952]
	ldr q31, [x9, #1968]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1984]
	ldr q29, [x9, #2000]
	ldr q30, [x9, #2016]
	ldr q31, [x9, #2032]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	sub v12.4s, v12.4s, v21.4s
	sub v13.4s, v13.4s, v23.4s
	sub v14.4s, v14.4s, v0.4s
	sub v15.4s, v15.4s, v1.4s
	eor v24.16b, v18.16b, v2.16b
	eor v25.16b, v18.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #2048]
	ldr q29, [x9, #2064]
	ldr q30, [x9, #2080]
	ldr q31, [x9, #2096]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2112]
	ldr q29, [x9, #2128]
	ldr q30, [x9, #2144]
	ldr q31, [x9, #2160]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2176]
	ldr q29, [x9, #2192]
	ldr q30, [x9, #2208]
	ldr q31, [x9, #2224]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2240]
	ldr q29, [x9, #2256]
	ldr q30, [x9, #2272]
	ldr q31, [x9, #2288]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2304]
	ldr q29, [x9, #2320]
	ldr q30, [x9, #2336]
	ldr q31, [x9, #2352]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2368]
	ldr q29, [x9, #2384]
	ldr q30, [x9, #2400]
	ldr q31, [x9, #2416]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2432]
	ldr q29, [x9, #2448]
	ldr q30, [x9, #2464]
	ldr q31, [x9, #2480]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2496]
	ldr q29, [x9, #2512]
	ldr q30, [x9, #2528]
	ldr q31, [x9, #2544]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2560]
	ldr q29, [x9, #2576]
	ldr q30, [x9, #2592]
	ldr q31, [x9, #2608]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2624]
	ldr q29, [x9, #2640]
	ldr q30, [x9, #2656]
	ldr q31, [x9, #2672]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2688]
	ldr q29, [x9, #2704]
	ldr q30, [x9, #2720]
	ldr q31, [x9, #2736]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2752]
	ldr q29, [x9, #2768]
	ldr q30, [x9, #2784]
	ldr q31, [x9, #2800]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2816]
	ldr q29, [x9, #2832]
	ldr q30, [x9, #2848]
	ldr q31, [x9, #2864]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2880]
	ldr q29, [x9, #2896]
	ldr q30, [x9, #2912]
	ldr q31, [x9, #2928]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2944]
	ldr q29, [x9, #2960]
	ldr q30, [x9, #2976]
	ldr q31, [x9, #2992]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3008]
	ldr q29, [x9, #3024]
	ldr q30, [x9, #3040]
	ldr q31, [x9, #3056]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	add v12.4s, v12.4s, v21.4s
	add v13.4s, v13.4s, v23.4s
	add v14.4s, v14.4s, v0.4s
	add v15.4s, v15.4s, v1.4s
	eor v24.16b, v19.16b, v2.16b
	eor v25.16b, v19.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #3072]
	ldr q29, [x9, #3088]
	ldr q30, [x9, #3104]
	ldr q31, [x9, #3120]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3136]
	ldr q29, [x9, #3152]
	ldr q30, [x9, #3168]
	ldr q31, [x9, #3184]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3200]
	ldr q29, [x9, #3216]
	ldr q30, [x9, #3232]
	ldr q31, [x9, #3248]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3264]
	ldr q29, [x9, #3280]
	ldr q30, [x9, #3296]
	ldr q31, [x9, #3312]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3328]
	ldr q29, [x9, #3344]
	ldr q30, [x9, #3360]
	ldr q31, [x9, #3376]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3392]
	ldr q29, [x9, #3408]
	ldr q30, [x9, #3424]
	ldr q31, [x9, #3440]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3456]
	ldr q29, [x9, #3472]
	ldr q30, [x9, #3488]
	ldr q31, [x9, #3504]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3520]
	ldr q29, [x9, #3536]
	ldr q30, [x9, #3552]
	ldr q31, [x9, #3568]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3584]
	ldr q29, [x9, #3600]
	ldr q30, [x9, #3616]
	ldr q31, [x9, #3632]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3648]
	ldr q29, [x9, #3664]
	ldr q30, [x9, #3680]
	ldr q31, [x9, #3696]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3712]
	ldr q29, [x9, #3728]
	ldr q30, [x9, #3744]
	ldr q31, [x9, #3760]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3776]
	ldr q29, [x9, #3792]
	ldr q30, [x9, #3808]
	ldr q31, [x9, #3824]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3840]
	ldr q29, [x9, #3856]
	ldr q30, [x9, #3872]
	ldr q31, [x9, #3888]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3904]
	ldr q29, [x9, #3920]
	ldr q30, [x9, #3936]
	ldr q31, [x9, #3952]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3968]
	ldr q29, [x9, #3984]
	ldr q30, [x9, #4000]
	ldr q31, [x9, #4016]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #4032]
	ldr q29, [x9, #4048]
	ldr q30, [x9, #4064]
	ldr q31, [x9, #4080]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	eor v12.16b, v12.16b, v21.16b
	eor v13.16b, v13.16b, v23.16b
	eor v14.16b, v14.16b, v0.16b
	eor v15.16b, v15.16b, v1.16b
	eor v12.16b, v4.16b, v12.16b
	eor v13.16b, v5.16b, v13.16b
	eor v14.16b, v6.16b, v14.16b
	eor v15.16b, v7.16b, v15.16b
	mov v4.16b, v8.16b
	mov v5.16b, v9.16b
	mov v6.16b, v10.16b
	mov v7.16b, v11.16b
	mov v8.16b, v12.16b
	mov v9.16b, v13.16b
	mov v10.16b, v14.16b
	mov v11.16b, v15.16b
	sub x5, x5, #4
	ldr w6, [x5, #0]
	dup v0.4s, w6
	ldr w13, [x5, #64]
	movz w4, #1, lsl #0
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	dup v27.4s, w4
	add v12.4s, v0.4s, v8.4s
	add v13.4s, v0.4s, v9.4s
	add v14.4s, v0.4s, v10.4s
	add v15.4s, v0.4s, v11.4s
	umull v0.2d, v12.2s, v27.2s
	umull2 v1.2d, v12.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v12.16b, v20.16b, v21.16b
	umull v0.2d, v13.2s, v27.2s
	umull2 v1.2d, v13.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v13.16b, v20.16b, v21.16b
	umull v0.2d, v14.2s, v27.2s
	umull2 v1.2d, v14.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v14.16b, v20.16b, v21.16b
	umull v0.2d, v15.2s, v27.2s
	umull2 v1.2d, v15.4s, v27.4s
	uzp1 v20.4s, v0.4s, v1.4s
	uzp2 v21.4s, v0.4s, v1.4s
	orr v15.16b, v20.16b, v21.16b
	uzp1 v0.16b, v12.16b, v13.16b
	uzp2 v1.16b, v12.16b, v13.16b
	uzp1 v20.16b, v14.16b, v15.16b
	uzp2 v21.16b, v14.16b, v15.16b
	uzp1 v19.16b, v0.16b, v20.16b
	uzp2 v17.16b, v0.16b, v20.16b
	uzp1 v18.16b, v1.16b, v21.16b
	uzp2 v16.16b, v1.16b, v21.16b
	eor v24.16b, v16.16b, v2.16b
	eor v25.16b, v16.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #0]
	ldr q29, [x9, #16]
	ldr q30, [x9, #32]
	ldr q31, [x9, #48]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #64]
	ldr q29, [x9, #80]
	ldr q30, [x9, #96]
	ldr q31, [x9, #112]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #128]
	ldr q29, [x9, #144]
	ldr q30, [x9, #160]
	ldr q31, [x9, #176]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #192]
	ldr q29, [x9, #208]
	ldr q30, [x9, #224]
	ldr q31, [x9, #240]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #256]
	ldr q29, [x9, #272]
	ldr q30, [x9, #288]
	ldr q31, [x9, #304]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #320]
	ldr q29, [x9, #336]
	ldr q30, [x9, #352]
	ldr q31, [x9, #368]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #384]
	ldr q29, [x9, #400]
	ldr q30, [x9, #416]
	ldr q31, [x9, #432]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #448]
	ldr q29, [x9, #464]
	ldr q30, [x9, #480]
	ldr q31, [x9, #496]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #512]
	ldr q29, [x9, #528]
	ldr q30, [x9, #544]
	ldr q31, [x9, #560]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #576]
	ldr q29, [x9, #592]
	ldr q30, [x9, #608]
	ldr q31, [x9, #624]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #640]
	ldr q29, [x9, #656]
	ldr q30, [x9, #672]
	ldr q31, [x9, #688]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #704]
	ldr q29, [x9, #720]
	ldr q30, [x9, #736]
	ldr q31, [x9, #752]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #768]
	ldr q29, [x9, #784]
	ldr q30, [x9, #800]
	ldr q31, [x9, #816]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x9, #832]
	ldr q29, [x9, #848]
	ldr q30, [x9, #864]
	ldr q31, [x9, #880]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #896]
	ldr q29, [x9, #912]
	ldr q30, [x9, #928]
	ldr q31, [x9, #944]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #960]
	ldr q29, [x9, #976]
	ldr q30, [x9, #992]
	ldr q31, [x9, #1008]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	mov v12.16b, v21.16b
	mov v13.16b, v23.16b
	mov v14.16b, v0.16b
	mov v15.16b, v1.16b
	eor v24.16b, v17.16b, v2.16b
	eor v25.16b, v17.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #1024]
	ldr q29, [x9, #1040]
	ldr q30, [x9, #1056]
	ldr q31, [x9, #1072]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1088]
	ldr q29, [x9, #1104]
	ldr q30, [x9, #1120]
	ldr q31, [x9, #1136]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1152]
	ldr q29, [x9, #1168]
	ldr q30, [x9, #1184]
	ldr q31, [x9, #1200]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1216]
	ldr q29, [x9, #1232]
	ldr q30, [x9, #1248]
	ldr q31, [x9, #1264]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1280]
	ldr q29, [x9, #1296]
	ldr q30, [x9, #1312]
	ldr q31, [x9, #1328]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1344]
	ldr q29, [x9, #1360]
	ldr q30, [x9, #1376]
	ldr q31, [x9, #1392]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1408]
	ldr q29, [x9, #1424]
	ldr q30, [x9, #1440]
	ldr q31, [x9, #1456]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1472]
	ldr q29, [x9, #1488]
	ldr q30, [x9, #1504]
	ldr q31, [x9, #1520]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1536]
	ldr q29, [x9, #1552]
	ldr q30, [x9, #1568]
	ldr q31, [x9, #1584]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1600]
	ldr q29, [x9, #1616]
	ldr q30, [x9, #1632]
	ldr q31, [x9, #1648]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1664]
	ldr q29, [x9, #1680]
	ldr q30, [x9, #1696]
	ldr q31, [x9, #1712]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1728]
	ldr q29, [x9, #1744]
	ldr q30, [x9, #1760]
	ldr q31, [x9, #1776]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #1792]
	ldr q29, [x9, #1808]
	ldr q30, [x9, #1824]
	ldr q31, [x9, #1840]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x9, #1856]
	ldr q29, [x9, #1872]
	ldr q30, [x9, #1888]
	ldr q31, [x9, #1904]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #1920]
	ldr q29, [x9, #1936]
	ldr q30, [x9, #1952]
	ldr q31, [x9, #1968]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #1984]
	ldr q29, [x9, #2000]
	ldr q30, [x9, #2016]
	ldr q31, [x9, #2032]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	eor v12.16b, v12.16b, v21.16b
	eor v13.16b, v13.16b, v23.16b
	eor v14.16b, v14.16b, v0.16b
	eor v15.16b, v15.16b, v1.16b
	eor v24.16b, v18.16b, v2.16b
	eor v25.16b, v18.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #2048]
	ldr q29, [x9, #2064]
	ldr q30, [x9, #2080]
	ldr q31, [x9, #2096]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2112]
	ldr q29, [x9, #2128]
	ldr q30, [x9, #2144]
	ldr q31, [x9, #2160]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2176]
	ldr q29, [x9, #2192]
	ldr q30, [x9, #2208]
	ldr q31, [x9, #2224]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2240]
	ldr q29, [x9, #2256]
	ldr q30, [x9, #2272]
	ldr q31, [x9, #2288]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2304]
	ldr q29, [x9, #2320]
	ldr q30, [x9, #2336]
	ldr q31, [x9, #2352]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2368]
	ldr q29, [x9, #2384]
	ldr q30, [x9, #2400]
	ldr q31, [x9, #2416]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2432]
	ldr q29, [x9, #2448]
	ldr q30, [x9, #2464]
	ldr q31, [x9, #2480]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2496]
	ldr q29, [x9, #2512]
	ldr q30, [x9, #2528]
	ldr q31, [x9, #2544]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2560]
	ldr q29, [x9, #2576]
	ldr q30, [x9, #2592]
	ldr q31, [x9, #2608]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2624]
	ldr q29, [x9, #2640]
	ldr q30, [x9, #2656]
	ldr q31, [x9, #2672]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2688]
	ldr q29, [x9, #2704]
	ldr q30, [x9, #2720]
	ldr q31, [x9, #2736]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #2752]
	ldr q29, [x9, #2768]
	ldr q30, [x9, #2784]
	ldr q31, [x9, #2800]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #2816]
	ldr q29, [x9, #2832]
	ldr q30, [x9, #2848]
	ldr q31, [x9, #2864]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x9, #2880]
	ldr q29, [x9, #2896]
	ldr q30, [x9, #2912]
	ldr q31, [x9, #2928]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #2944]
	ldr q29, [x9, #2960]
	ldr q30, [x9, #2976]
	ldr q31, [x9, #2992]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3008]
	ldr q29, [x9, #3024]
	ldr q30, [x9, #3040]
	ldr q31, [x9, #3056]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	sub v12.4s, v12.4s, v21.4s
	sub v13.4s, v13.4s, v23.4s
	sub v14.4s, v14.4s, v0.4s
	sub v15.4s, v15.4s, v1.4s
	eor v24.16b, v19.16b, v2.16b
	eor v25.16b, v19.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x9, #3072]
	ldr q29, [x9, #3088]
	ldr q30, [x9, #3104]
	ldr q31, [x9, #3120]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3136]
	ldr q29, [x9, #3152]
	ldr q30, [x9, #3168]
	ldr q31, [x9, #3184]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3200]
	ldr q29, [x9, #3216]
	ldr q30, [x9, #3232]
	ldr q31, [x9, #3248]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3264]
	ldr q29, [x9, #3280]
	ldr q30, [x9, #3296]
	ldr q31, [x9, #3312]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3328]
	ldr q29, [x9, #3344]
	ldr q30, [x9, #3360]
	ldr q31, [x9, #3376]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3392]
	ldr q29, [x9, #3408]
	ldr q30, [x9, #3424]
	ldr q31, [x9, #3440]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3456]
	ldr q29, [x9, #3472]
	ldr q30, [x9, #3488]
	ldr q31, [x9, #3504]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3520]
	ldr q29, [x9, #3536]
	ldr q30, [x9, #3552]
	ldr q31, [x9, #3568]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3584]
	ldr q29, [x9, #3600]
	ldr q30, [x9, #3616]
	ldr q31, [x9, #3632]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3648]
	ldr q29, [x9, #3664]
	ldr q30, [x9, #3680]
	ldr q31, [x9, #3696]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3712]
	ldr q29, [x9, #3728]
	ldr q30, [x9, #3744]
	ldr q31, [x9, #3760]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #3776]
	ldr q29, [x9, #3792]
	ldr q30, [x9, #3808]
	ldr q31, [x9, #3824]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x9, #3840]
	ldr q29, [x9, #3856]
	ldr q30, [x9, #3872]
	ldr q31, [x9, #3888]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x9, #3904]
	ldr q29, [x9, #3920]
	ldr q30, [x9, #3936]
	ldr q31, [x9, #3952]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x9, #3968]
	ldr q29, [x9, #3984]
	ldr q30, [x9, #4000]
	ldr q31, [x9, #4016]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x9, #4032]
	ldr q29, [x9, #4048]
	ldr q30, [x9, #4064]
	ldr q31, [x9, #4080]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	zip1 v0.16b, v20.16b, v22.16b
	zip2 v1.16b, v20.16b, v22.16b
	zip1 v20.16b, v21.16b, v23.16b
	zip2 v22.16b, v21.16b, v23.16b
	zip1 v21.16b, v0.16b, v20.16b
	zip2 v23.16b, v0.16b, v20.16b
	zip1 v0.16b, v1.16b, v22.16b
	zip2 v1.16b, v1.16b, v22.16b
	add v12.4s, v12.4s, v21.4s
	add v13.4s, v13.4s, v23.4s
	add v14.4s, v14.4s, v0.4s
	add v15.4s, v15.4s, v1.4s
	eor v12.16b, v4.16b, v12.16b
	eor v13.16b, v5.16b, v13.16b
	eor v14.16b, v6.16b, v14.16b
	eor v15.16b, v7.16b, v15.16b
	mov v4.16b, v8.16b
	mov v5.16b, v9.16b
	mov v6.16b, v10.16b
	mov v7.16b, v11.16b
	mov v8.16b, v12.16b
	mov v9.16b, v13.16b
	mov v10.16b, v14.16b
	mov v11.16b, v15.16b
	sub x5, x5, #4
	sub x7, x7, #1
	cbnz x7, 22b
	add x4, x17, #0
	zip1 v20.4s, v8.4s, v4.4s
	zip2 v21.4s, v8.4s, v4.4s
	rev32 v20.16b, v20.16b
	rev32 v21.16b, v21.16b
	str q20, [x4, #0]
	str q21, [x4, #16]
	zip1 v20.4s, v9.4s, v5.4s
	zip2 v21.4s, v9.4s, v5.4s
	rev32 v20.16b, v20.16b
	rev32 v21.16b, v21.16b
	str q20, [x4, #32]
	str q21, [x4, #48]
	zip1 v20.4s, v10.4s, v6.4s
	zip2 v21.4s, v10.4s, v6.4s
	rev32 v20.16b, v20.16b
	rev32 v21.16b, v21.16b
	str q20, [x4, #64]
	str q21, [x4, #80]
	zip1 v20.4s, v11.4s, v7.4s
	zip2 v21.4s, v11.4s, v7.4s
	rev32 v20.16b, v20.16b
	rev32 v21.16b, v21.16b
	str q20, [x4, #96]
	str q21, [x4, #112]
	ret
	.p2align 6
