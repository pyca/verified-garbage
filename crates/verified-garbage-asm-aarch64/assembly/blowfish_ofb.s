// The functions of `src/blowfish_ofb.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_ofb:
	sub sp, sp, #224
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #128]
	str x20, [x5, #136]
	str x21, [x5, #144]
	str x22, [x5, #152]
	str x23, [x5, #160]
	str x24, [x5, #168]
	str x25, [x5, #176]
	str x26, [x5, #184]
	str x27, [x5, #192]
	str x28, [x5, #200]
	add x25, x1, #0
	add x23, x2, #0
	add x24, x3, #0
	ldr x6, [x25, #0]
	str x6, [x5, #0]
	cbz x24, 20f
22:
	umov x8, v8.d[0]
	umov x9, v9.d[0]
	umov x10, v10.d[0]
	umov x11, v11.d[0]
	umov x12, v12.d[0]
	umov x13, v13.d[0]
	umov x14, v14.d[0]
	umov x15, v15.d[0]
	add x16, x5, #0
	add x4, x5, #0
	movz x6, #64, lsl #0
	dup v2.16b, w6
	movz x6, #128, lsl #0
	dup v3.16b, w6
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
	add x5, x0, #0
	movz x7, #8, lsl #0
23:
	ldr w6, [x5, #4096]
	dup v0.4s, w6
	eor v4.16b, v4.16b, v0.16b
	eor v5.16b, v5.16b, v0.16b
	eor v6.16b, v6.16b, v0.16b
	eor v7.16b, v7.16b, v0.16b
	uzp1 v0.16b, v4.16b, v5.16b
	uzp2 v1.16b, v4.16b, v5.16b
	uzp1 v20.16b, v6.16b, v7.16b
	uzp2 v21.16b, v6.16b, v7.16b
	uzp1 v19.16b, v0.16b, v20.16b
	uzp2 v17.16b, v0.16b, v20.16b
	uzp1 v18.16b, v1.16b, v21.16b
	uzp2 v16.16b, v1.16b, v21.16b
	eor v24.16b, v16.16b, v2.16b
	eor v25.16b, v16.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x0, #0]
	ldr q29, [x0, #16]
	ldr q30, [x0, #32]
	ldr q31, [x0, #48]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x0, #64]
	ldr q29, [x0, #80]
	ldr q30, [x0, #96]
	ldr q31, [x0, #112]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #128]
	ldr q29, [x0, #144]
	ldr q30, [x0, #160]
	ldr q31, [x0, #176]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #192]
	ldr q29, [x0, #208]
	ldr q30, [x0, #224]
	ldr q31, [x0, #240]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #256]
	ldr q29, [x0, #272]
	ldr q30, [x0, #288]
	ldr q31, [x0, #304]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x0, #320]
	ldr q29, [x0, #336]
	ldr q30, [x0, #352]
	ldr q31, [x0, #368]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #384]
	ldr q29, [x0, #400]
	ldr q30, [x0, #416]
	ldr q31, [x0, #432]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #448]
	ldr q29, [x0, #464]
	ldr q30, [x0, #480]
	ldr q31, [x0, #496]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #512]
	ldr q29, [x0, #528]
	ldr q30, [x0, #544]
	ldr q31, [x0, #560]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x0, #576]
	ldr q29, [x0, #592]
	ldr q30, [x0, #608]
	ldr q31, [x0, #624]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #640]
	ldr q29, [x0, #656]
	ldr q30, [x0, #672]
	ldr q31, [x0, #688]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #704]
	ldr q29, [x0, #720]
	ldr q30, [x0, #736]
	ldr q31, [x0, #752]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #768]
	ldr q29, [x0, #784]
	ldr q30, [x0, #800]
	ldr q31, [x0, #816]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x0, #832]
	ldr q29, [x0, #848]
	ldr q30, [x0, #864]
	ldr q31, [x0, #880]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #896]
	ldr q29, [x0, #912]
	ldr q30, [x0, #928]
	ldr q31, [x0, #944]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #960]
	ldr q29, [x0, #976]
	ldr q30, [x0, #992]
	ldr q31, [x0, #1008]
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
	ldr q28, [x0, #1024]
	ldr q29, [x0, #1040]
	ldr q30, [x0, #1056]
	ldr q31, [x0, #1072]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x0, #1088]
	ldr q29, [x0, #1104]
	ldr q30, [x0, #1120]
	ldr q31, [x0, #1136]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #1152]
	ldr q29, [x0, #1168]
	ldr q30, [x0, #1184]
	ldr q31, [x0, #1200]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #1216]
	ldr q29, [x0, #1232]
	ldr q30, [x0, #1248]
	ldr q31, [x0, #1264]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #1280]
	ldr q29, [x0, #1296]
	ldr q30, [x0, #1312]
	ldr q31, [x0, #1328]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x0, #1344]
	ldr q29, [x0, #1360]
	ldr q30, [x0, #1376]
	ldr q31, [x0, #1392]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #1408]
	ldr q29, [x0, #1424]
	ldr q30, [x0, #1440]
	ldr q31, [x0, #1456]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #1472]
	ldr q29, [x0, #1488]
	ldr q30, [x0, #1504]
	ldr q31, [x0, #1520]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #1536]
	ldr q29, [x0, #1552]
	ldr q30, [x0, #1568]
	ldr q31, [x0, #1584]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x0, #1600]
	ldr q29, [x0, #1616]
	ldr q30, [x0, #1632]
	ldr q31, [x0, #1648]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #1664]
	ldr q29, [x0, #1680]
	ldr q30, [x0, #1696]
	ldr q31, [x0, #1712]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #1728]
	ldr q29, [x0, #1744]
	ldr q30, [x0, #1760]
	ldr q31, [x0, #1776]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #1792]
	ldr q29, [x0, #1808]
	ldr q30, [x0, #1824]
	ldr q31, [x0, #1840]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x0, #1856]
	ldr q29, [x0, #1872]
	ldr q30, [x0, #1888]
	ldr q31, [x0, #1904]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #1920]
	ldr q29, [x0, #1936]
	ldr q30, [x0, #1952]
	ldr q31, [x0, #1968]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #1984]
	ldr q29, [x0, #2000]
	ldr q30, [x0, #2016]
	ldr q31, [x0, #2032]
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
	ldr q28, [x0, #2048]
	ldr q29, [x0, #2064]
	ldr q30, [x0, #2080]
	ldr q31, [x0, #2096]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x0, #2112]
	ldr q29, [x0, #2128]
	ldr q30, [x0, #2144]
	ldr q31, [x0, #2160]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #2176]
	ldr q29, [x0, #2192]
	ldr q30, [x0, #2208]
	ldr q31, [x0, #2224]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #2240]
	ldr q29, [x0, #2256]
	ldr q30, [x0, #2272]
	ldr q31, [x0, #2288]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #2304]
	ldr q29, [x0, #2320]
	ldr q30, [x0, #2336]
	ldr q31, [x0, #2352]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x0, #2368]
	ldr q29, [x0, #2384]
	ldr q30, [x0, #2400]
	ldr q31, [x0, #2416]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #2432]
	ldr q29, [x0, #2448]
	ldr q30, [x0, #2464]
	ldr q31, [x0, #2480]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #2496]
	ldr q29, [x0, #2512]
	ldr q30, [x0, #2528]
	ldr q31, [x0, #2544]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #2560]
	ldr q29, [x0, #2576]
	ldr q30, [x0, #2592]
	ldr q31, [x0, #2608]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x0, #2624]
	ldr q29, [x0, #2640]
	ldr q30, [x0, #2656]
	ldr q31, [x0, #2672]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #2688]
	ldr q29, [x0, #2704]
	ldr q30, [x0, #2720]
	ldr q31, [x0, #2736]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #2752]
	ldr q29, [x0, #2768]
	ldr q30, [x0, #2784]
	ldr q31, [x0, #2800]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #2816]
	ldr q29, [x0, #2832]
	ldr q30, [x0, #2848]
	ldr q31, [x0, #2864]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x0, #2880]
	ldr q29, [x0, #2896]
	ldr q30, [x0, #2912]
	ldr q31, [x0, #2928]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #2944]
	ldr q29, [x0, #2960]
	ldr q30, [x0, #2976]
	ldr q31, [x0, #2992]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #3008]
	ldr q29, [x0, #3024]
	ldr q30, [x0, #3040]
	ldr q31, [x0, #3056]
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
	ldr q28, [x0, #3072]
	ldr q29, [x0, #3088]
	ldr q30, [x0, #3104]
	ldr q31, [x0, #3120]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x0, #3136]
	ldr q29, [x0, #3152]
	ldr q30, [x0, #3168]
	ldr q31, [x0, #3184]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #3200]
	ldr q29, [x0, #3216]
	ldr q30, [x0, #3232]
	ldr q31, [x0, #3248]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #3264]
	ldr q29, [x0, #3280]
	ldr q30, [x0, #3296]
	ldr q31, [x0, #3312]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #3328]
	ldr q29, [x0, #3344]
	ldr q30, [x0, #3360]
	ldr q31, [x0, #3376]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x0, #3392]
	ldr q29, [x0, #3408]
	ldr q30, [x0, #3424]
	ldr q31, [x0, #3440]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #3456]
	ldr q29, [x0, #3472]
	ldr q30, [x0, #3488]
	ldr q31, [x0, #3504]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #3520]
	ldr q29, [x0, #3536]
	ldr q30, [x0, #3552]
	ldr q31, [x0, #3568]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #3584]
	ldr q29, [x0, #3600]
	ldr q30, [x0, #3616]
	ldr q31, [x0, #3632]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x0, #3648]
	ldr q29, [x0, #3664]
	ldr q30, [x0, #3680]
	ldr q31, [x0, #3696]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #3712]
	ldr q29, [x0, #3728]
	ldr q30, [x0, #3744]
	ldr q31, [x0, #3760]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #3776]
	ldr q29, [x0, #3792]
	ldr q30, [x0, #3808]
	ldr q31, [x0, #3824]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #3840]
	ldr q29, [x0, #3856]
	ldr q30, [x0, #3872]
	ldr q31, [x0, #3888]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x0, #3904]
	ldr q29, [x0, #3920]
	ldr q30, [x0, #3936]
	ldr q31, [x0, #3952]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #3968]
	ldr q29, [x0, #3984]
	ldr q30, [x0, #4000]
	ldr q31, [x0, #4016]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #4032]
	ldr q29, [x0, #4048]
	ldr q30, [x0, #4064]
	ldr q31, [x0, #4080]
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
	eor v8.16b, v8.16b, v12.16b
	eor v9.16b, v9.16b, v13.16b
	eor v10.16b, v10.16b, v14.16b
	eor v11.16b, v11.16b, v15.16b
	add x5, x5, #4
	ldr w6, [x5, #4096]
	dup v0.4s, w6
	eor v8.16b, v8.16b, v0.16b
	eor v9.16b, v9.16b, v0.16b
	eor v10.16b, v10.16b, v0.16b
	eor v11.16b, v11.16b, v0.16b
	uzp1 v0.16b, v8.16b, v9.16b
	uzp2 v1.16b, v8.16b, v9.16b
	uzp1 v20.16b, v10.16b, v11.16b
	uzp2 v21.16b, v10.16b, v11.16b
	uzp1 v19.16b, v0.16b, v20.16b
	uzp2 v17.16b, v0.16b, v20.16b
	uzp1 v18.16b, v1.16b, v21.16b
	uzp2 v16.16b, v1.16b, v21.16b
	eor v24.16b, v16.16b, v2.16b
	eor v25.16b, v16.16b, v3.16b
	eor v26.16b, v24.16b, v3.16b
	ldr q28, [x0, #0]
	ldr q29, [x0, #16]
	ldr q30, [x0, #32]
	ldr q31, [x0, #48]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x0, #64]
	ldr q29, [x0, #80]
	ldr q30, [x0, #96]
	ldr q31, [x0, #112]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #128]
	ldr q29, [x0, #144]
	ldr q30, [x0, #160]
	ldr q31, [x0, #176]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #192]
	ldr q29, [x0, #208]
	ldr q30, [x0, #224]
	ldr q31, [x0, #240]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #256]
	ldr q29, [x0, #272]
	ldr q30, [x0, #288]
	ldr q31, [x0, #304]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x0, #320]
	ldr q29, [x0, #336]
	ldr q30, [x0, #352]
	ldr q31, [x0, #368]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #384]
	ldr q29, [x0, #400]
	ldr q30, [x0, #416]
	ldr q31, [x0, #432]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #448]
	ldr q29, [x0, #464]
	ldr q30, [x0, #480]
	ldr q31, [x0, #496]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #512]
	ldr q29, [x0, #528]
	ldr q30, [x0, #544]
	ldr q31, [x0, #560]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x0, #576]
	ldr q29, [x0, #592]
	ldr q30, [x0, #608]
	ldr q31, [x0, #624]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #640]
	ldr q29, [x0, #656]
	ldr q30, [x0, #672]
	ldr q31, [x0, #688]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #704]
	ldr q29, [x0, #720]
	ldr q30, [x0, #736]
	ldr q31, [x0, #752]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #768]
	ldr q29, [x0, #784]
	ldr q30, [x0, #800]
	ldr q31, [x0, #816]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v16.16b
	ldr q28, [x0, #832]
	ldr q29, [x0, #848]
	ldr q30, [x0, #864]
	ldr q31, [x0, #880]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #896]
	ldr q29, [x0, #912]
	ldr q30, [x0, #928]
	ldr q31, [x0, #944]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #960]
	ldr q29, [x0, #976]
	ldr q30, [x0, #992]
	ldr q31, [x0, #1008]
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
	ldr q28, [x0, #1024]
	ldr q29, [x0, #1040]
	ldr q30, [x0, #1056]
	ldr q31, [x0, #1072]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x0, #1088]
	ldr q29, [x0, #1104]
	ldr q30, [x0, #1120]
	ldr q31, [x0, #1136]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #1152]
	ldr q29, [x0, #1168]
	ldr q30, [x0, #1184]
	ldr q31, [x0, #1200]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #1216]
	ldr q29, [x0, #1232]
	ldr q30, [x0, #1248]
	ldr q31, [x0, #1264]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #1280]
	ldr q29, [x0, #1296]
	ldr q30, [x0, #1312]
	ldr q31, [x0, #1328]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x0, #1344]
	ldr q29, [x0, #1360]
	ldr q30, [x0, #1376]
	ldr q31, [x0, #1392]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #1408]
	ldr q29, [x0, #1424]
	ldr q30, [x0, #1440]
	ldr q31, [x0, #1456]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #1472]
	ldr q29, [x0, #1488]
	ldr q30, [x0, #1504]
	ldr q31, [x0, #1520]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #1536]
	ldr q29, [x0, #1552]
	ldr q30, [x0, #1568]
	ldr q31, [x0, #1584]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x0, #1600]
	ldr q29, [x0, #1616]
	ldr q30, [x0, #1632]
	ldr q31, [x0, #1648]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #1664]
	ldr q29, [x0, #1680]
	ldr q30, [x0, #1696]
	ldr q31, [x0, #1712]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #1728]
	ldr q29, [x0, #1744]
	ldr q30, [x0, #1760]
	ldr q31, [x0, #1776]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #1792]
	ldr q29, [x0, #1808]
	ldr q30, [x0, #1824]
	ldr q31, [x0, #1840]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v17.16b
	ldr q28, [x0, #1856]
	ldr q29, [x0, #1872]
	ldr q30, [x0, #1888]
	ldr q31, [x0, #1904]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #1920]
	ldr q29, [x0, #1936]
	ldr q30, [x0, #1952]
	ldr q31, [x0, #1968]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #1984]
	ldr q29, [x0, #2000]
	ldr q30, [x0, #2016]
	ldr q31, [x0, #2032]
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
	ldr q28, [x0, #2048]
	ldr q29, [x0, #2064]
	ldr q30, [x0, #2080]
	ldr q31, [x0, #2096]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x0, #2112]
	ldr q29, [x0, #2128]
	ldr q30, [x0, #2144]
	ldr q31, [x0, #2160]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #2176]
	ldr q29, [x0, #2192]
	ldr q30, [x0, #2208]
	ldr q31, [x0, #2224]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #2240]
	ldr q29, [x0, #2256]
	ldr q30, [x0, #2272]
	ldr q31, [x0, #2288]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #2304]
	ldr q29, [x0, #2320]
	ldr q30, [x0, #2336]
	ldr q31, [x0, #2352]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x0, #2368]
	ldr q29, [x0, #2384]
	ldr q30, [x0, #2400]
	ldr q31, [x0, #2416]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #2432]
	ldr q29, [x0, #2448]
	ldr q30, [x0, #2464]
	ldr q31, [x0, #2480]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #2496]
	ldr q29, [x0, #2512]
	ldr q30, [x0, #2528]
	ldr q31, [x0, #2544]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #2560]
	ldr q29, [x0, #2576]
	ldr q30, [x0, #2592]
	ldr q31, [x0, #2608]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x0, #2624]
	ldr q29, [x0, #2640]
	ldr q30, [x0, #2656]
	ldr q31, [x0, #2672]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #2688]
	ldr q29, [x0, #2704]
	ldr q30, [x0, #2720]
	ldr q31, [x0, #2736]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #2752]
	ldr q29, [x0, #2768]
	ldr q30, [x0, #2784]
	ldr q31, [x0, #2800]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #2816]
	ldr q29, [x0, #2832]
	ldr q30, [x0, #2848]
	ldr q31, [x0, #2864]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v18.16b
	ldr q28, [x0, #2880]
	ldr q29, [x0, #2896]
	ldr q30, [x0, #2912]
	ldr q31, [x0, #2928]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #2944]
	ldr q29, [x0, #2960]
	ldr q30, [x0, #2976]
	ldr q31, [x0, #2992]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #3008]
	ldr q29, [x0, #3024]
	ldr q30, [x0, #3040]
	ldr q31, [x0, #3056]
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
	ldr q28, [x0, #3072]
	ldr q29, [x0, #3088]
	ldr q30, [x0, #3104]
	ldr q31, [x0, #3120]
	tbl v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x0, #3136]
	ldr q29, [x0, #3152]
	ldr q30, [x0, #3168]
	ldr q31, [x0, #3184]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #3200]
	ldr q29, [x0, #3216]
	ldr q30, [x0, #3232]
	ldr q31, [x0, #3248]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #3264]
	ldr q29, [x0, #3280]
	ldr q30, [x0, #3296]
	ldr q31, [x0, #3312]
	tbx v20.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #3328]
	ldr q29, [x0, #3344]
	ldr q30, [x0, #3360]
	ldr q31, [x0, #3376]
	tbl v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x0, #3392]
	ldr q29, [x0, #3408]
	ldr q30, [x0, #3424]
	ldr q31, [x0, #3440]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #3456]
	ldr q29, [x0, #3472]
	ldr q30, [x0, #3488]
	ldr q31, [x0, #3504]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #3520]
	ldr q29, [x0, #3536]
	ldr q30, [x0, #3552]
	ldr q31, [x0, #3568]
	tbx v21.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #3584]
	ldr q29, [x0, #3600]
	ldr q30, [x0, #3616]
	ldr q31, [x0, #3632]
	tbl v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x0, #3648]
	ldr q29, [x0, #3664]
	ldr q30, [x0, #3680]
	ldr q31, [x0, #3696]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #3712]
	ldr q29, [x0, #3728]
	ldr q30, [x0, #3744]
	ldr q31, [x0, #3760]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #3776]
	ldr q29, [x0, #3792]
	ldr q30, [x0, #3808]
	ldr q31, [x0, #3824]
	tbx v22.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v26.16b
	ldr q28, [x0, #3840]
	ldr q29, [x0, #3856]
	ldr q30, [x0, #3872]
	ldr q31, [x0, #3888]
	tbl v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v19.16b
	ldr q28, [x0, #3904]
	ldr q29, [x0, #3920]
	ldr q30, [x0, #3936]
	ldr q31, [x0, #3952]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v24.16b
	ldr q28, [x0, #3968]
	ldr q29, [x0, #3984]
	ldr q30, [x0, #4000]
	ldr q31, [x0, #4016]
	tbx v23.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v25.16b
	ldr q28, [x0, #4032]
	ldr q29, [x0, #4048]
	ldr q30, [x0, #4064]
	ldr q31, [x0, #4080]
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
	eor v4.16b, v4.16b, v12.16b
	eor v5.16b, v5.16b, v13.16b
	eor v6.16b, v6.16b, v14.16b
	eor v7.16b, v7.16b, v15.16b
	add x5, x5, #4
	sub x7, x7, #1
	cbnz x7, 23b
	ldr w6, [x0, #4160]
	dup v0.4s, w6
	eor v4.16b, v4.16b, v0.16b
	eor v5.16b, v5.16b, v0.16b
	eor v6.16b, v6.16b, v0.16b
	eor v7.16b, v7.16b, v0.16b
	ldr w6, [x0, #4164]
	dup v0.4s, w6
	eor v8.16b, v8.16b, v0.16b
	eor v9.16b, v9.16b, v0.16b
	eor v10.16b, v10.16b, v0.16b
	eor v11.16b, v11.16b, v0.16b
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
	dup v8.2d, x8
	dup v9.2d, x9
	dup v10.2d, x10
	dup v11.2d, x11
	dup v12.2d, x12
	dup v13.2d, x13
	dup v14.2d, x14
	dup v15.2d, x15
	add x5, x16, #0
	ldr x6, [x23, #0]
	ldr x7, [x5, #0]
	eor x6, x6, x7
	str x6, [x23, #0]
	add x23, x23, #8
	sub x24, x24, #1
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x6, [x5, #0]
	str x6, [x25, #0]
	ldr x19, [x5, #128]
	ldr x20, [x5, #136]
	ldr x21, [x5, #144]
	ldr x22, [x5, #152]
	ldr x23, [x5, #160]
	ldr x24, [x5, #168]
	ldr x25, [x5, #176]
	ldr x26, [x5, #184]
	ldr x27, [x5, #192]
	ldr x28, [x5, #200]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	add sp, sp, #224
	ret
	.p2align 6
