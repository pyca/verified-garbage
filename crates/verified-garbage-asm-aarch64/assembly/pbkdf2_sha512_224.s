// The functions of `src/pbkdf2_sha512_224.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha512_224_sha512:
	sub sp, sp, #3408
	add x7, sp, #0
	add x10, x4, #0
	add x4, x7, #0
	str x19, [x4, #1872]
	str x20, [x4, #1880]
	str x21, [x4, #1888]
	str x22, [x4, #1896]
	str x24, [x4, #1904]
	str x30, [x4, #1912]
	str x23, [x4, #1920]
	add x23, x4, #0
	str x5, [x23, #1928]
	sub w9, w10, #1
	str x9, [x23, #1936]
	str x6, [x23, #1944]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	lsr x9, x20, #7
	cbz x9, 20f
	sub x9, x20, #128
	cbz x9, 22f
	add x0, x23, #2528
	bl {vg_sha512_224_init}
	add x0, x23, #2528
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha512_update_scratch_sha512}
	add x0, x23, #2528
	add x1, x20, #0
	add x2, x23, #2776
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch_sha512}
	add x2, x23, #2776
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
	add x0, x23, #1952
	add x1, x23, #2144
	add x4, x23, #0
	bl {vg_hmac_sha512_224_init_scratch_sha512}
	ldr w9, [x23, #1952]
	str w9, [x23, #2336]
	ldr w9, [x23, #1956]
	str w9, [x23, #2340]
	ldr w9, [x23, #1960]
	str w9, [x23, #2344]
	ldr w9, [x23, #1964]
	str w9, [x23, #2348]
	ldr w9, [x23, #1968]
	str w9, [x23, #2352]
	ldr w9, [x23, #1972]
	str w9, [x23, #2356]
	ldr w9, [x23, #1976]
	str w9, [x23, #2360]
	ldr w9, [x23, #1980]
	str w9, [x23, #2364]
	ldr w9, [x23, #1984]
	str w9, [x23, #2368]
	ldr w9, [x23, #1988]
	str w9, [x23, #2372]
	ldr w9, [x23, #1992]
	str w9, [x23, #2376]
	ldr w9, [x23, #1996]
	str w9, [x23, #2380]
	ldr w9, [x23, #2000]
	str w9, [x23, #2384]
	ldr w9, [x23, #2004]
	str w9, [x23, #2388]
	ldr w9, [x23, #2008]
	str w9, [x23, #2392]
	ldr w9, [x23, #2012]
	str w9, [x23, #2396]
	ldr w9, [x23, #2016]
	str w9, [x23, #2400]
	ldr w9, [x23, #2020]
	str w9, [x23, #2404]
	ldr w9, [x23, #2024]
	str w9, [x23, #2408]
	ldr w9, [x23, #2028]
	str w9, [x23, #2412]
	ldr w9, [x23, #2032]
	str w9, [x23, #2416]
	ldr w9, [x23, #2036]
	str w9, [x23, #2420]
	ldr w9, [x23, #2040]
	str w9, [x23, #2424]
	ldr w9, [x23, #2044]
	str w9, [x23, #2428]
	ldr w9, [x23, #2048]
	str w9, [x23, #2432]
	ldr w9, [x23, #2052]
	str w9, [x23, #2436]
	ldr w9, [x23, #2056]
	str w9, [x23, #2440]
	ldr w9, [x23, #2060]
	str w9, [x23, #2444]
	ldr w9, [x23, #2064]
	str w9, [x23, #2448]
	ldr w9, [x23, #2068]
	str w9, [x23, #2452]
	ldr w9, [x23, #2072]
	str w9, [x23, #2456]
	ldr w9, [x23, #2076]
	str w9, [x23, #2460]
	ldr w9, [x23, #2080]
	str w9, [x23, #2464]
	ldr w9, [x23, #2084]
	str w9, [x23, #2468]
	ldr w9, [x23, #2088]
	str w9, [x23, #2472]
	ldr w9, [x23, #2092]
	str w9, [x23, #2476]
	ldr w9, [x23, #2096]
	str w9, [x23, #2480]
	ldr w9, [x23, #2100]
	str w9, [x23, #2484]
	ldr w9, [x23, #2104]
	str w9, [x23, #2488]
	ldr w9, [x23, #2108]
	str w9, [x23, #2492]
	ldr w9, [x23, #2112]
	str w9, [x23, #2496]
	ldr w9, [x23, #2116]
	str w9, [x23, #2500]
	ldr w9, [x23, #2120]
	str w9, [x23, #2504]
	ldr w9, [x23, #2124]
	str w9, [x23, #2508]
	ldr w9, [x23, #2128]
	str w9, [x23, #2512]
	ldr w9, [x23, #2132]
	str w9, [x23, #2516]
	ldr w9, [x23, #2136]
	str w9, [x23, #2520]
	ldr w9, [x23, #2140]
	str w9, [x23, #2524]
	add x0, x23, #2336
	movz x1, #128, lsl #0
	add x2, x21, #0
	add x3, x22, #0
	add x4, x23, #0
	bl {vg_sha512_update_scratch_sha512}
	add x20, x22, #0
	ldr x22, [x23, #1928]
	ldr x21, [x23, #1944]
	movz x19, #1, lsl #0
	cbz x21, 24f
26:
	ldr w9, [x23, #2336]
	str w9, [x23, #2528]
	ldr w9, [x23, #2340]
	str w9, [x23, #2532]
	ldr w9, [x23, #2344]
	str w9, [x23, #2536]
	ldr w9, [x23, #2348]
	str w9, [x23, #2540]
	ldr w9, [x23, #2352]
	str w9, [x23, #2544]
	ldr w9, [x23, #2356]
	str w9, [x23, #2548]
	ldr w9, [x23, #2360]
	str w9, [x23, #2552]
	ldr w9, [x23, #2364]
	str w9, [x23, #2556]
	ldr w9, [x23, #2368]
	str w9, [x23, #2560]
	ldr w9, [x23, #2372]
	str w9, [x23, #2564]
	ldr w9, [x23, #2376]
	str w9, [x23, #2568]
	ldr w9, [x23, #2380]
	str w9, [x23, #2572]
	ldr w9, [x23, #2384]
	str w9, [x23, #2576]
	ldr w9, [x23, #2388]
	str w9, [x23, #2580]
	ldr w9, [x23, #2392]
	str w9, [x23, #2584]
	ldr w9, [x23, #2396]
	str w9, [x23, #2588]
	ldr w9, [x23, #2400]
	str w9, [x23, #2592]
	ldr w9, [x23, #2404]
	str w9, [x23, #2596]
	ldr w9, [x23, #2408]
	str w9, [x23, #2600]
	ldr w9, [x23, #2412]
	str w9, [x23, #2604]
	ldr w9, [x23, #2416]
	str w9, [x23, #2608]
	ldr w9, [x23, #2420]
	str w9, [x23, #2612]
	ldr w9, [x23, #2424]
	str w9, [x23, #2616]
	ldr w9, [x23, #2428]
	str w9, [x23, #2620]
	ldr w9, [x23, #2432]
	str w9, [x23, #2624]
	ldr w9, [x23, #2436]
	str w9, [x23, #2628]
	ldr w9, [x23, #2440]
	str w9, [x23, #2632]
	ldr w9, [x23, #2444]
	str w9, [x23, #2636]
	ldr w9, [x23, #2448]
	str w9, [x23, #2640]
	ldr w9, [x23, #2452]
	str w9, [x23, #2644]
	ldr w9, [x23, #2456]
	str w9, [x23, #2648]
	ldr w9, [x23, #2460]
	str w9, [x23, #2652]
	ldr w9, [x23, #2464]
	str w9, [x23, #2656]
	ldr w9, [x23, #2468]
	str w9, [x23, #2660]
	ldr w9, [x23, #2472]
	str w9, [x23, #2664]
	ldr w9, [x23, #2476]
	str w9, [x23, #2668]
	ldr w9, [x23, #2480]
	str w9, [x23, #2672]
	ldr w9, [x23, #2484]
	str w9, [x23, #2676]
	ldr w9, [x23, #2488]
	str w9, [x23, #2680]
	ldr w9, [x23, #2492]
	str w9, [x23, #2684]
	ldr w9, [x23, #2496]
	str w9, [x23, #2688]
	ldr w9, [x23, #2500]
	str w9, [x23, #2692]
	ldr w9, [x23, #2504]
	str w9, [x23, #2696]
	ldr w9, [x23, #2508]
	str w9, [x23, #2700]
	ldr w9, [x23, #2512]
	str w9, [x23, #2704]
	ldr w9, [x23, #2516]
	str w9, [x23, #2708]
	ldr w9, [x23, #2520]
	str w9, [x23, #2712]
	ldr w9, [x23, #2524]
	str w9, [x23, #2716]
	rev w9, w19
	str w9, [x23, #2840]
	add x0, x23, #2528
	add x1, x20, #128
	add x2, x23, #2840
	movz x3, #4, lsl #0
	add x4, x23, #0
	bl {vg_sha512_update_scratch_sha512}
	add x0, x23, #2528
	add x1, x23, #2144
	add x2, x20, #132
	add x3, x23, #2720
	add x4, x23, #0
	bl {vg_hmac_sha512_224_finalize_scratch_sha512}
	ldr w9, [x23, #2720]
	str w9, [x23, #2748]
	ldr w9, [x23, #2724]
	str w9, [x23, #2752]
	ldr w9, [x23, #2728]
	str w9, [x23, #2756]
	ldr w9, [x23, #2732]
	str w9, [x23, #2760]
	ldr w9, [x23, #2736]
	str w9, [x23, #2764]
	ldr w9, [x23, #2740]
	str w9, [x23, #2768]
	ldr w9, [x23, #2744]
	str w9, [x23, #2772]
	add x0, x23, #1952
	add x1, x23, #2720
	ldr x2, [x23, #1936]
	add x3, x23, #2748
	add x4, x23, #0
	bl {vg_pbkdf2_hmac_sha512_224_iterate_sha512}
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
	ldrb w9, [x12, #2748]
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
	ldr x19, [x23, #1872]
	ldr x20, [x23, #1880]
	ldr x21, [x23, #1888]
	ldr x22, [x23, #1896]
	ldr x24, [x23, #1904]
	ldr x30, [x23, #1912]
	ldr x23, [x23, #1920]
	add sp, sp, #3408
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
	sub sp, sp, #3424
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
	add sp, sp, #3424
	ret
	.p2align 6

vg_pbkdf2_hmac_sha512_224:
	sub sp, sp, #3408
	add x7, sp, #0
	add x10, x4, #0
	add x4, x7, #0
	str x19, [x4, #1872]
	str x20, [x4, #1880]
	str x21, [x4, #1888]
	str x22, [x4, #1896]
	str x24, [x4, #1904]
	str x30, [x4, #1912]
	str x23, [x4, #1920]
	add x23, x4, #0
	str x5, [x23, #1928]
	sub w9, w10, #1
	str x9, [x23, #1936]
	str x6, [x23, #1944]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	lsr x9, x20, #7
	cbz x9, 20f
	sub x9, x20, #128
	cbz x9, 22f
	add x0, x23, #2528
	bl {vg_sha512_224_init}
	add x0, x23, #2528
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha512_update_scratch}
	add x0, x23, #2528
	add x1, x20, #0
	add x2, x23, #2776
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch}
	add x2, x23, #2776
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
	add x0, x23, #1952
	add x1, x23, #2144
	add x4, x23, #0
	bl {vg_hmac_sha512_224_init_scratch}
	ldr w9, [x23, #1952]
	str w9, [x23, #2336]
	ldr w9, [x23, #1956]
	str w9, [x23, #2340]
	ldr w9, [x23, #1960]
	str w9, [x23, #2344]
	ldr w9, [x23, #1964]
	str w9, [x23, #2348]
	ldr w9, [x23, #1968]
	str w9, [x23, #2352]
	ldr w9, [x23, #1972]
	str w9, [x23, #2356]
	ldr w9, [x23, #1976]
	str w9, [x23, #2360]
	ldr w9, [x23, #1980]
	str w9, [x23, #2364]
	ldr w9, [x23, #1984]
	str w9, [x23, #2368]
	ldr w9, [x23, #1988]
	str w9, [x23, #2372]
	ldr w9, [x23, #1992]
	str w9, [x23, #2376]
	ldr w9, [x23, #1996]
	str w9, [x23, #2380]
	ldr w9, [x23, #2000]
	str w9, [x23, #2384]
	ldr w9, [x23, #2004]
	str w9, [x23, #2388]
	ldr w9, [x23, #2008]
	str w9, [x23, #2392]
	ldr w9, [x23, #2012]
	str w9, [x23, #2396]
	ldr w9, [x23, #2016]
	str w9, [x23, #2400]
	ldr w9, [x23, #2020]
	str w9, [x23, #2404]
	ldr w9, [x23, #2024]
	str w9, [x23, #2408]
	ldr w9, [x23, #2028]
	str w9, [x23, #2412]
	ldr w9, [x23, #2032]
	str w9, [x23, #2416]
	ldr w9, [x23, #2036]
	str w9, [x23, #2420]
	ldr w9, [x23, #2040]
	str w9, [x23, #2424]
	ldr w9, [x23, #2044]
	str w9, [x23, #2428]
	ldr w9, [x23, #2048]
	str w9, [x23, #2432]
	ldr w9, [x23, #2052]
	str w9, [x23, #2436]
	ldr w9, [x23, #2056]
	str w9, [x23, #2440]
	ldr w9, [x23, #2060]
	str w9, [x23, #2444]
	ldr w9, [x23, #2064]
	str w9, [x23, #2448]
	ldr w9, [x23, #2068]
	str w9, [x23, #2452]
	ldr w9, [x23, #2072]
	str w9, [x23, #2456]
	ldr w9, [x23, #2076]
	str w9, [x23, #2460]
	ldr w9, [x23, #2080]
	str w9, [x23, #2464]
	ldr w9, [x23, #2084]
	str w9, [x23, #2468]
	ldr w9, [x23, #2088]
	str w9, [x23, #2472]
	ldr w9, [x23, #2092]
	str w9, [x23, #2476]
	ldr w9, [x23, #2096]
	str w9, [x23, #2480]
	ldr w9, [x23, #2100]
	str w9, [x23, #2484]
	ldr w9, [x23, #2104]
	str w9, [x23, #2488]
	ldr w9, [x23, #2108]
	str w9, [x23, #2492]
	ldr w9, [x23, #2112]
	str w9, [x23, #2496]
	ldr w9, [x23, #2116]
	str w9, [x23, #2500]
	ldr w9, [x23, #2120]
	str w9, [x23, #2504]
	ldr w9, [x23, #2124]
	str w9, [x23, #2508]
	ldr w9, [x23, #2128]
	str w9, [x23, #2512]
	ldr w9, [x23, #2132]
	str w9, [x23, #2516]
	ldr w9, [x23, #2136]
	str w9, [x23, #2520]
	ldr w9, [x23, #2140]
	str w9, [x23, #2524]
	add x0, x23, #2336
	movz x1, #128, lsl #0
	add x2, x21, #0
	add x3, x22, #0
	add x4, x23, #0
	bl {vg_sha512_update_scratch}
	add x20, x22, #0
	ldr x22, [x23, #1928]
	ldr x21, [x23, #1944]
	movz x19, #1, lsl #0
	cbz x21, 24f
26:
	ldr w9, [x23, #2336]
	str w9, [x23, #2528]
	ldr w9, [x23, #2340]
	str w9, [x23, #2532]
	ldr w9, [x23, #2344]
	str w9, [x23, #2536]
	ldr w9, [x23, #2348]
	str w9, [x23, #2540]
	ldr w9, [x23, #2352]
	str w9, [x23, #2544]
	ldr w9, [x23, #2356]
	str w9, [x23, #2548]
	ldr w9, [x23, #2360]
	str w9, [x23, #2552]
	ldr w9, [x23, #2364]
	str w9, [x23, #2556]
	ldr w9, [x23, #2368]
	str w9, [x23, #2560]
	ldr w9, [x23, #2372]
	str w9, [x23, #2564]
	ldr w9, [x23, #2376]
	str w9, [x23, #2568]
	ldr w9, [x23, #2380]
	str w9, [x23, #2572]
	ldr w9, [x23, #2384]
	str w9, [x23, #2576]
	ldr w9, [x23, #2388]
	str w9, [x23, #2580]
	ldr w9, [x23, #2392]
	str w9, [x23, #2584]
	ldr w9, [x23, #2396]
	str w9, [x23, #2588]
	ldr w9, [x23, #2400]
	str w9, [x23, #2592]
	ldr w9, [x23, #2404]
	str w9, [x23, #2596]
	ldr w9, [x23, #2408]
	str w9, [x23, #2600]
	ldr w9, [x23, #2412]
	str w9, [x23, #2604]
	ldr w9, [x23, #2416]
	str w9, [x23, #2608]
	ldr w9, [x23, #2420]
	str w9, [x23, #2612]
	ldr w9, [x23, #2424]
	str w9, [x23, #2616]
	ldr w9, [x23, #2428]
	str w9, [x23, #2620]
	ldr w9, [x23, #2432]
	str w9, [x23, #2624]
	ldr w9, [x23, #2436]
	str w9, [x23, #2628]
	ldr w9, [x23, #2440]
	str w9, [x23, #2632]
	ldr w9, [x23, #2444]
	str w9, [x23, #2636]
	ldr w9, [x23, #2448]
	str w9, [x23, #2640]
	ldr w9, [x23, #2452]
	str w9, [x23, #2644]
	ldr w9, [x23, #2456]
	str w9, [x23, #2648]
	ldr w9, [x23, #2460]
	str w9, [x23, #2652]
	ldr w9, [x23, #2464]
	str w9, [x23, #2656]
	ldr w9, [x23, #2468]
	str w9, [x23, #2660]
	ldr w9, [x23, #2472]
	str w9, [x23, #2664]
	ldr w9, [x23, #2476]
	str w9, [x23, #2668]
	ldr w9, [x23, #2480]
	str w9, [x23, #2672]
	ldr w9, [x23, #2484]
	str w9, [x23, #2676]
	ldr w9, [x23, #2488]
	str w9, [x23, #2680]
	ldr w9, [x23, #2492]
	str w9, [x23, #2684]
	ldr w9, [x23, #2496]
	str w9, [x23, #2688]
	ldr w9, [x23, #2500]
	str w9, [x23, #2692]
	ldr w9, [x23, #2504]
	str w9, [x23, #2696]
	ldr w9, [x23, #2508]
	str w9, [x23, #2700]
	ldr w9, [x23, #2512]
	str w9, [x23, #2704]
	ldr w9, [x23, #2516]
	str w9, [x23, #2708]
	ldr w9, [x23, #2520]
	str w9, [x23, #2712]
	ldr w9, [x23, #2524]
	str w9, [x23, #2716]
	rev w9, w19
	str w9, [x23, #2840]
	add x0, x23, #2528
	add x1, x20, #128
	add x2, x23, #2840
	movz x3, #4, lsl #0
	add x4, x23, #0
	bl {vg_sha512_update_scratch}
	add x0, x23, #2528
	add x1, x23, #2144
	add x2, x20, #132
	add x3, x23, #2720
	add x4, x23, #0
	bl {vg_hmac_sha512_224_finalize_scratch}
	ldr w9, [x23, #2720]
	str w9, [x23, #2748]
	ldr w9, [x23, #2724]
	str w9, [x23, #2752]
	ldr w9, [x23, #2728]
	str w9, [x23, #2756]
	ldr w9, [x23, #2732]
	str w9, [x23, #2760]
	ldr w9, [x23, #2736]
	str w9, [x23, #2764]
	ldr w9, [x23, #2740]
	str w9, [x23, #2768]
	ldr w9, [x23, #2744]
	str w9, [x23, #2772]
	add x0, x23, #1952
	add x1, x23, #2720
	ldr x2, [x23, #1936]
	add x3, x23, #2748
	add x4, x23, #0
	bl {vg_pbkdf2_hmac_sha512_224_iterate}
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
	ldrb w9, [x12, #2748]
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
	ldr x19, [x23, #1872]
	ldr x20, [x23, #1880]
	ldr x21, [x23, #1888]
	ldr x22, [x23, #1896]
	ldr x24, [x23, #1904]
	ldr x30, [x23, #1912]
	ldr x23, [x23, #1920]
	add sp, sp, #3408
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
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #3424
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
	add sp, sp, #3424
	ret
	.p2align 6
