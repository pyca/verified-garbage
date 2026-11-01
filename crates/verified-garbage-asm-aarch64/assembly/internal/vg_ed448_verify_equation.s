// The functions of `src/internal/vg_ed448_verify_equation.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_verify_equation:
	movz x12, #65535, lsl #0
	movk x12, #4095, lsl #16
	str x19, [x3, #0]
	str x20, [x3, #8]
	str x30, [x3, #3008]
	movz x20, #0, lsl #0
	add x4, x3, #64
20:
	str x20, [x4, #0]
	str x20, [x4, #8]
	str x20, [x4, #16]
	str x20, [x4, #24]
	str x20, [x4, #32]
	str x20, [x4, #40]
	str x20, [x4, #48]
	str x20, [x4, #56]
	add x4, x4, #64
	sub x12, x4, x3
	sub x12, x12, #2880
	cbnz x12, 20b
	movz x12, #65535, lsl #0
	movk x12, #4095, lsl #16
	movz x4, #49246, lsl #0
	movk x4, #50956, lsl #16
	movk x4, #43051, lsl #32
	movk x4, #38, lsl #48
	str x4, [x3, #1088]
	movz x4, #36390, lsl #0
	movk x4, #147, lsl #16
	movk x4, #57739, lsl #32
	movk x4, #128, lsl #48
	str x4, [x3, #1096]
	movz x4, #17211, lsl #0
	movk x4, #25873, lsl #16
	movk x4, #10934, lsl #32
	movk x4, #247, lsl #48
	str x4, [x3, #1104]
	movz x4, #44570, lsl #0
	movk x4, #25618, lsl #16
	movk x4, #54180, lsl #32
	movk x4, #163, lsl #48
	str x4, [x3, #1112]
	movz x4, #58148, lsl #0
	movk x4, #60013, lsl #16
	movk x4, #5991, lsl #32
	movk x4, #15, lsl #48
	str x4, [x3, #1120]
	movz x4, #28743, lsl #0
	movk x4, #5221, lsl #16
	movk x4, #55966, lsl #32
	movk x4, #54, lsl #48
	str x4, [x3, #1128]
	movz x4, #8895, lsl #0
	movk x4, #5542, lsl #16
	movk x4, #8733, lsl #32
	movk x4, #237, lsl #48
	str x4, [x3, #1136]
	movz x4, #60685, lsl #0
	movk x4, #50795, lsl #16
	movk x4, #6512, lsl #32
	movk x4, #79, lsl #48
	str x4, [x3, #1144]
	movz x4, #64020, lsl #0
	movk x4, #62000, lsl #16
	movk x4, #31067, lsl #32
	movk x4, #8, lsl #48
	str x4, [x3, #1216]
	movz x4, #44440, lsl #0
	movk x4, #55240, lsl #16
	movk x4, #11342, lsl #32
	movk x4, #19, lsl #48
	str x4, [x3, #1224]
	movz x4, #64957, lsl #0
	movk x4, #14788, lsl #16
	movk x4, #59004, lsl #32
	movk x4, #28, lsl #48
	str x4, [x3, #1232]
	movz x4, #54271, lsl #0
	movk x4, #55098, lsl #16
	movk x4, #41154, lsl #32
	movk x4, #5, lsl #48
	str x4, [x3, #1240]
	movz x4, #39966, lsl #0
	movk x4, #34680, lsl #16
	movk x4, #38976, lsl #32
	movk x4, #163, lsl #48
	str x4, [x3, #1248]
	movz x4, #29548, lsl #0
	movk x4, #60019, lsl #16
	movk x4, #25163, lsl #32
	movk x4, #199, lsl #48
	str x4, [x3, #1256]
	movz x4, #22217, lsl #0
	movk x4, #8247, lsl #16
	movk x4, #34934, lsl #32
	movk x4, #36, lsl #48
	str x4, [x3, #1264]
	movz x4, #46780, lsl #0
	movk x4, #29038, lsl #16
	movk x4, #16198, lsl #32
	movk x4, #105, lsl #48
	str x4, [x3, #1272]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1344]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1352]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1360]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1368]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1376]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1384]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1392]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1400]
	movz x4, #26454, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #255, lsl #48
	str x4, [x3, #1472]
	movz x4, #65535, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #255, lsl #48
	str x4, [x3, #1480]
	movz x4, #65535, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #255, lsl #48
	str x4, [x3, #1488]
	movz x4, #65535, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #255, lsl #48
	str x4, [x3, #1496]
	movz x4, #65534, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #255, lsl #48
	str x4, [x3, #1504]
	movz x4, #65535, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #255, lsl #48
	str x4, [x3, #1512]
	movz x4, #65535, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #255, lsl #48
	str x4, [x3, #1520]
	movz x4, #65535, lsl #0
	movk x4, #65535, lsl #16
	movk x4, #65535, lsl #32
	movk x4, #255, lsl #48
	str x4, [x3, #1528]
	ldrb w4, [x2, #0]
	strb w4, [x3, #2944]
	ldrb w4, [x2, #1]
	strb w4, [x3, #2945]
	ldrb w4, [x2, #2]
	strb w4, [x3, #2946]
	ldrb w4, [x2, #3]
	strb w4, [x3, #2947]
	ldrb w4, [x2, #4]
	strb w4, [x3, #2948]
	ldrb w4, [x2, #5]
	strb w4, [x3, #2949]
	ldrb w4, [x2, #6]
	strb w4, [x3, #2950]
	ldrb w4, [x2, #7]
	strb w4, [x3, #2951]
	ldrb w4, [x2, #8]
	strb w4, [x3, #2952]
	ldrb w4, [x2, #9]
	strb w4, [x3, #2953]
	ldrb w4, [x2, #10]
	strb w4, [x3, #2954]
	ldrb w4, [x2, #11]
	strb w4, [x3, #2955]
	ldrb w4, [x2, #12]
	strb w4, [x3, #2956]
	ldrb w4, [x2, #13]
	strb w4, [x3, #2957]
	ldrb w4, [x2, #14]
	strb w4, [x3, #2958]
	ldrb w4, [x2, #15]
	strb w4, [x3, #2959]
	ldrb w4, [x2, #16]
	strb w4, [x3, #2960]
	ldrb w4, [x2, #17]
	strb w4, [x3, #2961]
	ldrb w4, [x2, #18]
	strb w4, [x3, #2962]
	ldrb w4, [x2, #19]
	strb w4, [x3, #2963]
	ldrb w4, [x2, #20]
	strb w4, [x3, #2964]
	ldrb w4, [x2, #21]
	strb w4, [x3, #2965]
	ldrb w4, [x2, #22]
	strb w4, [x3, #2966]
	ldrb w4, [x2, #23]
	strb w4, [x3, #2967]
	ldrb w4, [x2, #24]
	strb w4, [x3, #2968]
	ldrb w4, [x2, #25]
	strb w4, [x3, #2969]
	ldrb w4, [x2, #26]
	strb w4, [x3, #2970]
	ldrb w4, [x2, #27]
	strb w4, [x3, #2971]
	ldrb w4, [x2, #28]
	strb w4, [x3, #2972]
	ldrb w4, [x2, #29]
	strb w4, [x3, #2973]
	ldrb w4, [x2, #30]
	strb w4, [x3, #2974]
	ldrb w4, [x2, #31]
	strb w4, [x3, #2975]
	ldrb w4, [x2, #32]
	strb w4, [x3, #2976]
	ldrb w4, [x2, #33]
	strb w4, [x3, #2977]
	ldrb w4, [x2, #34]
	strb w4, [x3, #2978]
	ldrb w4, [x2, #35]
	strb w4, [x3, #2979]
	ldrb w4, [x2, #36]
	strb w4, [x3, #2980]
	ldrb w4, [x2, #37]
	strb w4, [x3, #2981]
	ldrb w4, [x2, #38]
	strb w4, [x3, #2982]
	ldrb w4, [x2, #39]
	strb w4, [x3, #2983]
	ldrb w4, [x2, #40]
	strb w4, [x3, #2984]
	ldrb w4, [x2, #41]
	strb w4, [x3, #2985]
	ldrb w4, [x2, #42]
	strb w4, [x3, #2986]
	ldrb w4, [x2, #43]
	strb w4, [x3, #2987]
	ldrb w4, [x2, #44]
	strb w4, [x3, #2988]
	ldrb w4, [x2, #45]
	strb w4, [x3, #2989]
	ldrb w4, [x2, #46]
	strb w4, [x3, #2990]
	ldrb w4, [x2, #47]
	strb w4, [x3, #2991]
	ldrb w4, [x2, #48]
	strb w4, [x3, #2992]
	ldrb w4, [x2, #49]
	strb w4, [x3, #2993]
	ldrb w4, [x2, #50]
	strb w4, [x3, #2994]
	ldrb w4, [x2, #51]
	strb w4, [x3, #2995]
	ldrb w4, [x2, #52]
	strb w4, [x3, #2996]
	ldrb w4, [x2, #53]
	strb w4, [x3, #2997]
	ldrb w4, [x2, #54]
	strb w4, [x3, #2998]
	ldrb w4, [x2, #55]
	strb w4, [x3, #2999]
	ldrb w4, [x2, #56]
	strb w4, [x3, #3000]
	str x21, [x3, #2880]
	str x22, [x3, #2888]
	str x23, [x3, #2896]
	str x24, [x3, #2904]
	str x25, [x3, #2912]
	str x26, [x3, #2920]
	str x27, [x3, #2928]
	str x28, [x3, #2936]
	str q8, [x3, #4736]
	str q9, [x3, #4752]
	str q10, [x3, #4768]
	str q11, [x3, #4784]
	str q12, [x3, #4800]
	str q13, [x3, #4816]
	str q14, [x3, #4832]
	str q15, [x3, #4848]
	movz x19, #0, lsl #0
	movz x8, #1, lsl #0
21:
	add x11, x1, x19
	ldrb w4, [x11, #57]
	lsl x11, x19, #3
	add x11, x3, x11
	add x11, x11, #0
	lsr x5, x4, #0
	and x5, x5, x8
	strb w5, [x11, #3072]
	lsr x5, x4, #1
	and x5, x5, x8
	strb w5, [x11, #3073]
	lsr x5, x4, #2
	and x5, x5, x8
	strb w5, [x11, #3074]
	lsr x5, x4, #3
	and x5, x5, x8
	strb w5, [x11, #3075]
	lsr x5, x4, #4
	and x5, x5, x8
	strb w5, [x11, #3076]
	lsr x5, x4, #5
	and x5, x5, x8
	strb w5, [x11, #3077]
	lsr x5, x4, #6
	and x5, x5, x8
	strb w5, [x11, #3078]
	lsr x5, x4, #7
	and x5, x5, x8
	strb w5, [x11, #3079]
	add x19, x19, #1
	sub x11, x19, #57
	cbnz x11, 21b
	movz x5, #0, lsl #0
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x1, #63]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #62]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #61]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #60]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #59]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #58]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #57]
	add x4, x4, x7
	movz x6, #47885, lsl #0
	movk x6, #21671, lsl #16
	movk x6, #15725, lsl #32
	movk x6, #135, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x1, #70]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #69]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #68]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #67]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #66]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #65]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #64]
	add x4, x4, x7
	movz x6, #43740, lsl #0
	movk x6, #14960, lsl #16
	movk x6, #36210, lsl #32
	movk x6, #61, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x1, #77]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #76]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #75]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #74]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #73]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #72]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #71]
	add x4, x4, x7
	movz x6, #56979, lsl #0
	movk x6, #51567, lsl #16
	movk x6, #20777, lsl #32
	movk x6, #182, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x1, #84]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #83]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #82]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #81]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #80]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #79]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #78]
	add x4, x4, x7
	movz x6, #45348, lsl #0
	movk x6, #5691, lsl #16
	movk x6, #13788, lsl #32
	movk x6, #131, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x1, #91]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #90]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #89]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #88]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #87]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #86]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #85]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x1, #98]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #97]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #96]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #95]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #94]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #93]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #92]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x1, #105]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #104]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #103]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #102]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #101]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #100]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #99]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x1, #112]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #111]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #110]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #109]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #108]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #107]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x1, #106]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #192, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	orr x20, x20, x5
	ldrb w5, [x1, #113]
	orr x20, x20, x5
22:
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #6]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #5]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #4]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #3]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #2]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #1]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #0]
	add x4, x4, x7
	str x4, [x3, #1216]
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #13]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #12]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #11]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #10]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #9]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #8]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #7]
	add x4, x4, x7
	str x4, [x3, #1224]
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #20]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #19]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #18]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #17]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #16]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #15]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #14]
	add x4, x4, x7
	str x4, [x3, #1232]
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #27]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #26]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #25]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #24]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #23]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #22]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #21]
	add x4, x4, x7
	str x4, [x3, #1240]
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #34]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #33]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #32]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #31]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #30]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #29]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #28]
	add x4, x4, x7
	str x4, [x3, #1248]
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #41]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #40]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #39]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #38]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #37]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #36]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #35]
	add x4, x4, x7
	str x4, [x3, #1256]
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #48]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #47]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #46]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #45]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #44]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #43]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #42]
	add x4, x4, x7
	str x4, [x3, #1264]
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #55]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #54]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #53]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #52]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #51]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #50]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #49]
	add x4, x4, x7
	str x4, [x3, #1272]
	movz x5, #0, lsl #0
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #6]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #5]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #4]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #3]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #2]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #1]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #0]
	add x4, x4, x7
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #13]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #12]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #11]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #10]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #9]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #8]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #7]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #20]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #19]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #18]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #17]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #16]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #15]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #14]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #27]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #26]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #25]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #24]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #23]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #22]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #21]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #34]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #33]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #32]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #31]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #30]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #29]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #28]
	add x4, x4, x7
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #41]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #40]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #39]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #38]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #37]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #36]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #35]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #48]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #47]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #46]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #45]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #44]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #43]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #42]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	movz x4, #0, lsl #0
	lsl x4, x4, #8
	ldrb w7, [x0, #55]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #54]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #53]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #52]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #51]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #50]
	add x4, x4, x7
	lsl x4, x4, #8
	ldrb w7, [x0, #49]
	add x4, x4, x7
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	add x4, x4, x6
	add x4, x4, x5
	lsr x5, x4, #56
	orr x20, x20, x5
	ldrb w5, [x0, #56]
	lsr x17, x5, #7
	movz x6, #127, lsl #0
	and x5, x5, x6
	orr x20, x20, x5
	str x17, [x3, #16]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1344]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1352]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1360]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1368]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1376]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1384]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1392]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1400]
	ldr x0, [x3, #1216]
	ldr x2, [x3, #1224]
	ldr x4, [x3, #1232]
	ldr x5, [x3, #1240]
	ldr x6, [x3, #1248]
	ldr x7, [x3, #1256]
	ldr x8, [x3, #1264]
	ldr x9, [x3, #1272]
	movz x25, #65535, lsl #0
	movk x25, #65535, lsl #16
	movk x25, #65535, lsl #32
	movk x25, #255, lsl #48
	movz x26, #0, lsl #0
	add x10, x0, x6
	add x11, x2, x7
	add x13, x4, x8
	add x14, x5, x9
	add x15, x0, x0
	str x15, [x3, #3648]
	add x15, x6, x6
	str x15, [x3, #3672]
	add x15, x10, x10
	str x15, [x3, #3696]
	add x15, x2, x2
	str x15, [x3, #3656]
	add x15, x7, x7
	str x15, [x3, #3680]
	add x15, x11, x11
	str x15, [x3, #3704]
	add x15, x4, x4
	str x15, [x3, #3664]
	add x15, x8, x8
	str x15, [x3, #3688]
	add x15, x13, x13
	str x15, [x3, #3712]
	mul x21, x6, x6
	umulh x22, x6, x6
	ldr x17, [x3, #3680]
	mul x27, x17, x9
	umulh x28, x17, x9
	mul x15, x8, x8
	umulh x16, x8, x8
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x10, x10
	umulh x16, x10, x10
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3704]
	mul x15, x17, x14
	umulh x16, x17, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x13, x13
	umulh x16, x13, x13
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x0, x0
	umulh x16, x0, x0
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3656]
	mul x15, x17, x5
	umulh x16, x17, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	mul x15, x4, x4
	umulh x16, x4, x4
	subs x21, x21, x15
	sbc x22, x22, x16
	and x15, x21, x25
	str x15, [x3, #1600]
	extr x23, x22, x21, #56
	and x15, x27, x25
	str x15, [x3, #1632]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x7
	umulh x22, x17, x7
	ldr x17, [x3, #3688]
	mul x27, x17, x9
	umulh x28, x17, x9
	ldr x17, [x3, #3696]
	mul x15, x17, x11
	umulh x16, x17, x11
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3712]
	mul x15, x17, x14
	umulh x16, x17, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x2
	umulh x16, x17, x2
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3664]
	mul x15, x17, x5
	umulh x16, x17, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #1608]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #1640]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x8
	umulh x22, x17, x8
	mul x15, x7, x7
	umulh x16, x7, x7
	adds x21, x21, x15
	adc x22, x22, x16
	mul x27, x9, x9
	umulh x28, x9, x9
	ldr x17, [x3, #3696]
	mul x15, x17, x13
	umulh x16, x17, x13
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x11, x11
	umulh x16, x11, x11
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x14, x14
	umulh x16, x14, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x4
	umulh x16, x17, x4
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	mul x15, x2, x2
	umulh x16, x2, x2
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	mul x15, x5, x5
	umulh x16, x5, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #1616]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #1648]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x9
	umulh x22, x17, x9
	ldr x17, [x3, #3680]
	mul x15, x17, x8
	umulh x16, x17, x8
	adds x21, x21, x15
	adc x22, x22, x16
	ldr x17, [x3, #3696]
	mul x27, x17, x14
	umulh x28, x17, x14
	ldr x17, [x3, #3704]
	mul x15, x17, x13
	umulh x16, x17, x13
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x5
	umulh x16, x17, x5
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3656]
	mul x15, x17, x4
	umulh x16, x17, x4
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #1624]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #1656]
	extr x24, x28, x27, #56
	ldr x4, [x3, #1600]
	ldr x5, [x3, #1608]
	ldr x6, [x3, #1632]
	ldr x7, [x3, #1640]
	add x4, x4, x24
	add x6, x6, x24
	add x6, x6, x23
	lsr x8, x4, #56
	and x4, x4, x25
	add x5, x5, x8
	lsr x8, x6, #56
	and x6, x6, x25
	add x7, x7, x8
	str x4, [x3, #1600]
	str x5, [x3, #1608]
	str x6, [x3, #1632]
	str x7, [x3, #1640]
	movz x0, #65534, lsl #0
	movk x0, #65535, lsl #16
	movk x0, #65535, lsl #32
	movk x0, #511, lsl #48
	movz x2, #65532, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #511, lsl #48
	ldr x4, [x3, #1600]
	ldr x5, [x3, #1344]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1728]
	ldr x4, [x3, #1608]
	ldr x5, [x3, #1352]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1736]
	ldr x4, [x3, #1616]
	ldr x5, [x3, #1360]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1744]
	ldr x4, [x3, #1624]
	ldr x5, [x3, #1368]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1752]
	ldr x4, [x3, #1632]
	ldr x5, [x3, #1376]
	add x4, x4, x2
	sub x4, x4, x5
	str x4, [x3, #1760]
	ldr x4, [x3, #1640]
	ldr x5, [x3, #1384]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1768]
	ldr x4, [x3, #1648]
	ldr x5, [x3, #1392]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1776]
	ldr x4, [x3, #1656]
	ldr x5, [x3, #1400]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1784]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #576, lsl #0
	movz x2, #1472, lsl #0
	movz x3, #1600, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	movz x0, #65534, lsl #0
	movk x0, #65535, lsl #16
	movk x0, #65535, lsl #32
	movk x0, #511, lsl #48
	movz x2, #65532, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #511, lsl #48
	ldr x4, [x3, #576]
	ldr x5, [x3, #1344]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #448]
	ldr x4, [x3, #584]
	ldr x5, [x3, #1352]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #456]
	ldr x4, [x3, #592]
	ldr x5, [x3, #1360]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #464]
	ldr x4, [x3, #600]
	ldr x5, [x3, #1368]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #472]
	ldr x4, [x3, #608]
	ldr x5, [x3, #1376]
	add x4, x4, x2
	sub x4, x4, x5
	str x4, [x3, #480]
	ldr x4, [x3, #616]
	ldr x5, [x3, #1384]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #488]
	ldr x4, [x3, #624]
	ldr x5, [x3, #1392]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #496]
	ldr x4, [x3, #632]
	ldr x5, [x3, #1400]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #504]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #576, lsl #0
	movz x2, #1728, lsl #0
	movz x3, #448, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	ldr x0, [x3, #576]
	ldr x2, [x3, #584]
	ldr x4, [x3, #592]
	ldr x5, [x3, #600]
	ldr x6, [x3, #608]
	ldr x7, [x3, #616]
	ldr x8, [x3, #624]
	ldr x9, [x3, #632]
	movz x25, #65535, lsl #0
	movk x25, #65535, lsl #16
	movk x25, #65535, lsl #32
	movk x25, #255, lsl #48
	movz x26, #0, lsl #0
	add x10, x0, x6
	add x11, x2, x7
	add x13, x4, x8
	add x14, x5, x9
	add x15, x0, x0
	str x15, [x3, #3648]
	add x15, x6, x6
	str x15, [x3, #3672]
	add x15, x10, x10
	str x15, [x3, #3696]
	add x15, x2, x2
	str x15, [x3, #3656]
	add x15, x7, x7
	str x15, [x3, #3680]
	add x15, x11, x11
	str x15, [x3, #3704]
	add x15, x4, x4
	str x15, [x3, #3664]
	add x15, x8, x8
	str x15, [x3, #3688]
	add x15, x13, x13
	str x15, [x3, #3712]
	mul x21, x6, x6
	umulh x22, x6, x6
	ldr x17, [x3, #3680]
	mul x27, x17, x9
	umulh x28, x17, x9
	mul x15, x8, x8
	umulh x16, x8, x8
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x10, x10
	umulh x16, x10, x10
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3704]
	mul x15, x17, x14
	umulh x16, x17, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x13, x13
	umulh x16, x13, x13
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x0, x0
	umulh x16, x0, x0
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3656]
	mul x15, x17, x5
	umulh x16, x17, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	mul x15, x4, x4
	umulh x16, x4, x4
	subs x21, x21, x15
	sbc x22, x22, x16
	and x15, x21, x25
	str x15, [x3, #576]
	extr x23, x22, x21, #56
	and x15, x27, x25
	str x15, [x3, #608]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x7
	umulh x22, x17, x7
	ldr x17, [x3, #3688]
	mul x27, x17, x9
	umulh x28, x17, x9
	ldr x17, [x3, #3696]
	mul x15, x17, x11
	umulh x16, x17, x11
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3712]
	mul x15, x17, x14
	umulh x16, x17, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x2
	umulh x16, x17, x2
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3664]
	mul x15, x17, x5
	umulh x16, x17, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #584]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #616]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x8
	umulh x22, x17, x8
	mul x15, x7, x7
	umulh x16, x7, x7
	adds x21, x21, x15
	adc x22, x22, x16
	mul x27, x9, x9
	umulh x28, x9, x9
	ldr x17, [x3, #3696]
	mul x15, x17, x13
	umulh x16, x17, x13
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x11, x11
	umulh x16, x11, x11
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x14, x14
	umulh x16, x14, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x4
	umulh x16, x17, x4
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	mul x15, x2, x2
	umulh x16, x2, x2
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	mul x15, x5, x5
	umulh x16, x5, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #592]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #624]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x9
	umulh x22, x17, x9
	ldr x17, [x3, #3680]
	mul x15, x17, x8
	umulh x16, x17, x8
	adds x21, x21, x15
	adc x22, x22, x16
	ldr x17, [x3, #3696]
	mul x27, x17, x14
	umulh x28, x17, x14
	ldr x17, [x3, #3704]
	mul x15, x17, x13
	umulh x16, x17, x13
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x5
	umulh x16, x17, x5
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3656]
	mul x15, x17, x4
	umulh x16, x17, x4
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #600]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #632]
	extr x24, x28, x27, #56
	ldr x4, [x3, #576]
	ldr x5, [x3, #584]
	ldr x6, [x3, #608]
	ldr x7, [x3, #616]
	add x4, x4, x24
	add x6, x6, x24
	add x6, x6, x23
	lsr x8, x4, #56
	and x4, x4, x25
	add x5, x5, x8
	lsr x8, x6, #56
	and x6, x6, x25
	add x7, x7, x8
	str x4, [x3, #576]
	str x5, [x3, #584]
	str x6, [x3, #608]
	str x7, [x3, #616]
	ldr x0, [x3, #1728]
	ldr x2, [x3, #1736]
	ldr x4, [x3, #1744]
	ldr x5, [x3, #1752]
	ldr x6, [x3, #1760]
	ldr x7, [x3, #1768]
	ldr x8, [x3, #1776]
	ldr x9, [x3, #1784]
	movz x25, #65535, lsl #0
	movk x25, #65535, lsl #16
	movk x25, #65535, lsl #32
	movk x25, #255, lsl #48
	movz x26, #0, lsl #0
	add x10, x0, x6
	add x11, x2, x7
	add x13, x4, x8
	add x14, x5, x9
	add x15, x0, x0
	str x15, [x3, #3648]
	add x15, x6, x6
	str x15, [x3, #3672]
	add x15, x10, x10
	str x15, [x3, #3696]
	add x15, x2, x2
	str x15, [x3, #3656]
	add x15, x7, x7
	str x15, [x3, #3680]
	add x15, x11, x11
	str x15, [x3, #3704]
	add x15, x4, x4
	str x15, [x3, #3664]
	add x15, x8, x8
	str x15, [x3, #3688]
	add x15, x13, x13
	str x15, [x3, #3712]
	mul x21, x6, x6
	umulh x22, x6, x6
	ldr x17, [x3, #3680]
	mul x27, x17, x9
	umulh x28, x17, x9
	mul x15, x8, x8
	umulh x16, x8, x8
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x10, x10
	umulh x16, x10, x10
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3704]
	mul x15, x17, x14
	umulh x16, x17, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x13, x13
	umulh x16, x13, x13
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x0, x0
	umulh x16, x0, x0
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3656]
	mul x15, x17, x5
	umulh x16, x17, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	mul x15, x4, x4
	umulh x16, x4, x4
	subs x21, x21, x15
	sbc x22, x22, x16
	and x15, x21, x25
	str x15, [x3, #704]
	extr x23, x22, x21, #56
	and x15, x27, x25
	str x15, [x3, #736]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x7
	umulh x22, x17, x7
	ldr x17, [x3, #3688]
	mul x27, x17, x9
	umulh x28, x17, x9
	ldr x17, [x3, #3696]
	mul x15, x17, x11
	umulh x16, x17, x11
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3712]
	mul x15, x17, x14
	umulh x16, x17, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x2
	umulh x16, x17, x2
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3664]
	mul x15, x17, x5
	umulh x16, x17, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #712]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #744]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x8
	umulh x22, x17, x8
	mul x15, x7, x7
	umulh x16, x7, x7
	adds x21, x21, x15
	adc x22, x22, x16
	mul x27, x9, x9
	umulh x28, x9, x9
	ldr x17, [x3, #3696]
	mul x15, x17, x13
	umulh x16, x17, x13
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x11, x11
	umulh x16, x11, x11
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x14, x14
	umulh x16, x14, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x4
	umulh x16, x17, x4
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	mul x15, x2, x2
	umulh x16, x2, x2
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	mul x15, x5, x5
	umulh x16, x5, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #720]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #752]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x9
	umulh x22, x17, x9
	ldr x17, [x3, #3680]
	mul x15, x17, x8
	umulh x16, x17, x8
	adds x21, x21, x15
	adc x22, x22, x16
	ldr x17, [x3, #3696]
	mul x27, x17, x14
	umulh x28, x17, x14
	ldr x17, [x3, #3704]
	mul x15, x17, x13
	umulh x16, x17, x13
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x5
	umulh x16, x17, x5
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3656]
	mul x15, x17, x4
	umulh x16, x17, x4
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #728]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #760]
	extr x24, x28, x27, #56
	ldr x4, [x3, #704]
	ldr x5, [x3, #712]
	ldr x6, [x3, #736]
	ldr x7, [x3, #744]
	add x4, x4, x24
	add x6, x6, x24
	add x6, x6, x23
	lsr x8, x4, #56
	and x4, x4, x25
	add x5, x5, x8
	lsr x8, x6, #56
	and x6, x6, x25
	add x7, x7, x8
	str x4, [x3, #704]
	str x5, [x3, #712]
	str x6, [x3, #736]
	str x7, [x3, #744]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #704, lsl #0
	movz x2, #704, lsl #0
	movz x3, #1728, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #1088, lsl #0
	movz x2, #704, lsl #0
	movz x3, #448, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #1600, lsl #0
	movz x2, #1088, lsl #0
	movz x3, #576, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	add x0, x3, #0
	bl {vg_gf448_r56_pow_p34}
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #1088, lsl #0
	movz x2, #1088, lsl #0
	movz x3, #2752, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	ldr x0, [x3, #1088]
	ldr x2, [x3, #1096]
	ldr x4, [x3, #1104]
	ldr x5, [x3, #1112]
	ldr x6, [x3, #1120]
	ldr x7, [x3, #1128]
	ldr x8, [x3, #1136]
	ldr x9, [x3, #1144]
	movz x25, #65535, lsl #0
	movk x25, #65535, lsl #16
	movk x25, #65535, lsl #32
	movk x25, #255, lsl #48
	movz x26, #0, lsl #0
	add x10, x0, x6
	add x11, x2, x7
	add x13, x4, x8
	add x14, x5, x9
	add x15, x0, x0
	str x15, [x3, #3648]
	add x15, x6, x6
	str x15, [x3, #3672]
	add x15, x10, x10
	str x15, [x3, #3696]
	add x15, x2, x2
	str x15, [x3, #3656]
	add x15, x7, x7
	str x15, [x3, #3680]
	add x15, x11, x11
	str x15, [x3, #3704]
	add x15, x4, x4
	str x15, [x3, #3664]
	add x15, x8, x8
	str x15, [x3, #3688]
	add x15, x13, x13
	str x15, [x3, #3712]
	mul x21, x6, x6
	umulh x22, x6, x6
	ldr x17, [x3, #3680]
	mul x27, x17, x9
	umulh x28, x17, x9
	mul x15, x8, x8
	umulh x16, x8, x8
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x10, x10
	umulh x16, x10, x10
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3704]
	mul x15, x17, x14
	umulh x16, x17, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x13, x13
	umulh x16, x13, x13
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x0, x0
	umulh x16, x0, x0
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3656]
	mul x15, x17, x5
	umulh x16, x17, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	mul x15, x4, x4
	umulh x16, x4, x4
	subs x21, x21, x15
	sbc x22, x22, x16
	and x15, x21, x25
	str x15, [x3, #1600]
	extr x23, x22, x21, #56
	and x15, x27, x25
	str x15, [x3, #1632]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x7
	umulh x22, x17, x7
	ldr x17, [x3, #3688]
	mul x27, x17, x9
	umulh x28, x17, x9
	ldr x17, [x3, #3696]
	mul x15, x17, x11
	umulh x16, x17, x11
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3712]
	mul x15, x17, x14
	umulh x16, x17, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x2
	umulh x16, x17, x2
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3664]
	mul x15, x17, x5
	umulh x16, x17, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #1608]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #1640]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x8
	umulh x22, x17, x8
	mul x15, x7, x7
	umulh x16, x7, x7
	adds x21, x21, x15
	adc x22, x22, x16
	mul x27, x9, x9
	umulh x28, x9, x9
	ldr x17, [x3, #3696]
	mul x15, x17, x13
	umulh x16, x17, x13
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x11, x11
	umulh x16, x11, x11
	adds x27, x27, x15
	adc x28, x28, x16
	mul x15, x14, x14
	umulh x16, x14, x14
	adds x21, x21, x15
	adc x22, x22, x16
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x4
	umulh x16, x17, x4
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	mul x15, x2, x2
	umulh x16, x2, x2
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	mul x15, x5, x5
	umulh x16, x5, x5
	subs x21, x21, x15
	sbc x22, x22, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #1616]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #1648]
	extr x24, x28, x27, #56
	ldr x17, [x3, #3672]
	mul x21, x17, x9
	umulh x22, x17, x9
	ldr x17, [x3, #3680]
	mul x15, x17, x8
	umulh x16, x17, x8
	adds x21, x21, x15
	adc x22, x22, x16
	ldr x17, [x3, #3696]
	mul x27, x17, x14
	umulh x28, x17, x14
	ldr x17, [x3, #3704]
	mul x15, x17, x13
	umulh x16, x17, x13
	adds x27, x27, x15
	adc x28, x28, x16
	ldr x17, [x3, #3648]
	mul x15, x17, x5
	umulh x16, x17, x5
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	ldr x17, [x3, #3656]
	mul x15, x17, x4
	umulh x16, x17, x4
	adds x21, x21, x15
	adc x22, x22, x16
	subs x27, x27, x15
	sbc x28, x28, x16
	adds x21, x21, x23
	adc x22, x22, x26
	and x15, x21, x25
	str x15, [x3, #1624]
	extr x23, x22, x21, #56
	adds x27, x27, x24
	adc x28, x28, x26
	and x15, x27, x25
	str x15, [x3, #1656]
	extr x24, x28, x27, #56
	ldr x4, [x3, #1600]
	ldr x5, [x3, #1608]
	ldr x6, [x3, #1632]
	ldr x7, [x3, #1640]
	add x4, x4, x24
	add x6, x6, x24
	add x6, x6, x23
	lsr x8, x4, #56
	and x4, x4, x25
	add x5, x5, x8
	lsr x8, x6, #56
	and x6, x6, x25
	add x7, x7, x8
	str x4, [x3, #1600]
	str x5, [x3, #1608]
	str x6, [x3, #1632]
	str x7, [x3, #1640]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #1600, lsl #0
	movz x2, #1600, lsl #0
	movz x3, #448, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	movz x8, #2, lsl #0
23:
	sub x8, x8, #1
	cbnz x8, 24f
	ldr x4, [x3, #192]
	str x4, [x3, #4864]
	ldr x4, [x3, #200]
	str x4, [x3, #4872]
	ldr x4, [x3, #208]
	str x4, [x3, #4880]
	ldr x4, [x3, #216]
	str x4, [x3, #4888]
	ldr x4, [x3, #224]
	str x4, [x3, #4896]
	ldr x4, [x3, #232]
	str x4, [x3, #4904]
	ldr x4, [x3, #240]
	str x4, [x3, #4912]
	ldr x4, [x3, #248]
	str x4, [x3, #4920]
	ldr x4, [x3, #256]
	str x4, [x3, #4928]
	ldr x4, [x3, #264]
	str x4, [x3, #4936]
	ldr x4, [x3, #272]
	str x4, [x3, #4944]
	ldr x4, [x3, #280]
	str x4, [x3, #4952]
	ldr x4, [x3, #288]
	str x4, [x3, #4960]
	ldr x4, [x3, #296]
	str x4, [x3, #4968]
	ldr x4, [x3, #304]
	str x4, [x3, #4976]
	ldr x4, [x3, #312]
	str x4, [x3, #4984]
	ldr x4, [x3, #1728]
	str x4, [x3, #192]
	ldr x4, [x3, #1736]
	str x4, [x3, #200]
	ldr x4, [x3, #1744]
	str x4, [x3, #208]
	ldr x4, [x3, #1752]
	str x4, [x3, #216]
	ldr x4, [x3, #1760]
	str x4, [x3, #224]
	ldr x4, [x3, #1768]
	str x4, [x3, #232]
	ldr x4, [x3, #1776]
	str x4, [x3, #240]
	ldr x4, [x3, #1784]
	str x4, [x3, #248]
	b 25f
24:
	ldr x4, [x3, #1600]
	str x4, [x3, #192]
	ldr x4, [x3, #1608]
	str x4, [x3, #200]
	ldr x4, [x3, #1616]
	str x4, [x3, #208]
	ldr x4, [x3, #1624]
	str x4, [x3, #216]
	ldr x4, [x3, #1632]
	str x4, [x3, #224]
	ldr x4, [x3, #1640]
	str x4, [x3, #232]
	ldr x4, [x3, #1648]
	str x4, [x3, #240]
	ldr x4, [x3, #1656]
	str x4, [x3, #248]
25:
	ldr x4, [x3, #192]
	movz x5, #0, lsl #0
	str x4, [x3, #3840]
	str x5, [x3, #3848]
	ldr x4, [x3, #200]
	movz x5, #0, lsl #0
	str x4, [x3, #3856]
	str x5, [x3, #3864]
	ldr x4, [x3, #208]
	movz x5, #0, lsl #0
	str x4, [x3, #3872]
	str x5, [x3, #3880]
	ldr x4, [x3, #216]
	movz x5, #0, lsl #0
	str x4, [x3, #3888]
	str x5, [x3, #3896]
	ldr x4, [x3, #224]
	movz x5, #0, lsl #0
	str x4, [x3, #3904]
	str x5, [x3, #3912]
	ldr x4, [x3, #232]
	movz x5, #0, lsl #0
	str x4, [x3, #3920]
	str x5, [x3, #3928]
	ldr x4, [x3, #240]
	movz x5, #0, lsl #0
	str x4, [x3, #3936]
	str x5, [x3, #3944]
	ldr x4, [x3, #248]
	movz x5, #0, lsl #0
	str x4, [x3, #3952]
	str x5, [x3, #3960]
	movz x6, #0, lsl #0
	movz x11, #0, lsl #0
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #255, lsl #48
	ldr x4, [x3, #3840]
	ldr x5, [x3, #3848]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3840]
	str x11, [x3, #3848]
	ldr x4, [x3, #3856]
	ldr x5, [x3, #3864]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3856]
	str x11, [x3, #3864]
	ldr x4, [x3, #3872]
	ldr x5, [x3, #3880]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3872]
	str x11, [x3, #3880]
	ldr x4, [x3, #3888]
	ldr x5, [x3, #3896]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3888]
	str x11, [x3, #3896]
	ldr x4, [x3, #3904]
	ldr x5, [x3, #3912]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3904]
	str x11, [x3, #3912]
	ldr x4, [x3, #3920]
	ldr x5, [x3, #3928]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3920]
	str x11, [x3, #3928]
	ldr x4, [x3, #3936]
	ldr x5, [x3, #3944]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3936]
	str x11, [x3, #3944]
	ldr x4, [x3, #3952]
	ldr x5, [x3, #3960]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3952]
	str x11, [x3, #3960]
	ldr x4, [x3, #3840]
	add x4, x4, x6
	str x4, [x3, #3840]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	str x4, [x3, #3904]
	movz x6, #0, lsl #0
	movz x11, #0, lsl #0
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #255, lsl #48
	ldr x4, [x3, #3840]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3840]
	ldr x4, [x3, #3856]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3856]
	ldr x4, [x3, #3872]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3872]
	ldr x4, [x3, #3888]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3888]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3904]
	ldr x4, [x3, #3920]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3920]
	ldr x4, [x3, #3936]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3936]
	ldr x4, [x3, #3952]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3952]
	ldr x4, [x3, #3840]
	add x4, x4, x6
	str x4, [x3, #3840]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	str x4, [x3, #3904]
	movz x6, #0, lsl #0
	movz x11, #0, lsl #0
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #255, lsl #48
	ldr x4, [x3, #3840]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #192]
	str x5, [x3, #200]
	ldr x4, [x3, #3856]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #208]
	str x5, [x3, #216]
	ldr x4, [x3, #3872]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #224]
	str x5, [x3, #232]
	ldr x4, [x3, #3888]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #240]
	str x5, [x3, #248]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #256]
	str x5, [x3, #264]
	ldr x4, [x3, #3920]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #272]
	str x5, [x3, #280]
	ldr x4, [x3, #3936]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #288]
	str x5, [x3, #296]
	ldr x4, [x3, #3952]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #304]
	str x5, [x3, #312]
	ldr x4, [x3, #192]
	str x4, [x3, #3840]
	ldr x4, [x3, #200]
	str x4, [x3, #3848]
	ldr x4, [x3, #208]
	str x4, [x3, #3856]
	ldr x4, [x3, #216]
	str x4, [x3, #3864]
	ldr x4, [x3, #224]
	str x4, [x3, #3872]
	ldr x4, [x3, #232]
	str x4, [x3, #3880]
	ldr x4, [x3, #240]
	str x4, [x3, #3888]
	ldr x4, [x3, #248]
	str x4, [x3, #3896]
	ldr x4, [x3, #256]
	str x4, [x3, #3904]
	ldr x4, [x3, #264]
	str x4, [x3, #3912]
	ldr x4, [x3, #272]
	str x4, [x3, #3920]
	ldr x4, [x3, #280]
	str x4, [x3, #3928]
	ldr x4, [x3, #288]
	str x4, [x3, #3936]
	ldr x4, [x3, #296]
	str x4, [x3, #3944]
	ldr x4, [x3, #304]
	str x4, [x3, #3952]
	ldr x4, [x3, #312]
	str x4, [x3, #3960]
	ldr x4, [x3, #3840]
	add x4, x4, #1
	str x4, [x3, #3840]
	ldr x4, [x3, #3904]
	add x4, x4, #1
	str x4, [x3, #3904]
	movz x6, #0, lsl #0
	ldr x4, [x3, #3840]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3840]
	lsr x6, x4, #28
	ldr x4, [x3, #3848]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3848]
	lsr x6, x4, #28
	ldr x4, [x3, #3856]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3856]
	lsr x6, x4, #28
	ldr x4, [x3, #3864]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3864]
	lsr x6, x4, #28
	ldr x4, [x3, #3872]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3872]
	lsr x6, x4, #28
	ldr x4, [x3, #3880]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3880]
	lsr x6, x4, #28
	ldr x4, [x3, #3888]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3888]
	lsr x6, x4, #28
	ldr x4, [x3, #3896]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3896]
	lsr x6, x4, #28
	ldr x4, [x3, #3904]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3904]
	lsr x6, x4, #28
	ldr x4, [x3, #3912]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3912]
	lsr x6, x4, #28
	ldr x4, [x3, #3920]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3920]
	lsr x6, x4, #28
	ldr x4, [x3, #3928]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3928]
	lsr x6, x4, #28
	ldr x4, [x3, #3936]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3936]
	lsr x6, x4, #28
	ldr x4, [x3, #3944]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3944]
	lsr x6, x4, #28
	ldr x4, [x3, #3952]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3952]
	lsr x6, x4, #28
	ldr x4, [x3, #3960]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3960]
	lsr x6, x4, #28
	movz x7, #0, lsl #0
	sub x7, x7, x6
	ldr x4, [x3, #192]
	ldr x5, [x3, #3840]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #192]
	ldr x4, [x3, #200]
	ldr x5, [x3, #3848]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #200]
	ldr x4, [x3, #208]
	ldr x5, [x3, #3856]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #208]
	ldr x4, [x3, #216]
	ldr x5, [x3, #3864]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #216]
	ldr x4, [x3, #224]
	ldr x5, [x3, #3872]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #224]
	ldr x4, [x3, #232]
	ldr x5, [x3, #3880]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #232]
	ldr x4, [x3, #240]
	ldr x5, [x3, #3888]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #240]
	ldr x4, [x3, #248]
	ldr x5, [x3, #3896]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #248]
	ldr x4, [x3, #256]
	ldr x5, [x3, #3904]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #256]
	ldr x4, [x3, #264]
	ldr x5, [x3, #3912]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #264]
	ldr x4, [x3, #272]
	ldr x5, [x3, #3920]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #272]
	ldr x4, [x3, #280]
	ldr x5, [x3, #3928]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #280]
	ldr x4, [x3, #288]
	ldr x5, [x3, #3936]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #288]
	ldr x4, [x3, #296]
	ldr x5, [x3, #3944]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #296]
	ldr x4, [x3, #304]
	ldr x5, [x3, #3952]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #304]
	ldr x4, [x3, #312]
	ldr x5, [x3, #3960]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #312]
	cbnz x8, 23b
	movz x5, #0, lsl #0
	ldr x4, [x3, #192]
	ldr x6, [x3, #4864]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #200]
	ldr x6, [x3, #4872]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #208]
	ldr x6, [x3, #4880]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #216]
	ldr x6, [x3, #4888]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #224]
	ldr x6, [x3, #4896]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #232]
	ldr x6, [x3, #4904]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #240]
	ldr x6, [x3, #4912]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #248]
	ldr x6, [x3, #4920]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #256]
	ldr x6, [x3, #4928]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #264]
	ldr x6, [x3, #4936]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #272]
	ldr x6, [x3, #4944]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #280]
	ldr x6, [x3, #4952]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #288]
	ldr x6, [x3, #4960]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #296]
	ldr x6, [x3, #4968]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #304]
	ldr x6, [x3, #4976]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #312]
	ldr x6, [x3, #4984]
	eor x4, x4, x6
	orr x5, x5, x4
	orr x20, x20, x5
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1728]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1736]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1744]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1752]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1760]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1768]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1776]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1784]
	movz x0, #65534, lsl #0
	movk x0, #65535, lsl #16
	movk x0, #65535, lsl #32
	movk x0, #511, lsl #48
	movz x2, #65532, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #511, lsl #48
	ldr x4, [x3, #1728]
	ldr x5, [x3, #1088]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1600]
	ldr x4, [x3, #1736]
	ldr x5, [x3, #1096]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1608]
	ldr x4, [x3, #1744]
	ldr x5, [x3, #1104]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1616]
	ldr x4, [x3, #1752]
	ldr x5, [x3, #1112]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1624]
	ldr x4, [x3, #1760]
	ldr x5, [x3, #1120]
	add x4, x4, x2
	sub x4, x4, x5
	str x4, [x3, #1632]
	ldr x4, [x3, #1768]
	ldr x5, [x3, #1128]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1640]
	ldr x4, [x3, #1776]
	ldr x5, [x3, #1136]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1648]
	ldr x4, [x3, #1784]
	ldr x5, [x3, #1144]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1656]
	ldr x17, [x3, #16]
	ldr x4, [x3, #1088]
	str x4, [x3, #192]
	ldr x4, [x3, #1096]
	str x4, [x3, #200]
	ldr x4, [x3, #1104]
	str x4, [x3, #208]
	ldr x4, [x3, #1112]
	str x4, [x3, #216]
	ldr x4, [x3, #1120]
	str x4, [x3, #224]
	ldr x4, [x3, #1128]
	str x4, [x3, #232]
	ldr x4, [x3, #1136]
	str x4, [x3, #240]
	ldr x4, [x3, #1144]
	str x4, [x3, #248]
	ldr x4, [x3, #192]
	movz x5, #0, lsl #0
	str x4, [x3, #3840]
	str x5, [x3, #3848]
	ldr x4, [x3, #200]
	movz x5, #0, lsl #0
	str x4, [x3, #3856]
	str x5, [x3, #3864]
	ldr x4, [x3, #208]
	movz x5, #0, lsl #0
	str x4, [x3, #3872]
	str x5, [x3, #3880]
	ldr x4, [x3, #216]
	movz x5, #0, lsl #0
	str x4, [x3, #3888]
	str x5, [x3, #3896]
	ldr x4, [x3, #224]
	movz x5, #0, lsl #0
	str x4, [x3, #3904]
	str x5, [x3, #3912]
	ldr x4, [x3, #232]
	movz x5, #0, lsl #0
	str x4, [x3, #3920]
	str x5, [x3, #3928]
	ldr x4, [x3, #240]
	movz x5, #0, lsl #0
	str x4, [x3, #3936]
	str x5, [x3, #3944]
	ldr x4, [x3, #248]
	movz x5, #0, lsl #0
	str x4, [x3, #3952]
	str x5, [x3, #3960]
	movz x6, #0, lsl #0
	movz x11, #0, lsl #0
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #255, lsl #48
	ldr x4, [x3, #3840]
	ldr x5, [x3, #3848]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3840]
	str x11, [x3, #3848]
	ldr x4, [x3, #3856]
	ldr x5, [x3, #3864]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3856]
	str x11, [x3, #3864]
	ldr x4, [x3, #3872]
	ldr x5, [x3, #3880]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3872]
	str x11, [x3, #3880]
	ldr x4, [x3, #3888]
	ldr x5, [x3, #3896]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3888]
	str x11, [x3, #3896]
	ldr x4, [x3, #3904]
	ldr x5, [x3, #3912]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3904]
	str x11, [x3, #3912]
	ldr x4, [x3, #3920]
	ldr x5, [x3, #3928]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3920]
	str x11, [x3, #3928]
	ldr x4, [x3, #3936]
	ldr x5, [x3, #3944]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3936]
	str x11, [x3, #3944]
	ldr x4, [x3, #3952]
	ldr x5, [x3, #3960]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3952]
	str x11, [x3, #3960]
	ldr x4, [x3, #3840]
	add x4, x4, x6
	str x4, [x3, #3840]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	str x4, [x3, #3904]
	movz x6, #0, lsl #0
	movz x11, #0, lsl #0
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #255, lsl #48
	ldr x4, [x3, #3840]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3840]
	ldr x4, [x3, #3856]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3856]
	ldr x4, [x3, #3872]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3872]
	ldr x4, [x3, #3888]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3888]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3904]
	ldr x4, [x3, #3920]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3920]
	ldr x4, [x3, #3936]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3936]
	ldr x4, [x3, #3952]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3952]
	ldr x4, [x3, #3840]
	add x4, x4, x6
	str x4, [x3, #3840]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	str x4, [x3, #3904]
	movz x6, #0, lsl #0
	movz x11, #0, lsl #0
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #255, lsl #48
	ldr x4, [x3, #3840]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #192]
	str x5, [x3, #200]
	ldr x4, [x3, #3856]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #208]
	str x5, [x3, #216]
	ldr x4, [x3, #3872]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #224]
	str x5, [x3, #232]
	ldr x4, [x3, #3888]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #240]
	str x5, [x3, #248]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #256]
	str x5, [x3, #264]
	ldr x4, [x3, #3920]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #272]
	str x5, [x3, #280]
	ldr x4, [x3, #3936]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #288]
	str x5, [x3, #296]
	ldr x4, [x3, #3952]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #304]
	str x5, [x3, #312]
	ldr x4, [x3, #192]
	str x4, [x3, #3840]
	ldr x4, [x3, #200]
	str x4, [x3, #3848]
	ldr x4, [x3, #208]
	str x4, [x3, #3856]
	ldr x4, [x3, #216]
	str x4, [x3, #3864]
	ldr x4, [x3, #224]
	str x4, [x3, #3872]
	ldr x4, [x3, #232]
	str x4, [x3, #3880]
	ldr x4, [x3, #240]
	str x4, [x3, #3888]
	ldr x4, [x3, #248]
	str x4, [x3, #3896]
	ldr x4, [x3, #256]
	str x4, [x3, #3904]
	ldr x4, [x3, #264]
	str x4, [x3, #3912]
	ldr x4, [x3, #272]
	str x4, [x3, #3920]
	ldr x4, [x3, #280]
	str x4, [x3, #3928]
	ldr x4, [x3, #288]
	str x4, [x3, #3936]
	ldr x4, [x3, #296]
	str x4, [x3, #3944]
	ldr x4, [x3, #304]
	str x4, [x3, #3952]
	ldr x4, [x3, #312]
	str x4, [x3, #3960]
	ldr x4, [x3, #3840]
	add x4, x4, #1
	str x4, [x3, #3840]
	ldr x4, [x3, #3904]
	add x4, x4, #1
	str x4, [x3, #3904]
	movz x6, #0, lsl #0
	ldr x4, [x3, #3840]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3840]
	lsr x6, x4, #28
	ldr x4, [x3, #3848]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3848]
	lsr x6, x4, #28
	ldr x4, [x3, #3856]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3856]
	lsr x6, x4, #28
	ldr x4, [x3, #3864]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3864]
	lsr x6, x4, #28
	ldr x4, [x3, #3872]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3872]
	lsr x6, x4, #28
	ldr x4, [x3, #3880]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3880]
	lsr x6, x4, #28
	ldr x4, [x3, #3888]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3888]
	lsr x6, x4, #28
	ldr x4, [x3, #3896]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3896]
	lsr x6, x4, #28
	ldr x4, [x3, #3904]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3904]
	lsr x6, x4, #28
	ldr x4, [x3, #3912]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3912]
	lsr x6, x4, #28
	ldr x4, [x3, #3920]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3920]
	lsr x6, x4, #28
	ldr x4, [x3, #3928]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3928]
	lsr x6, x4, #28
	ldr x4, [x3, #3936]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3936]
	lsr x6, x4, #28
	ldr x4, [x3, #3944]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3944]
	lsr x6, x4, #28
	ldr x4, [x3, #3952]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3952]
	lsr x6, x4, #28
	ldr x4, [x3, #3960]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3960]
	lsr x6, x4, #28
	movz x7, #0, lsl #0
	sub x7, x7, x6
	ldr x4, [x3, #192]
	ldr x5, [x3, #3840]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #192]
	ldr x4, [x3, #200]
	ldr x5, [x3, #3848]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #200]
	ldr x4, [x3, #208]
	ldr x5, [x3, #3856]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #208]
	ldr x4, [x3, #216]
	ldr x5, [x3, #3864]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #216]
	ldr x4, [x3, #224]
	ldr x5, [x3, #3872]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #224]
	ldr x4, [x3, #232]
	ldr x5, [x3, #3880]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #232]
	ldr x4, [x3, #240]
	ldr x5, [x3, #3888]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #240]
	ldr x4, [x3, #248]
	ldr x5, [x3, #3896]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #248]
	ldr x4, [x3, #256]
	ldr x5, [x3, #3904]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #256]
	ldr x4, [x3, #264]
	ldr x5, [x3, #3912]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #264]
	ldr x4, [x3, #272]
	ldr x5, [x3, #3920]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #272]
	ldr x4, [x3, #280]
	ldr x5, [x3, #3928]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #280]
	ldr x4, [x3, #288]
	ldr x5, [x3, #3936]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #288]
	ldr x4, [x3, #296]
	ldr x5, [x3, #3944]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #296]
	ldr x4, [x3, #304]
	ldr x5, [x3, #3952]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #304]
	ldr x4, [x3, #312]
	ldr x5, [x3, #3960]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #312]
	movz x5, #0, lsl #0
	ldr x4, [x3, #192]
	orr x5, x5, x4
	ldr x4, [x3, #200]
	orr x5, x5, x4
	ldr x4, [x3, #208]
	orr x5, x5, x4
	ldr x4, [x3, #216]
	orr x5, x5, x4
	ldr x4, [x3, #224]
	orr x5, x5, x4
	ldr x4, [x3, #232]
	orr x5, x5, x4
	ldr x4, [x3, #240]
	orr x5, x5, x4
	ldr x4, [x3, #248]
	orr x5, x5, x4
	ldr x4, [x3, #256]
	orr x5, x5, x4
	ldr x4, [x3, #264]
	orr x5, x5, x4
	ldr x4, [x3, #272]
	orr x5, x5, x4
	ldr x4, [x3, #280]
	orr x5, x5, x4
	ldr x4, [x3, #288]
	orr x5, x5, x4
	ldr x4, [x3, #296]
	orr x5, x5, x4
	ldr x4, [x3, #304]
	orr x5, x5, x4
	ldr x4, [x3, #312]
	orr x5, x5, x4
	movz x6, #0, lsl #0
	subs x7, x6, x5
	adc x5, x6, x6
	and x5, x5, x17
	orr x20, x20, x5
	ldr x4, [x3, #192]
	movz x6, #1, lsl #0
	and x4, x4, x6
	eor x4, x4, x17
	movz x6, #0, lsl #0
	sub x17, x6, x4
	add x6, x17, #0
	ldr x4, [x3, #1088]
	ldr x5, [x3, #1600]
	eor x7, x4, x5
	and x7, x7, x6
	eor x4, x4, x7
	eor x5, x5, x7
	str x4, [x3, #1088]
	str x5, [x3, #1600]
	ldr x4, [x3, #1096]
	ldr x5, [x3, #1608]
	eor x7, x4, x5
	and x7, x7, x6
	eor x4, x4, x7
	eor x5, x5, x7
	str x4, [x3, #1096]
	str x5, [x3, #1608]
	ldr x4, [x3, #1104]
	ldr x5, [x3, #1616]
	eor x7, x4, x5
	and x7, x7, x6
	eor x4, x4, x7
	eor x5, x5, x7
	str x4, [x3, #1104]
	str x5, [x3, #1616]
	ldr x4, [x3, #1112]
	ldr x5, [x3, #1624]
	eor x7, x4, x5
	and x7, x7, x6
	eor x4, x4, x7
	eor x5, x5, x7
	str x4, [x3, #1112]
	str x5, [x3, #1624]
	ldr x4, [x3, #1120]
	ldr x5, [x3, #1632]
	eor x7, x4, x5
	and x7, x7, x6
	eor x4, x4, x7
	eor x5, x5, x7
	str x4, [x3, #1120]
	str x5, [x3, #1632]
	ldr x4, [x3, #1128]
	ldr x5, [x3, #1640]
	eor x7, x4, x5
	and x7, x7, x6
	eor x4, x4, x7
	eor x5, x5, x7
	str x4, [x3, #1128]
	str x5, [x3, #1640]
	ldr x4, [x3, #1136]
	ldr x5, [x3, #1648]
	eor x7, x4, x5
	and x7, x7, x6
	eor x4, x4, x7
	eor x5, x5, x7
	str x4, [x3, #1136]
	str x5, [x3, #1648]
	ldr x4, [x3, #1144]
	ldr x5, [x3, #1656]
	eor x7, x4, x5
	and x7, x7, x6
	eor x4, x4, x7
	eor x5, x5, x7
	str x4, [x3, #1144]
	str x5, [x3, #1656]
	sub x19, x1, x3
	cbnz x19, 26f
	add x0, x1, #0
	b 27f
26:
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #832, lsl #0
	movz x2, #1088, lsl #0
	movz x3, #1344, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	ldr x4, [x3, #1216]
	str x4, [x3, #960]
	ldr x4, [x3, #1224]
	str x4, [x3, #968]
	ldr x4, [x3, #1232]
	str x4, [x3, #976]
	ldr x4, [x3, #1240]
	str x4, [x3, #984]
	ldr x4, [x3, #1248]
	str x4, [x3, #992]
	ldr x4, [x3, #1256]
	str x4, [x3, #1000]
	ldr x4, [x3, #1264]
	str x4, [x3, #1008]
	ldr x4, [x3, #1272]
	str x4, [x3, #1016]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1728]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1736]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1744]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1752]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1760]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1768]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1776]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #1784]
	movz x0, #65534, lsl #0
	movk x0, #65535, lsl #16
	movk x0, #65535, lsl #32
	movk x0, #511, lsl #48
	movz x2, #65532, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #511, lsl #48
	ldr x4, [x3, #1728]
	ldr x5, [x3, #832]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1600]
	ldr x4, [x3, #1736]
	ldr x5, [x3, #840]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1608]
	ldr x4, [x3, #1744]
	ldr x5, [x3, #848]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1616]
	ldr x4, [x3, #1752]
	ldr x5, [x3, #856]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1624]
	ldr x4, [x3, #1760]
	ldr x5, [x3, #864]
	add x4, x4, x2
	sub x4, x4, x5
	str x4, [x3, #1632]
	ldr x4, [x3, #1768]
	ldr x5, [x3, #872]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1640]
	ldr x4, [x3, #1776]
	ldr x5, [x3, #880]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1648]
	ldr x4, [x3, #1784]
	ldr x5, [x3, #888]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #1656]
	ldr x4, [x3, #1600]
	str x4, [x3, #832]
	ldr x4, [x3, #1608]
	str x4, [x3, #840]
	ldr x4, [x3, #1616]
	str x4, [x3, #848]
	ldr x4, [x3, #1624]
	str x4, [x3, #856]
	ldr x4, [x3, #1632]
	str x4, [x3, #864]
	ldr x4, [x3, #1640]
	str x4, [x3, #872]
	ldr x4, [x3, #1648]
	str x4, [x3, #880]
	ldr x4, [x3, #1656]
	str x4, [x3, #888]
	add x0, x1, #0
	add x1, x3, #0
	sub x19, x0, x3
27:
	cbnz x19, 22b
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2624]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2632]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2640]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2648]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2656]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2664]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2672]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2680]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #832, lsl #0
	movz x2, #832, lsl #0
	movz x3, #2624, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	ldr x4, [x3, #1088]
	str x4, [x3, #8064]
	ldr x4, [x3, #1096]
	str x4, [x3, #8072]
	ldr x4, [x3, #1104]
	str x4, [x3, #8080]
	ldr x4, [x3, #1112]
	str x4, [x3, #8088]
	ldr x4, [x3, #1120]
	str x4, [x3, #8096]
	ldr x4, [x3, #1128]
	str x4, [x3, #8104]
	ldr x4, [x3, #1136]
	str x4, [x3, #8112]
	ldr x4, [x3, #1144]
	str x4, [x3, #8120]
	ldr x4, [x3, #1216]
	str x4, [x3, #4864]
	ldr x4, [x3, #1224]
	str x4, [x3, #4872]
	ldr x4, [x3, #1232]
	str x4, [x3, #4880]
	ldr x4, [x3, #1240]
	str x4, [x3, #4888]
	ldr x4, [x3, #1248]
	str x4, [x3, #4896]
	ldr x4, [x3, #1256]
	str x4, [x3, #4904]
	ldr x4, [x3, #1264]
	str x4, [x3, #4912]
	ldr x4, [x3, #1272]
	str x4, [x3, #4920]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2496]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2504]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2512]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2520]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2528]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2536]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2544]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2552]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2624]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2632]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2640]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2648]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2656]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2664]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2672]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2680]
	ldr x4, [x3, #832]
	str x4, [x3, #448]
	ldr x4, [x3, #840]
	str x4, [x3, #456]
	ldr x4, [x3, #848]
	str x4, [x3, #464]
	ldr x4, [x3, #856]
	str x4, [x3, #472]
	ldr x4, [x3, #864]
	str x4, [x3, #480]
	ldr x4, [x3, #872]
	str x4, [x3, #488]
	ldr x4, [x3, #880]
	str x4, [x3, #496]
	ldr x4, [x3, #888]
	str x4, [x3, #504]
	ldr x4, [x3, #960]
	str x4, [x3, #576]
	ldr x4, [x3, #968]
	str x4, [x3, #584]
	ldr x4, [x3, #976]
	str x4, [x3, #592]
	ldr x4, [x3, #984]
	str x4, [x3, #600]
	ldr x4, [x3, #992]
	str x4, [x3, #608]
	ldr x4, [x3, #1000]
	str x4, [x3, #616]
	ldr x4, [x3, #1008]
	str x4, [x3, #624]
	ldr x4, [x3, #1016]
	str x4, [x3, #632]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #704]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #712]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #720]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #728]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #736]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #744]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #752]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #760]
	movz x19, #0, lsl #0
	lsl x8, x19, #7
	lsl x9, x19, #6
	add x8, x8, x9
	add x8, x8, x3
	ldr x4, [x3, #448]
	str x4, [x8, #4992]
	ldr x4, [x3, #456]
	str x4, [x8, #5000]
	ldr x4, [x3, #464]
	str x4, [x8, #5008]
	ldr x4, [x3, #472]
	str x4, [x8, #5016]
	ldr x4, [x3, #480]
	str x4, [x8, #5024]
	ldr x4, [x3, #488]
	str x4, [x8, #5032]
	ldr x4, [x3, #496]
	str x4, [x8, #5040]
	ldr x4, [x3, #504]
	str x4, [x8, #5048]
	ldr x4, [x3, #576]
	str x4, [x8, #5056]
	ldr x4, [x3, #584]
	str x4, [x8, #5064]
	ldr x4, [x3, #592]
	str x4, [x8, #5072]
	ldr x4, [x3, #600]
	str x4, [x8, #5080]
	ldr x4, [x3, #608]
	str x4, [x8, #5088]
	ldr x4, [x3, #616]
	str x4, [x8, #5096]
	ldr x4, [x3, #624]
	str x4, [x8, #5104]
	ldr x4, [x3, #632]
	str x4, [x8, #5112]
	ldr x4, [x3, #704]
	str x4, [x8, #5120]
	ldr x4, [x3, #712]
	str x4, [x8, #5128]
	ldr x4, [x3, #720]
	str x4, [x8, #5136]
	ldr x4, [x3, #728]
	str x4, [x8, #5144]
	ldr x4, [x3, #736]
	str x4, [x8, #5152]
	ldr x4, [x3, #744]
	str x4, [x8, #5160]
	ldr x4, [x3, #752]
	str x4, [x8, #5168]
	ldr x4, [x3, #760]
	str x4, [x8, #5176]
	add x0, x3, #0
	bl {vg_ed448_r56_point_double}
	ldr x4, [x3, #448]
	str x4, [x3, #832]
	ldr x4, [x3, #456]
	str x4, [x3, #840]
	ldr x4, [x3, #464]
	str x4, [x3, #848]
	ldr x4, [x3, #472]
	str x4, [x3, #856]
	ldr x4, [x3, #480]
	str x4, [x3, #864]
	ldr x4, [x3, #488]
	str x4, [x3, #872]
	ldr x4, [x3, #496]
	str x4, [x3, #880]
	ldr x4, [x3, #504]
	str x4, [x3, #888]
	ldr x4, [x3, #576]
	str x4, [x3, #960]
	ldr x4, [x3, #584]
	str x4, [x3, #968]
	ldr x4, [x3, #592]
	str x4, [x3, #976]
	ldr x4, [x3, #600]
	str x4, [x3, #984]
	ldr x4, [x3, #608]
	str x4, [x3, #992]
	ldr x4, [x3, #616]
	str x4, [x3, #1000]
	ldr x4, [x3, #624]
	str x4, [x3, #1008]
	ldr x4, [x3, #632]
	str x4, [x3, #1016]
	ldr x4, [x3, #704]
	str x4, [x3, #1088]
	ldr x4, [x3, #712]
	str x4, [x3, #1096]
	ldr x4, [x3, #720]
	str x4, [x3, #1104]
	ldr x4, [x3, #728]
	str x4, [x3, #1112]
	ldr x4, [x3, #736]
	str x4, [x3, #1120]
	ldr x4, [x3, #744]
	str x4, [x3, #1128]
	ldr x4, [x3, #752]
	str x4, [x3, #1136]
	ldr x4, [x3, #760]
	str x4, [x3, #1144]
	ldr x4, [x3, #4992]
	str x4, [x3, #448]
	ldr x4, [x3, #5000]
	str x4, [x3, #456]
	ldr x4, [x3, #5008]
	str x4, [x3, #464]
	ldr x4, [x3, #5016]
	str x4, [x3, #472]
	ldr x4, [x3, #5024]
	str x4, [x3, #480]
	ldr x4, [x3, #5032]
	str x4, [x3, #488]
	ldr x4, [x3, #5040]
	str x4, [x3, #496]
	ldr x4, [x3, #5048]
	str x4, [x3, #504]
	ldr x4, [x3, #5056]
	str x4, [x3, #576]
	ldr x4, [x3, #5064]
	str x4, [x3, #584]
	ldr x4, [x3, #5072]
	str x4, [x3, #592]
	ldr x4, [x3, #5080]
	str x4, [x3, #600]
	ldr x4, [x3, #5088]
	str x4, [x3, #608]
	ldr x4, [x3, #5096]
	str x4, [x3, #616]
	ldr x4, [x3, #5104]
	str x4, [x3, #624]
	ldr x4, [x3, #5112]
	str x4, [x3, #632]
	ldr x4, [x3, #5120]
	str x4, [x3, #704]
	ldr x4, [x3, #5128]
	str x4, [x3, #712]
	ldr x4, [x3, #5136]
	str x4, [x3, #720]
	ldr x4, [x3, #5144]
	str x4, [x3, #728]
	ldr x4, [x3, #5152]
	str x4, [x3, #736]
	ldr x4, [x3, #5160]
	str x4, [x3, #744]
	ldr x4, [x3, #5168]
	str x4, [x3, #752]
	ldr x4, [x3, #5176]
	str x4, [x3, #760]
	movz x19, #1, lsl #0
28:
	add x0, x3, #0
	bl {vg_ed448_r56_point_add}
	lsl x8, x19, #7
	lsl x9, x19, #6
	add x8, x8, x9
	add x8, x8, x3
	ldr x4, [x3, #448]
	str x4, [x8, #4992]
	ldr x4, [x3, #456]
	str x4, [x8, #5000]
	ldr x4, [x3, #464]
	str x4, [x8, #5008]
	ldr x4, [x3, #472]
	str x4, [x8, #5016]
	ldr x4, [x3, #480]
	str x4, [x8, #5024]
	ldr x4, [x3, #488]
	str x4, [x8, #5032]
	ldr x4, [x3, #496]
	str x4, [x8, #5040]
	ldr x4, [x3, #504]
	str x4, [x8, #5048]
	ldr x4, [x3, #576]
	str x4, [x8, #5056]
	ldr x4, [x3, #584]
	str x4, [x8, #5064]
	ldr x4, [x3, #592]
	str x4, [x8, #5072]
	ldr x4, [x3, #600]
	str x4, [x8, #5080]
	ldr x4, [x3, #608]
	str x4, [x8, #5088]
	ldr x4, [x3, #616]
	str x4, [x8, #5096]
	ldr x4, [x3, #624]
	str x4, [x8, #5104]
	ldr x4, [x3, #632]
	str x4, [x8, #5112]
	ldr x4, [x3, #704]
	str x4, [x8, #5120]
	ldr x4, [x3, #712]
	str x4, [x8, #5128]
	ldr x4, [x3, #720]
	str x4, [x8, #5136]
	ldr x4, [x3, #728]
	str x4, [x8, #5144]
	ldr x4, [x3, #736]
	str x4, [x8, #5152]
	ldr x4, [x3, #744]
	str x4, [x8, #5160]
	ldr x4, [x3, #752]
	str x4, [x8, #5168]
	ldr x4, [x3, #760]
	str x4, [x8, #5176]
	add x19, x19, #1
	sub x9, x19, #8
	cbnz x9, 28b
	movz x4, #0, lsl #0
	str x4, [x3, #3528]
	movz x19, #0, lsl #0
	movz x6, #128, lsl #0
29:
	add x2, x3, x19
	ldrb w4, [x2, #3079]
	ldrb w5, [x2, #3078]
	lsl x4, x4, #1
	add x4, x4, x5
	ldrb w5, [x2, #3077]
	lsl x4, x4, #1
	add x4, x4, x5
	ldrb w5, [x2, #3076]
	lsl x4, x4, #1
	add x4, x4, x5
	ldrb w5, [x2, #3075]
	lsl x4, x4, #1
	add x4, x4, x5
	ldrb w5, [x2, #3074]
	lsl x4, x4, #1
	add x4, x4, x5
	ldrb w5, [x2, #3073]
	lsl x4, x4, #1
	add x4, x4, x5
	ldrb w5, [x2, #3072]
	lsl x4, x4, #1
	add x4, x4, x5
	add x4, x4, x6
	add x4, x4, #128
	movz x8, #255, lsl #0
	and x4, x4, x8
	sub x7, x4, #256
	movz x8, #128, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #128
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	sub x9, x19, #456
	cbnz x9, 29b
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #128
	movz x8, #255, lsl #0
	and x4, x4, x8
	sub x7, x4, #256
	movz x8, #128, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #128
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #128
	movz x8, #255, lsl #0
	and x4, x4, x8
	sub x7, x4, #256
	movz x8, #128, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #128
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #128
	movz x8, #255, lsl #0
	and x4, x4, x8
	sub x7, x4, #256
	movz x8, #128, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #128
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #128
	movz x8, #255, lsl #0
	and x4, x4, x8
	sub x7, x4, #256
	movz x8, #128, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #128
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #128
	movz x8, #255, lsl #0
	and x4, x4, x8
	sub x7, x4, #256
	movz x8, #128, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #128
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #128
	movz x8, #255, lsl #0
	and x4, x4, x8
	sub x7, x4, #256
	movz x8, #128, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #128
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #128
	movz x8, #255, lsl #0
	and x4, x4, x8
	sub x7, x4, #256
	movz x8, #128, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #128
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #128
	movz x8, #255, lsl #0
	and x4, x4, x8
	sub x7, x4, #256
	movz x8, #128, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #128
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x10, x3, #3400
	add x10, x10, #3400
	ldrb w4, [x3, #3072]
	strb w4, [x10, #0]
	ldrb w4, [x3, #3073]
	strb w4, [x10, #1]
	ldrb w4, [x3, #3074]
	strb w4, [x10, #2]
	ldrb w4, [x3, #3075]
	strb w4, [x10, #3]
	ldrb w4, [x3, #3076]
	strb w4, [x10, #4]
	ldrb w4, [x3, #3077]
	strb w4, [x10, #5]
	ldrb w4, [x3, #3078]
	strb w4, [x10, #6]
	ldrb w4, [x3, #3079]
	strb w4, [x10, #7]
	ldrb w4, [x3, #3080]
	strb w4, [x10, #8]
	ldrb w4, [x3, #3081]
	strb w4, [x10, #9]
	ldrb w4, [x3, #3082]
	strb w4, [x10, #10]
	ldrb w4, [x3, #3083]
	strb w4, [x10, #11]
	ldrb w4, [x3, #3084]
	strb w4, [x10, #12]
	ldrb w4, [x3, #3085]
	strb w4, [x10, #13]
	ldrb w4, [x3, #3086]
	strb w4, [x10, #14]
	ldrb w4, [x3, #3087]
	strb w4, [x10, #15]
	ldrb w4, [x3, #3088]
	strb w4, [x10, #16]
	ldrb w4, [x3, #3089]
	strb w4, [x10, #17]
	ldrb w4, [x3, #3090]
	strb w4, [x10, #18]
	ldrb w4, [x3, #3091]
	strb w4, [x10, #19]
	ldrb w4, [x3, #3092]
	strb w4, [x10, #20]
	ldrb w4, [x3, #3093]
	strb w4, [x10, #21]
	ldrb w4, [x3, #3094]
	strb w4, [x10, #22]
	ldrb w4, [x3, #3095]
	strb w4, [x10, #23]
	ldrb w4, [x3, #3096]
	strb w4, [x10, #24]
	ldrb w4, [x3, #3097]
	strb w4, [x10, #25]
	ldrb w4, [x3, #3098]
	strb w4, [x10, #26]
	ldrb w4, [x3, #3099]
	strb w4, [x10, #27]
	ldrb w4, [x3, #3100]
	strb w4, [x10, #28]
	ldrb w4, [x3, #3101]
	strb w4, [x10, #29]
	ldrb w4, [x3, #3102]
	strb w4, [x10, #30]
	ldrb w4, [x3, #3103]
	strb w4, [x10, #31]
	ldrb w4, [x3, #3104]
	strb w4, [x10, #32]
	ldrb w4, [x3, #3105]
	strb w4, [x10, #33]
	ldrb w4, [x3, #3106]
	strb w4, [x10, #34]
	ldrb w4, [x3, #3107]
	strb w4, [x10, #35]
	ldrb w4, [x3, #3108]
	strb w4, [x10, #36]
	ldrb w4, [x3, #3109]
	strb w4, [x10, #37]
	ldrb w4, [x3, #3110]
	strb w4, [x10, #38]
	ldrb w4, [x3, #3111]
	strb w4, [x10, #39]
	ldrb w4, [x3, #3112]
	strb w4, [x10, #40]
	ldrb w4, [x3, #3113]
	strb w4, [x10, #41]
	ldrb w4, [x3, #3114]
	strb w4, [x10, #42]
	ldrb w4, [x3, #3115]
	strb w4, [x10, #43]
	ldrb w4, [x3, #3116]
	strb w4, [x10, #44]
	ldrb w4, [x3, #3117]
	strb w4, [x10, #45]
	ldrb w4, [x3, #3118]
	strb w4, [x10, #46]
	ldrb w4, [x3, #3119]
	strb w4, [x10, #47]
	ldrb w4, [x3, #3120]
	strb w4, [x10, #48]
	ldrb w4, [x3, #3121]
	strb w4, [x10, #49]
	ldrb w4, [x3, #3122]
	strb w4, [x10, #50]
	ldrb w4, [x3, #3123]
	strb w4, [x10, #51]
	ldrb w4, [x3, #3124]
	strb w4, [x10, #52]
	ldrb w4, [x3, #3125]
	strb w4, [x10, #53]
	ldrb w4, [x3, #3126]
	strb w4, [x10, #54]
	ldrb w4, [x3, #3127]
	strb w4, [x10, #55]
	ldrb w4, [x3, #3128]
	strb w4, [x10, #56]
	ldrb w4, [x3, #3129]
	strb w4, [x10, #57]
	ldrb w4, [x3, #3130]
	strb w4, [x10, #58]
	ldrb w4, [x3, #3131]
	strb w4, [x10, #59]
	ldrb w4, [x3, #3132]
	strb w4, [x10, #60]
	ldrb w4, [x3, #3133]
	strb w4, [x10, #61]
	ldrb w4, [x3, #3134]
	strb w4, [x10, #62]
	ldrb w4, [x3, #3135]
	strb w4, [x10, #63]
	ldrb w4, [x3, #3136]
	strb w4, [x10, #64]
	ldrb w4, [x3, #3137]
	strb w4, [x10, #65]
	ldrb w4, [x3, #3138]
	strb w4, [x10, #66]
	ldrb w4, [x3, #3139]
	strb w4, [x10, #67]
	ldrb w4, [x3, #3140]
	strb w4, [x10, #68]
	ldrb w4, [x3, #3141]
	strb w4, [x10, #69]
	ldrb w4, [x3, #3142]
	strb w4, [x10, #70]
	ldrb w4, [x3, #3143]
	strb w4, [x10, #71]
	ldrb w4, [x3, #3144]
	strb w4, [x10, #72]
	ldrb w4, [x3, #3145]
	strb w4, [x10, #73]
	ldrb w4, [x3, #3146]
	strb w4, [x10, #74]
	ldrb w4, [x3, #3147]
	strb w4, [x10, #75]
	ldrb w4, [x3, #3148]
	strb w4, [x10, #76]
	ldrb w4, [x3, #3149]
	strb w4, [x10, #77]
	ldrb w4, [x3, #3150]
	strb w4, [x10, #78]
	ldrb w4, [x3, #3151]
	strb w4, [x10, #79]
	ldrb w4, [x3, #3152]
	strb w4, [x10, #80]
	ldrb w4, [x3, #3153]
	strb w4, [x10, #81]
	ldrb w4, [x3, #3154]
	strb w4, [x10, #82]
	ldrb w4, [x3, #3155]
	strb w4, [x10, #83]
	ldrb w4, [x3, #3156]
	strb w4, [x10, #84]
	ldrb w4, [x3, #3157]
	strb w4, [x10, #85]
	ldrb w4, [x3, #3158]
	strb w4, [x10, #86]
	ldrb w4, [x3, #3159]
	strb w4, [x10, #87]
	ldrb w4, [x3, #3160]
	strb w4, [x10, #88]
	ldrb w4, [x3, #3161]
	strb w4, [x10, #89]
	ldrb w4, [x3, #3162]
	strb w4, [x10, #90]
	ldrb w4, [x3, #3163]
	strb w4, [x10, #91]
	ldrb w4, [x3, #3164]
	strb w4, [x10, #92]
	ldrb w4, [x3, #3165]
	strb w4, [x10, #93]
	ldrb w4, [x3, #3166]
	strb w4, [x10, #94]
	ldrb w4, [x3, #3167]
	strb w4, [x10, #95]
	ldrb w4, [x3, #3168]
	strb w4, [x10, #96]
	ldrb w4, [x3, #3169]
	strb w4, [x10, #97]
	ldrb w4, [x3, #3170]
	strb w4, [x10, #98]
	ldrb w4, [x3, #3171]
	strb w4, [x10, #99]
	ldrb w4, [x3, #3172]
	strb w4, [x10, #100]
	ldrb w4, [x3, #3173]
	strb w4, [x10, #101]
	ldrb w4, [x3, #3174]
	strb w4, [x10, #102]
	ldrb w4, [x3, #3175]
	strb w4, [x10, #103]
	ldrb w4, [x3, #3176]
	strb w4, [x10, #104]
	ldrb w4, [x3, #3177]
	strb w4, [x10, #105]
	ldrb w4, [x3, #3178]
	strb w4, [x10, #106]
	ldrb w4, [x3, #3179]
	strb w4, [x10, #107]
	ldrb w4, [x3, #3180]
	strb w4, [x10, #108]
	ldrb w4, [x3, #3181]
	strb w4, [x10, #109]
	ldrb w4, [x3, #3182]
	strb w4, [x10, #110]
	ldrb w4, [x3, #3183]
	strb w4, [x10, #111]
	ldrb w4, [x3, #3184]
	strb w4, [x10, #112]
	ldrb w4, [x3, #3185]
	strb w4, [x10, #113]
	ldrb w4, [x3, #3186]
	strb w4, [x10, #114]
	ldrb w4, [x3, #3187]
	strb w4, [x10, #115]
	ldrb w4, [x3, #3188]
	strb w4, [x10, #116]
	ldrb w4, [x3, #3189]
	strb w4, [x10, #117]
	ldrb w4, [x3, #3190]
	strb w4, [x10, #118]
	ldrb w4, [x3, #3191]
	strb w4, [x10, #119]
	ldrb w4, [x3, #3192]
	strb w4, [x10, #120]
	ldrb w4, [x3, #3193]
	strb w4, [x10, #121]
	ldrb w4, [x3, #3194]
	strb w4, [x10, #122]
	ldrb w4, [x3, #3195]
	strb w4, [x10, #123]
	ldrb w4, [x3, #3196]
	strb w4, [x10, #124]
	ldrb w4, [x3, #3197]
	strb w4, [x10, #125]
	ldrb w4, [x3, #3198]
	strb w4, [x10, #126]
	ldrb w4, [x3, #3199]
	strb w4, [x10, #127]
	ldrb w4, [x3, #3200]
	strb w4, [x10, #128]
	ldrb w4, [x3, #3201]
	strb w4, [x10, #129]
	ldrb w4, [x3, #3202]
	strb w4, [x10, #130]
	ldrb w4, [x3, #3203]
	strb w4, [x10, #131]
	ldrb w4, [x3, #3204]
	strb w4, [x10, #132]
	ldrb w4, [x3, #3205]
	strb w4, [x10, #133]
	ldrb w4, [x3, #3206]
	strb w4, [x10, #134]
	ldrb w4, [x3, #3207]
	strb w4, [x10, #135]
	ldrb w4, [x3, #3208]
	strb w4, [x10, #136]
	ldrb w4, [x3, #3209]
	strb w4, [x10, #137]
	ldrb w4, [x3, #3210]
	strb w4, [x10, #138]
	ldrb w4, [x3, #3211]
	strb w4, [x10, #139]
	ldrb w4, [x3, #3212]
	strb w4, [x10, #140]
	ldrb w4, [x3, #3213]
	strb w4, [x10, #141]
	ldrb w4, [x3, #3214]
	strb w4, [x10, #142]
	ldrb w4, [x3, #3215]
	strb w4, [x10, #143]
	ldrb w4, [x3, #3216]
	strb w4, [x10, #144]
	ldrb w4, [x3, #3217]
	strb w4, [x10, #145]
	ldrb w4, [x3, #3218]
	strb w4, [x10, #146]
	ldrb w4, [x3, #3219]
	strb w4, [x10, #147]
	ldrb w4, [x3, #3220]
	strb w4, [x10, #148]
	ldrb w4, [x3, #3221]
	strb w4, [x10, #149]
	ldrb w4, [x3, #3222]
	strb w4, [x10, #150]
	ldrb w4, [x3, #3223]
	strb w4, [x10, #151]
	ldrb w4, [x3, #3224]
	strb w4, [x10, #152]
	ldrb w4, [x3, #3225]
	strb w4, [x10, #153]
	ldrb w4, [x3, #3226]
	strb w4, [x10, #154]
	ldrb w4, [x3, #3227]
	strb w4, [x10, #155]
	ldrb w4, [x3, #3228]
	strb w4, [x10, #156]
	ldrb w4, [x3, #3229]
	strb w4, [x10, #157]
	ldrb w4, [x3, #3230]
	strb w4, [x10, #158]
	ldrb w4, [x3, #3231]
	strb w4, [x10, #159]
	ldrb w4, [x3, #3232]
	strb w4, [x10, #160]
	ldrb w4, [x3, #3233]
	strb w4, [x10, #161]
	ldrb w4, [x3, #3234]
	strb w4, [x10, #162]
	ldrb w4, [x3, #3235]
	strb w4, [x10, #163]
	ldrb w4, [x3, #3236]
	strb w4, [x10, #164]
	ldrb w4, [x3, #3237]
	strb w4, [x10, #165]
	ldrb w4, [x3, #3238]
	strb w4, [x10, #166]
	ldrb w4, [x3, #3239]
	strb w4, [x10, #167]
	ldrb w4, [x3, #3240]
	strb w4, [x10, #168]
	ldrb w4, [x3, #3241]
	strb w4, [x10, #169]
	ldrb w4, [x3, #3242]
	strb w4, [x10, #170]
	ldrb w4, [x3, #3243]
	strb w4, [x10, #171]
	ldrb w4, [x3, #3244]
	strb w4, [x10, #172]
	ldrb w4, [x3, #3245]
	strb w4, [x10, #173]
	ldrb w4, [x3, #3246]
	strb w4, [x10, #174]
	ldrb w4, [x3, #3247]
	strb w4, [x10, #175]
	ldrb w4, [x3, #3248]
	strb w4, [x10, #176]
	ldrb w4, [x3, #3249]
	strb w4, [x10, #177]
	ldrb w4, [x3, #3250]
	strb w4, [x10, #178]
	ldrb w4, [x3, #3251]
	strb w4, [x10, #179]
	ldrb w4, [x3, #3252]
	strb w4, [x10, #180]
	ldrb w4, [x3, #3253]
	strb w4, [x10, #181]
	ldrb w4, [x3, #3254]
	strb w4, [x10, #182]
	ldrb w4, [x3, #3255]
	strb w4, [x10, #183]
	ldrb w4, [x3, #3256]
	strb w4, [x10, #184]
	ldrb w4, [x3, #3257]
	strb w4, [x10, #185]
	ldrb w4, [x3, #3258]
	strb w4, [x10, #186]
	ldrb w4, [x3, #3259]
	strb w4, [x10, #187]
	ldrb w4, [x3, #3260]
	strb w4, [x10, #188]
	ldrb w4, [x3, #3261]
	strb w4, [x10, #189]
	ldrb w4, [x3, #3262]
	strb w4, [x10, #190]
	ldrb w4, [x3, #3263]
	strb w4, [x10, #191]
	ldrb w4, [x3, #3264]
	strb w4, [x10, #192]
	ldrb w4, [x3, #3265]
	strb w4, [x10, #193]
	ldrb w4, [x3, #3266]
	strb w4, [x10, #194]
	ldrb w4, [x3, #3267]
	strb w4, [x10, #195]
	ldrb w4, [x3, #3268]
	strb w4, [x10, #196]
	ldrb w4, [x3, #3269]
	strb w4, [x10, #197]
	ldrb w4, [x3, #3270]
	strb w4, [x10, #198]
	ldrb w4, [x3, #3271]
	strb w4, [x10, #199]
	ldrb w4, [x3, #3272]
	strb w4, [x10, #200]
	ldrb w4, [x3, #3273]
	strb w4, [x10, #201]
	ldrb w4, [x3, #3274]
	strb w4, [x10, #202]
	ldrb w4, [x3, #3275]
	strb w4, [x10, #203]
	ldrb w4, [x3, #3276]
	strb w4, [x10, #204]
	ldrb w4, [x3, #3277]
	strb w4, [x10, #205]
	ldrb w4, [x3, #3278]
	strb w4, [x10, #206]
	ldrb w4, [x3, #3279]
	strb w4, [x10, #207]
	ldrb w4, [x3, #3280]
	strb w4, [x10, #208]
	ldrb w4, [x3, #3281]
	strb w4, [x10, #209]
	ldrb w4, [x3, #3282]
	strb w4, [x10, #210]
	ldrb w4, [x3, #3283]
	strb w4, [x10, #211]
	ldrb w4, [x3, #3284]
	strb w4, [x10, #212]
	ldrb w4, [x3, #3285]
	strb w4, [x10, #213]
	ldrb w4, [x3, #3286]
	strb w4, [x10, #214]
	ldrb w4, [x3, #3287]
	strb w4, [x10, #215]
	ldrb w4, [x3, #3288]
	strb w4, [x10, #216]
	ldrb w4, [x3, #3289]
	strb w4, [x10, #217]
	ldrb w4, [x3, #3290]
	strb w4, [x10, #218]
	ldrb w4, [x3, #3291]
	strb w4, [x10, #219]
	ldrb w4, [x3, #3292]
	strb w4, [x10, #220]
	ldrb w4, [x3, #3293]
	strb w4, [x10, #221]
	ldrb w4, [x3, #3294]
	strb w4, [x10, #222]
	ldrb w4, [x3, #3295]
	strb w4, [x10, #223]
	ldrb w4, [x3, #3296]
	strb w4, [x10, #224]
	ldrb w4, [x3, #3297]
	strb w4, [x10, #225]
	ldrb w4, [x3, #3298]
	strb w4, [x10, #226]
	ldrb w4, [x3, #3299]
	strb w4, [x10, #227]
	ldrb w4, [x3, #3300]
	strb w4, [x10, #228]
	ldrb w4, [x3, #3301]
	strb w4, [x10, #229]
	ldrb w4, [x3, #3302]
	strb w4, [x10, #230]
	ldrb w4, [x3, #3303]
	strb w4, [x10, #231]
	ldrb w4, [x3, #3304]
	strb w4, [x10, #232]
	ldrb w4, [x3, #3305]
	strb w4, [x10, #233]
	ldrb w4, [x3, #3306]
	strb w4, [x10, #234]
	ldrb w4, [x3, #3307]
	strb w4, [x10, #235]
	ldrb w4, [x3, #3308]
	strb w4, [x10, #236]
	ldrb w4, [x3, #3309]
	strb w4, [x10, #237]
	ldrb w4, [x3, #3310]
	strb w4, [x10, #238]
	ldrb w4, [x3, #3311]
	strb w4, [x10, #239]
	ldrb w4, [x3, #3312]
	strb w4, [x10, #240]
	ldrb w4, [x3, #3313]
	strb w4, [x10, #241]
	ldrb w4, [x3, #3314]
	strb w4, [x10, #242]
	ldrb w4, [x3, #3315]
	strb w4, [x10, #243]
	ldrb w4, [x3, #3316]
	strb w4, [x10, #244]
	ldrb w4, [x3, #3317]
	strb w4, [x10, #245]
	ldrb w4, [x3, #3318]
	strb w4, [x10, #246]
	ldrb w4, [x3, #3319]
	strb w4, [x10, #247]
	ldrb w4, [x3, #3320]
	strb w4, [x10, #248]
	ldrb w4, [x3, #3321]
	strb w4, [x10, #249]
	ldrb w4, [x3, #3322]
	strb w4, [x10, #250]
	ldrb w4, [x3, #3323]
	strb w4, [x10, #251]
	ldrb w4, [x3, #3324]
	strb w4, [x10, #252]
	ldrb w4, [x3, #3325]
	strb w4, [x10, #253]
	ldrb w4, [x3, #3326]
	strb w4, [x10, #254]
	ldrb w4, [x3, #3327]
	strb w4, [x10, #255]
	ldrb w4, [x3, #3328]
	strb w4, [x10, #256]
	ldrb w4, [x3, #3329]
	strb w4, [x10, #257]
	ldrb w4, [x3, #3330]
	strb w4, [x10, #258]
	ldrb w4, [x3, #3331]
	strb w4, [x10, #259]
	ldrb w4, [x3, #3332]
	strb w4, [x10, #260]
	ldrb w4, [x3, #3333]
	strb w4, [x10, #261]
	ldrb w4, [x3, #3334]
	strb w4, [x10, #262]
	ldrb w4, [x3, #3335]
	strb w4, [x10, #263]
	ldrb w4, [x3, #3336]
	strb w4, [x10, #264]
	ldrb w4, [x3, #3337]
	strb w4, [x10, #265]
	ldrb w4, [x3, #3338]
	strb w4, [x10, #266]
	ldrb w4, [x3, #3339]
	strb w4, [x10, #267]
	ldrb w4, [x3, #3340]
	strb w4, [x10, #268]
	ldrb w4, [x3, #3341]
	strb w4, [x10, #269]
	ldrb w4, [x3, #3342]
	strb w4, [x10, #270]
	ldrb w4, [x3, #3343]
	strb w4, [x10, #271]
	ldrb w4, [x3, #3344]
	strb w4, [x10, #272]
	ldrb w4, [x3, #3345]
	strb w4, [x10, #273]
	ldrb w4, [x3, #3346]
	strb w4, [x10, #274]
	ldrb w4, [x3, #3347]
	strb w4, [x10, #275]
	ldrb w4, [x3, #3348]
	strb w4, [x10, #276]
	ldrb w4, [x3, #3349]
	strb w4, [x10, #277]
	ldrb w4, [x3, #3350]
	strb w4, [x10, #278]
	ldrb w4, [x3, #3351]
	strb w4, [x10, #279]
	ldrb w4, [x3, #3352]
	strb w4, [x10, #280]
	ldrb w4, [x3, #3353]
	strb w4, [x10, #281]
	ldrb w4, [x3, #3354]
	strb w4, [x10, #282]
	ldrb w4, [x3, #3355]
	strb w4, [x10, #283]
	ldrb w4, [x3, #3356]
	strb w4, [x10, #284]
	ldrb w4, [x3, #3357]
	strb w4, [x10, #285]
	ldrb w4, [x3, #3358]
	strb w4, [x10, #286]
	ldrb w4, [x3, #3359]
	strb w4, [x10, #287]
	ldrb w4, [x3, #3360]
	strb w4, [x10, #288]
	ldrb w4, [x3, #3361]
	strb w4, [x10, #289]
	ldrb w4, [x3, #3362]
	strb w4, [x10, #290]
	ldrb w4, [x3, #3363]
	strb w4, [x10, #291]
	ldrb w4, [x3, #3364]
	strb w4, [x10, #292]
	ldrb w4, [x3, #3365]
	strb w4, [x10, #293]
	ldrb w4, [x3, #3366]
	strb w4, [x10, #294]
	ldrb w4, [x3, #3367]
	strb w4, [x10, #295]
	ldrb w4, [x3, #3368]
	strb w4, [x10, #296]
	ldrb w4, [x3, #3369]
	strb w4, [x10, #297]
	ldrb w4, [x3, #3370]
	strb w4, [x10, #298]
	ldrb w4, [x3, #3371]
	strb w4, [x10, #299]
	ldrb w4, [x3, #3372]
	strb w4, [x10, #300]
	ldrb w4, [x3, #3373]
	strb w4, [x10, #301]
	ldrb w4, [x3, #3374]
	strb w4, [x10, #302]
	ldrb w4, [x3, #3375]
	strb w4, [x10, #303]
	ldrb w4, [x3, #3376]
	strb w4, [x10, #304]
	ldrb w4, [x3, #3377]
	strb w4, [x10, #305]
	ldrb w4, [x3, #3378]
	strb w4, [x10, #306]
	ldrb w4, [x3, #3379]
	strb w4, [x10, #307]
	ldrb w4, [x3, #3380]
	strb w4, [x10, #308]
	ldrb w4, [x3, #3381]
	strb w4, [x10, #309]
	ldrb w4, [x3, #3382]
	strb w4, [x10, #310]
	ldrb w4, [x3, #3383]
	strb w4, [x10, #311]
	ldrb w4, [x3, #3384]
	strb w4, [x10, #312]
	ldrb w4, [x3, #3385]
	strb w4, [x10, #313]
	ldrb w4, [x3, #3386]
	strb w4, [x10, #314]
	ldrb w4, [x3, #3387]
	strb w4, [x10, #315]
	ldrb w4, [x3, #3388]
	strb w4, [x10, #316]
	ldrb w4, [x3, #3389]
	strb w4, [x10, #317]
	ldrb w4, [x3, #3390]
	strb w4, [x10, #318]
	ldrb w4, [x3, #3391]
	strb w4, [x10, #319]
	ldrb w4, [x3, #3392]
	strb w4, [x10, #320]
	ldrb w4, [x3, #3393]
	strb w4, [x10, #321]
	ldrb w4, [x3, #3394]
	strb w4, [x10, #322]
	ldrb w4, [x3, #3395]
	strb w4, [x10, #323]
	ldrb w4, [x3, #3396]
	strb w4, [x10, #324]
	ldrb w4, [x3, #3397]
	strb w4, [x10, #325]
	ldrb w4, [x3, #3398]
	strb w4, [x10, #326]
	ldrb w4, [x3, #3399]
	strb w4, [x10, #327]
	ldrb w4, [x3, #3400]
	strb w4, [x10, #328]
	ldrb w4, [x3, #3401]
	strb w4, [x10, #329]
	ldrb w4, [x3, #3402]
	strb w4, [x10, #330]
	ldrb w4, [x3, #3403]
	strb w4, [x10, #331]
	ldrb w4, [x3, #3404]
	strb w4, [x10, #332]
	ldrb w4, [x3, #3405]
	strb w4, [x10, #333]
	ldrb w4, [x3, #3406]
	strb w4, [x10, #334]
	ldrb w4, [x3, #3407]
	strb w4, [x10, #335]
	ldrb w4, [x3, #3408]
	strb w4, [x10, #336]
	ldrb w4, [x3, #3409]
	strb w4, [x10, #337]
	ldrb w4, [x3, #3410]
	strb w4, [x10, #338]
	ldrb w4, [x3, #3411]
	strb w4, [x10, #339]
	ldrb w4, [x3, #3412]
	strb w4, [x10, #340]
	ldrb w4, [x3, #3413]
	strb w4, [x10, #341]
	ldrb w4, [x3, #3414]
	strb w4, [x10, #342]
	ldrb w4, [x3, #3415]
	strb w4, [x10, #343]
	ldrb w4, [x3, #3416]
	strb w4, [x10, #344]
	ldrb w4, [x3, #3417]
	strb w4, [x10, #345]
	ldrb w4, [x3, #3418]
	strb w4, [x10, #346]
	ldrb w4, [x3, #3419]
	strb w4, [x10, #347]
	ldrb w4, [x3, #3420]
	strb w4, [x10, #348]
	ldrb w4, [x3, #3421]
	strb w4, [x10, #349]
	ldrb w4, [x3, #3422]
	strb w4, [x10, #350]
	ldrb w4, [x3, #3423]
	strb w4, [x10, #351]
	ldrb w4, [x3, #3424]
	strb w4, [x10, #352]
	ldrb w4, [x3, #3425]
	strb w4, [x10, #353]
	ldrb w4, [x3, #3426]
	strb w4, [x10, #354]
	ldrb w4, [x3, #3427]
	strb w4, [x10, #355]
	ldrb w4, [x3, #3428]
	strb w4, [x10, #356]
	ldrb w4, [x3, #3429]
	strb w4, [x10, #357]
	ldrb w4, [x3, #3430]
	strb w4, [x10, #358]
	ldrb w4, [x3, #3431]
	strb w4, [x10, #359]
	ldrb w4, [x3, #3432]
	strb w4, [x10, #360]
	ldrb w4, [x3, #3433]
	strb w4, [x10, #361]
	ldrb w4, [x3, #3434]
	strb w4, [x10, #362]
	ldrb w4, [x3, #3435]
	strb w4, [x10, #363]
	ldrb w4, [x3, #3436]
	strb w4, [x10, #364]
	ldrb w4, [x3, #3437]
	strb w4, [x10, #365]
	ldrb w4, [x3, #3438]
	strb w4, [x10, #366]
	ldrb w4, [x3, #3439]
	strb w4, [x10, #367]
	ldrb w4, [x3, #3440]
	strb w4, [x10, #368]
	ldrb w4, [x3, #3441]
	strb w4, [x10, #369]
	ldrb w4, [x3, #3442]
	strb w4, [x10, #370]
	ldrb w4, [x3, #3443]
	strb w4, [x10, #371]
	ldrb w4, [x3, #3444]
	strb w4, [x10, #372]
	ldrb w4, [x3, #3445]
	strb w4, [x10, #373]
	ldrb w4, [x3, #3446]
	strb w4, [x10, #374]
	ldrb w4, [x3, #3447]
	strb w4, [x10, #375]
	ldrb w4, [x3, #3448]
	strb w4, [x10, #376]
	ldrb w4, [x3, #3449]
	strb w4, [x10, #377]
	ldrb w4, [x3, #3450]
	strb w4, [x10, #378]
	ldrb w4, [x3, #3451]
	strb w4, [x10, #379]
	ldrb w4, [x3, #3452]
	strb w4, [x10, #380]
	ldrb w4, [x3, #3453]
	strb w4, [x10, #381]
	ldrb w4, [x3, #3454]
	strb w4, [x10, #382]
	ldrb w4, [x3, #3455]
	strb w4, [x10, #383]
	ldrb w4, [x3, #3456]
	strb w4, [x10, #384]
	ldrb w4, [x3, #3457]
	strb w4, [x10, #385]
	ldrb w4, [x3, #3458]
	strb w4, [x10, #386]
	ldrb w4, [x3, #3459]
	strb w4, [x10, #387]
	ldrb w4, [x3, #3460]
	strb w4, [x10, #388]
	ldrb w4, [x3, #3461]
	strb w4, [x10, #389]
	ldrb w4, [x3, #3462]
	strb w4, [x10, #390]
	ldrb w4, [x3, #3463]
	strb w4, [x10, #391]
	ldrb w4, [x3, #3464]
	strb w4, [x10, #392]
	ldrb w4, [x3, #3465]
	strb w4, [x10, #393]
	ldrb w4, [x3, #3466]
	strb w4, [x10, #394]
	ldrb w4, [x3, #3467]
	strb w4, [x10, #395]
	ldrb w4, [x3, #3468]
	strb w4, [x10, #396]
	ldrb w4, [x3, #3469]
	strb w4, [x10, #397]
	ldrb w4, [x3, #3470]
	strb w4, [x10, #398]
	ldrb w4, [x3, #3471]
	strb w4, [x10, #399]
	ldrb w4, [x3, #3472]
	strb w4, [x10, #400]
	ldrb w4, [x3, #3473]
	strb w4, [x10, #401]
	ldrb w4, [x3, #3474]
	strb w4, [x10, #402]
	ldrb w4, [x3, #3475]
	strb w4, [x10, #403]
	ldrb w4, [x3, #3476]
	strb w4, [x10, #404]
	ldrb w4, [x3, #3477]
	strb w4, [x10, #405]
	ldrb w4, [x3, #3478]
	strb w4, [x10, #406]
	ldrb w4, [x3, #3479]
	strb w4, [x10, #407]
	ldrb w4, [x3, #3480]
	strb w4, [x10, #408]
	ldrb w4, [x3, #3481]
	strb w4, [x10, #409]
	ldrb w4, [x3, #3482]
	strb w4, [x10, #410]
	ldrb w4, [x3, #3483]
	strb w4, [x10, #411]
	ldrb w4, [x3, #3484]
	strb w4, [x10, #412]
	ldrb w4, [x3, #3485]
	strb w4, [x10, #413]
	ldrb w4, [x3, #3486]
	strb w4, [x10, #414]
	ldrb w4, [x3, #3487]
	strb w4, [x10, #415]
	ldrb w4, [x3, #3488]
	strb w4, [x10, #416]
	ldrb w4, [x3, #3489]
	strb w4, [x10, #417]
	ldrb w4, [x3, #3490]
	strb w4, [x10, #418]
	ldrb w4, [x3, #3491]
	strb w4, [x10, #419]
	ldrb w4, [x3, #3492]
	strb w4, [x10, #420]
	ldrb w4, [x3, #3493]
	strb w4, [x10, #421]
	ldrb w4, [x3, #3494]
	strb w4, [x10, #422]
	ldrb w4, [x3, #3495]
	strb w4, [x10, #423]
	ldrb w4, [x3, #3496]
	strb w4, [x10, #424]
	ldrb w4, [x3, #3497]
	strb w4, [x10, #425]
	ldrb w4, [x3, #3498]
	strb w4, [x10, #426]
	ldrb w4, [x3, #3499]
	strb w4, [x10, #427]
	ldrb w4, [x3, #3500]
	strb w4, [x10, #428]
	ldrb w4, [x3, #3501]
	strb w4, [x10, #429]
	ldrb w4, [x3, #3502]
	strb w4, [x10, #430]
	ldrb w4, [x3, #3503]
	strb w4, [x10, #431]
	ldrb w4, [x3, #3504]
	strb w4, [x10, #432]
	ldrb w4, [x3, #3505]
	strb w4, [x10, #433]
	ldrb w4, [x3, #3506]
	strb w4, [x10, #434]
	ldrb w4, [x3, #3507]
	strb w4, [x10, #435]
	ldrb w4, [x3, #3508]
	strb w4, [x10, #436]
	ldrb w4, [x3, #3509]
	strb w4, [x10, #437]
	ldrb w4, [x3, #3510]
	strb w4, [x10, #438]
	ldrb w4, [x3, #3511]
	strb w4, [x10, #439]
	ldrb w4, [x3, #3512]
	strb w4, [x10, #440]
	ldrb w4, [x3, #3513]
	strb w4, [x10, #441]
	ldrb w4, [x3, #3514]
	strb w4, [x10, #442]
	ldrb w4, [x3, #3515]
	strb w4, [x10, #443]
	ldrb w4, [x3, #3516]
	strb w4, [x10, #444]
	ldrb w4, [x3, #3517]
	strb w4, [x10, #445]
	ldrb w4, [x3, #3518]
	strb w4, [x10, #446]
	ldrb w4, [x3, #3519]
	strb w4, [x10, #447]
	ldrb w4, [x3, #3520]
	strb w4, [x10, #448]
	ldrb w4, [x3, #3521]
	strb w4, [x10, #449]
	ldrb w4, [x3, #3522]
	strb w4, [x10, #450]
	ldrb w4, [x3, #3523]
	strb w4, [x10, #451]
	ldrb w4, [x3, #3524]
	strb w4, [x10, #452]
	ldrb w4, [x3, #3525]
	strb w4, [x10, #453]
	ldrb w4, [x3, #3526]
	strb w4, [x10, #454]
	ldrb w4, [x3, #3527]
	strb w4, [x10, #455]
	ldrb w4, [x3, #3528]
	strb w4, [x10, #456]
	ldrb w4, [x3, #3529]
	strb w4, [x10, #457]
	ldrb w4, [x3, #3530]
	strb w4, [x10, #458]
	ldrb w4, [x3, #3531]
	strb w4, [x10, #459]
	ldrb w4, [x3, #3532]
	strb w4, [x10, #460]
	ldrb w4, [x3, #3533]
	strb w4, [x10, #461]
	ldrb w4, [x3, #3534]
	strb w4, [x10, #462]
	ldrb w4, [x3, #3535]
	strb w4, [x10, #463]
	movz x19, #0, lsl #0
	movz x8, #1, lsl #0
210:
	add x11, x3, x19
	ldrb w4, [x11, #2944]
	lsl x11, x19, #3
	add x11, x3, x11
	add x11, x11, #0
	lsr x5, x4, #0
	and x5, x5, x8
	strb w5, [x11, #3072]
	lsr x5, x4, #1
	and x5, x5, x8
	strb w5, [x11, #3073]
	lsr x5, x4, #2
	and x5, x5, x8
	strb w5, [x11, #3074]
	lsr x5, x4, #3
	and x5, x5, x8
	strb w5, [x11, #3075]
	lsr x5, x4, #4
	and x5, x5, x8
	strb w5, [x11, #3076]
	lsr x5, x4, #5
	and x5, x5, x8
	strb w5, [x11, #3077]
	lsr x5, x4, #6
	and x5, x5, x8
	strb w5, [x11, #3078]
	lsr x5, x4, #7
	and x5, x5, x8
	strb w5, [x11, #3079]
	add x19, x19, #1
	sub x11, x19, #57
	cbnz x11, 210b
	movz x4, #0, lsl #0
	str x4, [x3, #3528]
	movz x19, #0, lsl #0
	movz x6, #16, lsl #0
211:
	add x2, x3, x19
	ldrb w4, [x2, #3076]
	ldrb w5, [x2, #3075]
	lsl x4, x4, #1
	add x4, x4, x5
	ldrb w5, [x2, #3074]
	lsl x4, x4, #1
	add x4, x4, x5
	ldrb w5, [x2, #3073]
	lsl x4, x4, #1
	add x4, x4, x5
	ldrb w5, [x2, #3072]
	lsl x4, x4, #1
	add x4, x4, x5
	add x4, x4, x6
	add x4, x4, #16
	movz x8, #31, lsl #0
	and x4, x4, x8
	sub x7, x4, #32
	movz x8, #16, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #16
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	sub x9, x19, #456
	cbnz x9, 211b
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #16
	movz x8, #31, lsl #0
	and x4, x4, x8
	sub x7, x4, #32
	movz x8, #16, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #16
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #16
	movz x8, #31, lsl #0
	and x4, x4, x8
	sub x7, x4, #32
	movz x8, #16, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #16
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #16
	movz x8, #31, lsl #0
	and x4, x4, x8
	sub x7, x4, #32
	movz x8, #16, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #16
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #16
	movz x8, #31, lsl #0
	and x4, x4, x8
	sub x7, x4, #32
	movz x8, #16, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #16
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #16
	movz x8, #31, lsl #0
	and x4, x4, x8
	sub x7, x4, #32
	movz x8, #16, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #16
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #16
	movz x8, #31, lsl #0
	and x4, x4, x8
	sub x7, x4, #32
	movz x8, #16, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #16
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #16
	movz x8, #31, lsl #0
	and x4, x4, x8
	sub x7, x4, #32
	movz x8, #16, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #16
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	add x2, x3, x19
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	add x4, x4, x6
	add x4, x4, #16
	movz x8, #31, lsl #0
	and x4, x4, x8
	sub x7, x4, #32
	movz x8, #16, lsl #0
	tst x4, x8
	csel x7, x4, x7, eq
	movz x8, #1, lsl #0
	tst x4, x8
	movz x9, #0, lsl #0
	csel x7, x9, x7, eq
	add x6, x6, x5
	add x6, x6, #16
	sub x6, x6, x7
	lsr x6, x6, #1
	strb w7, [x2, #3072]
	add x19, x19, #1
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #448]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #456]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #464]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #472]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #480]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #488]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #496]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #504]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #576]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #584]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #592]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #600]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #608]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #616]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #624]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #632]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #704]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #712]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #720]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #728]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #736]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #744]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #752]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #760]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2496]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2504]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2512]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2520]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2528]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2536]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2544]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2552]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2624]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2632]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2640]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2648]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2656]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2664]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2672]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #2680]
	movz x19, #464, lsl #0
212:
	sub x19, x19, #1
	add x2, x3, x19
	add x2, x2, #3400
	add x2, x2, #3400
	ldrb w11, [x2, #0]
	add x7, x11, #0
	add x2, x3, x19
	ldrb w11, [x2, #3072]
	orr x9, x7, x11
	sub x4, x19, #1
	lsr x4, x4, #63
	orr x9, x9, x4
	cbz x9, 212b
	add x19, x19, #1
213:
	sub x19, x19, #1
	add x0, x3, #0
	bl {vg_ed448_r56_point_double}
	add x2, x3, x19
	add x2, x2, #3400
	add x2, x2, #3400
	ldrb w11, [x2, #0]
	cbnz x11, 214f
	b 215f
214:
	lsr x21, x11, #7
	movz x9, #256, lsl #0
	sub x9, x9, x11
	movz x8, #128, lsl #0
	tst x11, x8
	csel x11, x9, x11, ne
	lsr x11, x11, #1
	adrp x8, {VG_ED448_VERIFY_ODD_BASE}
	add x8, x8, {VG_ED448_VERIFY_ODD_BASE}
	lsl x9, x11, #7
	add x8, x8, x9
	ldr x4, [x8, #0]
	str x4, [x3, #832]
	ldr x4, [x8, #8]
	str x4, [x3, #840]
	ldr x4, [x8, #16]
	str x4, [x3, #848]
	ldr x4, [x8, #24]
	str x4, [x3, #856]
	ldr x4, [x8, #32]
	str x4, [x3, #864]
	ldr x4, [x8, #40]
	str x4, [x3, #872]
	ldr x4, [x8, #48]
	str x4, [x3, #880]
	ldr x4, [x8, #56]
	str x4, [x3, #888]
	ldr x4, [x8, #64]
	str x4, [x3, #960]
	ldr x4, [x8, #72]
	str x4, [x3, #968]
	ldr x4, [x8, #80]
	str x4, [x3, #976]
	ldr x4, [x8, #88]
	str x4, [x3, #984]
	ldr x4, [x8, #96]
	str x4, [x3, #992]
	ldr x4, [x8, #104]
	str x4, [x3, #1000]
	ldr x4, [x8, #112]
	str x4, [x3, #1008]
	ldr x4, [x8, #120]
	str x4, [x3, #1016]
	cbnz x21, 216f
	b 217f
216:
	movz x0, #65534, lsl #0
	movk x0, #65535, lsl #16
	movk x0, #65535, lsl #32
	movk x0, #511, lsl #48
	movz x2, #65532, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #511, lsl #48
	ldr x4, [x3, #2496]
	ldr x5, [x3, #832]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #832]
	ldr x4, [x3, #2504]
	ldr x5, [x3, #840]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #840]
	ldr x4, [x3, #2512]
	ldr x5, [x3, #848]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #848]
	ldr x4, [x3, #2520]
	ldr x5, [x3, #856]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #856]
	ldr x4, [x3, #2528]
	ldr x5, [x3, #864]
	add x4, x4, x2
	sub x4, x4, x5
	str x4, [x3, #864]
	ldr x4, [x3, #2536]
	ldr x5, [x3, #872]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #872]
	ldr x4, [x3, #2544]
	ldr x5, [x3, #880]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #880]
	ldr x4, [x3, #2552]
	ldr x5, [x3, #888]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #888]
217:
	str x21, [x3, #7360]
	str x22, [x3, #7368]
	str x23, [x3, #7376]
	str x24, [x3, #7384]
	str x25, [x3, #7392]
	str x26, [x3, #7400]
	str x27, [x3, #7408]
	str x28, [x3, #7416]
	movz x12, #65535, lsl #0
	movk x12, #4095, lsl #16
	ldr x0, [x3, #704]
	dup v30.2d, x12
	movi v31.2d, #0
	ldr q0, [x3, #448]
	ldr x2, [x3, #712]
	ldr q1, [x3, #576]
	trn1 v2.2d, v0.2d, v1.2d
	ldr x4, [x3, #720]
	trn2 v3.2d, v0.2d, v1.2d
	and v0.16b, v2.16b, v30.16b
	ldr x5, [x3, #728]
	ushr v1.2d, v2.2d, #28
	uzp1 v2.4s, v0.4s, v1.4s
	str q2, [x3, #4096]
	ldr x6, [x3, #736]
	and v0.16b, v3.16b, v30.16b
	ushr v1.2d, v3.2d, #28
	ldr x7, [x3, #744]
	uzp1 v3.4s, v0.4s, v1.4s
	str q3, [x3, #4112]
	ldr x8, [x3, #752]
	ldr q0, [x3, #464]
	ldr q1, [x3, #592]
	trn1 v2.2d, v0.2d, v1.2d
	ldr x9, [x3, #760]
	trn2 v3.2d, v0.2d, v1.2d
	and v0.16b, v2.16b, v30.16b
	movz x25, #65535, lsl #0
	ushr v1.2d, v2.2d, #28
	uzp1 v2.4s, v0.4s, v1.4s
	movk x25, #65535, lsl #16
	str q2, [x3, #4128]
	and v0.16b, v3.16b, v30.16b
	movk x25, #65535, lsl #32
	ushr v1.2d, v3.2d, #28
	uzp1 v3.4s, v0.4s, v1.4s
	str q3, [x3, #4144]
	movk x25, #255, lsl #48
	ldr q0, [x3, #480]
	ldr q1, [x3, #608]
	movz x26, #0, lsl #0
	trn1 v2.2d, v0.2d, v1.2d
	trn2 v3.2d, v0.2d, v1.2d
	add x10, x0, x6
	and v0.16b, v2.16b, v30.16b
	ushr v1.2d, v2.2d, #28
	uzp1 v2.4s, v0.4s, v1.4s
	add x11, x2, x7
	str q2, [x3, #4160]
	and v0.16b, v3.16b, v30.16b
	add x13, x4, x8
	ushr v1.2d, v3.2d, #28
	uzp1 v3.4s, v0.4s, v1.4s
	add x14, x5, x9
	str q3, [x3, #4176]
	ldr q0, [x3, #496]
	ldr q1, [x3, #624]
	add x15, x0, x0
	trn1 v2.2d, v0.2d, v1.2d
	trn2 v3.2d, v0.2d, v1.2d
	str x15, [x3, #3648]
	and v0.16b, v2.16b, v30.16b
	ushr v1.2d, v2.2d, #28
	add x15, x6, x6
	uzp1 v2.4s, v0.4s, v1.4s
	str q2, [x3, #4192]
	str x15, [x3, #3672]
	and v0.16b, v3.16b, v30.16b
	ushr v1.2d, v3.2d, #28
	uzp1 v3.4s, v0.4s, v1.4s
	add x15, x10, x10
	str q3, [x3, #4208]
	ldr q4, [x3, #832]
	str x15, [x3, #3696]
	ldr q5, [x3, #960]
	trn1 v6.2d, v4.2d, v5.2d
	add x15, x2, x2
	trn2 v7.2d, v4.2d, v5.2d
	and v4.16b, v6.16b, v30.16b
	ushr v5.2d, v6.2d, #28
	str x15, [x3, #3656]
	uzp1 v6.4s, v4.4s, v5.4s
	str q6, [x3, #4224]
	add x15, x7, x7
	and v4.16b, v7.16b, v30.16b
	ushr v5.2d, v7.2d, #28
	str x15, [x3, #3680]
	uzp1 v7.4s, v4.4s, v5.4s
	str q7, [x3, #4240]
	add x15, x11, x11
	ldr q4, [x3, #848]
	ldr q5, [x3, #976]
	trn1 v6.2d, v4.2d, v5.2d
	str x15, [x3, #3704]
	trn2 v7.2d, v4.2d, v5.2d
	and v4.16b, v6.16b, v30.16b
	add x15, x4, x4
	ushr v5.2d, v6.2d, #28
	uzp1 v6.4s, v4.4s, v5.4s
	str x15, [x3, #3664]
	str q6, [x3, #4256]
	and v4.16b, v7.16b, v30.16b
	ushr v5.2d, v7.2d, #28
	add x15, x8, x8
	uzp1 v7.4s, v4.4s, v5.4s
	str q7, [x3, #4272]
	str x15, [x3, #3688]
	ldr q4, [x3, #864]
	ldr q5, [x3, #992]
	add x15, x13, x13
	trn1 v6.2d, v4.2d, v5.2d
	trn2 v7.2d, v4.2d, v5.2d
	and v4.16b, v6.16b, v30.16b
	str x15, [x3, #3712]
	ushr v5.2d, v6.2d, #28
	uzp1 v6.4s, v4.4s, v5.4s
	mul x21, x6, x6
	str q6, [x3, #4288]
	and v4.16b, v7.16b, v30.16b
	umulh x22, x6, x6
	ushr v5.2d, v7.2d, #28
	uzp1 v7.4s, v4.4s, v5.4s
	ldr x17, [x3, #3680]
	str q7, [x3, #4304]
	ldr q4, [x3, #880]
	ldr q5, [x3, #1008]
	mul x27, x17, x9
	trn1 v6.2d, v4.2d, v5.2d
	trn2 v7.2d, v4.2d, v5.2d
	umulh x28, x17, x9
	and v4.16b, v6.16b, v30.16b
	ushr v5.2d, v6.2d, #28
	mul x15, x8, x8
	uzp1 v6.4s, v4.4s, v5.4s
	str q6, [x3, #4320]
	and v4.16b, v7.16b, v30.16b
	umulh x16, x8, x8
	ushr v5.2d, v7.2d, #28
	uzp1 v7.4s, v4.4s, v5.4s
	adds x27, x27, x15
	str q7, [x3, #4336]
	ldr q0, [x3, #4096]
	adc x28, x28, x16
	ldr q1, [x3, #4160]
	add v0.4s, v0.4s, v1.4s
	str q0, [x3, #4352]
	mul x15, x10, x10
	ldr q2, [x3, #4224]
	ldr q3, [x3, #4288]
	umulh x16, x10, x10
	add v2.4s, v2.4s, v3.4s
	str q2, [x3, #4416]
	adds x27, x27, x15
	ldr q0, [x3, #4112]
	ldr q1, [x3, #4176]
	adc x28, x28, x16
	add v0.4s, v0.4s, v1.4s
	str q0, [x3, #4368]
	ldr q2, [x3, #4240]
	ldr x17, [x3, #3704]
	ldr q3, [x3, #4304]
	add v2.4s, v2.4s, v3.4s
	mul x15, x17, x14
	str q2, [x3, #4432]
	ldr q0, [x3, #4128]
	umulh x16, x17, x14
	ldr q1, [x3, #4192]
	add v0.4s, v0.4s, v1.4s
	str q0, [x3, #4384]
	adds x21, x21, x15
	ldr q2, [x3, #4256]
	ldr q3, [x3, #4320]
	adc x22, x22, x16
	add v2.4s, v2.4s, v3.4s
	str q2, [x3, #4448]
	adds x27, x27, x15
	ldr q0, [x3, #4144]
	ldr q1, [x3, #4208]
	adc x28, x28, x16
	add v0.4s, v0.4s, v1.4s
	str q0, [x3, #4400]
	ldr q2, [x3, #4272]
	mul x15, x13, x13
	ldr q3, [x3, #4336]
	add v2.4s, v2.4s, v3.4s
	umulh x16, x13, x13
	str q2, [x3, #4464]
	ldr q0, [x3, #4224]
	adds x21, x21, x15
	ldr q1, [x3, #4240]
	ldr q2, [x3, #4256]
	ldr q3, [x3, #4272]
	adc x22, x22, x16
	ext v4.16b, v31.16b, v0.16b, #8
	ext v5.16b, v0.16b, v1.16b, #8
	adds x27, x27, x15
	ext v6.16b, v1.16b, v2.16b, #8
	ext v7.16b, v2.16b, v3.16b, #8
	adc x28, x28, x16
	ext v8.16b, v3.16b, v31.16b, #8
	str q4, [x3, #4480]
	str q5, [x3, #4496]
	mul x15, x0, x0
	str q6, [x3, #4512]
	str q7, [x3, #4528]
	umulh x16, x0, x0
	str q8, [x3, #4544]
	ldr q0, [x3, #4288]
	adds x21, x21, x15
	ldr q1, [x3, #4304]
	ldr q2, [x3, #4320]
	adc x22, x22, x16
	ldr q3, [x3, #4336]
	ext v4.16b, v31.16b, v0.16b, #8
	ext v5.16b, v0.16b, v1.16b, #8
	subs x27, x27, x15
	ext v6.16b, v1.16b, v2.16b, #8
	ext v7.16b, v2.16b, v3.16b, #8
	sbc x28, x28, x16
	ext v8.16b, v3.16b, v31.16b, #8
	str q4, [x3, #4560]
	ldr x17, [x3, #3656]
	str q5, [x3, #4576]
	str q6, [x3, #4592]
	str q7, [x3, #4608]
	mul x15, x17, x5
	str q8, [x3, #4624]
	ldr q0, [x3, #4416]
	umulh x16, x17, x5
	ldr q1, [x3, #4432]
	ldr q2, [x3, #4448]
	subs x21, x21, x15
	ldr q3, [x3, #4464]
	ext v4.16b, v31.16b, v0.16b, #8
	sbc x22, x22, x16
	ext v5.16b, v0.16b, v1.16b, #8
	ext v6.16b, v1.16b, v2.16b, #8
	ext v7.16b, v2.16b, v3.16b, #8
	mul x15, x4, x4
	ext v8.16b, v3.16b, v31.16b, #8
	str q4, [x3, #4640]
	umulh x16, x4, x4
	str q5, [x3, #4656]
	str q6, [x3, #4672]
	subs x21, x21, x15
	str q7, [x3, #4688]
	str q8, [x3, #4704]
	ldr q23, [x3, #4096]
	sbc x22, x22, x16
	ldr q24, [x3, #4112]
	ldr q25, [x3, #4128]
	and x15, x21, x25
	ldr q26, [x3, #4144]
	ldr q27, [x3, #4224]
	str x15, [x3, #1344]
	umull v0.2d, v23.2s, v27.2s
	umull2 v2.2d, v23.4s, v27.4s
	umlal v2.2d, v24.2s, v27.2s
	extr x23, x22, x21, #56
	umull2 v4.2d, v24.4s, v27.4s
	umlal v4.2d, v25.2s, v27.2s
	and x15, x27, x25
	umull2 v6.2d, v25.4s, v27.4s
	umlal v6.2d, v26.2s, v27.2s
	str x15, [x3, #1376]
	umull2 v8.2d, v26.4s, v27.4s
	ldr q27, [x3, #4240]
	extr x24, x28, x27, #56
	umlal v2.2d, v23.2s, v27.2s
	umlal2 v4.2d, v23.4s, v27.4s
	umlal v4.2d, v24.2s, v27.2s
	ldr x17, [x3, #3672]
	umlal2 v6.2d, v24.4s, v27.4s
	umlal v6.2d, v25.2s, v27.2s
	mul x21, x17, x7
	umlal2 v8.2d, v25.4s, v27.4s
	umlal v8.2d, v26.2s, v27.2s
	umulh x22, x17, x7
	umull2 v10.2d, v26.4s, v27.4s
	ldr q27, [x3, #4256]
	umlal v4.2d, v23.2s, v27.2s
	ldr x17, [x3, #3688]
	umlal2 v6.2d, v23.4s, v27.4s
	umlal v6.2d, v24.2s, v27.2s
	mul x27, x17, x9
	umlal2 v8.2d, v24.4s, v27.4s
	umlal v8.2d, v25.2s, v27.2s
	umulh x28, x17, x9
	umlal2 v10.2d, v25.4s, v27.4s
	umlal v10.2d, v26.2s, v27.2s
	umull2 v12.2d, v26.4s, v27.4s
	ldr x17, [x3, #3696]
	ldr q27, [x3, #4272]
	umlal v6.2d, v23.2s, v27.2s
	mul x15, x17, x11
	umlal2 v8.2d, v23.4s, v27.4s
	umlal v8.2d, v24.2s, v27.2s
	umulh x16, x17, x11
	umlal2 v10.2d, v24.4s, v27.4s
	umlal v10.2d, v25.2s, v27.2s
	adds x27, x27, x15
	umlal2 v12.2d, v25.4s, v27.4s
	umlal v12.2d, v26.2s, v27.2s
	umull2 v14.2d, v26.4s, v27.4s
	adc x28, x28, x16
	ldr q27, [x3, #4480]
	umull2 v1.2d, v23.4s, v27.4s
	ldr x17, [x3, #3712]
	umull2 v3.2d, v24.4s, v27.4s
	umull2 v5.2d, v25.4s, v27.4s
	mul x15, x17, x14
	umull2 v7.2d, v26.4s, v27.4s
	ldr q27, [x3, #4496]
	umlal v1.2d, v23.2s, v27.2s
	umulh x16, x17, x14
	umlal2 v3.2d, v23.4s, v27.4s
	umlal v3.2d, v24.2s, v27.2s
	adds x21, x21, x15
	umlal2 v5.2d, v24.4s, v27.4s
	umlal v5.2d, v25.2s, v27.2s
	adc x22, x22, x16
	umlal2 v7.2d, v25.4s, v27.4s
	umlal v7.2d, v26.2s, v27.2s
	adds x27, x27, x15
	umull2 v9.2d, v26.4s, v27.4s
	ldr q27, [x3, #4512]
	umlal v3.2d, v23.2s, v27.2s
	adc x28, x28, x16
	umlal2 v5.2d, v23.4s, v27.4s
	umlal v5.2d, v24.2s, v27.2s
	ldr x17, [x3, #3648]
	umlal2 v7.2d, v24.4s, v27.4s
	umlal v7.2d, v25.2s, v27.2s
	mul x15, x17, x2
	umlal2 v9.2d, v25.4s, v27.4s
	umlal v9.2d, v26.2s, v27.2s
	umull2 v11.2d, v26.4s, v27.4s
	umulh x16, x17, x2
	ldr q27, [x3, #4528]
	umlal v5.2d, v23.2s, v27.2s
	adds x21, x21, x15
	umlal2 v7.2d, v23.4s, v27.4s
	umlal v7.2d, v24.2s, v27.2s
	adc x22, x22, x16
	umlal2 v9.2d, v24.4s, v27.4s
	umlal v9.2d, v25.2s, v27.2s
	umlal2 v11.2d, v25.4s, v27.4s
	subs x27, x27, x15
	umlal v11.2d, v26.2s, v27.2s
	umull2 v13.2d, v26.4s, v27.4s
	sbc x28, x28, x16
	ldr q27, [x3, #4544]
	umlal v7.2d, v23.2s, v27.2s
	ldr x17, [x3, #3664]
	umlal v9.2d, v24.2s, v27.2s
	umlal v11.2d, v25.2s, v27.2s
	mul x15, x17, x5
	umlal v13.2d, v26.2s, v27.2s
	mov v28.16b, v8.16b
	sub v8.2d, v31.2d, v0.2d
	umulh x16, x17, x5
	sub v0.2d, v0.2d, v28.2d
	mov v28.16b, v9.16b
	subs x21, x21, x15
	sub v9.2d, v31.2d, v1.2d
	sub v1.2d, v1.2d, v28.2d
	sbc x22, x22, x16
	mov v28.16b, v10.16b
	sub v10.2d, v31.2d, v2.2d
	sub v2.2d, v2.2d, v28.2d
	adds x21, x21, x23
	mov v28.16b, v11.16b
	sub v11.2d, v31.2d, v3.2d
	adc x22, x22, x26
	sub v3.2d, v3.2d, v28.2d
	mov v28.16b, v12.16b
	and x15, x21, x25
	sub v12.2d, v31.2d, v4.2d
	sub v4.2d, v4.2d, v28.2d
	str x15, [x3, #1352]
	mov v28.16b, v13.16b
	sub v13.2d, v31.2d, v5.2d
	sub v5.2d, v5.2d, v28.2d
	extr x23, x22, x21, #56
	mov v28.16b, v14.16b
	sub v14.2d, v31.2d, v6.2d
	adds x27, x27, x24
	sub v6.2d, v6.2d, v28.2d
	sub v15.2d, v31.2d, v7.2d
	adc x28, x28, x26
	ldr q23, [x3, #4160]
	ldr q24, [x3, #4176]
	ldr q25, [x3, #4192]
	and x15, x27, x25
	ldr q26, [x3, #4208]
	ldr q27, [x3, #4288]
	str x15, [x3, #1384]
	umlal v0.2d, v23.2s, v27.2s
	umlal2 v2.2d, v23.4s, v27.4s
	extr x24, x28, x27, #56
	umlal v2.2d, v24.2s, v27.2s
	umlal2 v4.2d, v24.4s, v27.4s
	umlal v4.2d, v25.2s, v27.2s
	ldr x17, [x3, #3672]
	umlal2 v6.2d, v25.4s, v27.4s
	umlal v6.2d, v26.2s, v27.2s
	mul x21, x17, x8
	umlal2 v8.2d, v26.4s, v27.4s
	ldr q27, [x3, #4304]
	umulh x22, x17, x8
	umlal v2.2d, v23.2s, v27.2s
	umlal2 v4.2d, v23.4s, v27.4s
	mul x15, x7, x7
	umlal v4.2d, v24.2s, v27.2s
	umlal2 v6.2d, v24.4s, v27.4s
	umlal v6.2d, v25.2s, v27.2s
	umulh x16, x7, x7
	umlal2 v8.2d, v25.4s, v27.4s
	umlal v8.2d, v26.2s, v27.2s
	adds x21, x21, x15
	umlal2 v10.2d, v26.4s, v27.4s
	ldr q27, [x3, #4320]
	adc x22, x22, x16
	umlal v4.2d, v23.2s, v27.2s
	umlal2 v6.2d, v23.4s, v27.4s
	umlal v6.2d, v24.2s, v27.2s
	mul x27, x9, x9
	umlal2 v8.2d, v24.4s, v27.4s
	umlal v8.2d, v25.2s, v27.2s
	umulh x28, x9, x9
	umlal2 v10.2d, v25.4s, v27.4s
	umlal v10.2d, v26.2s, v27.2s
	ldr x17, [x3, #3696]
	umlal2 v12.2d, v26.4s, v27.4s
	ldr q27, [x3, #4336]
	umlal v6.2d, v23.2s, v27.2s
	mul x15, x17, x13
	umlal2 v8.2d, v23.4s, v27.4s
	umlal v8.2d, v24.2s, v27.2s
	umulh x16, x17, x13
	umlal2 v10.2d, v24.4s, v27.4s
	umlal v10.2d, v25.2s, v27.2s
	adds x27, x27, x15
	umlal2 v12.2d, v25.4s, v27.4s
	umlal v12.2d, v26.2s, v27.2s
	adc x28, x28, x16
	umlal2 v14.2d, v26.4s, v27.4s
	ldr q27, [x3, #4560]
	umlal2 v1.2d, v23.4s, v27.4s
	mul x15, x11, x11
	umlal2 v3.2d, v24.4s, v27.4s
	umlal2 v5.2d, v25.4s, v27.4s
	umulh x16, x11, x11
	umlal2 v7.2d, v26.4s, v27.4s
	ldr q27, [x3, #4576]
	adds x27, x27, x15
	umlal v1.2d, v23.2s, v27.2s
	umlal2 v3.2d, v23.4s, v27.4s
	umlal v3.2d, v24.2s, v27.2s
	adc x28, x28, x16
	umlal2 v5.2d, v24.4s, v27.4s
	umlal v5.2d, v25.2s, v27.2s
	mul x15, x14, x14
	umlal2 v7.2d, v25.4s, v27.4s
	umlal v7.2d, v26.2s, v27.2s
	umulh x16, x14, x14
	umlal2 v9.2d, v26.4s, v27.4s
	ldr q27, [x3, #4592]
	adds x21, x21, x15
	umlal v3.2d, v23.2s, v27.2s
	umlal2 v5.2d, v23.4s, v27.4s
	umlal v5.2d, v24.2s, v27.2s
	adc x22, x22, x16
	umlal2 v7.2d, v24.4s, v27.4s
	umlal v7.2d, v25.2s, v27.2s
	adds x27, x27, x15
	umlal2 v9.2d, v25.4s, v27.4s
	umlal v9.2d, v26.2s, v27.2s
	adc x28, x28, x16
	umlal2 v11.2d, v26.4s, v27.4s
	ldr q27, [x3, #4608]
	umlal v5.2d, v23.2s, v27.2s
	ldr x17, [x3, #3648]
	umlal2 v7.2d, v23.4s, v27.4s
	umlal v7.2d, v24.2s, v27.2s
	mul x15, x17, x4
	umlal2 v9.2d, v24.4s, v27.4s
	umlal v9.2d, v25.2s, v27.2s
	umulh x16, x17, x4
	umlal2 v11.2d, v25.4s, v27.4s
	umlal v11.2d, v26.2s, v27.2s
	umlal2 v13.2d, v26.4s, v27.4s
	adds x21, x21, x15
	ldr q27, [x3, #4624]
	umlal v7.2d, v23.2s, v27.2s
	adc x22, x22, x16
	umlal v9.2d, v24.2s, v27.2s
	umlal v11.2d, v25.2s, v27.2s
	subs x27, x27, x15
	umlal v13.2d, v26.2s, v27.2s
	ldr q23, [x3, #4352]
	sbc x28, x28, x16
	ldr q24, [x3, #4368]
	ldr q25, [x3, #4384]
	ldr q26, [x3, #4400]
	mul x15, x2, x2
	ldr q27, [x3, #4416]
	umlal v8.2d, v23.2s, v27.2s
	umulh x16, x2, x2
	umlal2 v10.2d, v23.4s, v27.4s
	umlal v10.2d, v24.2s, v27.2s
	adds x21, x21, x15
	umlal2 v12.2d, v24.4s, v27.4s
	umlal v12.2d, v25.2s, v27.2s
	umlal2 v14.2d, v25.4s, v27.4s
	adc x22, x22, x16
	umlal v14.2d, v26.2s, v27.2s
	umull2 v16.2d, v26.4s, v27.4s
	subs x27, x27, x15
	ldr q27, [x3, #4432]
	umlal v10.2d, v23.2s, v27.2s
	sbc x28, x28, x16
	umlal2 v12.2d, v23.4s, v27.4s
	umlal v12.2d, v24.2s, v27.2s
	umlal2 v14.2d, v24.4s, v27.4s
	mul x15, x5, x5
	umlal v14.2d, v25.2s, v27.2s
	umlal2 v16.2d, v25.4s, v27.4s
	umulh x16, x5, x5
	umlal v16.2d, v26.2s, v27.2s
	umull2 v18.2d, v26.4s, v27.4s
	subs x21, x21, x15
	ldr q27, [x3, #4448]
	umlal v12.2d, v23.2s, v27.2s
	sbc x22, x22, x16
	umlal2 v14.2d, v23.4s, v27.4s
	umlal v14.2d, v24.2s, v27.2s
	umlal2 v16.2d, v24.4s, v27.4s
	adds x21, x21, x23
	umlal v16.2d, v25.2s, v27.2s
	umlal2 v18.2d, v25.4s, v27.4s
	adc x22, x22, x26
	umlal v18.2d, v26.2s, v27.2s
	umull2 v20.2d, v26.4s, v27.4s
	and x15, x21, x25
	ldr q27, [x3, #4464]
	umlal v14.2d, v23.2s, v27.2s
	umlal2 v16.2d, v23.4s, v27.4s
	str x15, [x3, #1360]
	umlal v16.2d, v24.2s, v27.2s
	umlal2 v18.2d, v24.4s, v27.4s
	extr x23, x22, x21, #56
	umlal v18.2d, v25.2s, v27.2s
	umlal2 v20.2d, v25.4s, v27.4s
	adds x27, x27, x24
	umlal v20.2d, v26.2s, v27.2s
	umull2 v22.2d, v26.4s, v27.4s
	adc x28, x28, x26
	ldr q27, [x3, #4640]
	umlal2 v9.2d, v23.4s, v27.4s
	umlal2 v11.2d, v24.4s, v27.4s
	and x15, x27, x25
	umlal2 v13.2d, v25.4s, v27.4s
	umlal2 v15.2d, v26.4s, v27.4s
	str x15, [x3, #1392]
	ldr q27, [x3, #4656]
	umlal v9.2d, v23.2s, v27.2s
	extr x24, x28, x27, #56
	umlal2 v11.2d, v23.4s, v27.4s
	umlal v11.2d, v24.2s, v27.2s
	umlal2 v13.2d, v24.4s, v27.4s
	ldr x17, [x3, #3672]
	umlal v13.2d, v25.2s, v27.2s
	umlal2 v15.2d, v25.4s, v27.4s
	mul x21, x17, x9
	umlal v15.2d, v26.2s, v27.2s
	umull2 v17.2d, v26.4s, v27.4s
	umulh x22, x17, x9
	ldr q27, [x3, #4672]
	umlal v11.2d, v23.2s, v27.2s
	umlal2 v13.2d, v23.4s, v27.4s
	ldr x17, [x3, #3680]
	umlal v13.2d, v24.2s, v27.2s
	umlal2 v15.2d, v24.4s, v27.4s
	mul x15, x17, x8
	umlal v15.2d, v25.2s, v27.2s
	umlal2 v17.2d, v25.4s, v27.4s
	umulh x16, x17, x8
	umlal v17.2d, v26.2s, v27.2s
	umull2 v19.2d, v26.4s, v27.4s
	adds x21, x21, x15
	ldr q27, [x3, #4688]
	umlal v13.2d, v23.2s, v27.2s
	umlal2 v15.2d, v23.4s, v27.4s
	adc x22, x22, x16
	umlal v15.2d, v24.2s, v27.2s
	umlal2 v17.2d, v24.4s, v27.4s
	ldr x17, [x3, #3696]
	umlal v17.2d, v25.2s, v27.2s
	umlal2 v19.2d, v25.4s, v27.4s
	mul x27, x17, x14
	umlal v19.2d, v26.2s, v27.2s
	umull2 v21.2d, v26.4s, v27.4s
	ldr q27, [x3, #4704]
	umulh x28, x17, x14
	umlal v15.2d, v23.2s, v27.2s
	umlal v17.2d, v24.2s, v27.2s
	ldr x17, [x3, #3704]
	umlal v19.2d, v25.2s, v27.2s
	umlal v21.2d, v26.2s, v27.2s
	mul x15, x17, x13
	add v0.2d, v0.2d, v16.2d
	add v8.2d, v8.2d, v16.2d
	umulh x16, x17, x13
	add v1.2d, v1.2d, v17.2d
	add v9.2d, v9.2d, v17.2d
	add v2.2d, v2.2d, v18.2d
	adds x27, x27, x15
	add v10.2d, v10.2d, v18.2d
	add v3.2d, v3.2d, v19.2d
	adc x28, x28, x16
	add v11.2d, v11.2d, v19.2d
	add v4.2d, v4.2d, v20.2d
	ldr x17, [x3, #3648]
	add v12.2d, v12.2d, v20.2d
	add v5.2d, v5.2d, v21.2d
	add v13.2d, v13.2d, v21.2d
	mul x15, x17, x5
	add v6.2d, v6.2d, v22.2d
	add v14.2d, v14.2d, v22.2d
	umulh x16, x17, x5
	ushr v28.2d, v0.2d, #28
	and v0.16b, v0.16b, v30.16b
	adds x21, x21, x15
	add v1.2d, v1.2d, v28.2d
	ushr v29.2d, v8.2d, #28
	and v8.16b, v8.16b, v30.16b
	adc x22, x22, x16
	add v9.2d, v9.2d, v29.2d
	ushr v28.2d, v1.2d, #28
	subs x27, x27, x15
	and v1.16b, v1.16b, v30.16b
	add v2.2d, v2.2d, v28.2d
	sbc x28, x28, x16
	ushr v29.2d, v9.2d, #28
	and v9.16b, v9.16b, v30.16b
	ldr x17, [x3, #3656]
	add v10.2d, v10.2d, v29.2d
	ushr v28.2d, v2.2d, #28
	and v2.16b, v2.16b, v30.16b
	mul x15, x17, x4
	add v3.2d, v3.2d, v28.2d
	ushr v29.2d, v10.2d, #28
	umulh x16, x17, x4
	and v10.16b, v10.16b, v30.16b
	add v11.2d, v11.2d, v29.2d
	adds x21, x21, x15
	ushr v28.2d, v3.2d, #28
	and v3.16b, v3.16b, v30.16b
	add v4.2d, v4.2d, v28.2d
	adc x22, x22, x16
	ushr v29.2d, v11.2d, #28
	and v11.16b, v11.16b, v30.16b
	subs x27, x27, x15
	add v12.2d, v12.2d, v29.2d
	ushr v28.2d, v4.2d, #28
	sbc x28, x28, x16
	and v4.16b, v4.16b, v30.16b
	add v5.2d, v5.2d, v28.2d
	ushr v29.2d, v12.2d, #28
	adds x21, x21, x23
	and v12.16b, v12.16b, v30.16b
	add v13.2d, v13.2d, v29.2d
	adc x22, x22, x26
	ushr v28.2d, v5.2d, #28
	and v5.16b, v5.16b, v30.16b
	and x15, x21, x25
	add v6.2d, v6.2d, v28.2d
	ushr v29.2d, v13.2d, #28
	str x15, [x3, #1368]
	and v13.16b, v13.16b, v30.16b
	add v14.2d, v14.2d, v29.2d
	ushr v28.2d, v6.2d, #28
	extr x23, x22, x21, #56
	and v6.16b, v6.16b, v30.16b
	add v7.2d, v7.2d, v28.2d
	adds x27, x27, x24
	ushr v29.2d, v14.2d, #28
	and v14.16b, v14.16b, v30.16b
	adc x28, x28, x26
	add v15.2d, v15.2d, v29.2d
	ushr v28.2d, v7.2d, #28
	and v7.16b, v7.16b, v30.16b
	and x15, x27, x25
	ushr v29.2d, v15.2d, #28
	and v15.16b, v15.16b, v30.16b
	str x15, [x3, #1400]
	add v8.2d, v8.2d, v28.2d
	add v8.2d, v8.2d, v29.2d
	extr x24, x28, x27, #56
	add v0.2d, v0.2d, v29.2d
	shl v16.2d, v1.2d, #28
	ldr x4, [x3, #1344]
	add v16.2d, v16.2d, v0.2d
	shl v17.2d, v3.2d, #28
	add v17.2d, v17.2d, v2.2d
	ldr x5, [x3, #1352]
	shl v18.2d, v5.2d, #28
	add v18.2d, v18.2d, v4.2d
	ldr x6, [x3, #1376]
	shl v19.2d, v7.2d, #28
	add v19.2d, v19.2d, v6.2d
	ldr x7, [x3, #1384]
	shl v20.2d, v9.2d, #28
	add v20.2d, v20.2d, v8.2d
	shl v21.2d, v11.2d, #28
	add x4, x4, x24
	add v21.2d, v21.2d, v10.2d
	shl v22.2d, v13.2d, #28
	add x6, x6, x24
	add v22.2d, v22.2d, v12.2d
	shl v23.2d, v15.2d, #28
	add x6, x6, x23
	add v23.2d, v23.2d, v14.2d
	shl v31.2d, v30.2d, #28
	add v31.2d, v31.2d, v30.2d
	lsr x8, x4, #56
	ushr v28.2d, v16.2d, #56
	and v16.16b, v16.16b, v31.16b
	and x4, x4, x25
	add v17.2d, v17.2d, v28.2d
	ushr v28.2d, v20.2d, #56
	add x5, x5, x8
	and v20.16b, v20.16b, v31.16b
	add v21.2d, v21.2d, v28.2d
	lsr x8, x6, #56
	trn1 v8.2d, v16.2d, v17.2d
	trn2 v9.2d, v16.2d, v17.2d
	str q8, [x3, #1472]
	and x6, x6, x25
	str q9, [x3, #1600]
	trn1 v8.2d, v18.2d, v19.2d
	add x7, x7, x8
	trn2 v9.2d, v18.2d, v19.2d
	str q8, [x3, #1488]
	str x4, [x3, #1344]
	str q9, [x3, #1616]
	trn1 v8.2d, v20.2d, v21.2d
	trn2 v9.2d, v20.2d, v21.2d
	str x5, [x3, #1352]
	str q8, [x3, #1504]
	str q9, [x3, #1632]
	str x6, [x3, #1376]
	trn1 v8.2d, v22.2d, v23.2d
	trn2 v9.2d, v22.2d, v23.2d
	str x7, [x3, #1384]
	str q8, [x3, #1520]
	str q9, [x3, #1648]
	ldr x0, [x3, #1472]
	dup v30.2d, x12
	ldr x2, [x3, #1480]
	movi v31.2d, #0
	ldr x4, [x3, #1488]
	ldr q0, [x3, #448]
	ldr x5, [x3, #1496]
	ldr q1, [x3, #576]
	ldr x6, [x3, #1504]
	trn1 v2.2d, v0.2d, v1.2d
	ldr x7, [x3, #1512]
	trn2 v3.2d, v0.2d, v1.2d
	ldr x8, [x3, #1520]
	and v0.16b, v2.16b, v30.16b
	ldr x9, [x3, #1528]
	ushr v1.2d, v2.2d, #28
	movz x25, #65535, lsl #0
	uzp1 v2.4s, v0.4s, v1.4s
	movk x25, #65535, lsl #16
	str q2, [x3, #4096]
	movk x25, #65535, lsl #32
	and v0.16b, v3.16b, v30.16b
	movk x25, #255, lsl #48
	ushr v1.2d, v3.2d, #28
	movz x26, #0, lsl #0
	uzp1 v3.4s, v0.4s, v1.4s
	add x13, x0, x6
	str q3, [x3, #4112]
	str x13, [x3, #3584]
	ldr q0, [x3, #464]
	ldr x10, [x3, #1600]
	ldr q1, [x3, #592]
	ldr x11, [x3, #1632]
	trn1 v2.2d, v0.2d, v1.2d
	add x10, x10, x11
	trn2 v3.2d, v0.2d, v1.2d
	str x10, [x3, #3616]
	and v0.16b, v2.16b, v30.16b
	add x13, x2, x7
	ushr v1.2d, v2.2d, #28
	str x13, [x3, #3592]
	uzp1 v2.4s, v0.4s, v1.4s
	ldr x10, [x3, #1608]
	str q2, [x3, #4128]
	ldr x11, [x3, #1640]
	and v0.16b, v3.16b, v30.16b
	add x10, x10, x11
	ushr v1.2d, v3.2d, #28
	str x10, [x3, #3624]
	uzp1 v3.4s, v0.4s, v1.4s
	add x13, x4, x8
	str q3, [x3, #4144]
	str x13, [x3, #3600]
	ldr q0, [x3, #480]
	ldr x10, [x3, #1616]
	ldr q1, [x3, #608]
	ldr x11, [x3, #1648]
	trn1 v2.2d, v0.2d, v1.2d
	add x10, x10, x11
	trn2 v3.2d, v0.2d, v1.2d
	str x10, [x3, #3632]
	and v0.16b, v2.16b, v30.16b
	add x13, x5, x9
	ushr v1.2d, v2.2d, #28
	str x13, [x3, #3608]
	uzp1 v2.4s, v0.4s, v1.4s
	ldr x10, [x3, #1624]
	str q2, [x3, #4160]
	ldr x11, [x3, #1656]
	and v0.16b, v3.16b, v30.16b
	add x10, x10, x11
	ushr v1.2d, v3.2d, #28
	str x10, [x3, #3640]
	uzp1 v3.4s, v0.4s, v1.4s
	ldr x11, [x3, #1632]
	str q3, [x3, #4176]
	mul x14, x6, x11
	ldr q0, [x3, #496]
	umulh x15, x6, x11
	ldr q1, [x3, #624]
	ldr x11, [x3, #1656]
	trn1 v2.2d, v0.2d, v1.2d
	mul x16, x7, x11
	trn2 v3.2d, v0.2d, v1.2d
	umulh x17, x7, x11
	and v0.16b, v2.16b, v30.16b
	ldr x11, [x3, #1648]
	ushr v1.2d, v2.2d, #28
	mul x10, x8, x11
	uzp1 v2.4s, v0.4s, v1.4s
	umulh x11, x8, x11
	str q2, [x3, #4192]
	adds x16, x16, x10
	and v0.16b, v3.16b, v30.16b
	adc x17, x17, x11
	ushr v1.2d, v3.2d, #28
	ldr x11, [x3, #1640]
	uzp1 v3.4s, v0.4s, v1.4s
	mul x10, x9, x11
	str q3, [x3, #4208]
	umulh x11, x9, x11
	ldr q4, [x3, #960]
	adds x16, x16, x10
	ldr q5, [x3, #832]
	adc x17, x17, x11
	trn1 v6.2d, v4.2d, v5.2d
	ldr x13, [x3, #3584]
	trn2 v7.2d, v4.2d, v5.2d
	ldr x11, [x3, #3616]
	and v4.16b, v6.16b, v30.16b
	mul x10, x13, x11
	ushr v5.2d, v6.2d, #28
	umulh x11, x13, x11
	uzp1 v6.4s, v4.4s, v5.4s
	adds x16, x16, x10
	str q6, [x3, #4224]
	adc x17, x17, x11
	and v4.16b, v7.16b, v30.16b
	ldr x13, [x3, #3592]
	ushr v5.2d, v7.2d, #28
	ldr x11, [x3, #3640]
	uzp1 v7.4s, v4.4s, v5.4s
	mul x27, x13, x11
	str q7, [x3, #4240]
	umulh x28, x13, x11
	ldr q4, [x3, #976]
	ldr x13, [x3, #3600]
	ldr q5, [x3, #848]
	ldr x11, [x3, #3632]
	trn1 v6.2d, v4.2d, v5.2d
	mul x10, x13, x11
	trn2 v7.2d, v4.2d, v5.2d
	umulh x11, x13, x11
	and v4.16b, v6.16b, v30.16b
	adds x27, x27, x10
	ushr v5.2d, v6.2d, #28
	adc x28, x28, x11
	uzp1 v6.4s, v4.4s, v5.4s
	ldr x13, [x3, #3608]
	str q6, [x3, #4256]
	ldr x11, [x3, #3624]
	and v4.16b, v7.16b, v30.16b
	mul x10, x13, x11
	ushr v5.2d, v7.2d, #28
	umulh x11, x13, x11
	uzp1 v7.4s, v4.4s, v5.4s
	adds x27, x27, x10
	str q7, [x3, #4272]
	adc x28, x28, x11
	ldr q4, [x3, #992]
	adds x14, x14, x27
	ldr q5, [x3, #864]
	adc x15, x15, x28
	trn1 v6.2d, v4.2d, v5.2d
	adds x16, x16, x27
	trn2 v7.2d, v4.2d, v5.2d
	adc x17, x17, x28
	and v4.16b, v6.16b, v30.16b
	ldr x11, [x3, #1600]
	ushr v5.2d, v6.2d, #28
	mul x10, x0, x11
	uzp1 v6.4s, v4.4s, v5.4s
	umulh x11, x0, x11
	str q6, [x3, #4288]
	adds x14, x14, x10
	and v4.16b, v7.16b, v30.16b
	adc x15, x15, x11
	ushr v5.2d, v7.2d, #28
	subs x16, x16, x10
	uzp1 v7.4s, v4.4s, v5.4s
	sbc x17, x17, x11
	str q7, [x3, #4304]
	ldr x11, [x3, #1624]
	ldr q4, [x3, #1008]
	mul x10, x2, x11
	ldr q5, [x3, #880]
	umulh x11, x2, x11
	trn1 v6.2d, v4.2d, v5.2d
	subs x14, x14, x10
	trn2 v7.2d, v4.2d, v5.2d
	sbc x15, x15, x11
	and v4.16b, v6.16b, v30.16b
	ldr x11, [x3, #1616]
	ushr v5.2d, v6.2d, #28
	mul x10, x4, x11
	uzp1 v6.4s, v4.4s, v5.4s
	umulh x11, x4, x11
	str q6, [x3, #4320]
	subs x14, x14, x10
	and v4.16b, v7.16b, v30.16b
	sbc x15, x15, x11
	ushr v5.2d, v7.2d, #28
	ldr x11, [x3, #1608]
	uzp1 v7.4s, v4.4s, v5.4s
	mul x10, x5, x11
	str q7, [x3, #4336]
	umulh x11, x5, x11
	ldr q0, [x3, #4096]
	subs x14, x14, x10
	ldr q1, [x3, #4160]
	sbc x15, x15, x11
	add v0.4s, v0.4s, v1.4s
	and x10, x14, x25
	str q0, [x3, #4352]
	str x10, [x3, #1728]
	ldr q2, [x3, #4224]
	extr x23, x15, x14, #56
	ldr q3, [x3, #4288]
	and x10, x16, x25
	add v2.4s, v2.4s, v3.4s
	str x10, [x3, #1760]
	str q2, [x3, #4416]
	extr x24, x17, x16, #56
	ldr q0, [x3, #4112]
	ldr x11, [x3, #1640]
	ldr q1, [x3, #4176]
	mul x14, x6, x11
	add v0.4s, v0.4s, v1.4s
	umulh x15, x6, x11
	str q0, [x3, #4368]
	ldr x11, [x3, #1632]
	ldr q2, [x3, #4240]
	mul x10, x7, x11
	ldr q3, [x3, #4304]
	umulh x11, x7, x11
	add v2.4s, v2.4s, v3.4s
	adds x14, x14, x10
	str q2, [x3, #4432]
	adc x15, x15, x11
	ldr q0, [x3, #4128]
	ldr x11, [x3, #1656]
	ldr q1, [x3, #4192]
	mul x16, x8, x11
	add v0.4s, v0.4s, v1.4s
	umulh x17, x8, x11
	str q0, [x3, #4384]
	ldr x11, [x3, #1648]
	ldr q2, [x3, #4256]
	mul x10, x9, x11
	ldr q3, [x3, #4320]
	umulh x11, x9, x11
	add v2.4s, v2.4s, v3.4s
	adds x16, x16, x10
	str q2, [x3, #4448]
	adc x17, x17, x11
	ldr q0, [x3, #4144]
	ldr x13, [x3, #3584]
	ldr q1, [x3, #4208]
	ldr x11, [x3, #3624]
	add v0.4s, v0.4s, v1.4s
	mul x10, x13, x11
	str q0, [x3, #4400]
	umulh x11, x13, x11
	ldr q2, [x3, #4272]
	adds x16, x16, x10
	ldr q3, [x3, #4336]
	adc x17, x17, x11
	add v2.4s, v2.4s, v3.4s
	ldr x13, [x3, #3592]
	str q2, [x3, #4464]
	ldr x11, [x3, #3616]
	ldr q0, [x3, #4224]
	mul x10, x13, x11
	ldr q1, [x3, #4240]
	umulh x11, x13, x11
	ldr q2, [x3, #4256]
	adds x16, x16, x10
	ldr q3, [x3, #4272]
	adc x17, x17, x11
	ext v4.16b, v31.16b, v0.16b, #8
	ldr x13, [x3, #3600]
	ext v5.16b, v0.16b, v1.16b, #8
	ldr x11, [x3, #3640]
	ext v6.16b, v1.16b, v2.16b, #8
	mul x27, x13, x11
	ext v7.16b, v2.16b, v3.16b, #8
	umulh x28, x13, x11
	ext v8.16b, v3.16b, v31.16b, #8
	ldr x13, [x3, #3608]
	str q4, [x3, #4480]
	ldr x11, [x3, #3632]
	str q5, [x3, #4496]
	mul x10, x13, x11
	str q6, [x3, #4512]
	umulh x11, x13, x11
	str q7, [x3, #4528]
	adds x27, x27, x10
	str q8, [x3, #4544]
	adc x28, x28, x11
	ldr q0, [x3, #4288]
	adds x14, x14, x27
	ldr q1, [x3, #4304]
	adc x15, x15, x28
	ldr q2, [x3, #4320]
	adds x16, x16, x27
	ldr q3, [x3, #4336]
	adc x17, x17, x28
	ext v4.16b, v31.16b, v0.16b, #8
	ldr x11, [x3, #1608]
	ext v5.16b, v0.16b, v1.16b, #8
	mul x21, x0, x11
	ext v6.16b, v1.16b, v2.16b, #8
	umulh x22, x0, x11
	ext v7.16b, v2.16b, v3.16b, #8
	ldr x11, [x3, #1600]
	ext v8.16b, v3.16b, v31.16b, #8
	mul x10, x2, x11
	str q4, [x3, #4560]
	umulh x11, x2, x11
	str q5, [x3, #4576]
	adds x21, x21, x10
	str q6, [x3, #4592]
	adc x22, x22, x11
	str q7, [x3, #4608]
	adds x14, x14, x21
	str q8, [x3, #4624]
	adc x15, x15, x22
	ldr q0, [x3, #4416]
	subs x16, x16, x21
	ldr q1, [x3, #4432]
	sbc x17, x17, x22
	ldr q2, [x3, #4448]
	ldr x11, [x3, #1624]
	ldr q3, [x3, #4464]
	mul x10, x4, x11
	ext v4.16b, v31.16b, v0.16b, #8
	umulh x11, x4, x11
	ext v5.16b, v0.16b, v1.16b, #8
	subs x14, x14, x10
	ext v6.16b, v1.16b, v2.16b, #8
	sbc x15, x15, x11
	ext v7.16b, v2.16b, v3.16b, #8
	ldr x11, [x3, #1616]
	ext v8.16b, v3.16b, v31.16b, #8
	mul x10, x5, x11
	str q4, [x3, #4640]
	umulh x11, x5, x11
	str q5, [x3, #4656]
	subs x14, x14, x10
	str q6, [x3, #4672]
	sbc x15, x15, x11
	str q7, [x3, #4688]
	adds x14, x14, x23
	str q8, [x3, #4704]
	adc x15, x15, x26
	ldr q23, [x3, #4096]
	and x10, x14, x25
	ldr q24, [x3, #4112]
	str x10, [x3, #1736]
	ldr q25, [x3, #4128]
	extr x23, x15, x14, #56
	ldr q26, [x3, #4144]
	adds x16, x16, x24
	ldr q27, [x3, #4224]
	adc x17, x17, x26
	umull v0.2d, v23.2s, v27.2s
	and x10, x16, x25
	umull2 v2.2d, v23.4s, v27.4s
	str x10, [x3, #1768]
	umlal v2.2d, v24.2s, v27.2s
	extr x24, x17, x16, #56
	umull2 v4.2d, v24.4s, v27.4s
	ldr x11, [x3, #1648]
	umlal v4.2d, v25.2s, v27.2s
	mul x14, x6, x11
	umull2 v6.2d, v25.4s, v27.4s
	umulh x15, x6, x11
	umlal v6.2d, v26.2s, v27.2s
	ldr x11, [x3, #1640]
	umull2 v8.2d, v26.4s, v27.4s
	mul x10, x7, x11
	ldr q27, [x3, #4240]
	umulh x11, x7, x11
	umlal v2.2d, v23.2s, v27.2s
	adds x14, x14, x10
	umlal2 v4.2d, v23.4s, v27.4s
	adc x15, x15, x11
	umlal v4.2d, v24.2s, v27.2s
	ldr x11, [x3, #1632]
	umlal2 v6.2d, v24.4s, v27.4s
	mul x10, x8, x11
	umlal v6.2d, v25.2s, v27.2s
	umulh x11, x8, x11
	umlal2 v8.2d, v25.4s, v27.4s
	adds x14, x14, x10
	umlal v8.2d, v26.2s, v27.2s
	adc x15, x15, x11
	umull2 v10.2d, v26.4s, v27.4s
	ldr x11, [x3, #1656]
	ldr q27, [x3, #4256]
	mul x16, x9, x11
	umlal v4.2d, v23.2s, v27.2s
	umulh x17, x9, x11
	umlal2 v6.2d, v23.4s, v27.4s
	ldr x13, [x3, #3584]
	umlal v6.2d, v24.2s, v27.2s
	ldr x11, [x3, #3632]
	umlal2 v8.2d, v24.4s, v27.4s
	mul x10, x13, x11
	umlal v8.2d, v25.2s, v27.2s
	umulh x11, x13, x11
	umlal2 v10.2d, v25.4s, v27.4s
	adds x16, x16, x10
	umlal v10.2d, v26.2s, v27.2s
	adc x17, x17, x11
	umull2 v12.2d, v26.4s, v27.4s
	ldr x13, [x3, #3592]
	ldr q27, [x3, #4272]
	ldr x11, [x3, #3624]
	umlal v6.2d, v23.2s, v27.2s
	mul x10, x13, x11
	umlal2 v8.2d, v23.4s, v27.4s
	umulh x11, x13, x11
	umlal v8.2d, v24.2s, v27.2s
	adds x16, x16, x10
	umlal2 v10.2d, v24.4s, v27.4s
	adc x17, x17, x11
	umlal v10.2d, v25.2s, v27.2s
	ldr x13, [x3, #3600]
	umlal2 v12.2d, v25.4s, v27.4s
	ldr x11, [x3, #3616]
	umlal v12.2d, v26.2s, v27.2s
	mul x10, x13, x11
	umull2 v14.2d, v26.4s, v27.4s
	umulh x11, x13, x11
	ldr q27, [x3, #4480]
	adds x16, x16, x10
	umull2 v1.2d, v23.4s, v27.4s
	adc x17, x17, x11
	umull2 v3.2d, v24.4s, v27.4s
	ldr x13, [x3, #3608]
	umull2 v5.2d, v25.4s, v27.4s
	ldr x11, [x3, #3640]
	umull2 v7.2d, v26.4s, v27.4s
	mul x10, x13, x11
	ldr q27, [x3, #4496]
	umulh x11, x13, x11
	umlal v1.2d, v23.2s, v27.2s
	adds x14, x14, x10
	umlal2 v3.2d, v23.4s, v27.4s
	adc x15, x15, x11
	umlal v3.2d, v24.2s, v27.2s
	adds x16, x16, x10
	umlal2 v5.2d, v24.4s, v27.4s
	adc x17, x17, x11
	umlal v5.2d, v25.2s, v27.2s
	ldr x11, [x3, #1616]
	umlal2 v7.2d, v25.4s, v27.4s
	mul x21, x0, x11
	umlal v7.2d, v26.2s, v27.2s
	umulh x22, x0, x11
	umull2 v9.2d, v26.4s, v27.4s
	ldr x11, [x3, #1608]
	ldr q27, [x3, #4512]
	mul x10, x2, x11
	umlal v3.2d, v23.2s, v27.2s
	umulh x11, x2, x11
	umlal2 v5.2d, v23.4s, v27.4s
	adds x21, x21, x10
	umlal v5.2d, v24.2s, v27.2s
	adc x22, x22, x11
	umlal2 v7.2d, v24.4s, v27.4s
	ldr x11, [x3, #1600]
	umlal v7.2d, v25.2s, v27.2s
	mul x10, x4, x11
	umlal2 v9.2d, v25.4s, v27.4s
	umulh x11, x4, x11
	umlal v9.2d, v26.2s, v27.2s
	adds x21, x21, x10
	umull2 v11.2d, v26.4s, v27.4s
	adc x22, x22, x11
	ldr q27, [x3, #4528]
	adds x14, x14, x21
	umlal v5.2d, v23.2s, v27.2s
	adc x15, x15, x22
	umlal2 v7.2d, v23.4s, v27.4s
	subs x16, x16, x21
	umlal v7.2d, v24.2s, v27.2s
	sbc x17, x17, x22
	umlal2 v9.2d, v24.4s, v27.4s
	ldr x11, [x3, #1624]
	umlal v9.2d, v25.2s, v27.2s
	mul x10, x5, x11
	umlal2 v11.2d, v25.4s, v27.4s
	umulh x11, x5, x11
	umlal v11.2d, v26.2s, v27.2s
	subs x14, x14, x10
	umull2 v13.2d, v26.4s, v27.4s
	sbc x15, x15, x11
	ldr q27, [x3, #4544]
	adds x14, x14, x23
	umlal v7.2d, v23.2s, v27.2s
	adc x15, x15, x26
	umlal v9.2d, v24.2s, v27.2s
	and x10, x14, x25
	umlal v11.2d, v25.2s, v27.2s
	str x10, [x3, #1744]
	umlal v13.2d, v26.2s, v27.2s
	extr x23, x15, x14, #56
	mov v28.16b, v8.16b
	adds x16, x16, x24
	sub v8.2d, v31.2d, v0.2d
	adc x17, x17, x26
	sub v0.2d, v0.2d, v28.2d
	and x10, x16, x25
	mov v28.16b, v9.16b
	str x10, [x3, #1776]
	sub v9.2d, v31.2d, v1.2d
	extr x24, x17, x16, #56
	sub v1.2d, v1.2d, v28.2d
	ldr x11, [x3, #1656]
	mov v28.16b, v10.16b
	mul x14, x6, x11
	sub v10.2d, v31.2d, v2.2d
	umulh x15, x6, x11
	sub v2.2d, v2.2d, v28.2d
	ldr x11, [x3, #1648]
	mov v28.16b, v11.16b
	mul x10, x7, x11
	sub v11.2d, v31.2d, v3.2d
	umulh x11, x7, x11
	sub v3.2d, v3.2d, v28.2d
	adds x14, x14, x10
	mov v28.16b, v12.16b
	adc x15, x15, x11
	sub v12.2d, v31.2d, v4.2d
	ldr x11, [x3, #1640]
	sub v4.2d, v4.2d, v28.2d
	mul x10, x8, x11
	mov v28.16b, v13.16b
	umulh x11, x8, x11
	sub v13.2d, v31.2d, v5.2d
	adds x14, x14, x10
	sub v5.2d, v5.2d, v28.2d
	adc x15, x15, x11
	mov v28.16b, v14.16b
	ldr x11, [x3, #1632]
	sub v14.2d, v31.2d, v6.2d
	mul x10, x9, x11
	sub v6.2d, v6.2d, v28.2d
	umulh x11, x9, x11
	sub v15.2d, v31.2d, v7.2d
	adds x14, x14, x10
	ldr q23, [x3, #4160]
	adc x15, x15, x11
	ldr q24, [x3, #4176]
	ldr x13, [x3, #3584]
	ldr q25, [x3, #4192]
	ldr x11, [x3, #3640]
	ldr q26, [x3, #4208]
	mul x16, x13, x11
	ldr q27, [x3, #4288]
	umulh x17, x13, x11
	umlal v0.2d, v23.2s, v27.2s
	ldr x13, [x3, #3592]
	umlal2 v2.2d, v23.4s, v27.4s
	ldr x11, [x3, #3632]
	umlal v2.2d, v24.2s, v27.2s
	mul x10, x13, x11
	umlal2 v4.2d, v24.4s, v27.4s
	umulh x11, x13, x11
	umlal v4.2d, v25.2s, v27.2s
	adds x16, x16, x10
	umlal2 v6.2d, v25.4s, v27.4s
	adc x17, x17, x11
	umlal v6.2d, v26.2s, v27.2s
	ldr x13, [x3, #3600]
	umlal2 v8.2d, v26.4s, v27.4s
	ldr x11, [x3, #3624]
	ldr q27, [x3, #4304]
	mul x10, x13, x11
	umlal v2.2d, v23.2s, v27.2s
	umulh x11, x13, x11
	umlal2 v4.2d, v23.4s, v27.4s
	adds x16, x16, x10
	umlal v4.2d, v24.2s, v27.2s
	adc x17, x17, x11
	umlal2 v6.2d, v24.4s, v27.4s
	ldr x13, [x3, #3608]
	umlal v6.2d, v25.2s, v27.2s
	ldr x11, [x3, #3616]
	umlal2 v8.2d, v25.4s, v27.4s
	mul x10, x13, x11
	umlal v8.2d, v26.2s, v27.2s
	umulh x11, x13, x11
	umlal2 v10.2d, v26.4s, v27.4s
	adds x16, x16, x10
	ldr q27, [x3, #4320]
	adc x17, x17, x11
	umlal v4.2d, v23.2s, v27.2s
	ldr x11, [x3, #1624]
	umlal2 v6.2d, v23.4s, v27.4s
	mul x21, x0, x11
	umlal v6.2d, v24.2s, v27.2s
	umulh x22, x0, x11
	umlal2 v8.2d, v24.4s, v27.4s
	ldr x11, [x3, #1616]
	umlal v8.2d, v25.2s, v27.2s
	mul x10, x2, x11
	umlal2 v10.2d, v25.4s, v27.4s
	umulh x11, x2, x11
	umlal v10.2d, v26.2s, v27.2s
	adds x21, x21, x10
	umlal2 v12.2d, v26.4s, v27.4s
	adc x22, x22, x11
	ldr q27, [x3, #4336]
	ldr x11, [x3, #1608]
	umlal v6.2d, v23.2s, v27.2s
	mul x10, x4, x11
	umlal2 v8.2d, v23.4s, v27.4s
	umulh x11, x4, x11
	umlal v8.2d, v24.2s, v27.2s
	adds x21, x21, x10
	umlal2 v10.2d, v24.4s, v27.4s
	adc x22, x22, x11
	umlal v10.2d, v25.2s, v27.2s
	ldr x11, [x3, #1600]
	umlal2 v12.2d, v25.4s, v27.4s
	mul x10, x5, x11
	umlal v12.2d, v26.2s, v27.2s
	umulh x11, x5, x11
	umlal2 v14.2d, v26.4s, v27.4s
	adds x21, x21, x10
	ldr q27, [x3, #4560]
	adc x22, x22, x11
	umlal2 v1.2d, v23.4s, v27.4s
	adds x14, x14, x21
	umlal2 v3.2d, v24.4s, v27.4s
	adc x15, x15, x22
	umlal2 v5.2d, v25.4s, v27.4s
	subs x16, x16, x21
	umlal2 v7.2d, v26.4s, v27.4s
	sbc x17, x17, x22
	ldr q27, [x3, #4576]
	adds x14, x14, x23
	umlal v1.2d, v23.2s, v27.2s
	adc x15, x15, x26
	umlal2 v3.2d, v23.4s, v27.4s
	and x10, x14, x25
	umlal v3.2d, v24.2s, v27.2s
	str x10, [x3, #1752]
	umlal2 v5.2d, v24.4s, v27.4s
	extr x23, x15, x14, #56
	umlal v5.2d, v25.2s, v27.2s
	adds x16, x16, x24
	umlal2 v7.2d, v25.4s, v27.4s
	adc x17, x17, x26
	umlal v7.2d, v26.2s, v27.2s
	and x10, x16, x25
	umlal2 v9.2d, v26.4s, v27.4s
	str x10, [x3, #1784]
	ldr q27, [x3, #4592]
	extr x24, x17, x16, #56
	umlal v3.2d, v23.2s, v27.2s
	ldr x4, [x3, #1728]
	umlal2 v5.2d, v23.4s, v27.4s
	ldr x5, [x3, #1736]
	umlal v5.2d, v24.2s, v27.2s
	ldr x6, [x3, #1760]
	umlal2 v7.2d, v24.4s, v27.4s
	ldr x7, [x3, #1768]
	umlal v7.2d, v25.2s, v27.2s
	add x4, x4, x24
	umlal2 v9.2d, v25.4s, v27.4s
	add x6, x6, x24
	umlal v9.2d, v26.2s, v27.2s
	add x6, x6, x23
	umlal2 v11.2d, v26.4s, v27.4s
	lsr x8, x4, #56
	ldr q27, [x3, #4608]
	and x4, x4, x25
	umlal v5.2d, v23.2s, v27.2s
	add x5, x5, x8
	umlal2 v7.2d, v23.4s, v27.4s
	lsr x8, x6, #56
	umlal v7.2d, v24.2s, v27.2s
	and x6, x6, x25
	umlal2 v9.2d, v24.4s, v27.4s
	add x7, x7, x8
	umlal v9.2d, v25.2s, v27.2s
	str x4, [x3, #1728]
	umlal2 v11.2d, v25.4s, v27.4s
	str x5, [x3, #1736]
	umlal v11.2d, v26.2s, v27.2s
	str x6, [x3, #1760]
	umlal2 v13.2d, v26.4s, v27.4s
	str x7, [x3, #1768]
	ldr q27, [x3, #4624]
	movz x0, #39081, lsl #0
	umlal v7.2d, v23.2s, v27.2s
	movz x2, #43264, lsl #0
	umlal v9.2d, v24.2s, v27.2s
	movk x2, #152, lsl #16
	umlal v11.2d, v25.2s, v27.2s
	ldr x24, [x3, #1728]
	umlal v13.2d, v26.2s, v27.2s
	ldr x13, [x3, #1344]
	ldr q23, [x3, #4352]
	madd x13, x24, x0, x13
	ldr q24, [x3, #4368]
	umulh x4, x24, x2
	ldr q25, [x3, #4384]
	lsl x24, x4, #56
	ldr q26, [x3, #4400]
	sub x13, x13, x24
	ldr q27, [x3, #4416]
	ldr x24, [x3, #1736]
	umlal v8.2d, v23.2s, v27.2s
	ldr x14, [x3, #1352]
	umlal2 v10.2d, v23.4s, v27.4s
	madd x14, x24, x0, x14
	umlal v10.2d, v24.2s, v27.2s
	umulh x5, x24, x2
	umlal2 v12.2d, v24.4s, v27.4s
	lsl x24, x5, #56
	umlal v12.2d, v25.2s, v27.2s
	sub x14, x14, x24
	umlal2 v14.2d, v25.4s, v27.4s
	ldr x24, [x3, #1744]
	umlal v14.2d, v26.2s, v27.2s
	ldr x15, [x3, #1360]
	umull2 v16.2d, v26.4s, v27.4s
	madd x15, x24, x0, x15
	ldr q27, [x3, #4432]
	umulh x6, x24, x2
	umlal v10.2d, v23.2s, v27.2s
	lsl x24, x6, #56
	umlal2 v12.2d, v23.4s, v27.4s
	sub x15, x15, x24
	umlal v12.2d, v24.2s, v27.2s
	ldr x24, [x3, #1752]
	umlal2 v14.2d, v24.4s, v27.4s
	ldr x16, [x3, #1368]
	umlal v14.2d, v25.2s, v27.2s
	madd x16, x24, x0, x16
	umlal2 v16.2d, v25.4s, v27.4s
	umulh x7, x24, x2
	umlal v16.2d, v26.2s, v27.2s
	lsl x24, x7, #56
	umull2 v18.2d, v26.4s, v27.4s
	sub x16, x16, x24
	ldr q27, [x3, #4448]
	ldr x24, [x3, #1760]
	umlal v12.2d, v23.2s, v27.2s
	ldr x17, [x3, #1376]
	umlal2 v14.2d, v23.4s, v27.4s
	madd x17, x24, x0, x17
	umlal v14.2d, v24.2s, v27.2s
	umulh x8, x24, x2
	umlal2 v16.2d, v24.4s, v27.4s
	lsl x24, x8, #56
	umlal v16.2d, v25.2s, v27.2s
	sub x17, x17, x24
	umlal2 v18.2d, v25.4s, v27.4s
	ldr x24, [x3, #1768]
	umlal v18.2d, v26.2s, v27.2s
	ldr x21, [x3, #1384]
	umull2 v20.2d, v26.4s, v27.4s
	madd x21, x24, x0, x21
	ldr q27, [x3, #4464]
	umulh x9, x24, x2
	umlal v14.2d, v23.2s, v27.2s
	lsl x24, x9, #56
	umlal2 v16.2d, v23.4s, v27.4s
	sub x21, x21, x24
	umlal v16.2d, v24.2s, v27.2s
	ldr x24, [x3, #1776]
	umlal2 v18.2d, v24.4s, v27.4s
	ldr x22, [x3, #1392]
	umlal v18.2d, v25.2s, v27.2s
	madd x22, x24, x0, x22
	umlal2 v20.2d, v25.4s, v27.4s
	umulh x10, x24, x2
	umlal v20.2d, v26.2s, v27.2s
	lsl x24, x10, #56
	umull2 v22.2d, v26.4s, v27.4s
	sub x22, x22, x24
	ldr q27, [x3, #4640]
	ldr x24, [x3, #1784]
	umlal2 v9.2d, v23.4s, v27.4s
	ldr x23, [x3, #1400]
	umlal2 v11.2d, v24.4s, v27.4s
	madd x23, x24, x0, x23
	umlal2 v13.2d, v25.4s, v27.4s
	umulh x11, x24, x2
	umlal2 v15.2d, v26.4s, v27.4s
	lsl x24, x11, #56
	ldr q27, [x3, #4656]
	sub x23, x23, x24
	umlal v9.2d, v23.2s, v27.2s
	add x13, x13, x11
	umlal2 v11.2d, v23.4s, v27.4s
	str x13, [x3, #1856]
	umlal v11.2d, v24.2s, v27.2s
	add x14, x14, x4
	umlal2 v13.2d, v24.4s, v27.4s
	str x14, [x3, #1864]
	umlal v13.2d, v25.2s, v27.2s
	add x15, x15, x5
	umlal2 v15.2d, v25.4s, v27.4s
	str x15, [x3, #1872]
	umlal v15.2d, v26.2s, v27.2s
	add x16, x16, x6
	umull2 v17.2d, v26.4s, v27.4s
	str x16, [x3, #1880]
	ldr q27, [x3, #4672]
	add x17, x17, x7
	umlal v11.2d, v23.2s, v27.2s
	add x17, x17, x11
	umlal2 v13.2d, v23.4s, v27.4s
	str x17, [x3, #1888]
	umlal v13.2d, v24.2s, v27.2s
	add x21, x21, x8
	umlal2 v15.2d, v24.4s, v27.4s
	str x21, [x3, #1896]
	umlal v15.2d, v25.2s, v27.2s
	add x22, x22, x9
	umlal2 v17.2d, v25.4s, v27.4s
	str x22, [x3, #1904]
	umlal v17.2d, v26.2s, v27.2s
	add x23, x23, x10
	umull2 v19.2d, v26.4s, v27.4s
	str x23, [x3, #1912]
	ldr q27, [x3, #4688]
	movz x0, #65534, lsl #0
	umlal v13.2d, v23.2s, v27.2s
	movk x0, #65535, lsl #16
	umlal2 v15.2d, v23.4s, v27.4s
	movk x0, #65535, lsl #32
	umlal v15.2d, v24.2s, v27.2s
	movk x0, #511, lsl #48
	umlal2 v17.2d, v24.4s, v27.4s
	movz x2, #65532, lsl #0
	umlal v17.2d, v25.2s, v27.2s
	movk x2, #65535, lsl #16
	umlal2 v19.2d, v25.4s, v27.4s
	movk x2, #65535, lsl #32
	umlal v19.2d, v26.2s, v27.2s
	movk x2, #511, lsl #48
	umull2 v21.2d, v26.4s, v27.4s
	ldr x4, [x3, #2496]
	ldr q27, [x3, #4704]
	ldr x5, [x3, #1728]
	umlal v15.2d, v23.2s, v27.2s
	add x4, x4, x0
	umlal v17.2d, v24.2s, v27.2s
	sub x4, x4, x5
	umlal v19.2d, v25.2s, v27.2s
	str x4, [x3, #1984]
	umlal v21.2d, v26.2s, v27.2s
	ldr x4, [x3, #2504]
	add v0.2d, v0.2d, v16.2d
	ldr x5, [x3, #1736]
	add v8.2d, v8.2d, v16.2d
	add x4, x4, x0
	add v1.2d, v1.2d, v17.2d
	sub x4, x4, x5
	add v9.2d, v9.2d, v17.2d
	str x4, [x3, #1992]
	add v2.2d, v2.2d, v18.2d
	ldr x4, [x3, #2512]
	add v10.2d, v10.2d, v18.2d
	ldr x5, [x3, #1744]
	add v3.2d, v3.2d, v19.2d
	add x4, x4, x0
	add v11.2d, v11.2d, v19.2d
	sub x4, x4, x5
	add v4.2d, v4.2d, v20.2d
	str x4, [x3, #2000]
	add v12.2d, v12.2d, v20.2d
	ldr x4, [x3, #2520]
	add v5.2d, v5.2d, v21.2d
	ldr x5, [x3, #1752]
	add v13.2d, v13.2d, v21.2d
	add x4, x4, x0
	add v6.2d, v6.2d, v22.2d
	sub x4, x4, x5
	add v14.2d, v14.2d, v22.2d
	str x4, [x3, #2008]
	ushr v28.2d, v0.2d, #28
	ldr x4, [x3, #2528]
	and v0.16b, v0.16b, v30.16b
	ldr x5, [x3, #1760]
	add v1.2d, v1.2d, v28.2d
	add x4, x4, x2
	ushr v29.2d, v8.2d, #28
	sub x4, x4, x5
	and v8.16b, v8.16b, v30.16b
	str x4, [x3, #2016]
	add v9.2d, v9.2d, v29.2d
	ldr x4, [x3, #2536]
	ushr v28.2d, v1.2d, #28
	ldr x5, [x3, #1768]
	and v1.16b, v1.16b, v30.16b
	add x4, x4, x0
	add v2.2d, v2.2d, v28.2d
	sub x4, x4, x5
	ushr v29.2d, v9.2d, #28
	str x4, [x3, #2024]
	and v9.16b, v9.16b, v30.16b
	ldr x4, [x3, #2544]
	add v10.2d, v10.2d, v29.2d
	ldr x5, [x3, #1776]
	ushr v28.2d, v2.2d, #28
	add x4, x4, x0
	and v2.16b, v2.16b, v30.16b
	sub x4, x4, x5
	add v3.2d, v3.2d, v28.2d
	str x4, [x3, #2032]
	ushr v29.2d, v10.2d, #28
	ldr x4, [x3, #2552]
	and v10.16b, v10.16b, v30.16b
	ldr x5, [x3, #1784]
	add v11.2d, v11.2d, v29.2d
	add x4, x4, x0
	ushr v28.2d, v3.2d, #28
	sub x4, x4, x5
	and v3.16b, v3.16b, v30.16b
	str x4, [x3, #2040]
	add v4.2d, v4.2d, v28.2d
	movz x0, #39081, lsl #0
	ushr v29.2d, v11.2d, #28
	movz x2, #43264, lsl #0
	and v11.16b, v11.16b, v30.16b
	movk x2, #152, lsl #16
	add v12.2d, v12.2d, v29.2d
	ldr x24, [x3, #1984]
	ushr v28.2d, v4.2d, #28
	ldr x13, [x3, #1344]
	and v4.16b, v4.16b, v30.16b
	madd x13, x24, x0, x13
	add v5.2d, v5.2d, v28.2d
	umulh x4, x24, x2
	ushr v29.2d, v12.2d, #28
	lsl x24, x4, #56
	and v12.16b, v12.16b, v30.16b
	sub x13, x13, x24
	add v13.2d, v13.2d, v29.2d
	ldr x24, [x3, #1992]
	ushr v28.2d, v5.2d, #28
	ldr x14, [x3, #1352]
	and v5.16b, v5.16b, v30.16b
	madd x14, x24, x0, x14
	add v6.2d, v6.2d, v28.2d
	umulh x5, x24, x2
	ushr v29.2d, v13.2d, #28
	lsl x24, x5, #56
	and v13.16b, v13.16b, v30.16b
	sub x14, x14, x24
	add v14.2d, v14.2d, v29.2d
	ldr x24, [x3, #2000]
	ushr v28.2d, v6.2d, #28
	ldr x15, [x3, #1360]
	and v6.16b, v6.16b, v30.16b
	madd x15, x24, x0, x15
	add v7.2d, v7.2d, v28.2d
	umulh x6, x24, x2
	ushr v29.2d, v14.2d, #28
	lsl x24, x6, #56
	and v14.16b, v14.16b, v30.16b
	sub x15, x15, x24
	add v15.2d, v15.2d, v29.2d
	ldr x24, [x3, #2008]
	ushr v28.2d, v7.2d, #28
	ldr x16, [x3, #1368]
	and v7.16b, v7.16b, v30.16b
	madd x16, x24, x0, x16
	ushr v29.2d, v15.2d, #28
	umulh x7, x24, x2
	and v15.16b, v15.16b, v30.16b
	lsl x24, x7, #56
	add v8.2d, v8.2d, v28.2d
	sub x16, x16, x24
	add v8.2d, v8.2d, v29.2d
	ldr x24, [x3, #2016]
	add v0.2d, v0.2d, v29.2d
	ldr x17, [x3, #1376]
	shl v16.2d, v1.2d, #28
	madd x17, x24, x0, x17
	add v16.2d, v16.2d, v0.2d
	umulh x8, x24, x2
	shl v17.2d, v3.2d, #28
	lsl x24, x8, #56
	add v17.2d, v17.2d, v2.2d
	sub x17, x17, x24
	shl v18.2d, v5.2d, #28
	ldr x24, [x3, #2024]
	add v18.2d, v18.2d, v4.2d
	ldr x21, [x3, #1384]
	shl v19.2d, v7.2d, #28
	madd x21, x24, x0, x21
	add v19.2d, v19.2d, v6.2d
	umulh x9, x24, x2
	shl v20.2d, v9.2d, #28
	lsl x24, x9, #56
	add v20.2d, v20.2d, v8.2d
	sub x21, x21, x24
	shl v21.2d, v11.2d, #28
	ldr x24, [x3, #2032]
	add v21.2d, v21.2d, v10.2d
	ldr x22, [x3, #1392]
	shl v22.2d, v13.2d, #28
	madd x22, x24, x0, x22
	add v22.2d, v22.2d, v12.2d
	umulh x10, x24, x2
	shl v23.2d, v15.2d, #28
	lsl x24, x10, #56
	add v23.2d, v23.2d, v14.2d
	sub x22, x22, x24
	shl v31.2d, v30.2d, #28
	ldr x24, [x3, #2040]
	add v31.2d, v31.2d, v30.2d
	ldr x23, [x3, #1400]
	ushr v28.2d, v16.2d, #56
	madd x23, x24, x0, x23
	and v16.16b, v16.16b, v31.16b
	umulh x11, x24, x2
	add v17.2d, v17.2d, v28.2d
	lsl x24, x11, #56
	ushr v28.2d, v20.2d, #56
	sub x23, x23, x24
	and v20.16b, v20.16b, v31.16b
	add x13, x13, x11
	add v21.2d, v21.2d, v28.2d
	str x13, [x3, #1344]
	trn1 v8.2d, v16.2d, v17.2d
	add x14, x14, x4
	trn2 v9.2d, v16.2d, v17.2d
	str x14, [x3, #1352]
	str q8, [x3, #2112]
	add x15, x15, x5
	str q9, [x3, #2240]
	str x15, [x3, #1360]
	trn1 v8.2d, v18.2d, v19.2d
	add x16, x16, x6
	trn2 v9.2d, v18.2d, v19.2d
	str x16, [x3, #1368]
	str q8, [x3, #2128]
	add x17, x17, x7
	str q9, [x3, #2256]
	add x17, x17, x11
	trn1 v8.2d, v20.2d, v21.2d
	str x17, [x3, #1376]
	trn2 v9.2d, v20.2d, v21.2d
	add x21, x21, x8
	str q8, [x3, #2144]
	str x21, [x3, #1384]
	str q9, [x3, #2272]
	add x22, x22, x9
	trn1 v8.2d, v22.2d, v23.2d
	str x22, [x3, #1392]
	trn2 v9.2d, v22.2d, v23.2d
	add x23, x23, x10
	str q8, [x3, #2160]
	str x23, [x3, #1400]
	str q9, [x3, #2288]
	movz x0, #65534, lsl #0
	movk x0, #65535, lsl #16
	movk x0, #65535, lsl #32
	movk x0, #511, lsl #48
	movz x2, #65532, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #511, lsl #48
	ldr x4, [x3, #2112]
	ldr x5, [x3, #2240]
	add x6, x4, x5
	str x6, [x3, #1728]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #1984]
	ldr x4, [x3, #2120]
	ldr x5, [x3, #2248]
	add x6, x4, x5
	str x6, [x3, #1736]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #1992]
	ldr x4, [x3, #2128]
	ldr x5, [x3, #2256]
	add x6, x4, x5
	str x6, [x3, #1744]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2000]
	ldr x4, [x3, #2136]
	ldr x5, [x3, #2264]
	add x6, x4, x5
	str x6, [x3, #1752]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2008]
	ldr x4, [x3, #2144]
	ldr x5, [x3, #2272]
	add x6, x4, x5
	str x6, [x3, #1760]
	add x7, x4, x2
	sub x7, x7, x5
	str x7, [x3, #2016]
	ldr x4, [x3, #2152]
	ldr x5, [x3, #2280]
	add x6, x4, x5
	str x6, [x3, #1768]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2024]
	ldr x4, [x3, #2160]
	ldr x5, [x3, #2288]
	add x6, x4, x5
	str x6, [x3, #1776]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2032]
	ldr x4, [x3, #2168]
	ldr x5, [x3, #2296]
	add x6, x4, x5
	str x6, [x3, #1784]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2040]
	movz x0, #65534, lsl #0
	movk x0, #65535, lsl #16
	movk x0, #65535, lsl #32
	movk x0, #511, lsl #48
	movz x2, #65532, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #511, lsl #48
	ldr x4, [x3, #1600]
	ldr x5, [x3, #1472]
	add x6, x4, x5
	str x6, [x3, #2112]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2240]
	ldr x4, [x3, #1608]
	ldr x5, [x3, #1480]
	add x6, x4, x5
	str x6, [x3, #2120]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2248]
	ldr x4, [x3, #1616]
	ldr x5, [x3, #1488]
	add x6, x4, x5
	str x6, [x3, #2128]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2256]
	ldr x4, [x3, #1624]
	ldr x5, [x3, #1496]
	add x6, x4, x5
	str x6, [x3, #2136]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2264]
	ldr x4, [x3, #1632]
	ldr x5, [x3, #1504]
	add x6, x4, x5
	str x6, [x3, #2144]
	add x7, x4, x2
	sub x7, x7, x5
	str x7, [x3, #2272]
	ldr x4, [x3, #1640]
	ldr x5, [x3, #1512]
	add x6, x4, x5
	str x6, [x3, #2152]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2280]
	ldr x4, [x3, #1648]
	ldr x5, [x3, #1520]
	add x6, x4, x5
	str x6, [x3, #2160]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2288]
	ldr x4, [x3, #1656]
	ldr x5, [x3, #1528]
	add x6, x4, x5
	str x6, [x3, #2168]
	add x7, x4, x0
	sub x7, x7, x5
	str x7, [x3, #2296]
	ldr x0, [x3, #1856]
	dup v30.2d, x12
	movi v31.2d, #0
	ldr x2, [x3, #1864]
	ldr q0, [x3, #704]
	ldr q1, [x3, #704]
	ldr x4, [x3, #1872]
	trn1 v2.2d, v0.2d, v1.2d
	ldr x5, [x3, #1880]
	trn2 v3.2d, v0.2d, v1.2d
	and v0.16b, v2.16b, v30.16b
	ldr x6, [x3, #1888]
	ushr v1.2d, v2.2d, #28
	ldr x7, [x3, #1896]
	uzp1 v2.4s, v0.4s, v1.4s
	str q2, [x3, #4096]
	ldr x8, [x3, #1904]
	and v0.16b, v3.16b, v30.16b
	ldr x9, [x3, #1912]
	ushr v1.2d, v3.2d, #28
	uzp1 v3.4s, v0.4s, v1.4s
	movz x25, #65535, lsl #0
	str q3, [x3, #4112]
	movk x25, #65535, lsl #16
	ldr q0, [x3, #720]
	ldr q1, [x3, #720]
	movk x25, #65535, lsl #32
	trn1 v2.2d, v0.2d, v1.2d
	movk x25, #255, lsl #48
	trn2 v3.2d, v0.2d, v1.2d
	and v0.16b, v2.16b, v30.16b
	movz x26, #0, lsl #0
	ushr v1.2d, v2.2d, #28
	add x13, x0, x6
	uzp1 v2.4s, v0.4s, v1.4s
	str q2, [x3, #4128]
	str x13, [x3, #3584]
	and v0.16b, v3.16b, v30.16b
	ushr v1.2d, v3.2d, #28
	ldr x10, [x3, #1344]
	uzp1 v3.4s, v0.4s, v1.4s
	ldr x11, [x3, #1376]
	str q3, [x3, #4144]
	ldr q0, [x3, #736]
	add x10, x10, x11
	ldr q1, [x3, #736]
	str x10, [x3, #3616]
	trn1 v2.2d, v0.2d, v1.2d
	trn2 v3.2d, v0.2d, v1.2d
	add x13, x2, x7
	and v0.16b, v2.16b, v30.16b
	str x13, [x3, #3592]
	ushr v1.2d, v2.2d, #28
	uzp1 v2.4s, v0.4s, v1.4s
	ldr x10, [x3, #1352]
	str q2, [x3, #4160]
	ldr x11, [x3, #1384]
	and v0.16b, v3.16b, v30.16b
	ushr v1.2d, v3.2d, #28
	add x10, x10, x11
	uzp1 v3.4s, v0.4s, v1.4s
	str x10, [x3, #3624]
	str q3, [x3, #4176]
	ldr q0, [x3, #752]
	add x13, x4, x8
	ldr q1, [x3, #752]
	str x13, [x3, #3600]
	trn1 v2.2d, v0.2d, v1.2d
	trn2 v3.2d, v0.2d, v1.2d
	ldr x10, [x3, #1360]
	and v0.16b, v2.16b, v30.16b
	ldr x11, [x3, #1392]
	ushr v1.2d, v2.2d, #28
	uzp1 v2.4s, v0.4s, v1.4s
	add x10, x10, x11
	str q2, [x3, #4192]
	and v0.16b, v3.16b, v30.16b
	str x10, [x3, #3632]
	ushr v1.2d, v3.2d, #28
	add x13, x5, x9
	uzp1 v3.4s, v0.4s, v1.4s
	str q3, [x3, #4208]
	str x13, [x3, #3608]
	ldr q4, [x3, #1856]
	ldr x10, [x3, #1368]
	ldr q5, [x3, #1344]
	trn1 v6.2d, v4.2d, v5.2d
	ldr x11, [x3, #1400]
	trn2 v7.2d, v4.2d, v5.2d
	add x10, x10, x11
	and v4.16b, v6.16b, v30.16b
	ushr v5.2d, v6.2d, #28
	str x10, [x3, #3640]
	uzp1 v6.4s, v4.4s, v5.4s
	ldr x11, [x3, #1376]
	str q6, [x3, #4224]
	and v4.16b, v7.16b, v30.16b
	mul x14, x6, x11
	ushr v5.2d, v7.2d, #28
	umulh x15, x6, x11
	uzp1 v7.4s, v4.4s, v5.4s
	str q7, [x3, #4240]
	ldr x11, [x3, #1400]
	ldr q4, [x3, #1872]
	mul x16, x7, x11
	ldr q5, [x3, #1360]
	trn1 v6.2d, v4.2d, v5.2d
	umulh x17, x7, x11
	trn2 v7.2d, v4.2d, v5.2d
	ldr x11, [x3, #1392]
	and v4.16b, v6.16b, v30.16b
	ushr v5.2d, v6.2d, #28
	mul x10, x8, x11
	uzp1 v6.4s, v4.4s, v5.4s
	str q6, [x3, #4256]
	umulh x11, x8, x11
	and v4.16b, v7.16b, v30.16b
	adds x16, x16, x10
	ushr v5.2d, v7.2d, #28
	uzp1 v7.4s, v4.4s, v5.4s
	adc x17, x17, x11
	str q7, [x3, #4272]
	ldr x11, [x3, #1384]
	ldr q4, [x3, #1888]
	ldr q5, [x3, #1376]
	mul x10, x9, x11
	trn1 v6.2d, v4.2d, v5.2d
	umulh x11, x9, x11
	trn2 v7.2d, v4.2d, v5.2d
	and v4.16b, v6.16b, v30.16b
	adds x16, x16, x10
	ushr v5.2d, v6.2d, #28
	adc x17, x17, x11
	uzp1 v6.4s, v4.4s, v5.4s
	str q6, [x3, #4288]
	ldr x13, [x3, #3584]
	and v4.16b, v7.16b, v30.16b
	ldr x11, [x3, #3616]
	ushr v5.2d, v7.2d, #28
	uzp1 v7.4s, v4.4s, v5.4s
	mul x10, x13, x11
	str q7, [x3, #4304]
	umulh x11, x13, x11
	ldr q4, [x3, #1904]
	ldr q5, [x3, #1392]
	adds x16, x16, x10
	trn1 v6.2d, v4.2d, v5.2d
	trn2 v7.2d, v4.2d, v5.2d
	adc x17, x17, x11
	and v4.16b, v6.16b, v30.16b
	ldr x13, [x3, #3592]
	ushr v5.2d, v6.2d, #28
	uzp1 v6.4s, v4.4s, v5.4s
	ldr x11, [x3, #3640]
	str q6, [x3, #4320]
	mul x27, x13, x11
	and v4.16b, v7.16b, v30.16b
	ushr v5.2d, v7.2d, #28
	umulh x28, x13, x11
	uzp1 v7.4s, v4.4s, v5.4s
	ldr x13, [x3, #3600]
	str q7, [x3, #4336]
	ldr q0, [x3, #4096]
	ldr x11, [x3, #3632]
	ldr q1, [x3, #4160]
	mul x10, x13, x11
	add v0.4s, v0.4s, v1.4s
	str q0, [x3, #4352]
	umulh x11, x13, x11
	ldr q2, [x3, #4224]
	adds x27, x27, x10
	ldr q3, [x3, #4288]
	add v2.4s, v2.4s, v3.4s
	adc x28, x28, x11
	str q2, [x3, #4416]
	ldr x13, [x3, #3608]
	ldr q0, [x3, #4112]
	ldr q1, [x3, #4176]
	ldr x11, [x3, #3624]
	add v0.4s, v0.4s, v1.4s
	mul x10, x13, x11
	str q0, [x3, #4368]
	ldr q2, [x3, #4240]
	umulh x11, x13, x11
	ldr q3, [x3, #4304]
	add v2.4s, v2.4s, v3.4s
	adds x27, x27, x10
	str q2, [x3, #4432]
	adc x28, x28, x11
	ldr q0, [x3, #4128]
	ldr q1, [x3, #4192]
	adds x14, x14, x27
	add v0.4s, v0.4s, v1.4s
	adc x15, x15, x28
	str q0, [x3, #4384]
	ldr q2, [x3, #4256]
	adds x16, x16, x27
	ldr q3, [x3, #4320]
	adc x17, x17, x28
	add v2.4s, v2.4s, v3.4s
	str q2, [x3, #4448]
	ldr x11, [x3, #1344]
	ldr q0, [x3, #4144]
	mul x10, x0, x11
	ldr q1, [x3, #4208]
	add v0.4s, v0.4s, v1.4s
	umulh x11, x0, x11
	str q0, [x3, #4400]
	adds x14, x14, x10
	ldr q2, [x3, #4272]
	ldr q3, [x3, #4336]
	adc x15, x15, x11
	add v2.4s, v2.4s, v3.4s
	subs x16, x16, x10
	str q2, [x3, #4464]
	ldr q0, [x3, #4224]
	sbc x17, x17, x11
	ldr q1, [x3, #4240]
	ldr x11, [x3, #1368]
	ldr q2, [x3, #4256]
	ldr q3, [x3, #4272]
	mul x10, x2, x11
	ext v4.16b, v31.16b, v0.16b, #8
	ext v5.16b, v0.16b, v1.16b, #8
	umulh x11, x2, x11
	ext v6.16b, v1.16b, v2.16b, #8
	subs x14, x14, x10
	ext v7.16b, v2.16b, v3.16b, #8
	ext v8.16b, v3.16b, v31.16b, #8
	sbc x15, x15, x11
	str q4, [x3, #4480]
	ldr x11, [x3, #1360]
	str q5, [x3, #4496]
	str q6, [x3, #4512]
	mul x10, x4, x11
	str q7, [x3, #4528]
	umulh x11, x4, x11
	str q8, [x3, #4544]
	ldr q0, [x3, #4288]
	subs x14, x14, x10
	ldr q1, [x3, #4304]
	sbc x15, x15, x11
	ldr q2, [x3, #4320]
	ldr q3, [x3, #4336]
	ldr x11, [x3, #1352]
	ext v4.16b, v31.16b, v0.16b, #8
	mul x10, x5, x11
	ext v5.16b, v0.16b, v1.16b, #8
	ext v6.16b, v1.16b, v2.16b, #8
	umulh x11, x5, x11
	ext v7.16b, v2.16b, v3.16b, #8
	subs x14, x14, x10
	ext v8.16b, v3.16b, v31.16b, #8
	str q4, [x3, #4560]
	sbc x15, x15, x11
	str q5, [x3, #4576]
	str q6, [x3, #4592]
	and x10, x14, x25
	str q7, [x3, #4608]
	str x10, [x3, #2368]
	str q8, [x3, #4624]
	ldr q0, [x3, #4416]
	extr x23, x15, x14, #56
	ldr q1, [x3, #4432]
	and x10, x16, x25
	ldr q2, [x3, #4448]
	ldr q3, [x3, #4464]
	str x10, [x3, #2400]
	ext v4.16b, v31.16b, v0.16b, #8
	extr x24, x17, x16, #56
	ext v5.16b, v0.16b, v1.16b, #8
	ext v6.16b, v1.16b, v2.16b, #8
	ldr x11, [x3, #1384]
	ext v7.16b, v2.16b, v3.16b, #8
	mul x14, x6, x11
	ext v8.16b, v3.16b, v31.16b, #8
	str q4, [x3, #4640]
	umulh x15, x6, x11
	str q5, [x3, #4656]
	ldr x11, [x3, #1376]
	str q6, [x3, #4672]
	str q7, [x3, #4688]
	mul x10, x7, x11
	str q8, [x3, #4704]
	umulh x11, x7, x11
	ldr q23, [x3, #4096]
	ldr q24, [x3, #4112]
	adds x14, x14, x10
	ldr q25, [x3, #4128]
	adc x15, x15, x11
	ldr q26, [x3, #4144]
	ldr q27, [x3, #4224]
	ldr x11, [x3, #1400]
	umull v0.2d, v23.2s, v27.2s
	umull2 v2.2d, v23.4s, v27.4s
	mul x16, x8, x11
	umlal v2.2d, v24.2s, v27.2s
	umulh x17, x8, x11
	umull2 v4.2d, v24.4s, v27.4s
	umlal v4.2d, v25.2s, v27.2s
	ldr x11, [x3, #1392]
	umull2 v6.2d, v25.4s, v27.4s
	mul x10, x9, x11
	umlal v6.2d, v26.2s, v27.2s
	umull2 v8.2d, v26.4s, v27.4s
	umulh x11, x9, x11
	ldr q27, [x3, #4240]
	adds x16, x16, x10
	umlal v2.2d, v23.2s, v27.2s
	umlal2 v4.2d, v23.4s, v27.4s
	adc x17, x17, x11
	umlal v4.2d, v24.2s, v27.2s
	ldr x13, [x3, #3584]
	umlal2 v6.2d, v24.4s, v27.4s
	umlal v6.2d, v25.2s, v27.2s
	ldr x11, [x3, #3624]
	umlal2 v8.2d, v25.4s, v27.4s
	mul x10, x13, x11
	umlal v8.2d, v26.2s, v27.2s
	umull2 v10.2d, v26.4s, v27.4s
	umulh x11, x13, x11
	ldr q27, [x3, #4256]
	adds x16, x16, x10
	umlal v4.2d, v23.2s, v27.2s
	umlal2 v6.2d, v23.4s, v27.4s
	adc x17, x17, x11
	umlal v6.2d, v24.2s, v27.2s
	ldr x13, [x3, #3592]
	umlal2 v8.2d, v24.4s, v27.4s
	umlal v8.2d, v25.2s, v27.2s
	ldr x11, [x3, #3616]
	umlal2 v10.2d, v25.4s, v27.4s
	umlal v10.2d, v26.2s, v27.2s
	mul x10, x13, x11
	umull2 v12.2d, v26.4s, v27.4s
	umulh x11, x13, x11
	ldr q27, [x3, #4272]
	umlal v6.2d, v23.2s, v27.2s
	adds x16, x16, x10
	umlal2 v8.2d, v23.4s, v27.4s
	adc x17, x17, x11
	umlal v8.2d, v24.2s, v27.2s
	umlal2 v10.2d, v24.4s, v27.4s
	ldr x13, [x3, #3600]
	umlal v10.2d, v25.2s, v27.2s
	ldr x11, [x3, #3640]
	umlal2 v12.2d, v25.4s, v27.4s
	umlal v12.2d, v26.2s, v27.2s
	mul x27, x13, x11
	umull2 v14.2d, v26.4s, v27.4s
	umulh x28, x13, x11
	ldr q27, [x3, #4480]
	umull2 v1.2d, v23.4s, v27.4s
	ldr x13, [x3, #3608]
	umull2 v3.2d, v24.4s, v27.4s
	ldr x11, [x3, #3632]
	umull2 v5.2d, v25.4s, v27.4s
	umull2 v7.2d, v26.4s, v27.4s
	mul x10, x13, x11
	ldr q27, [x3, #4496]
	umulh x11, x13, x11
	umlal v1.2d, v23.2s, v27.2s
	umlal2 v3.2d, v23.4s, v27.4s
	adds x27, x27, x10
	umlal v3.2d, v24.2s, v27.2s
	umlal2 v5.2d, v24.4s, v27.4s
	adc x28, x28, x11
	umlal v5.2d, v25.2s, v27.2s
	adds x14, x14, x27
	umlal2 v7.2d, v25.4s, v27.4s
	umlal v7.2d, v26.2s, v27.2s
	adc x15, x15, x28
	umull2 v9.2d, v26.4s, v27.4s
	adds x16, x16, x27
	ldr q27, [x3, #4512]
	umlal v3.2d, v23.2s, v27.2s
	adc x17, x17, x28
	umlal2 v5.2d, v23.4s, v27.4s
	ldr x11, [x3, #1352]
	umlal v5.2d, v24.2s, v27.2s
	umlal2 v7.2d, v24.4s, v27.4s
	mul x21, x0, x11
	umlal v7.2d, v25.2s, v27.2s
	umulh x22, x0, x11
	umlal2 v9.2d, v25.4s, v27.4s
	umlal v9.2d, v26.2s, v27.2s
	ldr x11, [x3, #1344]
	umull2 v11.2d, v26.4s, v27.4s
	mul x10, x2, x11
	ldr q27, [x3, #4528]
	umlal v5.2d, v23.2s, v27.2s
	umulh x11, x2, x11
	umlal2 v7.2d, v23.4s, v27.4s
	adds x21, x21, x10
	umlal v7.2d, v24.2s, v27.2s
	umlal2 v9.2d, v24.4s, v27.4s
	adc x22, x22, x11
	umlal v9.2d, v25.2s, v27.2s
	adds x14, x14, x21
	umlal2 v11.2d, v25.4s, v27.4s
	umlal v11.2d, v26.2s, v27.2s
	adc x15, x15, x22
	umull2 v13.2d, v26.4s, v27.4s
	ldr q27, [x3, #4544]
	subs x16, x16, x21
	umlal v7.2d, v23.2s, v27.2s
	sbc x17, x17, x22
	umlal v9.2d, v24.2s, v27.2s
	umlal v11.2d, v25.2s, v27.2s
	ldr x11, [x3, #1368]
	umlal v13.2d, v26.2s, v27.2s
	mul x10, x4, x11
	mov v28.16b, v8.16b
	sub v8.2d, v31.2d, v0.2d
	umulh x11, x4, x11
	sub v0.2d, v0.2d, v28.2d
	subs x14, x14, x10
	mov v28.16b, v9.16b
	sub v9.2d, v31.2d, v1.2d
	sbc x15, x15, x11
	sub v1.2d, v1.2d, v28.2d
	ldr x11, [x3, #1360]
	mov v28.16b, v10.16b
	sub v10.2d, v31.2d, v2.2d
	mul x10, x5, x11
	sub v2.2d, v2.2d, v28.2d
	umulh x11, x5, x11
	mov v28.16b, v11.16b
	sub v11.2d, v31.2d, v3.2d
	subs x14, x14, x10
	sub v3.2d, v3.2d, v28.2d
	sbc x15, x15, x11
	mov v28.16b, v12.16b
	sub v12.2d, v31.2d, v4.2d
	adds x14, x14, x23
	sub v4.2d, v4.2d, v28.2d
	adc x15, x15, x26
	mov v28.16b, v13.16b
	sub v13.2d, v31.2d, v5.2d
	and x10, x14, x25
	sub v5.2d, v5.2d, v28.2d
	mov v28.16b, v14.16b
	str x10, [x3, #2376]
	sub v14.2d, v31.2d, v6.2d
	extr x23, x15, x14, #56
	sub v6.2d, v6.2d, v28.2d
	sub v15.2d, v31.2d, v7.2d
	adds x16, x16, x24
	ldr q23, [x3, #4160]
	adc x17, x17, x26
	ldr q24, [x3, #4176]
	ldr q25, [x3, #4192]
	and x10, x16, x25
	ldr q26, [x3, #4208]
	str x10, [x3, #2408]
	ldr q27, [x3, #4288]
	umlal v0.2d, v23.2s, v27.2s
	extr x24, x17, x16, #56
	umlal2 v2.2d, v23.4s, v27.4s
	ldr x11, [x3, #1392]
	umlal v2.2d, v24.2s, v27.2s
	umlal2 v4.2d, v24.4s, v27.4s
	mul x14, x6, x11
	umlal v4.2d, v25.2s, v27.2s
	umulh x15, x6, x11
	umlal2 v6.2d, v25.4s, v27.4s
	umlal v6.2d, v26.2s, v27.2s
	ldr x11, [x3, #1384]
	umlal2 v8.2d, v26.4s, v27.4s
	mul x10, x7, x11
	ldr q27, [x3, #4304]
	umlal v2.2d, v23.2s, v27.2s
	umulh x11, x7, x11
	umlal2 v4.2d, v23.4s, v27.4s
	umlal v4.2d, v24.2s, v27.2s
	adds x14, x14, x10
	umlal2 v6.2d, v24.4s, v27.4s
	adc x15, x15, x11
	umlal v6.2d, v25.2s, v27.2s
	umlal2 v8.2d, v25.4s, v27.4s
	ldr x11, [x3, #1376]
	umlal v8.2d, v26.2s, v27.2s
	mul x10, x8, x11
	umlal2 v10.2d, v26.4s, v27.4s
	ldr q27, [x3, #4320]
	umulh x11, x8, x11
	umlal v4.2d, v23.2s, v27.2s
	adds x14, x14, x10
	umlal2 v6.2d, v23.4s, v27.4s
	umlal v6.2d, v24.2s, v27.2s
	adc x15, x15, x11
	umlal2 v8.2d, v24.4s, v27.4s
	ldr x11, [x3, #1400]
	umlal v8.2d, v25.2s, v27.2s
	umlal2 v10.2d, v25.4s, v27.4s
	mul x16, x9, x11
	umlal v10.2d, v26.2s, v27.2s
	umulh x17, x9, x11
	umlal2 v12.2d, v26.4s, v27.4s
	ldr q27, [x3, #4336]
	ldr x13, [x3, #3584]
	umlal v6.2d, v23.2s, v27.2s
	ldr x11, [x3, #3632]
	umlal2 v8.2d, v23.4s, v27.4s
	umlal v8.2d, v24.2s, v27.2s
	mul x10, x13, x11
	umlal2 v10.2d, v24.4s, v27.4s
	umulh x11, x13, x11
	umlal v10.2d, v25.2s, v27.2s
	umlal2 v12.2d, v25.4s, v27.4s
	adds x16, x16, x10
	umlal v12.2d, v26.2s, v27.2s
	umlal2 v14.2d, v26.4s, v27.4s
	adc x17, x17, x11
	ldr q27, [x3, #4560]
	ldr x13, [x3, #3592]
	umlal2 v1.2d, v23.4s, v27.4s
	umlal2 v3.2d, v24.4s, v27.4s
	ldr x11, [x3, #3624]
	umlal2 v5.2d, v25.4s, v27.4s
	mul x10, x13, x11
	umlal2 v7.2d, v26.4s, v27.4s
	ldr q27, [x3, #4576]
	umulh x11, x13, x11
	umlal v1.2d, v23.2s, v27.2s
	adds x16, x16, x10
	umlal2 v3.2d, v23.4s, v27.4s
	umlal v3.2d, v24.2s, v27.2s
	adc x17, x17, x11
	umlal2 v5.2d, v24.4s, v27.4s
	ldr x13, [x3, #3600]
	umlal v5.2d, v25.2s, v27.2s
	umlal2 v7.2d, v25.4s, v27.4s
	ldr x11, [x3, #3616]
	umlal v7.2d, v26.2s, v27.2s
	mul x10, x13, x11
	umlal2 v9.2d, v26.4s, v27.4s
	ldr q27, [x3, #4592]
	umulh x11, x13, x11
	umlal v3.2d, v23.2s, v27.2s
	adds x16, x16, x10
	umlal2 v5.2d, v23.4s, v27.4s
	umlal v5.2d, v24.2s, v27.2s
	adc x17, x17, x11
	umlal2 v7.2d, v24.4s, v27.4s
	ldr x13, [x3, #3608]
	umlal v7.2d, v25.2s, v27.2s
	umlal2 v9.2d, v25.4s, v27.4s
	ldr x11, [x3, #3640]
	umlal v9.2d, v26.2s, v27.2s
	umlal2 v11.2d, v26.4s, v27.4s
	mul x10, x13, x11
	ldr q27, [x3, #4608]
	umulh x11, x13, x11
	umlal v5.2d, v23.2s, v27.2s
	umlal2 v7.2d, v23.4s, v27.4s
	adds x14, x14, x10
	umlal v7.2d, v24.2s, v27.2s
	adc x15, x15, x11
	umlal2 v9.2d, v24.4s, v27.4s
	umlal v9.2d, v25.2s, v27.2s
	adds x16, x16, x10
	umlal2 v11.2d, v25.4s, v27.4s
	adc x17, x17, x11
	umlal v11.2d, v26.2s, v27.2s
	umlal2 v13.2d, v26.4s, v27.4s
	ldr x11, [x3, #1360]
	ldr q27, [x3, #4624]
	mul x21, x0, x11
	umlal v7.2d, v23.2s, v27.2s
	umlal v9.2d, v24.2s, v27.2s
	umulh x22, x0, x11
	umlal v11.2d, v25.2s, v27.2s
	ldr x11, [x3, #1352]
	umlal v13.2d, v26.2s, v27.2s
	ldr q23, [x3, #4352]
	mul x10, x2, x11
	ldr q24, [x3, #4368]
	umulh x11, x2, x11
	ldr q25, [x3, #4384]
	ldr q26, [x3, #4400]
	adds x21, x21, x10
	ldr q27, [x3, #4416]
	umlal v8.2d, v23.2s, v27.2s
	adc x22, x22, x11
	umlal2 v10.2d, v23.4s, v27.4s
	ldr x11, [x3, #1344]
	umlal v10.2d, v24.2s, v27.2s
	umlal2 v12.2d, v24.4s, v27.4s
	mul x10, x4, x11
	umlal v12.2d, v25.2s, v27.2s
	umulh x11, x4, x11
	umlal2 v14.2d, v25.4s, v27.4s
	umlal v14.2d, v26.2s, v27.2s
	adds x21, x21, x10
	umull2 v16.2d, v26.4s, v27.4s
	adc x22, x22, x11
	ldr q27, [x3, #4432]
	umlal v10.2d, v23.2s, v27.2s
	adds x14, x14, x21
	umlal2 v12.2d, v23.4s, v27.4s
	adc x15, x15, x22
	umlal v12.2d, v24.2s, v27.2s
	umlal2 v14.2d, v24.4s, v27.4s
	subs x16, x16, x21
	umlal v14.2d, v25.2s, v27.2s
	sbc x17, x17, x22
	umlal2 v16.2d, v25.4s, v27.4s
	umlal v16.2d, v26.2s, v27.2s
	ldr x11, [x3, #1368]
	umull2 v18.2d, v26.4s, v27.4s
	mul x10, x5, x11
	ldr q27, [x3, #4448]
	umlal v12.2d, v23.2s, v27.2s
	umulh x11, x5, x11
	umlal2 v14.2d, v23.4s, v27.4s
	subs x14, x14, x10
	umlal v14.2d, v24.2s, v27.2s
	umlal2 v16.2d, v24.4s, v27.4s
	sbc x15, x15, x11
	umlal v16.2d, v25.2s, v27.2s
	umlal2 v18.2d, v25.4s, v27.4s
	adds x14, x14, x23
	umlal v18.2d, v26.2s, v27.2s
	adc x15, x15, x26
	umull2 v20.2d, v26.4s, v27.4s
	ldr q27, [x3, #4464]
	and x10, x14, x25
	umlal v14.2d, v23.2s, v27.2s
	str x10, [x3, #2384]
	umlal2 v16.2d, v23.4s, v27.4s
	umlal v16.2d, v24.2s, v27.2s
	extr x23, x15, x14, #56
	umlal2 v18.2d, v24.4s, v27.4s
	adds x16, x16, x24
	umlal v18.2d, v25.2s, v27.2s
	umlal2 v20.2d, v25.4s, v27.4s
	adc x17, x17, x26
	umlal v20.2d, v26.2s, v27.2s
	and x10, x16, x25
	umull2 v22.2d, v26.4s, v27.4s
	ldr q27, [x3, #4640]
	str x10, [x3, #2416]
	umlal2 v9.2d, v23.4s, v27.4s
	extr x24, x17, x16, #56
	umlal2 v11.2d, v24.4s, v27.4s
	umlal2 v13.2d, v25.4s, v27.4s
	ldr x11, [x3, #1400]
	umlal2 v15.2d, v26.4s, v27.4s
	mul x14, x6, x11
	ldr q27, [x3, #4656]
	umlal v9.2d, v23.2s, v27.2s
	umulh x15, x6, x11
	umlal2 v11.2d, v23.4s, v27.4s
	ldr x11, [x3, #1392]
	umlal v11.2d, v24.2s, v27.2s
	umlal2 v13.2d, v24.4s, v27.4s
	mul x10, x7, x11
	umlal v13.2d, v25.2s, v27.2s
	umlal2 v15.2d, v25.4s, v27.4s
	umulh x11, x7, x11
	umlal v15.2d, v26.2s, v27.2s
	adds x14, x14, x10
	umull2 v17.2d, v26.4s, v27.4s
	ldr q27, [x3, #4672]
	adc x15, x15, x11
	umlal v11.2d, v23.2s, v27.2s
	ldr x11, [x3, #1384]
	umlal2 v13.2d, v23.4s, v27.4s
	umlal v13.2d, v24.2s, v27.2s
	mul x10, x8, x11
	umlal2 v15.2d, v24.4s, v27.4s
	umulh x11, x8, x11
	umlal v15.2d, v25.2s, v27.2s
	umlal2 v17.2d, v25.4s, v27.4s
	adds x14, x14, x10
	umlal v17.2d, v26.2s, v27.2s
	adc x15, x15, x11
	umull2 v19.2d, v26.4s, v27.4s
	ldr q27, [x3, #4688]
	ldr x11, [x3, #1376]
	umlal v13.2d, v23.2s, v27.2s
	mul x10, x9, x11
	umlal2 v15.2d, v23.4s, v27.4s
	umlal v15.2d, v24.2s, v27.2s
	umulh x11, x9, x11
	umlal2 v17.2d, v24.4s, v27.4s
	adds x14, x14, x10
	umlal v17.2d, v25.2s, v27.2s
	umlal2 v19.2d, v25.4s, v27.4s
	adc x15, x15, x11
	umlal v19.2d, v26.2s, v27.2s
	umull2 v21.2d, v26.4s, v27.4s
	ldr x13, [x3, #3584]
	ldr q27, [x3, #4704]
	ldr x11, [x3, #3640]
	umlal v15.2d, v23.2s, v27.2s
	umlal v17.2d, v24.2s, v27.2s
	mul x16, x13, x11
	umlal v19.2d, v25.2s, v27.2s
	umulh x17, x13, x11
	umlal v21.2d, v26.2s, v27.2s
	add v0.2d, v0.2d, v16.2d
	ldr x13, [x3, #3592]
	add v8.2d, v8.2d, v16.2d
	ldr x11, [x3, #3632]
	add v1.2d, v1.2d, v17.2d
	add v9.2d, v9.2d, v17.2d
	mul x10, x13, x11
	add v2.2d, v2.2d, v18.2d
	umulh x11, x13, x11
	add v10.2d, v10.2d, v18.2d
	add v3.2d, v3.2d, v19.2d
	adds x16, x16, x10
	add v11.2d, v11.2d, v19.2d
	adc x17, x17, x11
	add v4.2d, v4.2d, v20.2d
	add v12.2d, v12.2d, v20.2d
	ldr x13, [x3, #3600]
	add v5.2d, v5.2d, v21.2d
	ldr x11, [x3, #3624]
	add v13.2d, v13.2d, v21.2d
	add v6.2d, v6.2d, v22.2d
	mul x10, x13, x11
	add v14.2d, v14.2d, v22.2d
	umulh x11, x13, x11
	ushr v28.2d, v0.2d, #28
	and v0.16b, v0.16b, v30.16b
	adds x16, x16, x10
	add v1.2d, v1.2d, v28.2d
	ushr v29.2d, v8.2d, #28
	adc x17, x17, x11
	and v8.16b, v8.16b, v30.16b
	ldr x13, [x3, #3608]
	add v9.2d, v9.2d, v29.2d
	ushr v28.2d, v1.2d, #28
	ldr x11, [x3, #3616]
	and v1.16b, v1.16b, v30.16b
	mul x10, x13, x11
	add v2.2d, v2.2d, v28.2d
	ushr v29.2d, v9.2d, #28
	umulh x11, x13, x11
	and v9.16b, v9.16b, v30.16b
	adds x16, x16, x10
	add v10.2d, v10.2d, v29.2d
	ushr v28.2d, v2.2d, #28
	adc x17, x17, x11
	and v2.16b, v2.16b, v30.16b
	ldr x11, [x3, #1368]
	add v3.2d, v3.2d, v28.2d
	ushr v29.2d, v10.2d, #28
	mul x21, x0, x11
	and v10.16b, v10.16b, v30.16b
	umulh x22, x0, x11
	add v11.2d, v11.2d, v29.2d
	ushr v28.2d, v3.2d, #28
	ldr x11, [x3, #1360]
	and v3.16b, v3.16b, v30.16b
	mul x10, x2, x11
	add v4.2d, v4.2d, v28.2d
	ushr v29.2d, v11.2d, #28
	umulh x11, x2, x11
	and v11.16b, v11.16b, v30.16b
	adds x21, x21, x10
	add v12.2d, v12.2d, v29.2d
	ushr v28.2d, v4.2d, #28
	adc x22, x22, x11
	and v4.16b, v4.16b, v30.16b
	add v5.2d, v5.2d, v28.2d
	ldr x11, [x3, #1352]
	ushr v29.2d, v12.2d, #28
	mul x10, x4, x11
	and v12.16b, v12.16b, v30.16b
	add v13.2d, v13.2d, v29.2d
	umulh x11, x4, x11
	ushr v28.2d, v5.2d, #28
	adds x21, x21, x10
	and v5.16b, v5.16b, v30.16b
	add v6.2d, v6.2d, v28.2d
	adc x22, x22, x11
	ushr v29.2d, v13.2d, #28
	ldr x11, [x3, #1344]
	and v13.16b, v13.16b, v30.16b
	add v14.2d, v14.2d, v29.2d
	mul x10, x5, x11
	ushr v28.2d, v6.2d, #28
	umulh x11, x5, x11
	and v6.16b, v6.16b, v30.16b
	add v7.2d, v7.2d, v28.2d
	adds x21, x21, x10
	ushr v29.2d, v14.2d, #28
	adc x22, x22, x11
	and v14.16b, v14.16b, v30.16b
	add v15.2d, v15.2d, v29.2d
	adds x14, x14, x21
	ushr v28.2d, v7.2d, #28
	adc x15, x15, x22
	and v7.16b, v7.16b, v30.16b
	ushr v29.2d, v15.2d, #28
	subs x16, x16, x21
	and v15.16b, v15.16b, v30.16b
	add v8.2d, v8.2d, v28.2d
	sbc x17, x17, x22
	add v8.2d, v8.2d, v29.2d
	adds x14, x14, x23
	add v0.2d, v0.2d, v29.2d
	shl v16.2d, v1.2d, #28
	adc x15, x15, x26
	add v16.2d, v16.2d, v0.2d
	and x10, x14, x25
	shl v17.2d, v3.2d, #28
	add v17.2d, v17.2d, v2.2d
	str x10, [x3, #2392]
	shl v18.2d, v5.2d, #28
	extr x23, x15, x14, #56
	add v18.2d, v18.2d, v4.2d
	shl v19.2d, v7.2d, #28
	adds x16, x16, x24
	add v19.2d, v19.2d, v6.2d
	adc x17, x17, x26
	shl v20.2d, v9.2d, #28
	add v20.2d, v20.2d, v8.2d
	and x10, x16, x25
	shl v21.2d, v11.2d, #28
	str x10, [x3, #2424]
	add v21.2d, v21.2d, v10.2d
	shl v22.2d, v13.2d, #28
	extr x24, x17, x16, #56
	add v22.2d, v22.2d, v12.2d
	ldr x4, [x3, #2368]
	shl v23.2d, v15.2d, #28
	add v23.2d, v23.2d, v14.2d
	ldr x5, [x3, #2376]
	shl v31.2d, v30.2d, #28
	ldr x6, [x3, #2400]
	add v31.2d, v31.2d, v30.2d
	ushr v28.2d, v16.2d, #56
	ldr x7, [x3, #2408]
	and v16.16b, v16.16b, v31.16b
	add v17.2d, v17.2d, v28.2d
	add x4, x4, x24
	ushr v28.2d, v20.2d, #56
	add x6, x6, x24
	and v20.16b, v20.16b, v31.16b
	add v21.2d, v21.2d, v28.2d
	add x6, x6, x23
	trn1 v8.2d, v16.2d, v17.2d
	lsr x8, x4, #56
	trn2 v9.2d, v16.2d, v17.2d
	str q8, [x3, #1472]
	and x4, x4, x25
	str q9, [x3, #1600]
	add x5, x5, x8
	trn1 v8.2d, v18.2d, v19.2d
	trn2 v9.2d, v18.2d, v19.2d
	lsr x8, x6, #56
	str q8, [x3, #1488]
	and x6, x6, x25
	str q9, [x3, #1616]
	trn1 v8.2d, v20.2d, v21.2d
	add x7, x7, x8
	trn2 v9.2d, v20.2d, v21.2d
	str x4, [x3, #2368]
	str q8, [x3, #1504]
	str q9, [x3, #1632]
	str x5, [x3, #2376]
	trn1 v8.2d, v22.2d, v23.2d
	str x6, [x3, #2400]
	trn2 v9.2d, v22.2d, v23.2d
	str q8, [x3, #1520]
	str x7, [x3, #2408]
	str q9, [x3, #1648]
	ldr x4, [x3, #2368]
	dup v30.2d, x12
	movi v31.2d, #0
	ldr q0, [x3, #1472]
	ldr q1, [x3, #1600]
	trn1 v2.2d, v0.2d, v1.2d
	trn2 v3.2d, v0.2d, v1.2d
	and v0.16b, v2.16b, v30.16b
	ushr v1.2d, v2.2d, #28
	uzp1 v2.4s, v0.4s, v1.4s
	str q2, [x3, #4096]
	and v0.16b, v3.16b, v30.16b
	ushr v1.2d, v3.2d, #28
	uzp1 v3.4s, v0.4s, v1.4s
	str q3, [x3, #4112]
	ldr q0, [x3, #1488]
	ldr q1, [x3, #1616]
	trn1 v2.2d, v0.2d, v1.2d
	trn2 v3.2d, v0.2d, v1.2d
	and v0.16b, v2.16b, v30.16b
	ushr v1.2d, v2.2d, #28
	uzp1 v2.4s, v0.4s, v1.4s
	str q2, [x3, #4128]
	and v0.16b, v3.16b, v30.16b
	ushr v1.2d, v3.2d, #28
	uzp1 v3.4s, v0.4s, v1.4s
	str q3, [x3, #4144]
	ldr q0, [x3, #1504]
	ldr q1, [x3, #1632]
	trn1 v2.2d, v0.2d, v1.2d
	trn2 v3.2d, v0.2d, v1.2d
	and v0.16b, v2.16b, v30.16b
	ushr v1.2d, v2.2d, #28
	uzp1 v2.4s, v0.4s, v1.4s
	str x4, [x3, #704]
	str q2, [x3, #4160]
	and v0.16b, v3.16b, v30.16b
	ushr v1.2d, v3.2d, #28
	uzp1 v3.4s, v0.4s, v1.4s
	str q3, [x3, #4176]
	ldr q0, [x3, #1520]
	ldr q1, [x3, #1648]
	trn1 v2.2d, v0.2d, v1.2d
	trn2 v3.2d, v0.2d, v1.2d
	and v0.16b, v2.16b, v30.16b
	ushr v1.2d, v2.2d, #28
	uzp1 v2.4s, v0.4s, v1.4s
	str q2, [x3, #4192]
	and v0.16b, v3.16b, v30.16b
	ushr v1.2d, v3.2d, #28
	uzp1 v3.4s, v0.4s, v1.4s
	str q3, [x3, #4208]
	ldr q4, [x3, #1728]
	ldr q5, [x3, #2240]
	trn1 v6.2d, v4.2d, v5.2d
	trn2 v7.2d, v4.2d, v5.2d
	and v4.16b, v6.16b, v30.16b
	ushr v5.2d, v6.2d, #28
	uzp1 v6.4s, v4.4s, v5.4s
	str q6, [x3, #4224]
	and v4.16b, v7.16b, v30.16b
	ushr v5.2d, v7.2d, #28
	uzp1 v7.4s, v4.4s, v5.4s
	str q7, [x3, #4240]
	ldr q4, [x3, #1744]
	ldr q5, [x3, #2256]
	trn1 v6.2d, v4.2d, v5.2d
	trn2 v7.2d, v4.2d, v5.2d
	ldr x4, [x3, #2376]
	and v4.16b, v6.16b, v30.16b
	ushr v5.2d, v6.2d, #28
	uzp1 v6.4s, v4.4s, v5.4s
	str q6, [x3, #4256]
	and v4.16b, v7.16b, v30.16b
	ushr v5.2d, v7.2d, #28
	uzp1 v7.4s, v4.4s, v5.4s
	str q7, [x3, #4272]
	ldr q4, [x3, #1760]
	ldr q5, [x3, #2272]
	trn1 v6.2d, v4.2d, v5.2d
	trn2 v7.2d, v4.2d, v5.2d
	and v4.16b, v6.16b, v30.16b
	ushr v5.2d, v6.2d, #28
	uzp1 v6.4s, v4.4s, v5.4s
	str q6, [x3, #4288]
	and v4.16b, v7.16b, v30.16b
	ushr v5.2d, v7.2d, #28
	uzp1 v7.4s, v4.4s, v5.4s
	str q7, [x3, #4304]
	ldr q4, [x3, #1776]
	ldr q5, [x3, #2288]
	trn1 v6.2d, v4.2d, v5.2d
	trn2 v7.2d, v4.2d, v5.2d
	and v4.16b, v6.16b, v30.16b
	ushr v5.2d, v6.2d, #28
	uzp1 v6.4s, v4.4s, v5.4s
	str q6, [x3, #4320]
	and v4.16b, v7.16b, v30.16b
	ushr v5.2d, v7.2d, #28
	uzp1 v7.4s, v4.4s, v5.4s
	str q7, [x3, #4336]
	ldr q0, [x3, #4096]
	str x4, [x3, #712]
	ldr q1, [x3, #4160]
	add v0.4s, v0.4s, v1.4s
	str q0, [x3, #4352]
	ldr q2, [x3, #4224]
	ldr q3, [x3, #4288]
	add v2.4s, v2.4s, v3.4s
	str q2, [x3, #4416]
	ldr q0, [x3, #4112]
	ldr q1, [x3, #4176]
	add v0.4s, v0.4s, v1.4s
	str q0, [x3, #4368]
	ldr q2, [x3, #4240]
	ldr q3, [x3, #4304]
	add v2.4s, v2.4s, v3.4s
	str q2, [x3, #4432]
	ldr q0, [x3, #4128]
	ldr q1, [x3, #4192]
	add v0.4s, v0.4s, v1.4s
	str q0, [x3, #4384]
	ldr q2, [x3, #4256]
	ldr q3, [x3, #4320]
	add v2.4s, v2.4s, v3.4s
	str q2, [x3, #4448]
	ldr q0, [x3, #4144]
	ldr q1, [x3, #4208]
	add v0.4s, v0.4s, v1.4s
	str q0, [x3, #4400]
	ldr q2, [x3, #4272]
	ldr q3, [x3, #4336]
	add v2.4s, v2.4s, v3.4s
	str q2, [x3, #4464]
	ldr q0, [x3, #4224]
	ldr q1, [x3, #4240]
	ldr x4, [x3, #2384]
	ldr q2, [x3, #4256]
	ldr q3, [x3, #4272]
	ext v4.16b, v31.16b, v0.16b, #8
	ext v5.16b, v0.16b, v1.16b, #8
	ext v6.16b, v1.16b, v2.16b, #8
	ext v7.16b, v2.16b, v3.16b, #8
	ext v8.16b, v3.16b, v31.16b, #8
	str q4, [x3, #4480]
	str q5, [x3, #4496]
	str q6, [x3, #4512]
	str q7, [x3, #4528]
	str q8, [x3, #4544]
	ldr q0, [x3, #4288]
	ldr q1, [x3, #4304]
	ldr q2, [x3, #4320]
	ldr q3, [x3, #4336]
	ext v4.16b, v31.16b, v0.16b, #8
	ext v5.16b, v0.16b, v1.16b, #8
	ext v6.16b, v1.16b, v2.16b, #8
	ext v7.16b, v2.16b, v3.16b, #8
	ext v8.16b, v3.16b, v31.16b, #8
	str q4, [x3, #4560]
	str q5, [x3, #4576]
	str q6, [x3, #4592]
	str q7, [x3, #4608]
	str q8, [x3, #4624]
	ldr q0, [x3, #4416]
	ldr q1, [x3, #4432]
	ldr q2, [x3, #4448]
	ldr q3, [x3, #4464]
	ext v4.16b, v31.16b, v0.16b, #8
	ext v5.16b, v0.16b, v1.16b, #8
	ext v6.16b, v1.16b, v2.16b, #8
	str x4, [x3, #720]
	ext v7.16b, v2.16b, v3.16b, #8
	ext v8.16b, v3.16b, v31.16b, #8
	str q4, [x3, #4640]
	str q5, [x3, #4656]
	str q6, [x3, #4672]
	str q7, [x3, #4688]
	str q8, [x3, #4704]
	ldr q23, [x3, #4096]
	ldr q24, [x3, #4112]
	ldr q25, [x3, #4128]
	ldr q26, [x3, #4144]
	ldr q27, [x3, #4224]
	umull v0.2d, v23.2s, v27.2s
	umull2 v2.2d, v23.4s, v27.4s
	umlal v2.2d, v24.2s, v27.2s
	umull2 v4.2d, v24.4s, v27.4s
	umlal v4.2d, v25.2s, v27.2s
	umull2 v6.2d, v25.4s, v27.4s
	umlal v6.2d, v26.2s, v27.2s
	umull2 v8.2d, v26.4s, v27.4s
	ldr q27, [x3, #4240]
	umlal v2.2d, v23.2s, v27.2s
	umlal2 v4.2d, v23.4s, v27.4s
	umlal v4.2d, v24.2s, v27.2s
	umlal2 v6.2d, v24.4s, v27.4s
	umlal v6.2d, v25.2s, v27.2s
	umlal2 v8.2d, v25.4s, v27.4s
	umlal v8.2d, v26.2s, v27.2s
	umull2 v10.2d, v26.4s, v27.4s
	ldr q27, [x3, #4256]
	umlal v4.2d, v23.2s, v27.2s
	umlal2 v6.2d, v23.4s, v27.4s
	umlal v6.2d, v24.2s, v27.2s
	ldr x4, [x3, #2392]
	umlal2 v8.2d, v24.4s, v27.4s
	umlal v8.2d, v25.2s, v27.2s
	umlal2 v10.2d, v25.4s, v27.4s
	umlal v10.2d, v26.2s, v27.2s
	umull2 v12.2d, v26.4s, v27.4s
	ldr q27, [x3, #4272]
	umlal v6.2d, v23.2s, v27.2s
	umlal2 v8.2d, v23.4s, v27.4s
	umlal v8.2d, v24.2s, v27.2s
	umlal2 v10.2d, v24.4s, v27.4s
	umlal v10.2d, v25.2s, v27.2s
	umlal2 v12.2d, v25.4s, v27.4s
	umlal v12.2d, v26.2s, v27.2s
	umull2 v14.2d, v26.4s, v27.4s
	ldr q27, [x3, #4480]
	umull2 v1.2d, v23.4s, v27.4s
	umull2 v3.2d, v24.4s, v27.4s
	umull2 v5.2d, v25.4s, v27.4s
	umull2 v7.2d, v26.4s, v27.4s
	ldr q27, [x3, #4496]
	umlal v1.2d, v23.2s, v27.2s
	umlal2 v3.2d, v23.4s, v27.4s
	umlal v3.2d, v24.2s, v27.2s
	umlal2 v5.2d, v24.4s, v27.4s
	umlal v5.2d, v25.2s, v27.2s
	umlal2 v7.2d, v25.4s, v27.4s
	umlal v7.2d, v26.2s, v27.2s
	umull2 v9.2d, v26.4s, v27.4s
	ldr q27, [x3, #4512]
	umlal v3.2d, v23.2s, v27.2s
	umlal2 v5.2d, v23.4s, v27.4s
	umlal v5.2d, v24.2s, v27.2s
	umlal2 v7.2d, v24.4s, v27.4s
	str x4, [x3, #728]
	umlal v7.2d, v25.2s, v27.2s
	umlal2 v9.2d, v25.4s, v27.4s
	umlal v9.2d, v26.2s, v27.2s
	umull2 v11.2d, v26.4s, v27.4s
	ldr q27, [x3, #4528]
	umlal v5.2d, v23.2s, v27.2s
	umlal2 v7.2d, v23.4s, v27.4s
	umlal v7.2d, v24.2s, v27.2s
	umlal2 v9.2d, v24.4s, v27.4s
	umlal v9.2d, v25.2s, v27.2s
	umlal2 v11.2d, v25.4s, v27.4s
	umlal v11.2d, v26.2s, v27.2s
	umull2 v13.2d, v26.4s, v27.4s
	ldr q27, [x3, #4544]
	umlal v7.2d, v23.2s, v27.2s
	umlal v9.2d, v24.2s, v27.2s
	umlal v11.2d, v25.2s, v27.2s
	umlal v13.2d, v26.2s, v27.2s
	mov v28.16b, v8.16b
	sub v8.2d, v31.2d, v0.2d
	sub v0.2d, v0.2d, v28.2d
	mov v28.16b, v9.16b
	sub v9.2d, v31.2d, v1.2d
	sub v1.2d, v1.2d, v28.2d
	mov v28.16b, v10.16b
	sub v10.2d, v31.2d, v2.2d
	sub v2.2d, v2.2d, v28.2d
	mov v28.16b, v11.16b
	sub v11.2d, v31.2d, v3.2d
	sub v3.2d, v3.2d, v28.2d
	mov v28.16b, v12.16b
	sub v12.2d, v31.2d, v4.2d
	sub v4.2d, v4.2d, v28.2d
	ldr x4, [x3, #2400]
	mov v28.16b, v13.16b
	sub v13.2d, v31.2d, v5.2d
	sub v5.2d, v5.2d, v28.2d
	mov v28.16b, v14.16b
	sub v14.2d, v31.2d, v6.2d
	sub v6.2d, v6.2d, v28.2d
	sub v15.2d, v31.2d, v7.2d
	ldr q23, [x3, #4160]
	ldr q24, [x3, #4176]
	ldr q25, [x3, #4192]
	ldr q26, [x3, #4208]
	ldr q27, [x3, #4288]
	umlal v0.2d, v23.2s, v27.2s
	umlal2 v2.2d, v23.4s, v27.4s
	umlal v2.2d, v24.2s, v27.2s
	umlal2 v4.2d, v24.4s, v27.4s
	umlal v4.2d, v25.2s, v27.2s
	umlal2 v6.2d, v25.4s, v27.4s
	umlal v6.2d, v26.2s, v27.2s
	umlal2 v8.2d, v26.4s, v27.4s
	ldr q27, [x3, #4304]
	umlal v2.2d, v23.2s, v27.2s
	umlal2 v4.2d, v23.4s, v27.4s
	umlal v4.2d, v24.2s, v27.2s
	umlal2 v6.2d, v24.4s, v27.4s
	umlal v6.2d, v25.2s, v27.2s
	umlal2 v8.2d, v25.4s, v27.4s
	umlal v8.2d, v26.2s, v27.2s
	umlal2 v10.2d, v26.4s, v27.4s
	ldr q27, [x3, #4320]
	umlal v4.2d, v23.2s, v27.2s
	umlal2 v6.2d, v23.4s, v27.4s
	umlal v6.2d, v24.2s, v27.2s
	str x4, [x3, #736]
	umlal2 v8.2d, v24.4s, v27.4s
	umlal v8.2d, v25.2s, v27.2s
	umlal2 v10.2d, v25.4s, v27.4s
	umlal v10.2d, v26.2s, v27.2s
	umlal2 v12.2d, v26.4s, v27.4s
	ldr q27, [x3, #4336]
	umlal v6.2d, v23.2s, v27.2s
	umlal2 v8.2d, v23.4s, v27.4s
	umlal v8.2d, v24.2s, v27.2s
	umlal2 v10.2d, v24.4s, v27.4s
	umlal v10.2d, v25.2s, v27.2s
	umlal2 v12.2d, v25.4s, v27.4s
	umlal v12.2d, v26.2s, v27.2s
	umlal2 v14.2d, v26.4s, v27.4s
	ldr q27, [x3, #4560]
	umlal2 v1.2d, v23.4s, v27.4s
	umlal2 v3.2d, v24.4s, v27.4s
	umlal2 v5.2d, v25.4s, v27.4s
	umlal2 v7.2d, v26.4s, v27.4s
	ldr q27, [x3, #4576]
	umlal v1.2d, v23.2s, v27.2s
	umlal2 v3.2d, v23.4s, v27.4s
	umlal v3.2d, v24.2s, v27.2s
	umlal2 v5.2d, v24.4s, v27.4s
	umlal v5.2d, v25.2s, v27.2s
	umlal2 v7.2d, v25.4s, v27.4s
	umlal v7.2d, v26.2s, v27.2s
	umlal2 v9.2d, v26.4s, v27.4s
	ldr q27, [x3, #4592]
	umlal v3.2d, v23.2s, v27.2s
	umlal2 v5.2d, v23.4s, v27.4s
	umlal v5.2d, v24.2s, v27.2s
	umlal2 v7.2d, v24.4s, v27.4s
	ldr x4, [x3, #2408]
	umlal v7.2d, v25.2s, v27.2s
	umlal2 v9.2d, v25.4s, v27.4s
	umlal v9.2d, v26.2s, v27.2s
	umlal2 v11.2d, v26.4s, v27.4s
	ldr q27, [x3, #4608]
	umlal v5.2d, v23.2s, v27.2s
	umlal2 v7.2d, v23.4s, v27.4s
	umlal v7.2d, v24.2s, v27.2s
	umlal2 v9.2d, v24.4s, v27.4s
	umlal v9.2d, v25.2s, v27.2s
	umlal2 v11.2d, v25.4s, v27.4s
	umlal v11.2d, v26.2s, v27.2s
	umlal2 v13.2d, v26.4s, v27.4s
	ldr q27, [x3, #4624]
	umlal v7.2d, v23.2s, v27.2s
	umlal v9.2d, v24.2s, v27.2s
	umlal v11.2d, v25.2s, v27.2s
	umlal v13.2d, v26.2s, v27.2s
	ldr q23, [x3, #4352]
	ldr q24, [x3, #4368]
	ldr q25, [x3, #4384]
	ldr q26, [x3, #4400]
	ldr q27, [x3, #4416]
	umlal v8.2d, v23.2s, v27.2s
	umlal2 v10.2d, v23.4s, v27.4s
	umlal v10.2d, v24.2s, v27.2s
	umlal2 v12.2d, v24.4s, v27.4s
	umlal v12.2d, v25.2s, v27.2s
	umlal2 v14.2d, v25.4s, v27.4s
	umlal v14.2d, v26.2s, v27.2s
	umull2 v16.2d, v26.4s, v27.4s
	ldr q27, [x3, #4432]
	umlal v10.2d, v23.2s, v27.2s
	str x4, [x3, #744]
	umlal2 v12.2d, v23.4s, v27.4s
	umlal v12.2d, v24.2s, v27.2s
	umlal2 v14.2d, v24.4s, v27.4s
	umlal v14.2d, v25.2s, v27.2s
	umlal2 v16.2d, v25.4s, v27.4s
	umlal v16.2d, v26.2s, v27.2s
	umull2 v18.2d, v26.4s, v27.4s
	ldr q27, [x3, #4448]
	umlal v12.2d, v23.2s, v27.2s
	umlal2 v14.2d, v23.4s, v27.4s
	umlal v14.2d, v24.2s, v27.2s
	umlal2 v16.2d, v24.4s, v27.4s
	umlal v16.2d, v25.2s, v27.2s
	umlal2 v18.2d, v25.4s, v27.4s
	umlal v18.2d, v26.2s, v27.2s
	umull2 v20.2d, v26.4s, v27.4s
	ldr q27, [x3, #4464]
	umlal v14.2d, v23.2s, v27.2s
	umlal2 v16.2d, v23.4s, v27.4s
	umlal v16.2d, v24.2s, v27.2s
	umlal2 v18.2d, v24.4s, v27.4s
	umlal v18.2d, v25.2s, v27.2s
	umlal2 v20.2d, v25.4s, v27.4s
	umlal v20.2d, v26.2s, v27.2s
	umull2 v22.2d, v26.4s, v27.4s
	ldr q27, [x3, #4640]
	umlal2 v9.2d, v23.4s, v27.4s
	umlal2 v11.2d, v24.4s, v27.4s
	umlal2 v13.2d, v25.4s, v27.4s
	umlal2 v15.2d, v26.4s, v27.4s
	ldr q27, [x3, #4656]
	umlal v9.2d, v23.2s, v27.2s
	umlal2 v11.2d, v23.4s, v27.4s
	ldr x4, [x3, #2416]
	umlal v11.2d, v24.2s, v27.2s
	umlal2 v13.2d, v24.4s, v27.4s
	umlal v13.2d, v25.2s, v27.2s
	umlal2 v15.2d, v25.4s, v27.4s
	umlal v15.2d, v26.2s, v27.2s
	umull2 v17.2d, v26.4s, v27.4s
	ldr q27, [x3, #4672]
	umlal v11.2d, v23.2s, v27.2s
	umlal2 v13.2d, v23.4s, v27.4s
	umlal v13.2d, v24.2s, v27.2s
	umlal2 v15.2d, v24.4s, v27.4s
	umlal v15.2d, v25.2s, v27.2s
	umlal2 v17.2d, v25.4s, v27.4s
	umlal v17.2d, v26.2s, v27.2s
	umull2 v19.2d, v26.4s, v27.4s
	ldr q27, [x3, #4688]
	umlal v13.2d, v23.2s, v27.2s
	umlal2 v15.2d, v23.4s, v27.4s
	umlal v15.2d, v24.2s, v27.2s
	umlal2 v17.2d, v24.4s, v27.4s
	umlal v17.2d, v25.2s, v27.2s
	umlal2 v19.2d, v25.4s, v27.4s
	umlal v19.2d, v26.2s, v27.2s
	umull2 v21.2d, v26.4s, v27.4s
	ldr q27, [x3, #4704]
	umlal v15.2d, v23.2s, v27.2s
	umlal v17.2d, v24.2s, v27.2s
	umlal v19.2d, v25.2s, v27.2s
	umlal v21.2d, v26.2s, v27.2s
	add v0.2d, v0.2d, v16.2d
	add v8.2d, v8.2d, v16.2d
	add v1.2d, v1.2d, v17.2d
	add v9.2d, v9.2d, v17.2d
	str x4, [x3, #752]
	add v2.2d, v2.2d, v18.2d
	add v10.2d, v10.2d, v18.2d
	add v3.2d, v3.2d, v19.2d
	add v11.2d, v11.2d, v19.2d
	add v4.2d, v4.2d, v20.2d
	add v12.2d, v12.2d, v20.2d
	add v5.2d, v5.2d, v21.2d
	add v13.2d, v13.2d, v21.2d
	add v6.2d, v6.2d, v22.2d
	add v14.2d, v14.2d, v22.2d
	ushr v28.2d, v0.2d, #28
	and v0.16b, v0.16b, v30.16b
	add v1.2d, v1.2d, v28.2d
	ushr v29.2d, v8.2d, #28
	and v8.16b, v8.16b, v30.16b
	add v9.2d, v9.2d, v29.2d
	ushr v28.2d, v1.2d, #28
	and v1.16b, v1.16b, v30.16b
	add v2.2d, v2.2d, v28.2d
	ushr v29.2d, v9.2d, #28
	and v9.16b, v9.16b, v30.16b
	add v10.2d, v10.2d, v29.2d
	ushr v28.2d, v2.2d, #28
	and v2.16b, v2.16b, v30.16b
	add v3.2d, v3.2d, v28.2d
	ushr v29.2d, v10.2d, #28
	and v10.16b, v10.16b, v30.16b
	add v11.2d, v11.2d, v29.2d
	ushr v28.2d, v3.2d, #28
	and v3.16b, v3.16b, v30.16b
	add v4.2d, v4.2d, v28.2d
	ushr v29.2d, v11.2d, #28
	and v11.16b, v11.16b, v30.16b
	ldr x4, [x3, #2424]
	add v12.2d, v12.2d, v29.2d
	ushr v28.2d, v4.2d, #28
	and v4.16b, v4.16b, v30.16b
	add v5.2d, v5.2d, v28.2d
	ushr v29.2d, v12.2d, #28
	and v12.16b, v12.16b, v30.16b
	add v13.2d, v13.2d, v29.2d
	ushr v28.2d, v5.2d, #28
	and v5.16b, v5.16b, v30.16b
	add v6.2d, v6.2d, v28.2d
	ushr v29.2d, v13.2d, #28
	and v13.16b, v13.16b, v30.16b
	add v14.2d, v14.2d, v29.2d
	ushr v28.2d, v6.2d, #28
	and v6.16b, v6.16b, v30.16b
	add v7.2d, v7.2d, v28.2d
	ushr v29.2d, v14.2d, #28
	and v14.16b, v14.16b, v30.16b
	add v15.2d, v15.2d, v29.2d
	ushr v28.2d, v7.2d, #28
	and v7.16b, v7.16b, v30.16b
	ushr v29.2d, v15.2d, #28
	and v15.16b, v15.16b, v30.16b
	add v8.2d, v8.2d, v28.2d
	add v8.2d, v8.2d, v29.2d
	add v0.2d, v0.2d, v29.2d
	shl v16.2d, v1.2d, #28
	add v16.2d, v16.2d, v0.2d
	shl v17.2d, v3.2d, #28
	add v17.2d, v17.2d, v2.2d
	shl v18.2d, v5.2d, #28
	add v18.2d, v18.2d, v4.2d
	shl v19.2d, v7.2d, #28
	str x4, [x3, #760]
	add v19.2d, v19.2d, v6.2d
	shl v20.2d, v9.2d, #28
	add v20.2d, v20.2d, v8.2d
	shl v21.2d, v11.2d, #28
	add v21.2d, v21.2d, v10.2d
	shl v22.2d, v13.2d, #28
	add v22.2d, v22.2d, v12.2d
	shl v23.2d, v15.2d, #28
	add v23.2d, v23.2d, v14.2d
	shl v31.2d, v30.2d, #28
	add v31.2d, v31.2d, v30.2d
	ushr v28.2d, v16.2d, #56
	and v16.16b, v16.16b, v31.16b
	add v17.2d, v17.2d, v28.2d
	ushr v28.2d, v20.2d, #56
	and v20.16b, v20.16b, v31.16b
	add v21.2d, v21.2d, v28.2d
	trn1 v8.2d, v16.2d, v17.2d
	trn2 v9.2d, v16.2d, v17.2d
	str q8, [x3, #448]
	str q9, [x3, #576]
	trn1 v8.2d, v18.2d, v19.2d
	trn2 v9.2d, v18.2d, v19.2d
	str q8, [x3, #464]
	str q9, [x3, #592]
	trn1 v8.2d, v20.2d, v21.2d
	trn2 v9.2d, v20.2d, v21.2d
	str q8, [x3, #480]
	str q9, [x3, #608]
	trn1 v8.2d, v22.2d, v23.2d
	trn2 v9.2d, v22.2d, v23.2d
	str q8, [x3, #496]
	str q9, [x3, #624]
	ldr x21, [x3, #7360]
	ldr x22, [x3, #7368]
	ldr x23, [x3, #7376]
	ldr x24, [x3, #7384]
	ldr x25, [x3, #7392]
	ldr x26, [x3, #7400]
	ldr x27, [x3, #7408]
	ldr x28, [x3, #7416]
215:
	add x2, x3, x19
	ldrb w11, [x2, #3072]
	cbnz x11, 218f
	b 219f
218:
	lsr x21, x11, #7
	movz x9, #256, lsl #0
	sub x9, x9, x11
	movz x8, #128, lsl #0
	tst x11, x8
	csel x11, x9, x11, ne
	lsr x11, x11, #1
	lsl x8, x11, #7
	lsl x9, x11, #6
	add x8, x8, x9
	add x8, x8, x3
	ldr x4, [x8, #4992]
	str x4, [x3, #832]
	ldr x4, [x8, #5000]
	str x4, [x3, #840]
	ldr x4, [x8, #5008]
	str x4, [x3, #848]
	ldr x4, [x8, #5016]
	str x4, [x3, #856]
	ldr x4, [x8, #5024]
	str x4, [x3, #864]
	ldr x4, [x8, #5032]
	str x4, [x3, #872]
	ldr x4, [x8, #5040]
	str x4, [x3, #880]
	ldr x4, [x8, #5048]
	str x4, [x3, #888]
	ldr x4, [x8, #5056]
	str x4, [x3, #960]
	ldr x4, [x8, #5064]
	str x4, [x3, #968]
	ldr x4, [x8, #5072]
	str x4, [x3, #976]
	ldr x4, [x8, #5080]
	str x4, [x3, #984]
	ldr x4, [x8, #5088]
	str x4, [x3, #992]
	ldr x4, [x8, #5096]
	str x4, [x3, #1000]
	ldr x4, [x8, #5104]
	str x4, [x3, #1008]
	ldr x4, [x8, #5112]
	str x4, [x3, #1016]
	ldr x4, [x8, #5120]
	str x4, [x3, #1088]
	ldr x4, [x8, #5128]
	str x4, [x3, #1096]
	ldr x4, [x8, #5136]
	str x4, [x3, #1104]
	ldr x4, [x8, #5144]
	str x4, [x3, #1112]
	ldr x4, [x8, #5152]
	str x4, [x3, #1120]
	ldr x4, [x8, #5160]
	str x4, [x3, #1128]
	ldr x4, [x8, #5168]
	str x4, [x3, #1136]
	ldr x4, [x8, #5176]
	str x4, [x3, #1144]
	cbnz x21, 220f
	b 221f
220:
	movz x0, #65534, lsl #0
	movk x0, #65535, lsl #16
	movk x0, #65535, lsl #32
	movk x0, #511, lsl #48
	movz x2, #65532, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #511, lsl #48
	ldr x4, [x3, #2496]
	ldr x5, [x3, #832]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #832]
	ldr x4, [x3, #2504]
	ldr x5, [x3, #840]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #840]
	ldr x4, [x3, #2512]
	ldr x5, [x3, #848]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #848]
	ldr x4, [x3, #2520]
	ldr x5, [x3, #856]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #856]
	ldr x4, [x3, #2528]
	ldr x5, [x3, #864]
	add x4, x4, x2
	sub x4, x4, x5
	str x4, [x3, #864]
	ldr x4, [x3, #2536]
	ldr x5, [x3, #872]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #872]
	ldr x4, [x3, #2544]
	ldr x5, [x3, #880]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #880]
	ldr x4, [x3, #2552]
	ldr x5, [x3, #888]
	add x4, x4, x0
	sub x4, x4, x5
	str x4, [x3, #888]
221:
	add x0, x3, #0
	bl {vg_ed448_r56_point_add}
219:
	add x9, x19, #0
	cbnz x9, 213b
	add x0, x3, #0
	bl {vg_ed448_r56_point_double}
	add x0, x3, #0
	bl {vg_ed448_r56_point_double}
	ldr x4, [x3, #448]
	str x4, [x3, #64]
	ldr x4, [x3, #456]
	str x4, [x3, #72]
	ldr x4, [x3, #464]
	str x4, [x3, #80]
	ldr x4, [x3, #472]
	str x4, [x3, #88]
	ldr x4, [x3, #480]
	str x4, [x3, #96]
	ldr x4, [x3, #488]
	str x4, [x3, #104]
	ldr x4, [x3, #496]
	str x4, [x3, #112]
	ldr x4, [x3, #504]
	str x4, [x3, #120]
	ldr x4, [x3, #576]
	str x4, [x3, #192]
	ldr x4, [x3, #584]
	str x4, [x3, #200]
	ldr x4, [x3, #592]
	str x4, [x3, #208]
	ldr x4, [x3, #600]
	str x4, [x3, #216]
	ldr x4, [x3, #608]
	str x4, [x3, #224]
	ldr x4, [x3, #616]
	str x4, [x3, #232]
	ldr x4, [x3, #624]
	str x4, [x3, #240]
	ldr x4, [x3, #632]
	str x4, [x3, #248]
	ldr x4, [x3, #704]
	str x4, [x3, #320]
	ldr x4, [x3, #712]
	str x4, [x3, #328]
	ldr x4, [x3, #720]
	str x4, [x3, #336]
	ldr x4, [x3, #728]
	str x4, [x3, #344]
	ldr x4, [x3, #736]
	str x4, [x3, #352]
	ldr x4, [x3, #744]
	str x4, [x3, #360]
	ldr x4, [x3, #752]
	str x4, [x3, #368]
	ldr x4, [x3, #760]
	str x4, [x3, #376]
	ldr x4, [x3, #8064]
	str x4, [x3, #448]
	ldr x4, [x3, #8072]
	str x4, [x3, #456]
	ldr x4, [x3, #8080]
	str x4, [x3, #464]
	ldr x4, [x3, #8088]
	str x4, [x3, #472]
	ldr x4, [x3, #8096]
	str x4, [x3, #480]
	ldr x4, [x3, #8104]
	str x4, [x3, #488]
	ldr x4, [x3, #8112]
	str x4, [x3, #496]
	ldr x4, [x3, #8120]
	str x4, [x3, #504]
	ldr x4, [x3, #4864]
	str x4, [x3, #576]
	ldr x4, [x3, #4872]
	str x4, [x3, #584]
	ldr x4, [x3, #4880]
	str x4, [x3, #592]
	ldr x4, [x3, #4888]
	str x4, [x3, #600]
	ldr x4, [x3, #4896]
	str x4, [x3, #608]
	ldr x4, [x3, #4904]
	str x4, [x3, #616]
	ldr x4, [x3, #4912]
	str x4, [x3, #624]
	ldr x4, [x3, #4920]
	str x4, [x3, #632]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #704]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #712]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #720]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #728]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #736]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #744]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #752]
	movz x4, #0, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	str x4, [x3, #760]
	add x0, x3, #0
	bl {vg_ed448_r56_point_double}
	add x0, x3, #0
	bl {vg_ed448_r56_point_double}
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #1600, lsl #0
	movz x2, #64, lsl #0
	movz x3, #704, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #1728, lsl #0
	movz x2, #448, lsl #0
	movz x3, #320, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #1856, lsl #0
	movz x2, #192, lsl #0
	movz x3, #704, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	mov v26.d[0], x19
	mov v26.d[1], x30
	add x19, x1, #0
	add x0, x3, #0
	movz x1, #1984, lsl #0
	movz x2, #576, lsl #0
	movz x3, #320, lsl #0
	bl {vg_gf448_r56_mul}
	add x1, x19, #0
	umov x19, v26.d[0]
	umov x30, v26.d[1]
	movz x19, #2, lsl #0
222:
	movz x8, #2, lsl #0
223:
	sub x8, x8, #1
	cbnz x8, 224f
	ldr x4, [x3, #192]
	str x4, [x3, #4864]
	ldr x4, [x3, #200]
	str x4, [x3, #4872]
	ldr x4, [x3, #208]
	str x4, [x3, #4880]
	ldr x4, [x3, #216]
	str x4, [x3, #4888]
	ldr x4, [x3, #224]
	str x4, [x3, #4896]
	ldr x4, [x3, #232]
	str x4, [x3, #4904]
	ldr x4, [x3, #240]
	str x4, [x3, #4912]
	ldr x4, [x3, #248]
	str x4, [x3, #4920]
	ldr x4, [x3, #256]
	str x4, [x3, #4928]
	ldr x4, [x3, #264]
	str x4, [x3, #4936]
	ldr x4, [x3, #272]
	str x4, [x3, #4944]
	ldr x4, [x3, #280]
	str x4, [x3, #4952]
	ldr x4, [x3, #288]
	str x4, [x3, #4960]
	ldr x4, [x3, #296]
	str x4, [x3, #4968]
	ldr x4, [x3, #304]
	str x4, [x3, #4976]
	ldr x4, [x3, #312]
	str x4, [x3, #4984]
	ldr x4, [x3, #1728]
	str x4, [x3, #192]
	ldr x4, [x3, #1736]
	str x4, [x3, #200]
	ldr x4, [x3, #1744]
	str x4, [x3, #208]
	ldr x4, [x3, #1752]
	str x4, [x3, #216]
	ldr x4, [x3, #1760]
	str x4, [x3, #224]
	ldr x4, [x3, #1768]
	str x4, [x3, #232]
	ldr x4, [x3, #1776]
	str x4, [x3, #240]
	ldr x4, [x3, #1784]
	str x4, [x3, #248]
	b 225f
224:
	ldr x4, [x3, #1600]
	str x4, [x3, #192]
	ldr x4, [x3, #1608]
	str x4, [x3, #200]
	ldr x4, [x3, #1616]
	str x4, [x3, #208]
	ldr x4, [x3, #1624]
	str x4, [x3, #216]
	ldr x4, [x3, #1632]
	str x4, [x3, #224]
	ldr x4, [x3, #1640]
	str x4, [x3, #232]
	ldr x4, [x3, #1648]
	str x4, [x3, #240]
	ldr x4, [x3, #1656]
	str x4, [x3, #248]
225:
	ldr x4, [x3, #192]
	movz x5, #0, lsl #0
	str x4, [x3, #3840]
	str x5, [x3, #3848]
	ldr x4, [x3, #200]
	movz x5, #0, lsl #0
	str x4, [x3, #3856]
	str x5, [x3, #3864]
	ldr x4, [x3, #208]
	movz x5, #0, lsl #0
	str x4, [x3, #3872]
	str x5, [x3, #3880]
	ldr x4, [x3, #216]
	movz x5, #0, lsl #0
	str x4, [x3, #3888]
	str x5, [x3, #3896]
	ldr x4, [x3, #224]
	movz x5, #0, lsl #0
	str x4, [x3, #3904]
	str x5, [x3, #3912]
	ldr x4, [x3, #232]
	movz x5, #0, lsl #0
	str x4, [x3, #3920]
	str x5, [x3, #3928]
	ldr x4, [x3, #240]
	movz x5, #0, lsl #0
	str x4, [x3, #3936]
	str x5, [x3, #3944]
	ldr x4, [x3, #248]
	movz x5, #0, lsl #0
	str x4, [x3, #3952]
	str x5, [x3, #3960]
	movz x6, #0, lsl #0
	movz x11, #0, lsl #0
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #255, lsl #48
	ldr x4, [x3, #3840]
	ldr x5, [x3, #3848]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3840]
	str x11, [x3, #3848]
	ldr x4, [x3, #3856]
	ldr x5, [x3, #3864]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3856]
	str x11, [x3, #3864]
	ldr x4, [x3, #3872]
	ldr x5, [x3, #3880]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3872]
	str x11, [x3, #3880]
	ldr x4, [x3, #3888]
	ldr x5, [x3, #3896]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3888]
	str x11, [x3, #3896]
	ldr x4, [x3, #3904]
	ldr x5, [x3, #3912]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3904]
	str x11, [x3, #3912]
	ldr x4, [x3, #3920]
	ldr x5, [x3, #3928]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3920]
	str x11, [x3, #3928]
	ldr x4, [x3, #3936]
	ldr x5, [x3, #3944]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3936]
	str x11, [x3, #3944]
	ldr x4, [x3, #3952]
	ldr x5, [x3, #3960]
	adds x4, x4, x6
	adcs x5, x5, x11
	lsr x6, x4, #56
	lsl x5, x5, #8
	add x6, x6, x5
	and x4, x4, x9
	str x4, [x3, #3952]
	str x11, [x3, #3960]
	ldr x4, [x3, #3840]
	add x4, x4, x6
	str x4, [x3, #3840]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	str x4, [x3, #3904]
	movz x6, #0, lsl #0
	movz x11, #0, lsl #0
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #255, lsl #48
	ldr x4, [x3, #3840]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3840]
	ldr x4, [x3, #3856]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3856]
	ldr x4, [x3, #3872]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3872]
	ldr x4, [x3, #3888]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3888]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3904]
	ldr x4, [x3, #3920]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3920]
	ldr x4, [x3, #3936]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3936]
	ldr x4, [x3, #3952]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	str x4, [x3, #3952]
	ldr x4, [x3, #3840]
	add x4, x4, x6
	str x4, [x3, #3840]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	str x4, [x3, #3904]
	movz x6, #0, lsl #0
	movz x11, #0, lsl #0
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #255, lsl #48
	ldr x4, [x3, #3840]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #192]
	str x5, [x3, #200]
	ldr x4, [x3, #3856]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #208]
	str x5, [x3, #216]
	ldr x4, [x3, #3872]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #224]
	str x5, [x3, #232]
	ldr x4, [x3, #3888]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #240]
	str x5, [x3, #248]
	ldr x4, [x3, #3904]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #256]
	str x5, [x3, #264]
	ldr x4, [x3, #3920]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #272]
	str x5, [x3, #280]
	ldr x4, [x3, #3936]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #288]
	str x5, [x3, #296]
	ldr x4, [x3, #3952]
	add x4, x4, x6
	lsr x6, x4, #56
	and x4, x4, x9
	lsr x5, x4, #28
	and x4, x4, x12
	str x4, [x3, #304]
	str x5, [x3, #312]
	ldr x4, [x3, #192]
	str x4, [x3, #3840]
	ldr x4, [x3, #200]
	str x4, [x3, #3848]
	ldr x4, [x3, #208]
	str x4, [x3, #3856]
	ldr x4, [x3, #216]
	str x4, [x3, #3864]
	ldr x4, [x3, #224]
	str x4, [x3, #3872]
	ldr x4, [x3, #232]
	str x4, [x3, #3880]
	ldr x4, [x3, #240]
	str x4, [x3, #3888]
	ldr x4, [x3, #248]
	str x4, [x3, #3896]
	ldr x4, [x3, #256]
	str x4, [x3, #3904]
	ldr x4, [x3, #264]
	str x4, [x3, #3912]
	ldr x4, [x3, #272]
	str x4, [x3, #3920]
	ldr x4, [x3, #280]
	str x4, [x3, #3928]
	ldr x4, [x3, #288]
	str x4, [x3, #3936]
	ldr x4, [x3, #296]
	str x4, [x3, #3944]
	ldr x4, [x3, #304]
	str x4, [x3, #3952]
	ldr x4, [x3, #312]
	str x4, [x3, #3960]
	ldr x4, [x3, #3840]
	add x4, x4, #1
	str x4, [x3, #3840]
	ldr x4, [x3, #3904]
	add x4, x4, #1
	str x4, [x3, #3904]
	movz x6, #0, lsl #0
	ldr x4, [x3, #3840]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3840]
	lsr x6, x4, #28
	ldr x4, [x3, #3848]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3848]
	lsr x6, x4, #28
	ldr x4, [x3, #3856]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3856]
	lsr x6, x4, #28
	ldr x4, [x3, #3864]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3864]
	lsr x6, x4, #28
	ldr x4, [x3, #3872]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3872]
	lsr x6, x4, #28
	ldr x4, [x3, #3880]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3880]
	lsr x6, x4, #28
	ldr x4, [x3, #3888]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3888]
	lsr x6, x4, #28
	ldr x4, [x3, #3896]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3896]
	lsr x6, x4, #28
	ldr x4, [x3, #3904]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3904]
	lsr x6, x4, #28
	ldr x4, [x3, #3912]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3912]
	lsr x6, x4, #28
	ldr x4, [x3, #3920]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3920]
	lsr x6, x4, #28
	ldr x4, [x3, #3928]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3928]
	lsr x6, x4, #28
	ldr x4, [x3, #3936]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3936]
	lsr x6, x4, #28
	ldr x4, [x3, #3944]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3944]
	lsr x6, x4, #28
	ldr x4, [x3, #3952]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3952]
	lsr x6, x4, #28
	ldr x4, [x3, #3960]
	add x4, x4, x6
	and x5, x4, x12
	str x5, [x3, #3960]
	lsr x6, x4, #28
	movz x7, #0, lsl #0
	sub x7, x7, x6
	ldr x4, [x3, #192]
	ldr x5, [x3, #3840]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #192]
	ldr x4, [x3, #200]
	ldr x5, [x3, #3848]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #200]
	ldr x4, [x3, #208]
	ldr x5, [x3, #3856]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #208]
	ldr x4, [x3, #216]
	ldr x5, [x3, #3864]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #216]
	ldr x4, [x3, #224]
	ldr x5, [x3, #3872]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #224]
	ldr x4, [x3, #232]
	ldr x5, [x3, #3880]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #232]
	ldr x4, [x3, #240]
	ldr x5, [x3, #3888]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #240]
	ldr x4, [x3, #248]
	ldr x5, [x3, #3896]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #248]
	ldr x4, [x3, #256]
	ldr x5, [x3, #3904]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #256]
	ldr x4, [x3, #264]
	ldr x5, [x3, #3912]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #264]
	ldr x4, [x3, #272]
	ldr x5, [x3, #3920]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #272]
	ldr x4, [x3, #280]
	ldr x5, [x3, #3928]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #280]
	ldr x4, [x3, #288]
	ldr x5, [x3, #3936]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #288]
	ldr x4, [x3, #296]
	ldr x5, [x3, #3944]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #296]
	ldr x4, [x3, #304]
	ldr x5, [x3, #3952]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #304]
	ldr x4, [x3, #312]
	ldr x5, [x3, #3960]
	eor x5, x5, x4
	and x5, x5, x7
	eor x4, x4, x5
	str x4, [x3, #312]
	cbnz x8, 223b
	movz x5, #0, lsl #0
	ldr x4, [x3, #192]
	ldr x6, [x3, #4864]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #200]
	ldr x6, [x3, #4872]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #208]
	ldr x6, [x3, #4880]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #216]
	ldr x6, [x3, #4888]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #224]
	ldr x6, [x3, #4896]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #232]
	ldr x6, [x3, #4904]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #240]
	ldr x6, [x3, #4912]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #248]
	ldr x6, [x3, #4920]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #256]
	ldr x6, [x3, #4928]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #264]
	ldr x6, [x3, #4936]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #272]
	ldr x6, [x3, #4944]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #280]
	ldr x6, [x3, #4952]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #288]
	ldr x6, [x3, #4960]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #296]
	ldr x6, [x3, #4968]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #304]
	ldr x6, [x3, #4976]
	eor x4, x4, x6
	orr x5, x5, x4
	ldr x4, [x3, #312]
	ldr x6, [x3, #4984]
	eor x4, x4, x6
	orr x5, x5, x4
	orr x20, x20, x5
	ldr x4, [x3, #1856]
	str x4, [x3, #1600]
	ldr x4, [x3, #1864]
	str x4, [x3, #1608]
	ldr x4, [x3, #1872]
	str x4, [x3, #1616]
	ldr x4, [x3, #1880]
	str x4, [x3, #1624]
	ldr x4, [x3, #1888]
	str x4, [x3, #1632]
	ldr x4, [x3, #1896]
	str x4, [x3, #1640]
	ldr x4, [x3, #1904]
	str x4, [x3, #1648]
	ldr x4, [x3, #1912]
	str x4, [x3, #1656]
	ldr x4, [x3, #1984]
	str x4, [x3, #1728]
	ldr x4, [x3, #1992]
	str x4, [x3, #1736]
	ldr x4, [x3, #2000]
	str x4, [x3, #1744]
	ldr x4, [x3, #2008]
	str x4, [x3, #1752]
	ldr x4, [x3, #2016]
	str x4, [x3, #1760]
	ldr x4, [x3, #2024]
	str x4, [x3, #1768]
	ldr x4, [x3, #2032]
	str x4, [x3, #1776]
	ldr x4, [x3, #2040]
	str x4, [x3, #1784]
	sub x19, x19, #1
	cbnz x19, 222b
	add x5, x20, #0
	movz x6, #0, lsl #0
	subs x7, x6, x5
	adc x5, x6, x6
	add x0, x5, #0
	ldr x19, [x3, #0]
	ldr x20, [x3, #8]
	ldr x30, [x3, #3008]
	ldr x21, [x3, #2880]
	ldr x22, [x3, #2888]
	ldr x23, [x3, #2896]
	ldr x24, [x3, #2904]
	ldr x25, [x3, #2912]
	ldr x26, [x3, #2920]
	ldr x27, [x3, #2928]
	ldr x28, [x3, #2936]
	ldr q8, [x3, #4736]
	ldr q9, [x3, #4752]
	ldr q10, [x3, #4768]
	ldr q11, [x3, #4784]
	ldr q12, [x3, #4800]
	ldr q13, [x3, #4816]
	ldr q14, [x3, #4832]
	ldr q15, [x3, #4848]
	ret
	.p2align 6
