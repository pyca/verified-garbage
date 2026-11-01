// The functions of `src/internal/vg_mlkem_inv_ntt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_inv_ntt:
	movz x9, #1746, lsl #0
	movk x9, #821, lsl #16
	movk x9, #1974, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #512]
	movz x9, #910, lsl #0
	movk x9, #1227, lsl #16
	movk x9, #3110, lsl #32
	movk x9, #2474, lsl #48
	str x9, [x1, #520]
	movz x9, #17186, lsl #0
	movk x9, #8081, lsl #16
	movk x9, #19430, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #528]
	movz x9, #8957, lsl #0
	movk x9, #12078, lsl #16
	movk x9, #30612, lsl #32
	movk x9, #24352, lsl #48
	str x9, [x1, #536]
	movz x9, #2154, lsl #0
	movk x9, #885, lsl #16
	movk x9, #2935, lsl #32
	movk x9, #2110, lsl #48
	str x9, [x1, #544]
	movz x9, #1029, lsl #0
	movk x9, #1874, lsl #16
	movk x9, #1212, lsl #32
	movk x9, #1722, lsl #48
	str x9, [x1, #552]
	movz x9, #21202, lsl #0
	movk x9, #8711, lsl #16
	movk x9, #28890, lsl #32
	movk x9, #20769, lsl #48
	str x9, [x1, #560]
	movz x9, #10129, lsl #0
	movk x9, #18446, lsl #16
	movk x9, #11930, lsl #32
	movk x9, #16950, lsl #48
	str x9, [x1, #568]
	movz x9, #569, lsl #0
	movk x9, #2879, lsl #16
	movk x9, #2393, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #576]
	movz x9, #648, lsl #0
	movk x9, #1481, lsl #16
	movk x9, #2617, lsl #32
	movk x9, #2647, lsl #48
	str x9, [x1, #584]
	movz x9, #5601, lsl #0
	movk x9, #28339, lsl #16
	movk x9, #23555, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #592]
	movz x9, #6378, lsl #0
	movk x9, #14578, lsl #16
	movk x9, #25760, lsl #32
	movk x9, #26055, lsl #48
	str x9, [x1, #600]
	movz x9, #886, lsl #0
	movk x9, #2775, lsl #16
	movk x9, #2150, lsl #32
	movk x9, #1143, lsl #48
	str x9, [x1, #608]
	movz x9, #1026, lsl #0
	movk x9, #403, lsl #16
	movk x9, #1092, lsl #32
	movk x9, #2804, lsl #48
	str x9, [x1, #616]
	movz x9, #8721, lsl #0
	movk x9, #27315, lsl #16
	movk x9, #21163, lsl #32
	movk x9, #11251, lsl #48
	str x9, [x1, #624]
	movz x9, #10099, lsl #0
	movk x9, #3967, lsl #16
	movk x9, #10749, lsl #32
	movk x9, #27600, lsl #48
	str x9, [x1, #632]
	movz x9, #3260, lsl #0
	movk x9, #2882, lsl #16
	movk x9, #535, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #640]
	movz x9, #2402, lsl #0
	movk x9, #1534, lsl #16
	movk x9, #2868, lsl #32
	movk x9, #1438, lsl #48
	str x9, [x1, #648]
	movz x9, #32089, lsl #0
	movk x9, #28368, lsl #16
	movk x9, #5266, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #656]
	movz x9, #23643, lsl #0
	movk x9, #15099, lsl #16
	movk x9, #28230, lsl #32
	movk x9, #14155, lsl #48
	str x9, [x1, #664]
	movz x9, #2594, lsl #0
	movk x9, #2466, lsl #16
	movk x9, #561, lsl #32
	movk x9, #2099, lsl #48
	str x9, [x1, #672]
	movz x9, #757, lsl #0
	movk x9, #2773, lsl #16
	movk x9, #319, lsl #32
	movk x9, #1063, lsl #48
	str x9, [x1, #680]
	movz x9, #25533, lsl #0
	movk x9, #24273, lsl #16
	movk x9, #5522, lsl #32
	movk x9, #20661, lsl #48
	str x9, [x1, #688]
	movz x9, #7451, lsl #0
	movk x9, #27295, lsl #16
	movk x9, #3140, lsl #32
	movk x9, #10463, lsl #48
	str x9, [x1, #696]
	movz x9, #2786, lsl #0
	movk x9, #2094, lsl #16
	movk x9, #1426, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #704]
	movz x9, #452, lsl #0
	movk x9, #807, lsl #16
	movk x9, #1435, lsl #32
	movk x9, #2319, lsl #48
	str x9, [x1, #712]
	movz x9, #27423, lsl #0
	movk x9, #20612, lsl #16
	movk x9, #14036, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #720]
	movz x9, #4449, lsl #0
	movk x9, #7943, lsl #16
	movk x9, #14125, lsl #32
	movk x9, #22826, lsl #48
	str x9, [x1, #728]
	movz x9, #1645, lsl #0
	movk x9, #2090, lsl #16
	movk x9, #2549, lsl #32
	movk x9, #375, lsl #48
	str x9, [x1, #736]
	movz x9, #3220, lsl #0
	movk x9, #2037, lsl #16
	movk x9, #2298, lsl #32
	movk x9, #1584, lsl #48
	str x9, [x1, #744]
	movz x9, #16192, lsl #0
	movk x9, #20572, lsl #16
	movk x9, #25090, lsl #32
	movk x9, #3691, lsl #48
	str x9, [x1, #752]
	movz x9, #31695, lsl #0
	movk x9, #20051, lsl #16
	movk x9, #22620, lsl #32
	movk x9, #15592, lsl #48
	str x9, [x1, #760]
	movz x9, #797, lsl #0
	movk x9, #1333, lsl #16
	movk x9, #2240, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #768]
	movz x9, #1915, lsl #0
	movk x9, #1320, lsl #16
	movk x9, #33, lsl #32
	movk x9, #2865, lsl #48
	str x9, [x1, #776]
	movz x9, #7845, lsl #0
	movk x9, #13121, lsl #16
	movk x9, #22049, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #784]
	movz x9, #18850, lsl #0
	movk x9, #12993, lsl #16
	movk x9, #325, lsl #32
	movk x9, #28201, lsl #48
	str x9, [x1, #792]
	movz x9, #641, lsl #0
	movk x9, #268, lsl #16
	movk x9, #2337, lsl #32
	movk x9, #733, lsl #48
	str x9, [x1, #800]
	movz x9, #2388, lsl #0
	movk x9, #2437, lsl #16
	movk x9, #2308, lsl #32
	movk x9, #939, lsl #48
	str x9, [x1, #808]
	movz x9, #6309, lsl #0
	movk x9, #2638, lsl #16
	movk x9, #23004, lsl #32
	movk x9, #7215, lsl #48
	str x9, [x1, #816]
	movz x9, #23506, lsl #0
	movk x9, #23988, lsl #16
	movk x9, #22718, lsl #32
	movk x9, #9243, lsl #48
	str x9, [x1, #824]
	movz x9, #193, lsl #0
	movk x9, #56, lsl #16
	movk x9, #3046, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #832]
	movz x9, #632, lsl #0
	movk x9, #2513, lsl #16
	movk x9, #1977, lsl #32
	movk x9, #650, lsl #48
	str x9, [x1, #840]
	movz x9, #1900, lsl #0
	movk x9, #551, lsl #16
	movk x9, #29982, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #848]
	movz x9, #6221, lsl #0
	movk x9, #24736, lsl #16
	movk x9, #19460, lsl #32
	movk x9, #6398, lsl #48
	str x9, [x1, #856]
	movz x9, #2687, lsl #0
	movk x9, #1461, lsl #16
	movk x9, #952, lsl #32
	movk x9, #1847, lsl #48
	str x9, [x1, #864]
	movz x9, #1789, lsl #0
	movk x9, #2789, lsl #16
	movk x9, #1651, lsl #32
	movk x9, #1703, lsl #48
	str x9, [x1, #872]
	movz x9, #26449, lsl #0
	movk x9, #14381, lsl #16
	movk x9, #9371, lsl #32
	movk x9, #18180, lsl #48
	str x9, [x1, #880]
	movz x9, #17609, lsl #0
	movk x9, #27453, lsl #16
	movk x9, #16251, lsl #32
	movk x9, #16763, lsl #48
	str x9, [x1, #888]
	movz x9, #1919, lsl #0
	movk x9, #1476, lsl #16
	movk x9, #1339, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #896]
	movz x9, #2055, lsl #0
	movk x9, #2277, lsl #16
	movk x9, #2304, lsl #32
	movk x9, #1197, lsl #48
	str x9, [x1, #904]
	movz x9, #18889, lsl #0
	movk x9, #14529, lsl #16
	movk x9, #13180, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #912]
	movz x9, #20228, lsl #0
	movk x9, #22413, lsl #16
	movk x9, #22679, lsl #32
	movk x9, #11782, lsl #48
	str x9, [x1, #920]
	movz x9, #3050, lsl #0
	movk x9, #3015, lsl #16
	movk x9, #2156, lsl #32
	movk x9, #756, lsl #48
	str x9, [x1, #928]
	movz x9, #233, lsl #0
	movk x9, #3281, lsl #16
	movk x9, #2662, lsl #32
	movk x9, #1409, lsl #48
	str x9, [x1, #936]
	movz x9, #30022, lsl #0
	movk x9, #29677, lsl #16
	movk x9, #21222, lsl #32
	movk x9, #7441, lsl #48
	str x9, [x1, #944]
	movz x9, #2293, lsl #0
	movk x9, #32296, lsl #16
	movk x9, #26203, lsl #32
	movk x9, #13869, lsl #48
	str x9, [x1, #952]
	movz x9, #1062, lsl #0
	movk x9, #2447, lsl #16
	movk x9, #296, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #960]
	movz x9, #1756, lsl #0
	movk x9, #3253, lsl #16
	movk x9, #331, lsl #32
	movk x9, #289, lsl #48
	str x9, [x1, #968]
	movz x9, #10453, lsl #0
	movk x9, #24086, lsl #16
	movk x9, #2914, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #976]
	movz x9, #17285, lsl #0
	movk x9, #32020, lsl #16
	movk x9, #3258, lsl #32
	movk x9, #2845, lsl #48
	str x9, [x1, #984]
	movz x9, #1100, lsl #0
	movk x9, #2288, lsl #16
	movk x9, #723, lsl #32
	movk x9, #1637, lsl #48
	str x9, [x1, #992]
	movz x9, #2649, lsl #0
	movk x9, #583, lsl #16
	movk x9, #2761, lsl #32
	movk x9, #17, lsl #48
	str x9, [x1, #1000]
	movz x9, #10828, lsl #0
	movk x9, #22521, lsl #16
	movk x9, #7117, lsl #32
	movk x9, #16113, lsl #48
	str x9, [x1, #1008]
	movz x9, #26075, lsl #0
	movk x9, #5739, lsl #16
	movk x9, #27177, lsl #32
	movk x9, #167, lsl #48
	str x9, [x1, #1016]
	movz x9, #3329, lsl #0
	dup v31.8h, w9
	movz x9, #10, lsl #0
	dup v30.8h, w9
	movi v29.2d, #0
	add x2, x0, #0
	add x3, x1, #0
	add x6, x1, #512
	movz x5, #8, lsl #0
20:
	ldr q20, [x2, #0]
	ldr q21, [x2, #16]
	uzp1 v0.8h, v20.8h, v21.8h
	ldr q20, [x2, #32]
	ldr q21, [x2, #48]
	uzp1 v1.8h, v20.8h, v21.8h
	ldr q20, [x2, #64]
	ldr q21, [x2, #80]
	uzp1 v2.8h, v20.8h, v21.8h
	ldr q20, [x2, #96]
	ldr q21, [x2, #112]
	uzp1 v3.8h, v20.8h, v21.8h
	ldr q20, [x6, #0]
	ldr q21, [x6, #16]
	ldr q22, [x6, #32]
	ldr q23, [x6, #48]
	zip2 v24.8h, v20.8h, v20.8h
	zip2 v25.8h, v21.8h, v21.8h
	zip1 v28.8h, v22.8h, v22.8h
	zip1 v19.8h, v23.8h, v23.8h
	zip1 v26.4s, v24.4s, v24.4s
	zip1 v27.4s, v25.4s, v25.4s
	trn1 v4.2d, v0.2d, v1.2d
	trn2 v5.2d, v0.2d, v1.2d
	trn1 v0.4s, v4.4s, v5.4s
	trn2 v1.4s, v4.4s, v5.4s
	sub v17.8h, v1.8h, v0.8h
	add v0.8h, v0.8h, v1.8h
	mul v1.8h, v17.8h, v28.8h
	sqrdmulh v17.8h, v17.8h, v19.8h
	mls v1.8h, v17.8h, v31.8h
	trn1 v4.4s, v0.4s, v1.4s
	trn2 v5.4s, v0.4s, v1.4s
	sub v17.8h, v5.8h, v4.8h
	add v4.8h, v4.8h, v5.8h
	mul v5.8h, v17.8h, v26.8h
	sqrdmulh v17.8h, v17.8h, v27.8h
	mls v5.8h, v17.8h, v31.8h
	trn1 v0.2d, v4.2d, v5.2d
	trn2 v1.2d, v4.2d, v5.2d
	zip2 v28.8h, v22.8h, v22.8h
	zip2 v19.8h, v23.8h, v23.8h
	zip2 v26.4s, v24.4s, v24.4s
	zip2 v27.4s, v25.4s, v25.4s
	trn1 v4.2d, v2.2d, v3.2d
	trn2 v5.2d, v2.2d, v3.2d
	trn1 v2.4s, v4.4s, v5.4s
	trn2 v3.4s, v4.4s, v5.4s
	sub v17.8h, v3.8h, v2.8h
	add v2.8h, v2.8h, v3.8h
	mul v3.8h, v17.8h, v28.8h
	sqrdmulh v17.8h, v17.8h, v19.8h
	mls v3.8h, v17.8h, v31.8h
	trn1 v4.4s, v2.4s, v3.4s
	trn2 v5.4s, v2.4s, v3.4s
	sub v17.8h, v5.8h, v4.8h
	add v4.8h, v4.8h, v5.8h
	mul v5.8h, v17.8h, v26.8h
	sqrdmulh v17.8h, v17.8h, v27.8h
	mls v5.8h, v17.8h, v31.8h
	trn1 v2.2d, v4.2d, v5.2d
	trn2 v3.2d, v4.2d, v5.2d
	dup v24.8h, v20.h[1]
	dup v25.8h, v21.h[1]
	sub v17.8h, v1.8h, v0.8h
	add v0.8h, v0.8h, v1.8h
	mul v1.8h, v17.8h, v24.8h
	sqrdmulh v17.8h, v17.8h, v25.8h
	mls v1.8h, v17.8h, v31.8h
	dup v24.8h, v20.h[2]
	dup v25.8h, v21.h[2]
	sub v17.8h, v3.8h, v2.8h
	add v2.8h, v2.8h, v3.8h
	mul v3.8h, v17.8h, v24.8h
	sqrdmulh v17.8h, v17.8h, v25.8h
	mls v3.8h, v17.8h, v31.8h
	sqrdmulh v16.8h, v0.8h, v30.8h
	mls v0.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v1.8h, v30.8h
	mls v1.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v2.8h, v30.8h
	mls v2.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v3.8h, v30.8h
	mls v3.8h, v16.8h, v31.8h
	dup v24.8h, v20.h[0]
	dup v25.8h, v21.h[0]
	sub v17.8h, v2.8h, v0.8h
	add v0.8h, v0.8h, v2.8h
	mul v2.8h, v17.8h, v24.8h
	sqrdmulh v17.8h, v17.8h, v25.8h
	mls v2.8h, v17.8h, v31.8h
	sub v17.8h, v3.8h, v1.8h
	add v1.8h, v1.8h, v3.8h
	mul v3.8h, v17.8h, v24.8h
	sqrdmulh v17.8h, v17.8h, v25.8h
	mls v3.8h, v17.8h, v31.8h
	str q0, [x3, #0]
	str q1, [x3, #16]
	str q2, [x3, #32]
	str q3, [x3, #48]
	add x2, x2, #128
	add x3, x3, #64
	add x6, x6, #64
	sub x5, x5, #1
	cbnz x5, 20b
	movz x9, #848, lsl #0
	mov v18.h[0], w9
	movz x9, #8347, lsl #0
	mov v19.h[0], w9
	movz x9, #1897, lsl #0
	mov v18.h[1], w9
	movz x9, #18673, lsl #0
	mov v19.h[1], w9
	movz x9, #630, lsl #0
	mov v18.h[2], w9
	movz x9, #6201, lsl #0
	mov v19.h[2], w9
	movz x9, #2642, lsl #0
	mov v18.h[3], w9
	movz x9, #26006, lsl #0
	mov v19.h[3], w9
	movz x9, #3289, lsl #0
	mov v18.h[4], w9
	movz x9, #32374, lsl #0
	mov v19.h[4], w9
	movz x9, #2580, lsl #0
	mov v18.h[5], w9
	movz x9, #25395, lsl #0
	mov v19.h[5], w9
	movz x9, #1729, lsl #0
	mov v18.h[6], w9
	movz x9, #17019, lsl #0
	mov v19.h[6], w9
	movz x9, #3303, lsl #0
	mov v18.h[7], w9
	movz x9, #32512, lsl #0
	mov v19.h[7], w9
	add x2, x1, #0
	add x3, x0, #0
	movz x5, #4, lsl #0
21:
	ldr q0, [x2, #0]
	ldr q1, [x2, #64]
	ldr q2, [x2, #128]
	ldr q3, [x2, #192]
	ldr q4, [x2, #256]
	ldr q5, [x2, #320]
	ldr q6, [x2, #384]
	ldr q7, [x2, #448]
	dup v22.8h, v18.h[0]
	dup v23.8h, v19.h[0]
	sub v17.8h, v1.8h, v0.8h
	add v0.8h, v0.8h, v1.8h
	mul v1.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v1.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[1]
	dup v23.8h, v19.h[1]
	sub v17.8h, v3.8h, v2.8h
	add v2.8h, v2.8h, v3.8h
	mul v3.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v3.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[2]
	dup v23.8h, v19.h[2]
	sub v17.8h, v5.8h, v4.8h
	add v4.8h, v4.8h, v5.8h
	mul v5.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v5.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[3]
	dup v23.8h, v19.h[3]
	sub v17.8h, v7.8h, v6.8h
	add v6.8h, v6.8h, v7.8h
	mul v7.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v7.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[4]
	dup v23.8h, v19.h[4]
	sub v17.8h, v2.8h, v0.8h
	add v0.8h, v0.8h, v2.8h
	mul v2.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v2.8h, v17.8h, v31.8h
	sub v17.8h, v3.8h, v1.8h
	add v1.8h, v1.8h, v3.8h
	mul v3.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v3.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[5]
	dup v23.8h, v19.h[5]
	sub v17.8h, v6.8h, v4.8h
	add v4.8h, v4.8h, v6.8h
	mul v6.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v6.8h, v17.8h, v31.8h
	sub v17.8h, v7.8h, v5.8h
	add v5.8h, v5.8h, v7.8h
	mul v7.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v7.8h, v17.8h, v31.8h
	sqrdmulh v16.8h, v0.8h, v30.8h
	mls v0.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v1.8h, v30.8h
	mls v1.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v2.8h, v30.8h
	mls v2.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v3.8h, v30.8h
	mls v3.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v4.8h, v30.8h
	mls v4.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v5.8h, v30.8h
	mls v5.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v6.8h, v30.8h
	mls v6.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v7.8h, v30.8h
	mls v7.8h, v16.8h, v31.8h
	dup v22.8h, v18.h[6]
	dup v23.8h, v19.h[6]
	sub v17.8h, v4.8h, v0.8h
	add v0.8h, v0.8h, v4.8h
	mul v4.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v4.8h, v17.8h, v31.8h
	sub v17.8h, v5.8h, v1.8h
	add v1.8h, v1.8h, v5.8h
	mul v5.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v5.8h, v17.8h, v31.8h
	sub v17.8h, v6.8h, v2.8h
	add v2.8h, v2.8h, v6.8h
	mul v6.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v6.8h, v17.8h, v31.8h
	sub v17.8h, v7.8h, v3.8h
	add v3.8h, v3.8h, v7.8h
	mul v7.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v7.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[7]
	dup v23.8h, v19.h[7]
	mul v16.8h, v0.8h, v22.8h
	sqrdmulh v17.8h, v0.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #0]
	str q25, [x3, #16]
	mul v16.8h, v1.8h, v22.8h
	sqrdmulh v17.8h, v1.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #128]
	str q25, [x3, #144]
	mul v16.8h, v2.8h, v22.8h
	sqrdmulh v17.8h, v2.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #256]
	str q25, [x3, #272]
	mul v16.8h, v3.8h, v22.8h
	sqrdmulh v17.8h, v3.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #384]
	str q25, [x3, #400]
	mul v16.8h, v4.8h, v22.8h
	sqrdmulh v17.8h, v4.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #512]
	str q25, [x3, #528]
	mul v16.8h, v5.8h, v22.8h
	sqrdmulh v17.8h, v5.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #640]
	str q25, [x3, #656]
	mul v16.8h, v6.8h, v22.8h
	sqrdmulh v17.8h, v6.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #768]
	str q25, [x3, #784]
	mul v16.8h, v7.8h, v22.8h
	sqrdmulh v17.8h, v7.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #896]
	str q25, [x3, #912]
	add x2, x2, #16
	add x3, x3, #32
	sub x5, x5, #1
	cbnz x5, 21b
	ret
	.p2align 6
