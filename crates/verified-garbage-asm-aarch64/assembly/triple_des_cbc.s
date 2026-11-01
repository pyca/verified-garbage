// The functions of `src/triple_des_cbc.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_cbc_encrypt_chained:
	sub sp, sp, #464
	add x4, sp, #0
	add x14, x0, #0
	add x15, x4, #0
	cbz x3, 20f
	str x19, [x15, #384]
	str x20, [x15, #392]
	str x21, [x15, #400]
	str x22, [x15, #408]
	str x23, [x15, #416]
	str x24, [x15, #424]
	str x25, [x15, #432]
	str x26, [x15, #440]
	str x27, [x15, #448]
	movz x6, #5427, lsl #0
	movk x6, #4656, lsl #16
	movk x6, #36, lsl #32
	movk x6, #801, lsl #48
	movz x7, #7483, lsl #0
	movk x7, #6712, lsl #16
	movk x7, #2092, lsl #32
	movk x7, #2857, lsl #48
	mov v5.d[0], x6
	mov v5.d[1], x7
	movz x6, #63, lsl #0
	dup v6.16b, w6
	movz x6, #0, lsl #0
	movk x6, #16576, lsl #16
	movk x6, #49216, lsl #32
	movk x6, #32896, lsl #48
	dup v7.2d, x6
	add x6, x14, #0
	add x7, x15, #0
	movz x16, #24, lsl #0
22:
	ldr q0, [x6, #0]
	ushr v1.2d, v0.2d, #2
	ushr v2.2d, v0.2d, #4
	ushr v3.2d, v0.2d, #6
	tbl v4.16b, {v0.16b, v1.16b, v2.16b, v3.16b}, v5.16b
	and v4.16b, v4.16b, v6.16b
	eor v4.16b, v4.16b, v7.16b
	str q4, [x7, #0]
	add x6, x6, #16
	add x7, x7, #16
	sub x16, x16, #1
	cbnz x16, 22b
	movz x6, #43207, lsl #0
	movk x6, #32516, lsl #16
	movk x6, #5620, lsl #32
	movk x6, #42138, lsl #48
	movz x7, #26379, lsl #0
	movk x7, #2423, lsl #16
	movk x7, #24315, lsl #32
	movk x7, #37480, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #17201, lsl #0
	movk x6, #34281, lsl #16
	movk x6, #27789, lsl #32
	movk x6, #56174, lsl #48
	movz x7, #55478, lsl #0
	movk x7, #46680, lsl #16
	movk x7, #47874, lsl #32
	movk x7, #24725, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #30124, lsl #0
	movk x6, #50714, lsl #16
	movk x6, #59469, lsl #32
	movk x6, #480, lsl #48
	movz x7, #3796, lsl #0
	movk x7, #61615, lsl #16
	movk x7, #36899, lsl #32
	movk x7, #16209, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #7415, lsl #0
	movk x6, #64356, lsl #16
	movk x6, #39762, lsl #32
	movk x6, #26525, lsl #48
	movz x7, #58169, lsl #0
	movk x7, #10435, lsl #16
	movk x7, #1950, lsl #32
	movk x7, #56362, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #27622, lsl #0
	movk x6, #64553, lsl #16
	movk x6, #49157, lsl #32
	movk x6, #43926, lsl #48
	movz x7, #42963, lsl #0
	movk x7, #21358, lsl #16
	movk x7, #7546, lsl #32
	movk x7, #38593, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #38188, lsl #0
	movk x6, #179, lsl #16
	movk x6, #31058, lsl #32
	movk x6, #20221, lsl #48
	movz x7, #53917, lsl #0
	movk x7, #15360, lsl #16
	movk x7, #12009, lsl #32
	movk x7, #57630, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #64513, lsl #0
	movk x6, #3270, lsl #16
	movk x6, #4018, lsl #32
	movk x6, #29054, lsl #48
	movz x7, #12878, lsl #0
	movk x7, #61337, lsl #16
	movk x7, #49397, lsl #32
	movk x7, #6952, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #26617, lsl #0
	movk x6, #56092, lsl #16
	movk x6, #41613, lsl #32
	movk x6, #40083, lsl #48
	movz x7, #18533, lsl #0
	movk x7, #41330, lsl #16
	movk x7, #38658, lsl #32
	movk x7, #29935, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #40684, lsl #0
	movk x6, #54031, lsl #16
	movk x6, #26298, lsl #32
	movk x6, #7413, lsl #48
	movz x7, #31105, lsl #0
	movk x7, #60984, lsl #16
	movk x7, #33110, lsl #32
	movk x7, #26018, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #22532, lsl #0
	movk x6, #11745, lsl #16
	movk x6, #57619, lsl #32
	movk x6, #55884, lsl #48
	movz x7, #1270, lsl #0
	movk x7, #45915, lsl #16
	movk x7, #15177, lsl #32
	movk x7, #34495, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #25763, lsl #0
	movk x6, #16376, lsl #16
	movk x6, #4311, lsl #32
	movk x6, #59457, lsl #48
	movz x7, #41754, lsl #0
	movk x7, #17830, lsl #16
	movk x7, #57324, lsl #32
	movk x7, #37407, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #38783, lsl #0
	movk x6, #55300, lsl #16
	movk x6, #3428, lsl #32
	movk x6, #30650, lsl #48
	movz x7, #23053, lsl #0
	movk x7, #11489, lsl #16
	movk x7, #41107, lsl #32
	movk x7, #60248, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #51534, lsl #0
	movk x6, #22193, lsl #16
	movk x6, #59172, lsl #32
	movk x6, #11690, lsl #48
	movz x7, #7355, lsl #0
	movk x7, #53590, lsl #16
	movk x7, #21460, lsl #32
	movk x7, #41673, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #44597, lsl #0
	movk x6, #25548, lsl #16
	movk x6, #7121, lsl #32
	movk x6, #56383, lsl #48
	movz x7, #8267, lsl #0
	movk x7, #49056, lsl #16
	movk x7, #50222, lsl #32
	movk x7, #14419, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14419, lsl #0
	movk x6, #57692, lsl #16
	movk x6, #40867, lsl #32
	movk x6, #53961, lsl #48
	movz x7, #972, lsl #0
	movk x7, #7207, lsl #16
	movk x7, #42047, lsl #32
	movk x7, #28600, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #55200, lsl #0
	movk x6, #4027, lsl #16
	movk x6, #17468, lsl #32
	movk x6, #43462, lsl #48
	movz x7, #63574, lsl #0
	movk x7, #25177, lsl #16
	movk x7, #13251, lsl #32
	movk x7, #56356, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #64, lsl #0
	dup v4.16b, w6
	movz x6, #128, lsl #0
	dup v5.16b, w6
	movz x6, #192, lsl #0
	dup v6.16b, w6
	movz x19, #0, lsl #0
	movk x19, #16, lsl #32
	movk x19, #32, lsl #48
	movz x20, #8208, lsl #0
	movk x20, #2064, lsl #16
	movk x20, #4096, lsl #32
	movk x20, #512, lsl #48
	movz x21, #1026, lsl #0
	movk x21, #288, lsl #32
	movk x21, #256, lsl #48
	movz x22, #2080, lsl #0
	movk x22, #1282, lsl #16
	movk x22, #2048, lsl #32
	movk x22, #8198, lsl #48
	movz x23, #0, lsl #0
	movk x23, #4, lsl #16
	movz x24, #0, lsl #0
	movk x24, #2048, lsl #48
	movz x25, #257, lsl #0
	movk x25, #512, lsl #16
	movk x25, #1032, lsl #32
	movk x25, #8, lsl #48
	movz x26, #0, lsl #0
	movk x26, #8201, lsl #16
	movk x26, #4096, lsl #48
	movz x27, #4608, lsl #0
	movk x27, #4096, lsl #16
	movk x27, #517, lsl #32
	movk x27, #1, lsl #48
	movz x0, #4, lsl #0
	movk x0, #32, lsl #16
	movk x0, #1024, lsl #48
	movz x8, #8, lsl #0
	movk x8, #8194, lsl #32
	movk x8, #16, lsl #48
23:
	ldr x5, [x1, #0]
	ldr x6, [x2, #0]
	eor x5, x5, x6
	rev x5, x5
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x11, x5, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #1
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #2
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #3
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #6
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #7
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #9
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #11
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #12
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #15
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #16
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4, lsl #0
	ror x6, x5, #18
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #20
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #512, lsl #0
	ror x6, x5, #21
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #2, lsl #0
	ror x6, x5, #27
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #29
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #31
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #36
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #37
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #38
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #40
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #43
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #44
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #46
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #47
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #49
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #52
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #53
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #55
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #56
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #57
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #58
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #61
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #62
	and x6, x6, x7
	eor x11, x11, x6
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	ror x12, x5, #1
	and x12, x12, x7
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x5, #2
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x5, #3
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2048, lsl #0
	movk x7, #512, lsl #48
	ror x6, x5, #4
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x5, #7
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x5, #8
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8, lsl #0
	movk x7, #2, lsl #48
	ror x6, x5, #10
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	movk x7, #256, lsl #48
	ror x6, x5, #11
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x5, #12
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1024, lsl #0
	ror x6, x5, #13
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x5, #16
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	movk x7, #1, lsl #48
	ror x6, x5, #17
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4, lsl #0
	ror x6, x5, #19
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x5, #21
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #512, lsl #0
	ror x6, x5, #22
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #2, lsl #0
	ror x6, x5, #28
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x5, #30
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #256, lsl #0
	movk x7, #256, lsl #32
	ror x6, x5, #31
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	movk x7, #8192, lsl #48
	ror x6, x5, #32
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #1, lsl #0
	movk x7, #1, lsl #32
	ror x6, x5, #37
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	movk x7, #32, lsl #48
	ror x6, x5, #38
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x5, #39
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x5, #41
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #8192, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x5, #44
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x5, #45
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #48
	ror x6, x5, #47
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x5, #48
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x5, #50
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x5, #53
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x5, #54
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #48
	ror x6, x5, #56
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x5, #57
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #32, lsl #0
	movk x7, #32, lsl #32
	ror x6, x5, #58
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #4096, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x5, #59
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x5, #62
	and x6, x6, x7
	eor x12, x12, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x5, #63
	and x6, x6, x7
	eor x12, x12, x6
	add x10, x15, #0
	movz x16, #8, lsl #0
24:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 24b
	add x10, x10, #120
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
25:
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	sub x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 25b
	add x10, x10, #136
	add x5, x11, #0
	add x11, x12, #0
	add x12, x5, #0
	movz x16, #8, lsl #0
26:
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x12
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x11, x11, x6
	eor x9, x9, x17
	eor x11, x11, x9
	ldr x5, [x10, #0]
	add x10, x10, #8
	eor x5, x5, x11
	mov v0.d[0], x5
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x5, v0.d[0]
	ror x6, x5, #6
	and x6, x6, x19
	ror x7, x5, #10
	and x7, x7, x20
	eor x6, x6, x7
	ror x7, x5, #18
	and x7, x7, x21
	eor x6, x6, x7
	ror x7, x5, #22
	and x7, x7, x22
	eor x6, x6, x7
	ror x9, x5, #23
	and x9, x9, x23
	ror x13, x5, #29
	and x13, x13, x24
	eor x9, x9, x13
	ror x13, x5, #34
	and x13, x13, x25
	eor x9, x9, x13
	ror x13, x5, #38
	and x13, x13, x26
	eor x9, x9, x13
	ror x17, x5, #46
	and x17, x17, x27
	ror x7, x5, #50
	and x7, x7, x0
	eor x17, x17, x7
	ror x7, x5, #58
	and x7, x7, x8
	eor x17, x17, x7
	eor x12, x12, x6
	eor x9, x9, x17
	eor x12, x12, x9
	sub x16, x16, #1
	cbnz x16, 26b
	movz x7, #16, lsl #0
	movk x7, #4, lsl #48
	and x5, x12, x7
	movz x7, #0, lsl #0
	movk x7, #1, lsl #16
	ror x6, x12, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #32
	ror x6, x12, #3
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #64, lsl #0
	movk x7, #16, lsl #48
	ror x6, x12, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #48
	ror x6, x12, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #16
	ror x6, x12, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #32
	ror x6, x12, #9
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #256, lsl #0
	ror x6, x12, #11
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #32
	ror x6, x12, #15
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1024, lsl #0
	ror x6, x12, #17
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #1, lsl #0
	ror x6, x12, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #48
	ror x6, x12, #21
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4, lsl #0
	ror x6, x12, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #48
	ror x6, x12, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #32
	ror x6, x12, #28
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #48
	ror x6, x12, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #32
	ror x6, x12, #34
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4096, lsl #16
	ror x6, x12, #37
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #16
	ror x6, x12, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #48
	ror x6, x12, #44
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16, lsl #16
	ror x6, x12, #46
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #32
	ror x6, x12, #48
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #64, lsl #16
	ror x6, x12, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #16384, lsl #32
	ror x6, x12, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #4, lsl #32
	ror x6, x12, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #4096, lsl #0
	ror x6, x12, #55
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #256, lsl #16
	ror x6, x12, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1, lsl #48
	ror x6, x12, #58
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #16384, lsl #0
	ror x6, x12, #61
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #1024, lsl #16
	ror x6, x12, #63
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #16
	ror x6, x11, #1
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #32
	ror x6, x11, #2
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #128, lsl #0
	movk x7, #32, lsl #48
	ror x6, x11, #5
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #48
	ror x6, x11, #6
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #16
	ror x6, x11, #7
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #32
	ror x6, x11, #8
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #512, lsl #0
	ror x6, x11, #10
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #32
	ror x6, x11, #14
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2048, lsl #0
	ror x6, x11, #16
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #2, lsl #0
	ror x6, x11, #19
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #48
	ror x6, x11, #20
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8, lsl #0
	ror x6, x11, #25
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #48
	ror x6, x11, #26
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #32
	ror x6, x11, #27
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #48
	ror x6, x11, #32
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #32
	ror x6, x11, #33
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8192, lsl #16
	ror x6, x11, #36
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #16
	ror x6, x11, #42
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #48
	ror x6, x11, #43
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32, lsl #16
	ror x6, x11, #45
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #32
	ror x6, x11, #47
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #128, lsl #16
	ror x6, x11, #51
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #32768, lsl #32
	ror x6, x11, #52
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #8, lsl #32
	ror x6, x11, #53
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #8192, lsl #0
	ror x6, x11, #54
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #512, lsl #16
	ror x6, x11, #56
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2, lsl #48
	ror x6, x11, #57
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32768, lsl #0
	ror x6, x11, #60
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #0, lsl #0
	movk x7, #2048, lsl #16
	ror x6, x11, #62
	and x6, x6, x7
	eor x5, x5, x6
	movz x7, #32, lsl #0
	movk x7, #8, lsl #48
	ror x6, x11, #63
	and x6, x6, x7
	eor x5, x5, x6
	rev x5, x5
	str x5, [x2, #0]
	str x5, [x1, #0]
	add x2, x2, #8
	sub x3, x3, #1
	cbnz x3, 23b
	ldr x19, [x15, #384]
	ldr x20, [x15, #392]
	ldr x21, [x15, #400]
	ldr x22, [x15, #408]
	ldr x23, [x15, #416]
	ldr x24, [x15, #424]
	ldr x25, [x15, #432]
	ldr x26, [x15, #440]
	ldr x27, [x15, #448]
	b 21f
20:
21:
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
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	add sp, sp, #464
	ret
	.p2align 6

vg_triple_des_cbc_decrypt_chained:
	sub sp, sp, #1008
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #904]
	str x20, [x5, #912]
	str x21, [x5, #920]
	str x22, [x5, #928]
	str x23, [x5, #936]
	str x24, [x5, #944]
	str x25, [x5, #952]
	str x26, [x5, #960]
	str x27, [x5, #968]
	str x28, [x5, #976]
	ldr x6, [x1, #0]
	str x6, [x5, #984]
	cbz x3, 20f
	sub x7, x3, #1
	lsl x7, x7, #3
	add x7, x7, x2
	ldr x6, [x7, #0]
	str x6, [x1, #0]
	b 21f
20:
21:
	add x23, x2, #0
	add x24, x3, #0
	ldr x6, [x0, #0]
	str x6, [x5, #520]
	ldr x6, [x0, #8]
	str x6, [x5, #528]
	ldr x6, [x0, #16]
	str x6, [x5, #536]
	ldr x6, [x0, #24]
	str x6, [x5, #544]
	ldr x6, [x0, #32]
	str x6, [x5, #552]
	ldr x6, [x0, #40]
	str x6, [x5, #560]
	ldr x6, [x0, #48]
	str x6, [x5, #568]
	ldr x6, [x0, #56]
	str x6, [x5, #576]
	ldr x6, [x0, #64]
	str x6, [x5, #584]
	ldr x6, [x0, #72]
	str x6, [x5, #592]
	ldr x6, [x0, #80]
	str x6, [x5, #600]
	ldr x6, [x0, #88]
	str x6, [x5, #608]
	ldr x6, [x0, #96]
	str x6, [x5, #616]
	ldr x6, [x0, #104]
	str x6, [x5, #624]
	ldr x6, [x0, #112]
	str x6, [x5, #632]
	ldr x6, [x0, #120]
	str x6, [x5, #640]
	ldr x6, [x0, #128]
	str x6, [x5, #648]
	ldr x6, [x0, #136]
	str x6, [x5, #656]
	ldr x6, [x0, #144]
	str x6, [x5, #664]
	ldr x6, [x0, #152]
	str x6, [x5, #672]
	ldr x6, [x0, #160]
	str x6, [x5, #680]
	ldr x6, [x0, #168]
	str x6, [x5, #688]
	ldr x6, [x0, #176]
	str x6, [x5, #696]
	ldr x6, [x0, #184]
	str x6, [x5, #704]
	ldr x6, [x0, #192]
	str x6, [x5, #712]
	ldr x6, [x0, #200]
	str x6, [x5, #720]
	ldr x6, [x0, #208]
	str x6, [x5, #728]
	ldr x6, [x0, #216]
	str x6, [x5, #736]
	ldr x6, [x0, #224]
	str x6, [x5, #744]
	ldr x6, [x0, #232]
	str x6, [x5, #752]
	ldr x6, [x0, #240]
	str x6, [x5, #760]
	ldr x6, [x0, #248]
	str x6, [x5, #768]
	ldr x6, [x0, #256]
	str x6, [x5, #776]
	ldr x6, [x0, #264]
	str x6, [x5, #784]
	ldr x6, [x0, #272]
	str x6, [x5, #792]
	ldr x6, [x0, #280]
	str x6, [x5, #800]
	ldr x6, [x0, #288]
	str x6, [x5, #808]
	ldr x6, [x0, #296]
	str x6, [x5, #816]
	ldr x6, [x0, #304]
	str x6, [x5, #824]
	ldr x6, [x0, #312]
	str x6, [x5, #832]
	ldr x6, [x0, #320]
	str x6, [x5, #840]
	ldr x6, [x0, #328]
	str x6, [x5, #848]
	ldr x6, [x0, #336]
	str x6, [x5, #856]
	ldr x6, [x0, #344]
	str x6, [x5, #864]
	ldr x6, [x0, #352]
	str x6, [x5, #872]
	ldr x6, [x0, #360]
	str x6, [x5, #880]
	ldr x6, [x0, #368]
	str x6, [x5, #888]
	ldr x6, [x0, #376]
	str x6, [x5, #896]
	cbz x24, 22f
24:
	lsr x13, x24, #0
	cbnz x13, 25f
	add x16, x24, #0
	b 26f
25:
	movz x16, #1, lsl #0
26:
	add x14, x5, #0
	add x14, x14, #512
	add x15, x23, #0
	add x17, x16, #0
27:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	add x14, x14, #8
	add x15, x15, #8
	sub x17, x17, #1
	cbnz x17, 27b
	add x0, x5, #520
	add x1, x5, #512
	add x2, x5, #0
	add x26, x30, #0
	bl {vg_triple_des_decrypt_block}
	add x5, x2, #0
	add x30, x26, #0
	lsr x13, x24, #0
	cbnz x13, 28f
	add x16, x24, #0
	b 29f
28:
	movz x16, #1, lsl #0
29:
	add x14, x5, #0
	add x14, x14, #512
	add x15, x23, #0
	add x17, x16, #0
210:
	ldr x8, [x14, #0]
	ldr x9, [x5, #984]
	eor x8, x8, x9
	str x8, [x14, #0]
	ldr x8, [x15, #0]
	str x8, [x5, #984]
	ldr x8, [x14, #0]
	str x8, [x15, #0]
	add x14, x14, #8
	add x15, x15, #8
	sub x17, x17, #1
	cbnz x17, 210b
	add x23, x15, #0
	sub x24, x24, x16
	cbnz x24, 24b
	b 23f
22:
23:
	ldr x19, [x5, #904]
	ldr x20, [x5, #912]
	ldr x21, [x5, #920]
	ldr x22, [x5, #928]
	ldr x23, [x5, #936]
	ldr x24, [x5, #944]
	ldr x25, [x5, #952]
	ldr x26, [x5, #960]
	ldr x27, [x5, #968]
	ldr x28, [x5, #976]
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
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
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
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	str x17, [sp, #992]
	add sp, sp, #1008
	ret
	.p2align 6
