// The functions of `src/internal/vg_ecdsa_p224_sign.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p224_sign:
	str x19, [x4, #0]
	str x20, [x4, #8]
	str x21, [x4, #16]
	str x22, [x4, #24]
	str x23, [x4, #32]
	str x24, [x4, #40]
	str x25, [x4, #48]
	str x30, [x4, #56]
	add x20, x0, #0
	add x0, x4, #0
	add x17, x3, #20
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #1056]
	add x17, x3, #12
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #1064]
	add x17, x3, #4
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #1072]
	ldr x5, [x3, #0]
	rev x5, x5
	lsr x5, x5, #32
	str x5, [x0, #1080]
	add x17, x1, #20
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #1088]
	add x17, x1, #12
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #1096]
	add x17, x1, #4
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #1104]
	ldr x5, [x1, #0]
	rev x5, x5
	lsr x5, x5, #32
	str x5, [x0, #1112]
	add x17, x2, #20
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #1120]
	add x17, x2, #12
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #1128]
	add x17, x2, #4
	ldr x5, [x17, #0]
	rev x5, x5
	str x5, [x0, #1136]
	ldr x5, [x2, #0]
	rev x5, x5
	lsr x5, x5, #32
	str x5, [x0, #1144]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #64]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #72]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #80]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #88]
	movz x1, #10813, lsl #0
	movk x1, #23644, lsl #16
	movk x1, #10565, lsl #32
	movk x1, #5085, lsl #48
	str x1, [x0, #96]
	movz x1, #61502, lsl #0
	movk x1, #57528, lsl #16
	movk x1, #5794, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #104]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #112]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #120]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #160]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #168]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #176]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #184]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #192]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #200]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #208]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #216]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #224]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #232]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #248]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #3, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #256]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #264]
	movz x1, #65532, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #272]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #280]
	movz x1, #22989, lsl #0
	movk x1, #25536, lsl #16
	movk x1, #52726, lsl #32
	movk x1, #59240, lsl #48
	str x1, [x0, #288]
	movz x1, #4880, lsl #0
	movk x1, #52464, lsl #16
	movk x1, #49907, lsl #32
	movk x1, #4218, lsl #48
	str x1, [x0, #296]
	movz x1, #33105, lsl #0
	movk x1, #51282, lsl #16
	movk x1, #47768, lsl #32
	movk x1, #15822, lsl #48
	str x1, [x0, #304]
	movz x1, #12179, lsl #0
	movk x1, #32704, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #312]
	movz x1, #19178, lsl #0
	movk x1, #27914, lsl #16
	movk x1, #21030, lsl #32
	movk x1, #48272, lsl #48
	str x1, [x0, #320]
	movz x1, #49066, lsl #0
	movk x1, #24600, lsl #16
	movk x1, #38710, lsl #32
	movk x1, #34085, lsl #48
	str x1, [x0, #328]
	movz x1, #60421, lsl #0
	movk x1, #63851, lsl #16
	movk x1, #44955, lsl #32
	movk x1, #28115, lsl #48
	str x1, [x0, #336]
	movz x1, #24160, lsl #0
	movk x1, #41499, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #344]
	movz x1, #60904, lsl #0
	movk x1, #61427, lsl #16
	movk x1, #41445, lsl #32
	movk x1, #11996, lsl #48
	str x1, [x0, #352]
	movz x1, #23147, lsl #0
	movk x1, #1331, lsl #16
	movk x1, #26411, lsl #32
	movk x1, #63693, lsl #48
	str x1, [x0, #360]
	movz x1, #59512, lsl #0
	movk x1, #991, lsl #16
	movk x1, #50606, lsl #32
	movk x1, #44713, lsl #48
	str x1, [x0, #368]
	movz x1, #34545, lsl #0
	movk x1, #24903, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #376]
	movz x1, #32021, lsl #0
	movk x1, #24401, lsl #16
	movk x1, #31337, lsl #32
	movk x1, #10644, lsl #48
	str x1, [x0, #384]
	movz x1, #16203, lsl #0
	movk x1, #12758, lsl #16
	movk x1, #65369, lsl #32
	movk x1, #43976, lsl #48
	str x1, [x0, #392]
	movz x1, #18518, lsl #0
	movk x1, #55665, lsl #16
	movk x1, #24444, lsl #32
	movk x1, #27345, lsl #48
	str x1, [x0, #400]
	movz x1, #31073, lsl #0
	movk x1, #45545, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #54723, lsl #32
	movk x1, #41891, lsl #48
	str x1, [x0, #416]
	movz x1, #54970, lsl #0
	movk x1, #60450, lsl #16
	movk x1, #4033, lsl #32
	movk x1, #8007, lsl #48
	str x1, [x0, #424]
	movz x1, #59741, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #432]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #440]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #512]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #520]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #528]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #536]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #544]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #552]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #560]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #568]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #576]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #584]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #592]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #600]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1472]
	movz x19, #32, lsl #0
	movz x5, #1, lsl #0
20:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #1056]
	lsl x17, x19, #3
	add x17, x0, x17
	and x2, x1, x5
	strb w2, [x17, #1504]
	lsr x2, x1, #1
	and x2, x2, x5
	strb w2, [x17, #1505]
	lsr x2, x1, #2
	and x2, x2, x5
	strb w2, [x17, #1506]
	lsr x2, x1, #3
	and x2, x2, x5
	strb w2, [x17, #1507]
	lsr x2, x1, #4
	and x2, x2, x5
	strb w2, [x17, #1508]
	lsr x2, x1, #5
	and x2, x2, x5
	strb w2, [x17, #1509]
	lsr x2, x1, #6
	and x2, x2, x5
	strb w2, [x17, #1510]
	lsr x2, x1, #7
	and x2, x2, x5
	strb w2, [x17, #1511]
	cbnz x19, 20b
	ldr x1, [x0, #288]
	str x1, [x0, #1344]
	ldr x1, [x0, #296]
	str x1, [x0, #1352]
	ldr x1, [x0, #304]
	str x1, [x0, #1360]
	ldr x1, [x0, #312]
	str x1, [x0, #1368]
	movz x1, #62856, lsl #0
	movk x1, #27387, lsl #16
	movk x1, #58071, lsl #32
	movk x1, #61189, lsl #48
	str x1, [x0, #512]
	movz x1, #20932, lsl #0
	movk x1, #62748, lsl #16
	movk x1, #13005, lsl #32
	movk x1, #23827, lsl #48
	str x1, [x0, #520]
	movz x1, #48691, lsl #0
	movk x1, #28946, lsl #16
	movk x1, #62854, lsl #32
	movk x1, #59839, lsl #48
	str x1, [x0, #528]
	movz x1, #40775, lsl #0
	movk x1, #51478, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #536]
	movz x1, #27774, lsl #0
	movk x1, #41811, lsl #16
	movk x1, #19422, lsl #32
	movk x1, #41013, lsl #48
	str x1, [x0, #544]
	movz x1, #29324, lsl #0
	movk x1, #29120, lsl #16
	movk x1, #4503, lsl #32
	movk x1, #8918, lsl #48
	str x1, [x0, #552]
	movz x1, #13878, lsl #0
	movk x1, #29309, lsl #16
	movk x1, #45942, lsl #32
	movk x1, #17055, lsl #48
	str x1, [x0, #560]
	movz x1, #36546, lsl #0
	movk x1, #17537, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #568]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #576]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #584]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #592]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #600]
	movz x7, #0, lsl #0
	str x7, [x0, #1760]
	movz x19, #37, lsl #0
21:
	sub x19, x19, #1
	movz x16, #7, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	movz x2, #0, lsl #0
	add x2, x2, x2
	ldrb w4, [x16, #1510]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1509]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1508]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1507]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1506]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1505]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1504]
	add x2, x2, x4
	sub x3, x2, #64
	lsr x4, x3, #63
	movz x9, #0, lsl #0
	sub x4, x9, x4
	eor x2, x3, x4
	sub x2, x2, x4
	movz x7, #0, lsl #0
	adrp x16, {VG_P224_COMB}
	add x16, x16, {VG_P224_COMB}
	movz x17, #4096, lsl #0
	mul x17, x19, x17
	add x16, x16, x17
	movz x5, #1, lsl #0
	movz x1, #0, lsl #0
	dup v19.2d, x2
	dup v28.2d, x5
	add v18.2d, v28.2d, v28.2d
	movi v17.2d, #0
	sub v17.2d, v17.2d, v28.2d
	movi v30.2d, #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #0]
	ldr q21, [x16, #16]
	ldr q22, [x16, #32]
	ldr q23, [x16, #48]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #64]
	ldr q25, [x16, #80]
	ldr q26, [x16, #96]
	ldr q27, [x16, #112]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #128]
	ldr q21, [x16, #144]
	ldr q22, [x16, #160]
	ldr q23, [x16, #176]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #192]
	ldr q25, [x16, #208]
	ldr q26, [x16, #224]
	ldr q27, [x16, #240]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #256]
	ldr q21, [x16, #272]
	ldr q22, [x16, #288]
	ldr q23, [x16, #304]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #320]
	ldr q25, [x16, #336]
	ldr q26, [x16, #352]
	ldr q27, [x16, #368]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #384]
	ldr q21, [x16, #400]
	ldr q22, [x16, #416]
	ldr q23, [x16, #432]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #448]
	ldr q25, [x16, #464]
	ldr q26, [x16, #480]
	ldr q27, [x16, #496]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #512]
	ldr q21, [x16, #528]
	ldr q22, [x16, #544]
	ldr q23, [x16, #560]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #576]
	ldr q25, [x16, #592]
	ldr q26, [x16, #608]
	ldr q27, [x16, #624]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #640]
	ldr q21, [x16, #656]
	ldr q22, [x16, #672]
	ldr q23, [x16, #688]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #704]
	ldr q25, [x16, #720]
	ldr q26, [x16, #736]
	ldr q27, [x16, #752]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #768]
	ldr q21, [x16, #784]
	ldr q22, [x16, #800]
	ldr q23, [x16, #816]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #832]
	ldr q25, [x16, #848]
	ldr q26, [x16, #864]
	ldr q27, [x16, #880]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #896]
	ldr q21, [x16, #912]
	ldr q22, [x16, #928]
	ldr q23, [x16, #944]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #960]
	ldr q25, [x16, #976]
	ldr q26, [x16, #992]
	ldr q27, [x16, #1008]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1024]
	ldr q21, [x16, #1040]
	ldr q22, [x16, #1056]
	ldr q23, [x16, #1072]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1088]
	ldr q25, [x16, #1104]
	ldr q26, [x16, #1120]
	ldr q27, [x16, #1136]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1152]
	ldr q21, [x16, #1168]
	ldr q22, [x16, #1184]
	ldr q23, [x16, #1200]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1216]
	ldr q25, [x16, #1232]
	ldr q26, [x16, #1248]
	ldr q27, [x16, #1264]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1280]
	ldr q21, [x16, #1296]
	ldr q22, [x16, #1312]
	ldr q23, [x16, #1328]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1344]
	ldr q25, [x16, #1360]
	ldr q26, [x16, #1376]
	ldr q27, [x16, #1392]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1408]
	ldr q21, [x16, #1424]
	ldr q22, [x16, #1440]
	ldr q23, [x16, #1456]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1472]
	ldr q25, [x16, #1488]
	ldr q26, [x16, #1504]
	ldr q27, [x16, #1520]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1536]
	ldr q21, [x16, #1552]
	ldr q22, [x16, #1568]
	ldr q23, [x16, #1584]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1600]
	ldr q25, [x16, #1616]
	ldr q26, [x16, #1632]
	ldr q27, [x16, #1648]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1664]
	ldr q21, [x16, #1680]
	ldr q22, [x16, #1696]
	ldr q23, [x16, #1712]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1728]
	ldr q25, [x16, #1744]
	ldr q26, [x16, #1760]
	ldr q27, [x16, #1776]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1792]
	ldr q21, [x16, #1808]
	ldr q22, [x16, #1824]
	ldr q23, [x16, #1840]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1856]
	ldr q25, [x16, #1872]
	ldr q26, [x16, #1888]
	ldr q27, [x16, #1904]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1920]
	ldr q21, [x16, #1936]
	ldr q22, [x16, #1952]
	ldr q23, [x16, #1968]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1984]
	ldr q25, [x16, #2000]
	ldr q26, [x16, #2016]
	ldr q27, [x16, #2032]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2048]
	ldr q21, [x16, #2064]
	ldr q22, [x16, #2080]
	ldr q23, [x16, #2096]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2112]
	ldr q25, [x16, #2128]
	ldr q26, [x16, #2144]
	ldr q27, [x16, #2160]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2176]
	ldr q21, [x16, #2192]
	ldr q22, [x16, #2208]
	ldr q23, [x16, #2224]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2240]
	ldr q25, [x16, #2256]
	ldr q26, [x16, #2272]
	ldr q27, [x16, #2288]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2304]
	ldr q21, [x16, #2320]
	ldr q22, [x16, #2336]
	ldr q23, [x16, #2352]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2368]
	ldr q25, [x16, #2384]
	ldr q26, [x16, #2400]
	ldr q27, [x16, #2416]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2432]
	ldr q21, [x16, #2448]
	ldr q22, [x16, #2464]
	ldr q23, [x16, #2480]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2496]
	ldr q25, [x16, #2512]
	ldr q26, [x16, #2528]
	ldr q27, [x16, #2544]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2560]
	ldr q21, [x16, #2576]
	ldr q22, [x16, #2592]
	ldr q23, [x16, #2608]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2624]
	ldr q25, [x16, #2640]
	ldr q26, [x16, #2656]
	ldr q27, [x16, #2672]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2688]
	ldr q21, [x16, #2704]
	ldr q22, [x16, #2720]
	ldr q23, [x16, #2736]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2752]
	ldr q25, [x16, #2768]
	ldr q26, [x16, #2784]
	ldr q27, [x16, #2800]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2816]
	ldr q21, [x16, #2832]
	ldr q22, [x16, #2848]
	ldr q23, [x16, #2864]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2880]
	ldr q25, [x16, #2896]
	ldr q26, [x16, #2912]
	ldr q27, [x16, #2928]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2944]
	ldr q21, [x16, #2960]
	ldr q22, [x16, #2976]
	ldr q23, [x16, #2992]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3008]
	ldr q25, [x16, #3024]
	ldr q26, [x16, #3040]
	ldr q27, [x16, #3056]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3072]
	ldr q21, [x16, #3088]
	ldr q22, [x16, #3104]
	ldr q23, [x16, #3120]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3136]
	ldr q25, [x16, #3152]
	ldr q26, [x16, #3168]
	ldr q27, [x16, #3184]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3200]
	ldr q21, [x16, #3216]
	ldr q22, [x16, #3232]
	ldr q23, [x16, #3248]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3264]
	ldr q25, [x16, #3280]
	ldr q26, [x16, #3296]
	ldr q27, [x16, #3312]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3328]
	ldr q21, [x16, #3344]
	ldr q22, [x16, #3360]
	ldr q23, [x16, #3376]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3392]
	ldr q25, [x16, #3408]
	ldr q26, [x16, #3424]
	ldr q27, [x16, #3440]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3456]
	ldr q21, [x16, #3472]
	ldr q22, [x16, #3488]
	ldr q23, [x16, #3504]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3520]
	ldr q25, [x16, #3536]
	ldr q26, [x16, #3552]
	ldr q27, [x16, #3568]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3584]
	ldr q21, [x16, #3600]
	ldr q22, [x16, #3616]
	ldr q23, [x16, #3632]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3648]
	ldr q25, [x16, #3664]
	ldr q26, [x16, #3680]
	ldr q27, [x16, #3696]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3712]
	ldr q21, [x16, #3728]
	ldr q22, [x16, #3744]
	ldr q23, [x16, #3760]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3776]
	ldr q25, [x16, #3792]
	ldr q26, [x16, #3808]
	ldr q27, [x16, #3824]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3840]
	ldr q21, [x16, #3856]
	ldr q22, [x16, #3872]
	ldr q23, [x16, #3888]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3904]
	ldr q25, [x16, #3920]
	ldr q26, [x16, #3936]
	ldr q27, [x16, #3952]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3968]
	ldr q21, [x16, #3984]
	ldr q22, [x16, #4000]
	ldr q23, [x16, #4016]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4032]
	ldr q25, [x16, #4048]
	ldr q26, [x16, #4064]
	ldr q27, [x16, #4080]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	orr v0.16b, v0.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	orr v2.16b, v2.16b, v6.16b
	orr v3.16b, v3.16b, v7.16b
	movi v16.2d, #0
	cmeq v16.2d, v16.2d, v19.2d
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[0], x6
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v3.16b, v20.16b, v16.16b
	str q0, [x0, #704]
	str q1, [x0, #720]
	str q2, [x0, #736]
	str q3, [x0, #752]
	subs x4, x2, x5
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #768]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #776]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #784]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #792]
	movz x7, #0, lsl #0
	ldr x8, [x0, #160]
	ldr x9, [x0, #168]
	ldr x10, [x0, #176]
	ldr x11, [x0, #184]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	str x8, [x0, #1024]
	str x9, [x0, #1032]
	str x10, [x0, #1040]
	str x11, [x0, #1048]
	movz x16, #7, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	ldrb w3, [x16, #1510]
	sub x3, x3, #1
	ldr x1, [x0, #736]
	ldr x2, [x0, #1024]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #736]
	ldr x1, [x0, #744]
	ldr x2, [x0, #1032]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #744]
	ldr x1, [x0, #752]
	ldr x2, [x0, #1040]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #752]
	ldr x1, [x0, #760]
	ldr x2, [x0, #1048]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #760]
	mov v29.d[0], x30
	bl {vg_p224_proj_add}
	umov x30, v29.d[0]
	ldr x1, [x0, #608]
	str x1, [x0, #512]
	ldr x1, [x0, #616]
	str x1, [x0, #520]
	ldr x1, [x0, #624]
	str x1, [x0, #528]
	ldr x1, [x0, #632]
	str x1, [x0, #536]
	ldr x1, [x0, #640]
	str x1, [x0, #544]
	ldr x1, [x0, #648]
	str x1, [x0, #552]
	ldr x1, [x0, #656]
	str x1, [x0, #560]
	ldr x1, [x0, #664]
	str x1, [x0, #568]
	ldr x1, [x0, #672]
	str x1, [x0, #576]
	ldr x1, [x0, #680]
	str x1, [x0, #584]
	ldr x1, [x0, #688]
	str x1, [x0, #592]
	ldr x1, [x0, #696]
	str x1, [x0, #600]
	cbnz x19, 21b
	mov v29.d[0], x30
	bl {vg_p224_inv_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x4, [x0, #992]
	ldr x5, [x0, #1000]
	ldr x16, [x0, #1008]
	ldr x17, [x0, #1016]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #512]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	mul x1, x8, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #520]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #528]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #536]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #64]
	subs x1, x12, x2
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1152]
	str x13, [x0, #1160]
	str x8, [x0, #1168]
	str x9, [x0, #1176]
	movz x7, #0, lsl #0
	ldr x4, [x0, #192]
	ldr x5, [x0, #200]
	ldr x16, [x0, #208]
	ldr x17, [x0, #216]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1152]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	mul x1, x8, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1160]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1168]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1176]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #64]
	subs x1, x12, x2
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1184]
	str x13, [x0, #1192]
	str x8, [x0, #1200]
	str x9, [x0, #1208]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1184]
	ldr x9, [x0, #1192]
	ldr x10, [x0, #1200]
	ldr x11, [x0, #1208]
	ldr x2, [x0, #160]
	adds x8, x8, x2
	ldr x2, [x0, #168]
	adcs x9, x9, x2
	ldr x2, [x0, #176]
	adcs x10, x10, x2
	ldr x2, [x0, #184]
	adcs x11, x11, x2
	adc x12, x7, x7
	ldr x2, [x0, #96]
	subs x1, x8, x2
	ldr x2, [x0, #104]
	sbcs x3, x9, x2
	ldr x2, [x0, #112]
	sbcs x4, x10, x2
	ldr x2, [x0, #120]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	str x8, [x0, #1216]
	str x9, [x0, #1224]
	str x10, [x0, #1232]
	str x11, [x0, #1240]
	movz x7, #0, lsl #0
	ldr x4, [x0, #384]
	ldr x5, [x0, #392]
	ldr x16, [x0, #400]
	ldr x17, [x0, #408]
	movz x6, #49899, lsl #0
	movk x6, #27167, lsl #16
	movk x6, #17008, lsl #32
	movk x6, #55010, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1056]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	mul x1, x8, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1064]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1072]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1080]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1248]
	str x13, [x0, #1256]
	str x8, [x0, #1264]
	str x9, [x0, #1272]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1088]
	ldr x2, [x0, #96]
	subs x16, x1, x2
	ldr x1, [x0, #1096]
	ldr x2, [x0, #104]
	sbcs x16, x1, x2
	ldr x1, [x0, #1104]
	ldr x2, [x0, #112]
	sbcs x16, x1, x2
	ldr x1, [x0, #1112]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1088]
	ldr x2, [x0, #1096]
	orr x1, x1, x2
	ldr x2, [x0, #1104]
	orr x1, x1, x2
	ldr x2, [x0, #1112]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1056]
	ldr x2, [x0, #96]
	subs x16, x1, x2
	ldr x1, [x0, #1064]
	ldr x2, [x0, #104]
	sbcs x16, x1, x2
	ldr x1, [x0, #1072]
	ldr x2, [x0, #112]
	sbcs x16, x1, x2
	ldr x1, [x0, #1080]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1056]
	ldr x2, [x0, #1064]
	orr x1, x1, x2
	ldr x2, [x0, #1072]
	orr x1, x1, x2
	ldr x2, [x0, #1080]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1216]
	ldr x2, [x0, #1224]
	orr x1, x1, x2
	ldr x2, [x0, #1232]
	orr x1, x1, x2
	ldr x2, [x0, #1240]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	mov v29.d[0], x30
	bl {vg_p224_inv_mod_n}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x4, [x0, #384]
	ldr x5, [x0, #392]
	ldr x16, [x0, #400]
	ldr x17, [x0, #408]
	movz x6, #49899, lsl #0
	movk x6, #27167, lsl #16
	movk x6, #17008, lsl #32
	movk x6, #55010, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1216]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	mul x1, x8, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1224]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1232]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1240]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1280]
	str x13, [x0, #1288]
	str x8, [x0, #1296]
	str x9, [x0, #1304]
	movz x7, #0, lsl #0
	ldr x4, [x0, #384]
	ldr x5, [x0, #392]
	ldr x16, [x0, #400]
	ldr x17, [x0, #408]
	movz x6, #49899, lsl #0
	movk x6, #27167, lsl #16
	movk x6, #17008, lsl #32
	movk x6, #55010, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1088]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	mul x1, x8, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1096]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1104]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1112]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1312]
	str x13, [x0, #1320]
	str x8, [x0, #1328]
	str x9, [x0, #1336]
	movz x7, #0, lsl #0
	ldr x4, [x0, #384]
	ldr x5, [x0, #392]
	ldr x16, [x0, #400]
	ldr x17, [x0, #408]
	movz x6, #49899, lsl #0
	movk x6, #27167, lsl #16
	movk x6, #17008, lsl #32
	movk x6, #55010, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1120]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	mul x1, x8, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1128]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1136]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1144]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1344]
	str x13, [x0, #1352]
	str x8, [x0, #1360]
	str x9, [x0, #1368]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	movz x6, #49899, lsl #0
	movk x6, #27167, lsl #16
	movk x6, #17008, lsl #32
	movk x6, #55010, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1280]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	mul x1, x8, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1288]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1296]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1304]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1376]
	str x13, [x0, #1384]
	str x8, [x0, #1392]
	str x9, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1376]
	ldr x9, [x0, #1384]
	ldr x10, [x0, #1392]
	ldr x11, [x0, #1400]
	ldr x2, [x0, #1344]
	adds x8, x8, x2
	ldr x2, [x0, #1352]
	adcs x9, x9, x2
	ldr x2, [x0, #1360]
	adcs x10, x10, x2
	ldr x2, [x0, #1368]
	adcs x11, x11, x2
	adc x12, x7, x7
	ldr x2, [x0, #96]
	subs x1, x8, x2
	ldr x2, [x0, #104]
	sbcs x3, x9, x2
	ldr x2, [x0, #112]
	sbcs x4, x10, x2
	ldr x2, [x0, #120]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	str x8, [x0, #1376]
	str x9, [x0, #1384]
	str x10, [x0, #1392]
	str x11, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1376]
	ldr x5, [x0, #1384]
	ldr x16, [x0, #1392]
	ldr x17, [x0, #1400]
	movz x6, #49899, lsl #0
	movk x6, #27167, lsl #16
	movk x6, #17008, lsl #32
	movk x6, #55010, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #992]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	mul x1, x8, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1000]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1008]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1016]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1408]
	str x13, [x0, #1416]
	str x8, [x0, #1424]
	str x9, [x0, #1432]
	movz x7, #0, lsl #0
	ldr x4, [x0, #192]
	ldr x5, [x0, #200]
	ldr x16, [x0, #208]
	ldr x17, [x0, #216]
	movz x6, #49899, lsl #0
	movk x6, #27167, lsl #16
	movk x6, #17008, lsl #32
	movk x6, #55010, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1408]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	mul x1, x8, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x0, #1416]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x9, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1424]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1432]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #104]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #112]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #120]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #120]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #104]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #112]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x2, [x0, #96]
	subs x1, x12, x2
	ldr x2, [x0, #104]
	sbcs x3, x13, x2
	ldr x2, [x0, #112]
	sbcs x4, x8, x2
	ldr x2, [x0, #120]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #1440]
	str x13, [x0, #1448]
	str x8, [x0, #1456]
	str x9, [x0, #1464]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1440]
	ldr x2, [x0, #1448]
	orr x1, x1, x2
	ldr x2, [x0, #1456]
	orr x1, x1, x2
	ldr x2, [x0, #1464]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	ldr x3, [x0, #1472]
	ldr x1, [x0, #1216]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #20
	str x1, [x17, #0]
	ldr x1, [x0, #1224]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #12
	str x1, [x17, #0]
	ldr x1, [x0, #1232]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #4
	str x1, [x17, #0]
	ldr x1, [x0, #1240]
	and x1, x1, x3
	lsr x2, x1, #24
	strb w2, [x20, #0]
	lsr x2, x1, #16
	strb w2, [x20, #1]
	lsr x2, x1, #8
	strb w2, [x20, #2]
	strb w1, [x20, #3]
	ldr x1, [x0, #1440]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #48]
	ldr x1, [x0, #1448]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #40]
	ldr x1, [x0, #1456]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #32]
	ldr x1, [x0, #1464]
	and x1, x1, x3
	lsr x2, x1, #24
	strb w2, [x20, #28]
	lsr x2, x1, #16
	strb w2, [x20, #29]
	lsr x2, x1, #8
	strb w2, [x20, #30]
	strb w1, [x20, #31]
	ldr x19, [x0, #0]
	ldr x20, [x0, #8]
	ldr x21, [x0, #16]
	ldr x22, [x0, #24]
	ldr x23, [x0, #32]
	ldr x24, [x0, #40]
	ldr x25, [x0, #48]
	ldr x30, [x0, #56]
	movz x1, #1, lsl #0
	and x0, x3, x1
	ret
	.p2align 6
