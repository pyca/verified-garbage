// The functions of `src/internal/vg_ecdsa_p256_sign.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_sign:
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
	ldr x5, [x3, #24]
	rev x5, x5
	str x5, [x0, #1056]
	ldr x5, [x3, #16]
	rev x5, x5
	str x5, [x0, #1064]
	ldr x5, [x3, #8]
	rev x5, x5
	str x5, [x0, #1072]
	ldr x5, [x3, #0]
	rev x5, x5
	str x5, [x0, #1080]
	ldr x5, [x1, #24]
	rev x5, x5
	str x5, [x0, #1088]
	ldr x5, [x1, #16]
	rev x5, x5
	str x5, [x0, #1096]
	ldr x5, [x1, #8]
	rev x5, x5
	str x5, [x0, #1104]
	ldr x5, [x1, #0]
	rev x5, x5
	str x5, [x0, #1112]
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #1120]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1128]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1136]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1144]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #64]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #72]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #80]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #88]
	movz x1, #9553, lsl #0
	movk x1, #64611, lsl #16
	movk x1, #51906, lsl #32
	movk x1, #62393, lsl #48
	str x1, [x0, #96]
	movz x1, #40580, lsl #0
	movk x1, #42775, lsl #16
	movk x1, #64173, lsl #32
	movk x1, #48358, lsl #48
	str x1, [x0, #104]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #112]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #224]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #232]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #240]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #248]
	movz x1, #65532, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #256]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #3, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #264]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #272]
	movz x1, #4, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65532, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #280]
	movz x1, #48607, lsl #0
	movk x1, #10692, lsl #16
	movk x1, #57186, lsl #32
	movk x1, #55452, lsl #48
	str x1, [x0, #288]
	movz x1, #12432, lsl #0
	movk x1, #30852, lsl #16
	movk x1, #1485, lsl #32
	movk x1, #44272, lsl #48
	str x1, [x0, #296]
	movz x1, #11990, lsl #0
	movk x1, #63265, lsl #16
	movk x1, #8363, lsl #32
	movk x1, #58786, lsl #48
	str x1, [x0, #304]
	movz x1, #18484, lsl #0
	movk x1, #1159, lsl #16
	movk x1, #1565, lsl #32
	movk x1, #56368, lsl #48
	str x1, [x0, #312]
	movz x1, #5180, lsl #0
	movk x1, #6313, lsl #16
	movk x1, #12500, lsl #32
	movk x1, #31207, lsl #48
	str x1, [x0, #320]
	movz x1, #46593, lsl #0
	movk x1, #24557, lsl #16
	movk x1, #38396, lsl #32
	movk x1, #30138, lsl #48
	str x1, [x0, #328]
	movz x1, #9488, lsl #0
	movk x1, #30562, lsl #16
	movk x1, #29483, lsl #32
	movk x1, #31227, lsl #48
	str x1, [x0, #336]
	movz x1, #21958, lsl #0
	movk x1, #42295, lsl #16
	movk x1, #24438, lsl #32
	movk x1, #6288, lsl #48
	str x1, [x0, #344]
	movz x1, #22026, lsl #0
	movk x1, #52885, lsl #16
	movk x1, #21335, lsl #32
	movk x1, #56818, lsl #48
	str x1, [x0, #352]
	movz x1, #58460, lsl #0
	movk x1, #47641, lsl #16
	movk x1, #47332, lsl #32
	movk x1, #35658, lsl #48
	str x1, [x0, #360]
	movz x1, #62245, lsl #0
	movk x1, #56609, lsl #16
	movk x1, #34440, lsl #32
	movk x1, #53992, lsl #48
	str x1, [x0, #368]
	movz x1, #23941, lsl #0
	movk x1, #9608, lsl #16
	movk x1, #65304, lsl #32
	movk x1, #34161, lsl #48
	str x1, [x0, #376]
	movz x1, #61090, lsl #0
	movk x1, #48761, lsl #16
	movk x1, #19605, lsl #32
	movk x1, #33572, lsl #48
	str x1, [x0, #384]
	movz x1, #28582, lsl #0
	movk x1, #18877, lsl #16
	movk x1, #31132, lsl #32
	movk x1, #18073, lsl #48
	str x1, [x0, #392]
	movz x1, #60505, lsl #0
	movk x1, #11115, lsl #16
	movk x1, #45625, lsl #32
	movk x1, #10309, lsl #48
	str x1, [x0, #400]
	movz x1, #22048, lsl #0
	movk x1, #62425, lsl #16
	movk x1, #11668, lsl #32
	movk x1, #26337, lsl #48
	str x1, [x0, #408]
	movz x1, #55983, lsl #0
	movk x1, #924, lsl #16
	movk x1, #13629, lsl #32
	movk x1, #3142, lsl #48
	str x1, [x0, #416]
	movz x1, #24955, lsl #0
	movk x1, #22760, lsl #16
	movk x1, #1362, lsl #32
	movk x1, #17177, lsl #48
	str x1, [x0, #424]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #432]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
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
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #544]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #552]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #560]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
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
	movz x7, #0, lsl #0
	str x7, [x0, #1760]
	movz x19, #0, lsl #0
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
	movz x7, #0, lsl #0
	ldrb w4, [x16, #1510]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	adrp x16, {VG_P256_COMB}
	add x16, x16, {VG_P256_COMB}
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
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[0], x6
	movz x6, #65534, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v3.16b, v20.16b, v16.16b
	str q0, [x0, #704]
	str q1, [x0, #720]
	str q2, [x0, #736]
	str q3, [x0, #752]
	subs x4, x2, x5
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #768]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #776]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #784]
	movz x6, #65534, lsl #0
	movk x6, #65535, lsl #16
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
	movz x7, #0, lsl #0
	ldrb w4, [x16, #1510]
	sub x3, x7, x4
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
	ldr x1, [x0, #704]
	str x1, [x0, #512]
	ldr x1, [x0, #712]
	str x1, [x0, #520]
	ldr x1, [x0, #720]
	str x1, [x0, #528]
	ldr x1, [x0, #728]
	str x1, [x0, #536]
	ldr x1, [x0, #736]
	str x1, [x0, #544]
	ldr x1, [x0, #744]
	str x1, [x0, #552]
	ldr x1, [x0, #752]
	str x1, [x0, #560]
	ldr x1, [x0, #760]
	str x1, [x0, #568]
	ldr x1, [x0, #768]
	str x1, [x0, #576]
	ldr x1, [x0, #776]
	str x1, [x0, #584]
	ldr x1, [x0, #784]
	str x1, [x0, #592]
	ldr x1, [x0, #792]
	str x1, [x0, #600]
	movz x19, #1, lsl #0
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
	ldrb w4, [x16, #1503]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #1510]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	adrp x16, {VG_P256_COMB}
	add x16, x16, {VG_P256_COMB}
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
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[0], x6
	movz x6, #65534, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v3.16b, v20.16b, v16.16b
	str q0, [x0, #704]
	str q1, [x0, #720]
	str q2, [x0, #736]
	str q3, [x0, #752]
	subs x4, x2, x5
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #768]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #776]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #784]
	movz x6, #65534, lsl #0
	movk x6, #65535, lsl #16
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
	movz x7, #0, lsl #0
	ldrb w4, [x16, #1510]
	sub x3, x7, x4
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
21:
	add x19, x19, #1
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
	ldrb w4, [x16, #1503]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #1510]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	sub x19, x19, #1
	adrp x21, {VG_P256_COMB}
	add x21, x21, {VG_P256_COMB}
	movz x17, #4096, lsl #0
	add x5, x19, #1
	mul x17, x5, x17
	add x21, x21, x17
	movz x5, #1, lsl #0
	dup v19.2d, x2
	dup v28.2d, x5
	add v18.2d, v28.2d, v28.2d
	movz x7, #0, lsl #0
	movi v17.2d, #0
	ldr x4, [x0, #576]
	ldr x5, [x0, #584]
	sub v17.2d, v17.2d, v28.2d
	ldr x16, [x0, #592]
	ldr x17, [x0, #600]
	movi v30.2d, #0
	mul x9, x5, x4
	umulh x2, x5, x4
	mul x10, x16, x4
	movi v0.2d, #0
	umulh x3, x16, x4
	mul x11, x17, x4
	movi v1.2d, #0
	umulh x12, x17, x4
	adds x10, x10, x2
	movi v2.2d, #0
	mul x1, x16, x5
	umulh x2, x16, x5
	adcs x11, x11, x3
	movi v3.2d, #0
	mul x3, x17, x5
	umulh x6, x17, x5
	movi v4.2d, #0
	adc x12, x12, x7
	mul x13, x17, x16
	movi v5.2d, #0
	umulh x14, x17, x16
	adds x2, x2, x3
	mul x8, x4, x4
	movi v6.2d, #0
	adc x3, x6, x7
	adds x11, x11, x1
	movi v7.2d, #0
	umulh x4, x4, x4
	adcs x12, x12, x2
	mul x2, x5, x5
	add v17.2d, v17.2d, v18.2d
	adcs x13, x13, x3
	umulh x5, x5, x5
	cmeq v16.2d, v17.2d, v19.2d
	adc x14, x14, x7
	adds x9, x9, x9
	ldr q20, [x21, #0]
	mul x3, x16, x16
	adcs x10, x10, x10
	umulh x16, x16, x16
	ldr q21, [x21, #16]
	adcs x11, x11, x11
	mul x6, x17, x17
	ldr q22, [x21, #32]
	adcs x12, x12, x12
	umulh x17, x17, x17
	ldr q23, [x21, #48]
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x15, x7, x7
	bit v0.16b, v20.16b, v16.16b
	adds x9, x9, x4
	adcs x10, x10, x2
	bit v1.16b, v21.16b, v16.16b
	adcs x11, x11, x5
	adcs x12, x12, x3
	bit v2.16b, v22.16b, v16.16b
	adcs x13, x13, x16
	lsl x1, x8, #32
	adcs x14, x14, x6
	bit v3.16b, v23.16b, v16.16b
	lsr x2, x8, #32
	adc x15, x15, x17
	add v30.2d, v30.2d, v18.2d
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	cmeq v31.2d, v30.2d, v19.2d
	adcs x9, x10, x2
	lsl x1, x8, #32
	ldr q24, [x21, #64]
	adcs x10, x11, x3
	lsr x2, x8, #32
	ldr q25, [x21, #80]
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	ldr q26, [x21, #96]
	adds x8, x9, x1
	adcs x9, x10, x2
	ldr q27, [x21, #112]
	lsl x1, x8, #32
	adcs x10, x11, x3
	bit v4.16b, v24.16b, v31.16b
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	bit v5.16b, v25.16b, v31.16b
	sbc x6, x8, x2
	adds x8, x9, x1
	bit v6.16b, v26.16b, v31.16b
	adcs x9, x10, x2
	lsl x1, x8, #32
	bit v7.16b, v27.16b, v31.16b
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	add v17.2d, v17.2d, v18.2d
	subs x3, x8, x1
	sbc x6, x8, x2
	cmeq v16.2d, v17.2d, v19.2d
	adds x8, x9, x1
	adcs x9, x10, x2
	adcs x10, x11, x3
	ldr q20, [x21, #128]
	adc x11, x6, x7
	adds x8, x8, x12
	ldr q21, [x21, #144]
	adcs x9, x9, x13
	adcs x10, x10, x14
	ldr q22, [x21, #160]
	adcs x11, x11, x15
	adc x12, x7, x7
	ldr x2, [x0, #64]
	ldr q23, [x21, #176]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	bit v0.16b, v20.16b, v16.16b
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	bit v1.16b, v21.16b, v16.16b
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	bit v2.16b, v22.16b, v16.16b
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	bit v3.16b, v23.16b, v16.16b
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	add v30.2d, v30.2d, v18.2d
	str x8, [x0, #800]
	str x9, [x0, #808]
	cmeq v31.2d, v30.2d, v19.2d
	str x10, [x0, #816]
	str x11, [x0, #824]
	ldr q24, [x21, #192]
	orr x4, x8, x8
	orr x5, x9, x9
	orr x16, x10, x10
	ldr q25, [x21, #208]
	orr x17, x11, x11
	movz x6, #1, lsl #0
	ldr q26, [x21, #224]
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	ldr q27, [x21, #240]
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	bit v4.16b, v24.16b, v31.16b
	ldr x1, [x0, #704]
	mul x8, x1, x4
	bit v5.16b, v25.16b, v31.16b
	mul x9, x1, x5
	mul x10, x1, x16
	bit v6.16b, v26.16b, v31.16b
	mul x11, x1, x17
	umulh x2, x1, x4
	adds x9, x9, x2
	bit v7.16b, v27.16b, v31.16b
	umulh x2, x1, x5
	adcs x10, x10, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	cmeq v16.2d, v17.2d, v19.2d
	adcs x12, x12, x2
	lsl x2, x8, #32
	ldr q20, [x21, #256]
	adds x9, x9, x2
	lsr x2, x8, #32
	ldr q21, [x21, #272]
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	ldr q22, [x21, #288]
	umulh x2, x8, x6
	adcs x12, x12, x2
	ldr q23, [x21, #304]
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	bit v0.16b, v20.16b, v16.16b
	ldr x1, [x0, #712]
	mul x2, x1, x4
	adds x9, x9, x2
	bit v1.16b, v21.16b, v16.16b
	mul x2, x1, x5
	adcs x10, x10, x2
	bit v2.16b, v22.16b, v16.16b
	mul x2, x1, x16
	adcs x11, x11, x2
	bit v3.16b, v23.16b, v16.16b
	mul x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x17
	add v30.2d, v30.2d, v18.2d
	adcs x13, x13, x2
	umulh x2, x1, x4
	cmeq v31.2d, v30.2d, v19.2d
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	ldr q24, [x21, #320]
	umulh x2, x1, x16
	adcs x12, x12, x2
	ldr q25, [x21, #336]
	adcs x13, x13, x7
	lsl x2, x9, #32
	ldr q26, [x21, #352]
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	ldr q27, [x21, #368]
	mul x2, x9, x6
	adcs x12, x12, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x9, x6
	adcs x13, x13, x2
	bit v5.16b, v25.16b, v31.16b
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #720]
	bit v6.16b, v26.16b, v31.16b
	mul x2, x1, x4
	adds x10, x10, x2
	bit v7.16b, v27.16b, v31.16b
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	add v17.2d, v17.2d, v18.2d
	adcs x12, x12, x2
	mul x2, x1, x17
	cmeq v16.2d, v17.2d, v19.2d
	adcs x13, x13, x2
	umulh x2, x1, x17
	ldr q20, [x21, #384]
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	ldr q21, [x21, #400]
	umulh x2, x1, x5
	adcs x12, x12, x2
	ldr q22, [x21, #416]
	umulh x2, x1, x16
	adcs x13, x13, x2
	ldr q23, [x21, #432]
	adcs x8, x8, x7
	lsl x2, x10, #32
	adds x11, x11, x2
	bit v0.16b, v20.16b, v16.16b
	lsr x2, x10, #32
	adcs x12, x12, x2
	bit v1.16b, v21.16b, v16.16b
	mul x2, x10, x6
	adcs x13, x13, x2
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	bit v3.16b, v23.16b, v16.16b
	movz x10, #0, lsl #0
	ldr x1, [x0, #728]
	add v30.2d, v30.2d, v18.2d
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	cmeq v31.2d, v30.2d, v19.2d
	adcs x12, x12, x2
	mul x2, x1, x16
	ldr q24, [x21, #448]
	adcs x13, x13, x2
	mul x2, x1, x17
	ldr q25, [x21, #464]
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	ldr q26, [x21, #480]
	umulh x2, x1, x4
	adds x12, x12, x2
	ldr q27, [x21, #496]
	umulh x2, x1, x5
	adcs x13, x13, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x16
	adcs x8, x8, x2
	adcs x9, x9, x7
	bit v5.16b, v25.16b, v31.16b
	lsl x2, x11, #32
	adds x12, x12, x2
	bit v6.16b, v26.16b, v31.16b
	lsr x2, x11, #32
	adcs x13, x13, x2
	bit v7.16b, v27.16b, v31.16b
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	add v17.2d, v17.2d, v18.2d
	adcs x9, x9, x2
	adcs x10, x10, x7
	cmeq v16.2d, v17.2d, v19.2d
	movz x11, #0, lsl #0
	ldr x2, [x0, #64]
	subs x1, x12, x2
	ldr q20, [x21, #512]
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	ldr q21, [x21, #528]
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr q22, [x21, #544]
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	ldr q23, [x21, #560]
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	bit v0.16b, v20.16b, v16.16b
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	bit v1.16b, v21.16b, v16.16b
	str x12, [x0, #832]
	str x13, [x0, #840]
	str x8, [x0, #848]
	bit v2.16b, v22.16b, v16.16b
	str x9, [x0, #856]
	ldr x4, [x0, #800]
	bit v3.16b, v23.16b, v16.16b
	ldr x5, [x0, #808]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	add v30.2d, v30.2d, v18.2d
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	cmeq v31.2d, v30.2d, v19.2d
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr q24, [x21, #576]
	ldr x1, [x0, #576]
	mul x8, x1, x4
	mul x9, x1, x5
	ldr q25, [x21, #592]
	mul x10, x1, x16
	mul x11, x1, x17
	ldr q26, [x21, #608]
	umulh x2, x1, x4
	adds x9, x9, x2
	ldr q27, [x21, #624]
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	bit v4.16b, v24.16b, v31.16b
	adcs x11, x11, x2
	umulh x2, x1, x17
	bit v5.16b, v25.16b, v31.16b
	adcs x12, x12, x2
	lsl x2, x8, #32
	bit v6.16b, v26.16b, v31.16b
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	bit v7.16b, v27.16b, v31.16b
	mul x2, x8, x6
	adcs x11, x11, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	cmeq v16.2d, v17.2d, v19.2d
	movz x8, #0, lsl #0
	ldr x1, [x0, #584]
	ldr q20, [x21, #640]
	mul x2, x1, x4
	adds x9, x9, x2
	ldr q21, [x21, #656]
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	ldr q22, [x21, #672]
	adcs x11, x11, x2
	mul x2, x1, x17
	ldr q23, [x21, #688]
	adcs x12, x12, x2
	umulh x2, x1, x17
	bit v0.16b, v20.16b, v16.16b
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x1, x5
	adcs x11, x11, x2
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x1, x16
	adcs x12, x12, x2
	bit v3.16b, v23.16b, v16.16b
	adcs x13, x13, x7
	lsl x2, x9, #32
	adds x10, x10, x2
	add v30.2d, v30.2d, v18.2d
	lsr x2, x9, #32
	adcs x11, x11, x2
	cmeq v31.2d, v30.2d, v19.2d
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	ldr q24, [x21, #704]
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr q25, [x21, #720]
	movz x9, #0, lsl #0
	ldr x1, [x0, #592]
	ldr q26, [x21, #736]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	ldr q27, [x21, #752]
	adcs x11, x11, x2
	mul x2, x1, x16
	bit v4.16b, v24.16b, v31.16b
	adcs x12, x12, x2
	mul x2, x1, x17
	bit v5.16b, v25.16b, v31.16b
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	bit v6.16b, v26.16b, v31.16b
	umulh x2, x1, x4
	adds x11, x11, x2
	bit v7.16b, v27.16b, v31.16b
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	add v17.2d, v17.2d, v18.2d
	adcs x13, x13, x2
	adcs x8, x8, x7
	cmeq v16.2d, v17.2d, v19.2d
	lsl x2, x10, #32
	adds x11, x11, x2
	ldr q20, [x21, #768]
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	ldr q21, [x21, #784]
	adcs x13, x13, x2
	umulh x2, x10, x6
	ldr q22, [x21, #800]
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr q23, [x21, #816]
	movz x10, #0, lsl #0
	ldr x1, [x0, #600]
	mul x2, x1, x4
	bit v0.16b, v20.16b, v16.16b
	adds x11, x11, x2
	mul x2, x1, x5
	bit v1.16b, v21.16b, v16.16b
	adcs x12, x12, x2
	mul x2, x1, x16
	bit v2.16b, v22.16b, v16.16b
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	bit v3.16b, v23.16b, v16.16b
	umulh x2, x1, x17
	adcs x9, x9, x2
	add v30.2d, v30.2d, v18.2d
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	cmeq v31.2d, v30.2d, v19.2d
	adcs x13, x13, x2
	umulh x2, x1, x16
	ldr q24, [x21, #832]
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr q25, [x21, #848]
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	ldr q26, [x21, #864]
	adcs x13, x13, x2
	mul x2, x11, x6
	ldr q27, [x21, #880]
	adcs x8, x8, x2
	umulh x2, x11, x6
	bit v4.16b, v24.16b, v31.16b
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
	bit v5.16b, v25.16b, v31.16b
	ldr x2, [x0, #64]
	subs x1, x12, x2
	bit v6.16b, v26.16b, v31.16b
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	bit v7.16b, v27.16b, v31.16b
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	add v17.2d, v17.2d, v18.2d
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	cmeq v16.2d, v17.2d, v19.2d
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	ldr q20, [x21, #896]
	csel x9, x5, x9, hs
	orr x4, x12, x12
	ldr q21, [x21, #912]
	orr x5, x13, x13
	orr x16, x8, x8
	ldr q22, [x21, #928]
	orr x17, x9, x9
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	ldr q23, [x21, #944]
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	bit v0.16b, v20.16b, v16.16b
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	bit v1.16b, v21.16b, v16.16b
	ldr x1, [x0, #736]
	mul x8, x1, x4
	mul x9, x1, x5
	bit v2.16b, v22.16b, v16.16b
	mul x10, x1, x16
	mul x11, x1, x17
	bit v3.16b, v23.16b, v16.16b
	umulh x2, x1, x4
	adds x9, x9, x2
	add v30.2d, v30.2d, v18.2d
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	cmeq v31.2d, v30.2d, v19.2d
	adcs x11, x11, x2
	umulh x2, x1, x17
	ldr q24, [x21, #960]
	adcs x12, x12, x2
	lsl x2, x8, #32
	adds x9, x9, x2
	ldr q25, [x21, #976]
	lsr x2, x8, #32
	adcs x10, x10, x2
	ldr q26, [x21, #992]
	mul x2, x8, x6
	adcs x11, x11, x2
	ldr q27, [x21, #1008]
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	bit v4.16b, v24.16b, v31.16b
	movz x8, #0, lsl #0
	ldr x1, [x0, #744]
	bit v5.16b, v25.16b, v31.16b
	mul x2, x1, x4
	adds x9, x9, x2
	bit v6.16b, v26.16b, v31.16b
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	bit v7.16b, v27.16b, v31.16b
	adcs x11, x11, x2
	mul x2, x1, x17
	add v17.2d, v17.2d, v18.2d
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x1, x4
	adds x10, x10, x2
	ldr q20, [x21, #1024]
	umulh x2, x1, x5
	adcs x11, x11, x2
	ldr q21, [x21, #1040]
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr q22, [x21, #1056]
	lsl x2, x9, #32
	adds x10, x10, x2
	ldr q23, [x21, #1072]
	lsr x2, x9, #32
	adcs x11, x11, x2
	bit v0.16b, v20.16b, v16.16b
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	bit v1.16b, v21.16b, v16.16b
	adcs x13, x13, x2
	adcs x8, x8, x7
	bit v2.16b, v22.16b, v16.16b
	movz x9, #0, lsl #0
	ldr x1, [x0, #752]
	bit v3.16b, v23.16b, v16.16b
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	add v30.2d, v30.2d, v18.2d
	adcs x11, x11, x2
	mul x2, x1, x16
	cmeq v31.2d, v30.2d, v19.2d
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr q24, [x21, #1088]
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr q25, [x21, #1104]
	umulh x2, x1, x4
	adds x11, x11, x2
	ldr q26, [x21, #1120]
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	ldr q27, [x21, #1136]
	adcs x13, x13, x2
	adcs x8, x8, x7
	bit v4.16b, v24.16b, v31.16b
	lsl x2, x10, #32
	adds x11, x11, x2
	bit v5.16b, v25.16b, v31.16b
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	bit v6.16b, v26.16b, v31.16b
	adcs x13, x13, x2
	umulh x2, x10, x6
	bit v7.16b, v27.16b, v31.16b
	adcs x8, x8, x2
	adcs x9, x9, x7
	add v17.2d, v17.2d, v18.2d
	movz x10, #0, lsl #0
	ldr x1, [x0, #760]
	mul x2, x1, x4
	cmeq v16.2d, v17.2d, v19.2d
	adds x11, x11, x2
	mul x2, x1, x5
	ldr q20, [x21, #1152]
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	ldr q21, [x21, #1168]
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr q22, [x21, #1184]
	umulh x2, x1, x17
	adcs x9, x9, x2
	ldr q23, [x21, #1200]
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	bit v0.16b, v20.16b, v16.16b
	adcs x13, x13, x2
	umulh x2, x1, x16
	bit v1.16b, v21.16b, v16.16b
	adcs x8, x8, x2
	adcs x9, x9, x7
	bit v2.16b, v22.16b, v16.16b
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	bit v3.16b, v23.16b, v16.16b
	adcs x13, x13, x2
	mul x2, x11, x6
	add v30.2d, v30.2d, v18.2d
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	cmeq v31.2d, v30.2d, v19.2d
	adcs x10, x10, x7
	movz x11, #0, lsl #0
	ldr q24, [x21, #1216]
	ldr x2, [x0, #64]
	subs x1, x12, x2
	ldr q25, [x21, #1232]
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	ldr q26, [x21, #1248]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	ldr q27, [x21, #1264]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	bit v4.16b, v24.16b, v31.16b
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	bit v5.16b, v25.16b, v31.16b
	csel x9, x5, x9, hs
	str x8, [x0, #880]
	bit v6.16b, v26.16b, v31.16b
	str x9, [x0, #888]
	ldr x8, [x0, #832]
	bit v7.16b, v27.16b, v31.16b
	ldr x9, [x0, #840]
	ldr x10, [x0, #848]
	ldr x11, [x0, #856]
	add v17.2d, v17.2d, v18.2d
	ldr x2, [x0, #512]
	subs x8, x8, x2
	cmeq v16.2d, v17.2d, v19.2d
	ldr x2, [x0, #520]
	sbcs x9, x9, x2
	ldr x2, [x0, #528]
	ldr q20, [x21, #1280]
	sbcs x10, x10, x2
	ldr x2, [x0, #536]
	ldr q21, [x21, #1296]
	sbcs x11, x11, x2
	sbc x17, x7, x7
	ldr q22, [x21, #1312]
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr q23, [x21, #1328]
	ldr x2, [x0, #72]
	and x2, x2, x17
	bit v0.16b, v20.16b, v16.16b
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	bit v1.16b, v21.16b, v16.16b
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	bit v2.16b, v22.16b, v16.16b
	and x2, x2, x17
	adcs x11, x11, x2
	bit v3.16b, v23.16b, v16.16b
	str x8, [x0, #832]
	str x9, [x0, #840]
	add v30.2d, v30.2d, v18.2d
	str x10, [x0, #848]
	str x11, [x0, #856]
	orr x8, x12, x12
	cmeq v31.2d, v30.2d, v19.2d
	orr x9, x13, x13
	ldr x10, [x0, #880]
	ldr q24, [x21, #1344]
	ldr x11, [x0, #888]
	ldr x2, [x0, #544]
	subs x8, x8, x2
	ldr q25, [x21, #1360]
	ldr x2, [x0, #552]
	sbcs x9, x9, x2
	ldr q26, [x21, #1376]
	ldr x2, [x0, #560]
	sbcs x10, x10, x2
	ldr q27, [x21, #1392]
	ldr x2, [x0, #568]
	sbcs x11, x11, x2
	sbc x17, x7, x7
	bit v4.16b, v24.16b, v31.16b
	ldr x2, [x0, #64]
	and x2, x2, x17
	bit v5.16b, v25.16b, v31.16b
	adds x8, x8, x2
	ldr x2, [x0, #72]
	bit v6.16b, v26.16b, v31.16b
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	bit v7.16b, v27.16b, v31.16b
	and x2, x2, x17
	adcs x10, x10, x2
	add v17.2d, v17.2d, v18.2d
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	cmeq v16.2d, v17.2d, v19.2d
	str x8, [x0, #864]
	str x9, [x0, #872]
	ldr q20, [x21, #1408]
	str x10, [x0, #880]
	str x11, [x0, #888]
	ldr q21, [x21, #1424]
	ldr x4, [x0, #832]
	ldr x5, [x0, #840]
	ldr x16, [x0, #848]
	ldr q22, [x21, #1440]
	ldr x17, [x0, #856]
	mul x9, x5, x4
	ldr q23, [x21, #1456]
	umulh x2, x5, x4
	mul x10, x16, x4
	bit v0.16b, v20.16b, v16.16b
	umulh x3, x16, x4
	mul x11, x17, x4
	umulh x12, x17, x4
	bit v1.16b, v21.16b, v16.16b
	adds x10, x10, x2
	mul x1, x16, x5
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x16, x5
	adcs x11, x11, x3
	bit v3.16b, v23.16b, v16.16b
	mul x3, x17, x5
	umulh x6, x17, x5
	adc x12, x12, x7
	add v30.2d, v30.2d, v18.2d
	mul x13, x17, x16
	umulh x14, x17, x16
	cmeq v31.2d, v30.2d, v19.2d
	adds x2, x2, x3
	mul x8, x4, x4
	adc x3, x6, x7
	ldr q24, [x21, #1472]
	adds x11, x11, x1
	umulh x4, x4, x4
	ldr q25, [x21, #1488]
	adcs x12, x12, x2
	mul x2, x5, x5
	ldr q26, [x21, #1504]
	adcs x13, x13, x3
	umulh x5, x5, x5
	adc x14, x14, x7
	ldr q27, [x21, #1520]
	adds x9, x9, x9
	mul x3, x16, x16
	bit v4.16b, v24.16b, v31.16b
	adcs x10, x10, x10
	umulh x16, x16, x16
	bit v5.16b, v25.16b, v31.16b
	adcs x11, x11, x11
	mul x6, x17, x17
	adcs x12, x12, x12
	bit v6.16b, v26.16b, v31.16b
	umulh x17, x17, x17
	adcs x13, x13, x13
	bit v7.16b, v27.16b, v31.16b
	adcs x14, x14, x14
	adc x15, x7, x7
	add v17.2d, v17.2d, v18.2d
	adds x9, x9, x4
	adcs x10, x10, x2
	adcs x11, x11, x5
	cmeq v16.2d, v17.2d, v19.2d
	adcs x12, x12, x3
	adcs x13, x13, x16
	ldr q20, [x21, #1536]
	lsl x1, x8, #32
	adcs x14, x14, x6
	lsr x2, x8, #32
	ldr q21, [x21, #1552]
	adc x15, x15, x17
	subs x3, x8, x1
	ldr q22, [x21, #1568]
	sbc x6, x8, x2
	adds x8, x9, x1
	ldr q23, [x21, #1584]
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	bit v0.16b, v20.16b, v16.16b
	lsr x2, x8, #32
	adc x11, x6, x7
	bit v1.16b, v21.16b, v16.16b
	subs x3, x8, x1
	sbc x6, x8, x2
	bit v2.16b, v22.16b, v16.16b
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	bit v3.16b, v23.16b, v16.16b
	adcs x10, x11, x3
	lsr x2, x8, #32
	add v30.2d, v30.2d, v18.2d
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	cmeq v31.2d, v30.2d, v19.2d
	adds x8, x9, x1
	adcs x9, x10, x2
	ldr q24, [x21, #1600]
	lsl x1, x8, #32
	adcs x10, x11, x3
	ldr q25, [x21, #1616]
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	ldr q26, [x21, #1632]
	sbc x6, x8, x2
	adds x8, x9, x1
	ldr q27, [x21, #1648]
	adcs x9, x10, x2
	adcs x10, x11, x3
	bit v4.16b, v24.16b, v31.16b
	adc x11, x6, x7
	adds x8, x8, x12
	adcs x9, x9, x13
	bit v5.16b, v25.16b, v31.16b
	adcs x10, x10, x14
	adcs x11, x11, x15
	bit v6.16b, v26.16b, v31.16b
	adc x12, x7, x7
	ldr x2, [x0, #64]
	bit v7.16b, v27.16b, v31.16b
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	add v17.2d, v17.2d, v18.2d
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	cmeq v16.2d, v17.2d, v19.2d
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	ldr q20, [x21, #1664]
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	ldr q21, [x21, #1680]
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	ldr q22, [x21, #1696]
	str x8, [x0, #896]
	str x9, [x0, #904]
	orr x4, x8, x8
	ldr q23, [x21, #1712]
	orr x5, x9, x9
	orr x16, x10, x10
	bit v0.16b, v20.16b, v16.16b
	orr x17, x11, x11
	movz x6, #1, lsl #0
	bit v1.16b, v21.16b, v16.16b
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	bit v2.16b, v22.16b, v16.16b
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	bit v3.16b, v23.16b, v16.16b
	ldr x1, [x0, #832]
	mul x8, x1, x4
	add v30.2d, v30.2d, v18.2d
	mul x9, x1, x5
	mul x10, x1, x16
	mul x11, x1, x17
	cmeq v31.2d, v30.2d, v19.2d
	umulh x2, x1, x4
	adds x9, x9, x2
	ldr q24, [x21, #1728]
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	ldr q25, [x21, #1744]
	adcs x11, x11, x2
	umulh x2, x1, x17
	ldr q26, [x21, #1760]
	adcs x12, x12, x2
	lsl x2, x8, #32
	ldr q27, [x21, #1776]
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	bit v4.16b, v24.16b, v31.16b
	mul x2, x8, x6
	adcs x11, x11, x2
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x8, x6
	adcs x12, x12, x2
	bit v6.16b, v26.16b, v31.16b
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #840]
	bit v7.16b, v27.16b, v31.16b
	mul x2, x1, x4
	adds x9, x9, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x1, x5
	adcs x10, x10, x2
	cmeq v16.2d, v17.2d, v19.2d
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	ldr q20, [x21, #1792]
	adcs x12, x12, x2
	umulh x2, x1, x17
	ldr q21, [x21, #1808]
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	ldr q22, [x21, #1824]
	umulh x2, x1, x5
	adcs x11, x11, x2
	ldr q23, [x21, #1840]
	umulh x2, x1, x16
	adcs x12, x12, x2
	bit v0.16b, v20.16b, v16.16b
	adcs x13, x13, x7
	lsl x2, x9, #32
	adds x10, x10, x2
	bit v1.16b, v21.16b, v16.16b
	lsr x2, x9, #32
	adcs x11, x11, x2
	bit v2.16b, v22.16b, v16.16b
	mul x2, x9, x6
	adcs x12, x12, x2
	bit v3.16b, v23.16b, v16.16b
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	add v30.2d, v30.2d, v18.2d
	movz x9, #0, lsl #0
	ldr x1, [x0, #848]
	cmeq v31.2d, v30.2d, v19.2d
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	ldr q24, [x21, #1856]
	adcs x11, x11, x2
	mul x2, x1, x16
	ldr q25, [x21, #1872]
	adcs x12, x12, x2
	mul x2, x1, x17
	ldr q26, [x21, #1888]
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr q27, [x21, #1904]
	umulh x2, x1, x4
	adds x11, x11, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x5
	adcs x12, x12, x2
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x1, x16
	adcs x13, x13, x2
	adcs x8, x8, x7
	bit v6.16b, v26.16b, v31.16b
	lsl x2, x10, #32
	adds x11, x11, x2
	bit v7.16b, v27.16b, v31.16b
	lsr x2, x10, #32
	adcs x12, x12, x2
	add v17.2d, v17.2d, v18.2d
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	cmeq v16.2d, v17.2d, v19.2d
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr q20, [x21, #1920]
	movz x10, #0, lsl #0
	ldr x1, [x0, #856]
	mul x2, x1, x4
	ldr q21, [x21, #1936]
	adds x11, x11, x2
	mul x2, x1, x5
	ldr q22, [x21, #1952]
	adcs x12, x12, x2
	mul x2, x1, x16
	ldr q23, [x21, #1968]
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	bit v0.16b, v20.16b, v16.16b
	umulh x2, x1, x17
	adcs x9, x9, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x1, x4
	adds x12, x12, x2
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	bit v3.16b, v23.16b, v16.16b
	adcs x8, x8, x2
	adcs x9, x9, x7
	add v30.2d, v30.2d, v18.2d
	lsl x2, x11, #32
	adds x12, x12, x2
	cmeq v31.2d, v30.2d, v19.2d
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	ldr q24, [x21, #1984]
	adcs x8, x8, x2
	umulh x2, x11, x6
	ldr q25, [x21, #2000]
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
	ldr q26, [x21, #2016]
	ldr x2, [x0, #64]
	subs x1, x12, x2
	ldr q27, [x21, #2032]
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	bit v4.16b, v24.16b, v31.16b
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	bit v5.16b, v25.16b, v31.16b
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	bit v6.16b, v26.16b, v31.16b
	csel x12, x1, x12, hs
	csel x13, x3, x13, hs
	bit v7.16b, v27.16b, v31.16b
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	str x12, [x0, #928]
	add v17.2d, v17.2d, v18.2d
	str x13, [x0, #936]
	str x8, [x0, #944]
	cmeq v16.2d, v17.2d, v19.2d
	str x9, [x0, #952]
	ldr x4, [x0, #896]
	ldr x5, [x0, #904]
	ldr q20, [x21, #2048]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	ldr q21, [x21, #2064]
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	ldr q22, [x21, #2080]
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #512]
	ldr q23, [x21, #2096]
	mul x8, x1, x4
	mul x9, x1, x5
	bit v0.16b, v20.16b, v16.16b
	mul x10, x1, x16
	mul x11, x1, x17
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	bit v2.16b, v22.16b, v16.16b
	adcs x10, x10, x2
	umulh x2, x1, x16
	bit v3.16b, v23.16b, v16.16b
	adcs x11, x11, x2
	umulh x2, x1, x17
	add v30.2d, v30.2d, v18.2d
	adcs x12, x12, x2
	lsl x2, x8, #32
	adds x9, x9, x2
	cmeq v31.2d, v30.2d, v19.2d
	lsr x2, x8, #32
	adcs x10, x10, x2
	ldr q24, [x21, #2112]
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	ldr q25, [x21, #2128]
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr q26, [x21, #2144]
	movz x8, #0, lsl #0
	ldr x1, [x0, #520]
	ldr q27, [x21, #2160]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	bit v4.16b, v24.16b, v31.16b
	adcs x10, x10, x2
	mul x2, x1, x16
	bit v5.16b, v25.16b, v31.16b
	adcs x11, x11, x2
	mul x2, x1, x17
	bit v6.16b, v26.16b, v31.16b
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	bit v7.16b, v27.16b, v31.16b
	umulh x2, x1, x4
	adds x10, x10, x2
	add v17.2d, v17.2d, v18.2d
	umulh x2, x1, x5
	adcs x11, x11, x2
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x1, x16
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr q20, [x21, #2176]
	lsl x2, x9, #32
	adds x10, x10, x2
	ldr q21, [x21, #2192]
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	ldr q22, [x21, #2208]
	adcs x12, x12, x2
	umulh x2, x9, x6
	ldr q23, [x21, #2224]
	adcs x13, x13, x2
	adcs x8, x8, x7
	bit v0.16b, v20.16b, v16.16b
	movz x9, #0, lsl #0
	ldr x1, [x0, #528]
	mul x2, x1, x4
	bit v1.16b, v21.16b, v16.16b
	adds x10, x10, x2
	mul x2, x1, x5
	bit v2.16b, v22.16b, v16.16b
	adcs x11, x11, x2
	mul x2, x1, x16
	bit v3.16b, v23.16b, v16.16b
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	add v30.2d, v30.2d, v18.2d
	umulh x2, x1, x17
	adcs x8, x8, x2
	cmeq v31.2d, v30.2d, v19.2d
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	ldr q24, [x21, #2240]
	adcs x12, x12, x2
	umulh x2, x1, x16
	ldr q25, [x21, #2256]
	adcs x13, x13, x2
	adcs x8, x8, x7
	ldr q26, [x21, #2272]
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	ldr q27, [x21, #2288]
	adcs x12, x12, x2
	mul x2, x10, x6
	bit v4.16b, v24.16b, v31.16b
	adcs x13, x13, x2
	umulh x2, x10, x6
	bit v5.16b, v25.16b, v31.16b
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	bit v6.16b, v26.16b, v31.16b
	ldr x1, [x0, #536]
	mul x2, x1, x4
	bit v7.16b, v27.16b, v31.16b
	adds x11, x11, x2
	mul x2, x1, x5
	add v17.2d, v17.2d, v18.2d
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	cmeq v16.2d, v17.2d, v19.2d
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr q20, [x21, #2304]
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	ldr q21, [x21, #2320]
	adds x12, x12, x2
	umulh x2, x1, x5
	ldr q22, [x21, #2336]
	adcs x13, x13, x2
	umulh x2, x1, x16
	ldr q23, [x21, #2352]
	adcs x8, x8, x2
	adcs x9, x9, x7
	lsl x2, x11, #32
	bit v0.16b, v20.16b, v16.16b
	adds x12, x12, x2
	lsr x2, x11, #32
	bit v1.16b, v21.16b, v16.16b
	adcs x13, x13, x2
	mul x2, x11, x6
	bit v2.16b, v22.16b, v16.16b
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	bit v3.16b, v23.16b, v16.16b
	adcs x10, x10, x7
	movz x11, #0, lsl #0
	add v30.2d, v30.2d, v18.2d
	ldr x2, [x0, #64]
	subs x1, x12, x2
	cmeq v31.2d, v30.2d, v19.2d
	ldr x2, [x0, #72]
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	ldr q24, [x21, #2368]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	ldr q25, [x21, #2384]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	ldr q26, [x21, #2400]
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	ldr q27, [x21, #2416]
	csel x9, x5, x9, hs
	str x12, [x0, #896]
	bit v4.16b, v24.16b, v31.16b
	str x13, [x0, #904]
	str x8, [x0, #912]
	str x9, [x0, #920]
	bit v5.16b, v25.16b, v31.16b
	ldr x4, [x0, #864]
	ldr x5, [x0, #872]
	bit v6.16b, v26.16b, v31.16b
	ldr x16, [x0, #880]
	ldr x17, [x0, #888]
	bit v7.16b, v27.16b, v31.16b
	mul x9, x5, x4
	umulh x2, x5, x4
	mul x10, x16, x4
	add v17.2d, v17.2d, v18.2d
	umulh x3, x16, x4
	mul x11, x17, x4
	cmeq v16.2d, v17.2d, v19.2d
	umulh x12, x17, x4
	adds x10, x10, x2
	mul x1, x16, x5
	ldr q20, [x21, #2432]
	umulh x2, x16, x5
	adcs x11, x11, x3
	ldr q21, [x21, #2448]
	mul x3, x17, x5
	umulh x6, x17, x5
	ldr q22, [x21, #2464]
	adc x12, x12, x7
	mul x13, x17, x16
	umulh x14, x17, x16
	ldr q23, [x21, #2480]
	adds x2, x2, x3
	mul x8, x4, x4
	bit v0.16b, v20.16b, v16.16b
	adc x3, x6, x7
	adds x11, x11, x1
	bit v1.16b, v21.16b, v16.16b
	umulh x4, x4, x4
	adcs x12, x12, x2
	mul x2, x5, x5
	bit v2.16b, v22.16b, v16.16b
	adcs x13, x13, x3
	umulh x5, x5, x5
	bit v3.16b, v23.16b, v16.16b
	adc x14, x14, x7
	adds x9, x9, x9
	add v30.2d, v30.2d, v18.2d
	mul x3, x16, x16
	adcs x10, x10, x10
	umulh x16, x16, x16
	cmeq v31.2d, v30.2d, v19.2d
	adcs x11, x11, x11
	mul x6, x17, x17
	ldr q24, [x21, #2496]
	adcs x12, x12, x12
	umulh x17, x17, x17
	adcs x13, x13, x13
	ldr q25, [x21, #2512]
	adcs x14, x14, x14
	adc x15, x7, x7
	ldr q26, [x21, #2528]
	adds x9, x9, x4
	adcs x10, x10, x2
	ldr q27, [x21, #2544]
	adcs x11, x11, x5
	adcs x12, x12, x3
	adcs x13, x13, x16
	bit v4.16b, v24.16b, v31.16b
	lsl x1, x8, #32
	adcs x14, x14, x6
	bit v5.16b, v25.16b, v31.16b
	lsr x2, x8, #32
	adc x15, x15, x17
	bit v6.16b, v26.16b, v31.16b
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	bit v7.16b, v27.16b, v31.16b
	adcs x9, x10, x2
	lsl x1, x8, #32
	add v17.2d, v17.2d, v18.2d
	adcs x10, x11, x3
	lsr x2, x8, #32
	cmeq v16.2d, v17.2d, v19.2d
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	ldr q20, [x21, #2560]
	adds x8, x9, x1
	adcs x9, x10, x2
	ldr q21, [x21, #2576]
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	ldr q22, [x21, #2592]
	adc x11, x6, x7
	subs x3, x8, x1
	ldr q23, [x21, #2608]
	sbc x6, x8, x2
	adds x8, x9, x1
	bit v0.16b, v20.16b, v16.16b
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	bit v1.16b, v21.16b, v16.16b
	lsr x2, x8, #32
	adc x11, x6, x7
	bit v2.16b, v22.16b, v16.16b
	subs x3, x8, x1
	sbc x6, x8, x2
	bit v3.16b, v23.16b, v16.16b
	adds x8, x9, x1
	adcs x9, x10, x2
	adcs x10, x11, x3
	add v30.2d, v30.2d, v18.2d
	adc x11, x6, x7
	adds x8, x8, x12
	cmeq v31.2d, v30.2d, v19.2d
	adcs x9, x9, x13
	adcs x10, x10, x14
	ldr q24, [x21, #2624]
	adcs x11, x11, x15
	adc x12, x7, x7
	ldr x2, [x0, #64]
	ldr q25, [x21, #2640]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	ldr q26, [x21, #2656]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr q27, [x21, #2672]
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	bit v4.16b, v24.16b, v31.16b
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	bit v5.16b, v25.16b, v31.16b
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	bit v6.16b, v26.16b, v31.16b
	ldr x2, [x0, #928]
	subs x8, x8, x2
	bit v7.16b, v27.16b, v31.16b
	ldr x2, [x0, #936]
	sbcs x9, x9, x2
	add v17.2d, v17.2d, v18.2d
	ldr x2, [x0, #944]
	sbcs x10, x10, x2
	ldr x2, [x0, #952]
	cmeq v16.2d, v17.2d, v19.2d
	sbcs x11, x11, x2
	sbc x17, x7, x7
	ldr q20, [x21, #2688]
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr q21, [x21, #2704]
	ldr x2, [x0, #72]
	and x2, x2, x17
	ldr q22, [x21, #2720]
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	ldr q23, [x21, #2736]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	bit v0.16b, v20.16b, v16.16b
	and x2, x2, x17
	adcs x11, x11, x2
	bit v1.16b, v21.16b, v16.16b
	str x8, [x0, #608]
	str x9, [x0, #616]
	bit v2.16b, v22.16b, v16.16b
	str x10, [x0, #624]
	str x11, [x0, #632]
	ldr x8, [x0, #896]
	bit v3.16b, v23.16b, v16.16b
	ldr x9, [x0, #904]
	ldr x10, [x0, #912]
	add v30.2d, v30.2d, v18.2d
	ldr x11, [x0, #920]
	adds x8, x8, x8
	cmeq v31.2d, v30.2d, v19.2d
	adcs x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	ldr q24, [x21, #2752]
	adc x12, x7, x7
	ldr x2, [x0, #64]
	ldr q25, [x21, #2768]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr q26, [x21, #2784]
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr q27, [x21, #2800]
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	bit v4.16b, v24.16b, v31.16b
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	bit v5.16b, v25.16b, v31.16b
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	bit v6.16b, v26.16b, v31.16b
	str x8, [x0, #960]
	str x9, [x0, #968]
	bit v7.16b, v27.16b, v31.16b
	str x10, [x0, #976]
	str x11, [x0, #984]
	ldr x8, [x0, #608]
	add v17.2d, v17.2d, v18.2d
	ldr x9, [x0, #616]
	ldr x10, [x0, #624]
	cmeq v16.2d, v17.2d, v19.2d
	ldr x11, [x0, #632]
	ldr x2, [x0, #960]
	ldr q20, [x21, #2816]
	subs x8, x8, x2
	ldr x2, [x0, #968]
	sbcs x9, x9, x2
	ldr q21, [x21, #2832]
	ldr x2, [x0, #976]
	sbcs x10, x10, x2
	ldr q22, [x21, #2848]
	ldr x2, [x0, #984]
	sbcs x11, x11, x2
	sbc x17, x7, x7
	ldr q23, [x21, #2864]
	ldr x2, [x0, #64]
	and x2, x2, x17
	bit v0.16b, v20.16b, v16.16b
	adds x8, x8, x2
	ldr x2, [x0, #72]
	bit v1.16b, v21.16b, v16.16b
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	bit v2.16b, v22.16b, v16.16b
	and x2, x2, x17
	adcs x10, x10, x2
	bit v3.16b, v23.16b, v16.16b
	ldr x2, [x0, #88]
	and x2, x2, x17
	add v30.2d, v30.2d, v18.2d
	adcs x11, x11, x2
	str x8, [x0, #608]
	str x9, [x0, #616]
	cmeq v31.2d, v30.2d, v19.2d
	str x10, [x0, #624]
	str x11, [x0, #632]
	ldr q24, [x21, #2880]
	ldr x8, [x0, #896]
	ldr x9, [x0, #904]
	ldr x10, [x0, #912]
	ldr q25, [x21, #2896]
	ldr x11, [x0, #920]
	ldr x2, [x0, #608]
	ldr q26, [x21, #2912]
	subs x8, x8, x2
	ldr x2, [x0, #616]
	ldr q27, [x21, #2928]
	sbcs x9, x9, x2
	ldr x2, [x0, #624]
	sbcs x10, x10, x2
	bit v4.16b, v24.16b, v31.16b
	ldr x2, [x0, #632]
	sbcs x11, x11, x2
	bit v5.16b, v25.16b, v31.16b
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	bit v6.16b, v26.16b, v31.16b
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	bit v7.16b, v27.16b, v31.16b
	and x2, x2, x17
	adcs x9, x9, x2
	add v17.2d, v17.2d, v18.2d
	ldr x2, [x0, #80]
	and x2, x2, x17
	cmeq v16.2d, v17.2d, v19.2d
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	ldr q20, [x21, #2944]
	adcs x11, x11, x2
	orr x4, x8, x8
	ldr q21, [x21, #2960]
	orr x5, x9, x9
	orr x16, x10, x10
	orr x17, x11, x11
	ldr q22, [x21, #2976]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	ldr q23, [x21, #2992]
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	bit v0.16b, v20.16b, v16.16b
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #864]
	bit v1.16b, v21.16b, v16.16b
	mul x8, x1, x4
	mul x9, x1, x5
	bit v2.16b, v22.16b, v16.16b
	mul x10, x1, x16
	mul x11, x1, x17
	bit v3.16b, v23.16b, v16.16b
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	add v30.2d, v30.2d, v18.2d
	adcs x10, x10, x2
	umulh x2, x1, x16
	cmeq v31.2d, v30.2d, v19.2d
	adcs x11, x11, x2
	umulh x2, x1, x17
	ldr q24, [x21, #3008]
	adcs x12, x12, x2
	lsl x2, x8, #32
	adds x9, x9, x2
	ldr q25, [x21, #3024]
	lsr x2, x8, #32
	adcs x10, x10, x2
	ldr q26, [x21, #3040]
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	ldr q27, [x21, #3056]
	adcs x12, x12, x2
	adcs x13, x13, x7
	bit v4.16b, v24.16b, v31.16b
	movz x8, #0, lsl #0
	ldr x1, [x0, #872]
	bit v5.16b, v25.16b, v31.16b
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	bit v6.16b, v26.16b, v31.16b
	adcs x10, x10, x2
	mul x2, x1, x16
	bit v7.16b, v27.16b, v31.16b
	adcs x11, x11, x2
	mul x2, x1, x17
	add v17.2d, v17.2d, v18.2d
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	cmeq v16.2d, v17.2d, v19.2d
	umulh x2, x1, x4
	adds x10, x10, x2
	ldr q20, [x21, #3072]
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	ldr q21, [x21, #3088]
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr q22, [x21, #3104]
	lsl x2, x9, #32
	adds x10, x10, x2
	ldr q23, [x21, #3120]
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	bit v0.16b, v20.16b, v16.16b
	adcs x12, x12, x2
	umulh x2, x9, x6
	bit v1.16b, v21.16b, v16.16b
	adcs x13, x13, x2
	adcs x8, x8, x7
	bit v2.16b, v22.16b, v16.16b
	movz x9, #0, lsl #0
	ldr x1, [x0, #880]
	mul x2, x1, x4
	bit v3.16b, v23.16b, v16.16b
	adds x10, x10, x2
	mul x2, x1, x5
	add v30.2d, v30.2d, v18.2d
	adcs x11, x11, x2
	mul x2, x1, x16
	cmeq v31.2d, v30.2d, v19.2d
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr q24, [x21, #3136]
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr q25, [x21, #3152]
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	ldr q26, [x21, #3168]
	adcs x12, x12, x2
	umulh x2, x1, x16
	ldr q27, [x21, #3184]
	adcs x13, x13, x2
	adcs x8, x8, x7
	bit v4.16b, v24.16b, v31.16b
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	bit v5.16b, v25.16b, v31.16b
	adcs x12, x12, x2
	mul x2, x10, x6
	bit v6.16b, v26.16b, v31.16b
	adcs x13, x13, x2
	umulh x2, x10, x6
	bit v7.16b, v27.16b, v31.16b
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	add v17.2d, v17.2d, v18.2d
	ldr x1, [x0, #888]
	mul x2, x1, x4
	cmeq v16.2d, v17.2d, v19.2d
	adds x11, x11, x2
	mul x2, x1, x5
	ldr q20, [x21, #3200]
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	ldr q21, [x21, #3216]
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr q22, [x21, #3232]
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x4
	ldr q23, [x21, #3248]
	adds x12, x12, x2
	umulh x2, x1, x5
	bit v0.16b, v20.16b, v16.16b
	adcs x13, x13, x2
	umulh x2, x1, x16
	bit v1.16b, v21.16b, v16.16b
	adcs x8, x8, x2
	adcs x9, x9, x7
	lsl x2, x11, #32
	bit v2.16b, v22.16b, v16.16b
	adds x12, x12, x2
	lsr x2, x11, #32
	bit v3.16b, v23.16b, v16.16b
	adcs x13, x13, x2
	mul x2, x11, x6
	add v30.2d, v30.2d, v18.2d
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	cmeq v31.2d, v30.2d, v19.2d
	adcs x10, x10, x7
	movz x11, #0, lsl #0
	ldr q24, [x21, #3264]
	ldr x2, [x0, #64]
	subs x1, x12, x2
	ldr x2, [x0, #72]
	ldr q25, [x21, #3280]
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	ldr q26, [x21, #3296]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	ldr q27, [x21, #3312]
	sbcs x5, x9, x2
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	bit v4.16b, v24.16b, v31.16b
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	bit v5.16b, v25.16b, v31.16b
	csel x9, x5, x9, hs
	str x12, [x0, #896]
	bit v6.16b, v26.16b, v31.16b
	str x13, [x0, #904]
	str x8, [x0, #912]
	str x9, [x0, #920]
	bit v7.16b, v27.16b, v31.16b
	ldr x4, [x0, #928]
	ldr x5, [x0, #936]
	add v17.2d, v17.2d, v18.2d
	ldr x16, [x0, #944]
	ldr x17, [x0, #952]
	cmeq v16.2d, v17.2d, v19.2d
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	ldr q20, [x21, #3328]
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	ldr q21, [x21, #3344]
	movz x13, #0, lsl #0
	ldr x1, [x0, #544]
	mul x8, x1, x4
	ldr q22, [x21, #3360]
	mul x9, x1, x5
	mul x10, x1, x16
	ldr q23, [x21, #3376]
	mul x11, x1, x17
	umulh x2, x1, x4
	bit v0.16b, v20.16b, v16.16b
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x1, x16
	adcs x11, x11, x2
	bit v2.16b, v22.16b, v16.16b
	umulh x2, x1, x17
	adcs x12, x12, x2
	bit v3.16b, v23.16b, v16.16b
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	add v30.2d, v30.2d, v18.2d
	adcs x10, x10, x2
	mul x2, x8, x6
	cmeq v31.2d, v30.2d, v19.2d
	adcs x11, x11, x2
	umulh x2, x8, x6
	ldr q24, [x21, #3392]
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr q25, [x21, #3408]
	ldr x1, [x0, #552]
	mul x2, x1, x4
	ldr q26, [x21, #3424]
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	ldr q27, [x21, #3440]
	mul x2, x1, x16
	adcs x11, x11, x2
	bit v4.16b, v24.16b, v31.16b
	mul x2, x1, x17
	adcs x12, x12, x2
	bit v5.16b, v25.16b, v31.16b
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	bit v6.16b, v26.16b, v31.16b
	adds x10, x10, x2
	umulh x2, x1, x5
	bit v7.16b, v27.16b, v31.16b
	adcs x11, x11, x2
	umulh x2, x1, x16
	add v17.2d, v17.2d, v18.2d
	adcs x12, x12, x2
	adcs x13, x13, x7
	lsl x2, x9, #32
	cmeq v16.2d, v17.2d, v19.2d
	adds x10, x10, x2
	lsr x2, x9, #32
	ldr q20, [x21, #3456]
	adcs x11, x11, x2
	mul x2, x9, x6
	ldr q21, [x21, #3472]
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	ldr q22, [x21, #3488]
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr q23, [x21, #3504]
	ldr x1, [x0, #560]
	mul x2, x1, x4
	adds x10, x10, x2
	bit v0.16b, v20.16b, v16.16b
	mul x2, x1, x5
	adcs x11, x11, x2
	bit v1.16b, v21.16b, v16.16b
	mul x2, x1, x16
	adcs x12, x12, x2
	bit v2.16b, v22.16b, v16.16b
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	bit v3.16b, v23.16b, v16.16b
	adcs x8, x8, x2
	umulh x2, x1, x4
	add v30.2d, v30.2d, v18.2d
	adds x11, x11, x2
	umulh x2, x1, x5
	cmeq v31.2d, v30.2d, v19.2d
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	ldr q24, [x21, #3520]
	adcs x8, x8, x7
	lsl x2, x10, #32
	ldr q25, [x21, #3536]
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	ldr q26, [x21, #3552]
	mul x2, x10, x6
	adcs x13, x13, x2
	ldr q27, [x21, #3568]
	umulh x2, x10, x6
	adcs x8, x8, x2
	bit v4.16b, v24.16b, v31.16b
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #568]
	bit v5.16b, v25.16b, v31.16b
	mul x2, x1, x4
	adds x11, x11, x2
	bit v6.16b, v26.16b, v31.16b
	mul x2, x1, x5
	adcs x12, x12, x2
	bit v7.16b, v27.16b, v31.16b
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	add v17.2d, v17.2d, v18.2d
	adcs x8, x8, x2
	umulh x2, x1, x17
	cmeq v16.2d, v17.2d, v19.2d
	adcs x9, x9, x2
	umulh x2, x1, x4
	ldr q20, [x21, #3584]
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	ldr q21, [x21, #3600]
	umulh x2, x1, x16
	adcs x8, x8, x2
	ldr q22, [x21, #3616]
	adcs x9, x9, x7
	lsl x2, x11, #32
	adds x12, x12, x2
	ldr q23, [x21, #3632]
	lsr x2, x11, #32
	adcs x13, x13, x2
	bit v0.16b, v20.16b, v16.16b
	mul x2, x11, x6
	adcs x8, x8, x2
	bit v1.16b, v21.16b, v16.16b
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	bit v2.16b, v22.16b, v16.16b
	movz x11, #0, lsl #0
	ldr x2, [x0, #64]
	bit v3.16b, v23.16b, v16.16b
	subs x1, x12, x2
	ldr x2, [x0, #72]
	add v30.2d, v30.2d, v18.2d
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	cmeq v31.2d, v30.2d, v19.2d
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	ldr q24, [x21, #3648]
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	ldr q25, [x21, #3664]
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	ldr q26, [x21, #3680]
	str x12, [x0, #928]
	str x13, [x0, #936]
	ldr q27, [x21, #3696]
	str x8, [x0, #944]
	str x9, [x0, #952]
	ldr x8, [x0, #896]
	bit v4.16b, v24.16b, v31.16b
	ldr x9, [x0, #904]
	ldr x10, [x0, #912]
	bit v5.16b, v25.16b, v31.16b
	ldr x11, [x0, #920]
	subs x8, x8, x12
	bit v6.16b, v26.16b, v31.16b
	sbcs x9, x9, x13
	ldr x2, [x0, #944]
	sbcs x10, x10, x2
	bit v7.16b, v27.16b, v31.16b
	ldr x2, [x0, #952]
	sbcs x11, x11, x2
	add v17.2d, v17.2d, v18.2d
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	cmeq v16.2d, v17.2d, v19.2d
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	ldr q20, [x21, #3712]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr q21, [x21, #3728]
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr q22, [x21, #3744]
	ldr x2, [x0, #88]
	and x2, x2, x17
	ldr q23, [x21, #3760]
	adcs x11, x11, x2
	str x8, [x0, #640]
	bit v0.16b, v20.16b, v16.16b
	str x9, [x0, #648]
	str x10, [x0, #656]
	str x11, [x0, #664]
	bit v1.16b, v21.16b, v16.16b
	ldr x4, [x0, #832]
	ldr x5, [x0, #840]
	bit v2.16b, v22.16b, v16.16b
	ldr x16, [x0, #848]
	ldr x17, [x0, #856]
	bit v3.16b, v23.16b, v16.16b
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	add v30.2d, v30.2d, v18.2d
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	cmeq v31.2d, v30.2d, v19.2d
	movz x13, #0, lsl #0
	ldr x1, [x0, #576]
	ldr q24, [x21, #3776]
	mul x8, x1, x4
	mul x9, x1, x5
	mul x10, x1, x16
	ldr q25, [x21, #3792]
	mul x11, x1, x17
	umulh x2, x1, x4
	ldr q26, [x21, #3808]
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	ldr q27, [x21, #3824]
	umulh x2, x1, x16
	adcs x11, x11, x2
	bit v4.16b, v24.16b, v31.16b
	umulh x2, x1, x17
	adcs x12, x12, x2
	bit v5.16b, v25.16b, v31.16b
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	bit v6.16b, v26.16b, v31.16b
	adcs x10, x10, x2
	mul x2, x8, x6
	bit v7.16b, v27.16b, v31.16b
	adcs x11, x11, x2
	umulh x2, x8, x6
	add v17.2d, v17.2d, v18.2d
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	cmeq v16.2d, v17.2d, v19.2d
	ldr x1, [x0, #584]
	mul x2, x1, x4
	ldr q20, [x21, #3840]
	adds x9, x9, x2
	mul x2, x1, x5
	ldr q21, [x21, #3856]
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	ldr q22, [x21, #3872]
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr q23, [x21, #3888]
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x4
	bit v0.16b, v20.16b, v16.16b
	adds x10, x10, x2
	umulh x2, x1, x5
	bit v1.16b, v21.16b, v16.16b
	adcs x11, x11, x2
	umulh x2, x1, x16
	bit v2.16b, v22.16b, v16.16b
	adcs x12, x12, x2
	adcs x13, x13, x7
	lsl x2, x9, #32
	bit v3.16b, v23.16b, v16.16b
	adds x10, x10, x2
	lsr x2, x9, #32
	add v30.2d, v30.2d, v18.2d
	adcs x11, x11, x2
	mul x2, x9, x6
	cmeq v31.2d, v30.2d, v19.2d
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	ldr q24, [x21, #3904]
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr q25, [x21, #3920]
	ldr x1, [x0, #592]
	mul x2, x1, x4
	adds x10, x10, x2
	ldr q26, [x21, #3936]
	mul x2, x1, x5
	adcs x11, x11, x2
	ldr q27, [x21, #3952]
	mul x2, x1, x16
	adcs x12, x12, x2
	bit v4.16b, v24.16b, v31.16b
	mul x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x17
	bit v5.16b, v25.16b, v31.16b
	adcs x8, x8, x2
	umulh x2, x1, x4
	bit v6.16b, v26.16b, v31.16b
	adds x11, x11, x2
	umulh x2, x1, x5
	bit v7.16b, v27.16b, v31.16b
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	add v17.2d, v17.2d, v18.2d
	adcs x8, x8, x7
	lsl x2, x10, #32
	cmeq v16.2d, v17.2d, v19.2d
	adds x11, x11, x2
	lsr x2, x10, #32
	ldr q20, [x21, #3968]
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	ldr q21, [x21, #3984]
	umulh x2, x10, x6
	adcs x8, x8, x2
	ldr q22, [x21, #4000]
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #600]
	ldr q23, [x21, #4016]
	mul x2, x1, x4
	adds x11, x11, x2
	bit v0.16b, v20.16b, v16.16b
	mul x2, x1, x5
	adcs x12, x12, x2
	bit v1.16b, v21.16b, v16.16b
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	bit v2.16b, v22.16b, v16.16b
	adcs x8, x8, x2
	umulh x2, x1, x17
	bit v3.16b, v23.16b, v16.16b
	adcs x9, x9, x2
	umulh x2, x1, x4
	add v30.2d, v30.2d, v18.2d
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	cmeq v31.2d, v30.2d, v19.2d
	umulh x2, x1, x16
	adcs x8, x8, x2
	ldr q24, [x21, #4032]
	adcs x9, x9, x7
	lsl x2, x11, #32
	ldr q25, [x21, #4048]
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	ldr q26, [x21, #4064]
	mul x2, x11, x6
	adcs x8, x8, x2
	ldr q27, [x21, #4080]
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	bit v4.16b, v24.16b, v31.16b
	movz x11, #0, lsl #0
	ldr x2, [x0, #64]
	bit v5.16b, v25.16b, v31.16b
	subs x1, x12, x2
	ldr x2, [x0, #72]
	bit v6.16b, v26.16b, v31.16b
	sbcs x3, x13, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	bit v7.16b, v27.16b, v31.16b
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	orr v0.16b, v0.16b, v4.16b
	sbcs x2, x10, x7
	csel x12, x1, x12, hs
	orr v1.16b, v1.16b, v5.16b
	csel x13, x3, x13, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	orr v2.16b, v2.16b, v6.16b
	str x12, [x0, #672]
	str x13, [x0, #680]
	orr v3.16b, v3.16b, v7.16b
	str x8, [x0, #688]
	str x9, [x0, #696]
	movz x7, #0, lsl #0
	ldr x1, [x0, #576]
	ldr x2, [x0, #584]
	orr x1, x1, x2
	ldr x2, [x0, #592]
	orr x1, x1, x2
	ldr x2, [x0, #600]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x3, x7, x7
	ldr x1, [x0, #704]
	ldr x2, [x0, #608]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #608]
	ldr x1, [x0, #712]
	ldr x2, [x0, #616]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #616]
	ldr x1, [x0, #720]
	ldr x2, [x0, #624]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #624]
	ldr x1, [x0, #728]
	ldr x2, [x0, #632]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #632]
	ldr x1, [x0, #736]
	ldr x2, [x0, #640]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #640]
	ldr x1, [x0, #744]
	ldr x2, [x0, #648]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #648]
	ldr x1, [x0, #752]
	ldr x2, [x0, #656]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #656]
	ldr x1, [x0, #760]
	ldr x2, [x0, #664]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #664]
	ldr x1, [x0, #768]
	ldr x2, [x0, #672]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #672]
	ldr x1, [x0, #776]
	ldr x2, [x0, #680]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #680]
	ldr x1, [x0, #784]
	ldr x2, [x0, #688]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #688]
	ldr x1, [x0, #792]
	ldr x2, [x0, #696]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #696]
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
	ldrb w4, [x16, #1503]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #1510]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	movz x5, #1, lsl #0
	subs x16, x2, x5
	sbc x3, x7, x7
	ldr x1, [x0, #608]
	ldr x2, [x0, #512]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #512]
	ldr x1, [x0, #616]
	ldr x2, [x0, #520]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #520]
	ldr x1, [x0, #624]
	ldr x2, [x0, #528]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #528]
	ldr x1, [x0, #632]
	ldr x2, [x0, #536]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #536]
	ldr x1, [x0, #640]
	ldr x2, [x0, #544]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #544]
	ldr x1, [x0, #648]
	ldr x2, [x0, #552]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #552]
	ldr x1, [x0, #656]
	ldr x2, [x0, #560]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #560]
	ldr x1, [x0, #664]
	ldr x2, [x0, #568]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #568]
	ldr x1, [x0, #672]
	ldr x2, [x0, #576]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #576]
	ldr x1, [x0, #680]
	ldr x2, [x0, #584]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #584]
	ldr x1, [x0, #688]
	ldr x2, [x0, #592]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #592]
	ldr x1, [x0, #696]
	ldr x2, [x0, #600]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #600]
	add x19, x19, #1
	sub x4, x19, #37
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
	ldrb w4, [x16, #1503]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #1510]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	movz x5, #1, lsl #0
	movi v16.2d, #0
	cmeq v16.2d, v16.2d, v19.2d
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[0], x6
	movz x6, #65534, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v3.16b, v20.16b, v16.16b
	str q0, [x0, #704]
	str q1, [x0, #720]
	str q2, [x0, #736]
	str q3, [x0, #752]
	subs x4, x2, x5
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #768]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #776]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #784]
	movz x6, #65534, lsl #0
	movk x6, #65535, lsl #16
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
	movz x7, #0, lsl #0
	ldrb w4, [x16, #1510]
	sub x3, x7, x4
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
	sub x4, x19, #36
	cbnz x4, 21b
	movz x7, #0, lsl #0
	ldr x4, [x0, #576]
	ldr x5, [x0, #584]
	ldr x16, [x0, #592]
	ldr x17, [x0, #600]
	mul x9, x5, x4
	umulh x2, x5, x4
	mul x10, x16, x4
	umulh x3, x16, x4
	mul x11, x17, x4
	umulh x12, x17, x4
	adds x10, x10, x2
	mul x1, x16, x5
	umulh x2, x16, x5
	adcs x11, x11, x3
	mul x3, x17, x5
	umulh x6, x17, x5
	adc x12, x12, x7
	mul x13, x17, x16
	umulh x14, x17, x16
	adds x2, x2, x3
	mul x8, x4, x4
	adc x3, x6, x7
	adds x11, x11, x1
	umulh x4, x4, x4
	adcs x12, x12, x2
	mul x2, x5, x5
	adcs x13, x13, x3
	umulh x5, x5, x5
	adc x14, x14, x7
	adds x9, x9, x9
	mul x3, x16, x16
	adcs x10, x10, x10
	umulh x16, x16, x16
	adcs x11, x11, x11
	mul x6, x17, x17
	adcs x12, x12, x12
	umulh x17, x17, x17
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x15, x7, x7
	adds x9, x9, x4
	adcs x10, x10, x2
	adcs x11, x11, x5
	adcs x12, x12, x3
	adcs x13, x13, x16
	lsl x1, x8, #32
	adcs x14, x14, x6
	lsr x2, x8, #32
	adc x15, x15, x17
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	adcs x10, x11, x3
	adc x11, x6, x7
	adds x8, x8, x12
	adcs x9, x9, x13
	adcs x10, x10, x14
	adcs x11, x11, x15
	adc x12, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	str x8, [x0, #800]
	str x9, [x0, #808]
	str x10, [x0, #816]
	str x11, [x0, #824]
	orr x4, x8, x8
	orr x5, x9, x9
	orr x16, x10, x10
	orr x17, x11, x11
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #704]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #712]
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #720]
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #728]
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #832]
	str x13, [x0, #840]
	str x8, [x0, #848]
	str x9, [x0, #856]
	ldr x4, [x0, #800]
	ldr x5, [x0, #808]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #576]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #584]
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #592]
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #600]
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	orr x4, x12, x12
	orr x5, x13, x13
	orr x16, x8, x8
	orr x17, x9, x9
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #736]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #744]
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #752]
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #760]
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x8, [x0, #880]
	str x9, [x0, #888]
	ldr x8, [x0, #832]
	ldr x9, [x0, #840]
	ldr x10, [x0, #848]
	ldr x11, [x0, #856]
	ldr x2, [x0, #512]
	subs x8, x8, x2
	ldr x2, [x0, #520]
	sbcs x9, x9, x2
	ldr x2, [x0, #528]
	sbcs x10, x10, x2
	ldr x2, [x0, #536]
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
	str x8, [x0, #832]
	str x9, [x0, #840]
	str x10, [x0, #848]
	str x11, [x0, #856]
	orr x8, x12, x12
	orr x9, x13, x13
	ldr x10, [x0, #880]
	ldr x11, [x0, #888]
	ldr x2, [x0, #544]
	subs x8, x8, x2
	ldr x2, [x0, #552]
	sbcs x9, x9, x2
	ldr x2, [x0, #560]
	sbcs x10, x10, x2
	ldr x2, [x0, #568]
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
	str x8, [x0, #864]
	str x9, [x0, #872]
	str x10, [x0, #880]
	str x11, [x0, #888]
	ldr x4, [x0, #832]
	ldr x5, [x0, #840]
	ldr x16, [x0, #848]
	ldr x17, [x0, #856]
	mul x9, x5, x4
	umulh x2, x5, x4
	mul x10, x16, x4
	umulh x3, x16, x4
	mul x11, x17, x4
	umulh x12, x17, x4
	adds x10, x10, x2
	mul x1, x16, x5
	umulh x2, x16, x5
	adcs x11, x11, x3
	mul x3, x17, x5
	umulh x6, x17, x5
	adc x12, x12, x7
	mul x13, x17, x16
	umulh x14, x17, x16
	adds x2, x2, x3
	mul x8, x4, x4
	adc x3, x6, x7
	adds x11, x11, x1
	umulh x4, x4, x4
	adcs x12, x12, x2
	mul x2, x5, x5
	adcs x13, x13, x3
	umulh x5, x5, x5
	adc x14, x14, x7
	adds x9, x9, x9
	mul x3, x16, x16
	adcs x10, x10, x10
	umulh x16, x16, x16
	adcs x11, x11, x11
	mul x6, x17, x17
	adcs x12, x12, x12
	umulh x17, x17, x17
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x15, x7, x7
	adds x9, x9, x4
	adcs x10, x10, x2
	adcs x11, x11, x5
	adcs x12, x12, x3
	adcs x13, x13, x16
	lsl x1, x8, #32
	adcs x14, x14, x6
	lsr x2, x8, #32
	adc x15, x15, x17
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	adcs x10, x11, x3
	adc x11, x6, x7
	adds x8, x8, x12
	adcs x9, x9, x13
	adcs x10, x10, x14
	adcs x11, x11, x15
	adc x12, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	str x8, [x0, #896]
	str x9, [x0, #904]
	orr x4, x8, x8
	orr x5, x9, x9
	orr x16, x10, x10
	orr x17, x11, x11
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #832]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #840]
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #848]
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #856]
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #928]
	str x13, [x0, #936]
	str x8, [x0, #944]
	str x9, [x0, #952]
	ldr x4, [x0, #896]
	ldr x5, [x0, #904]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #896]
	str x13, [x0, #904]
	str x8, [x0, #912]
	str x9, [x0, #920]
	ldr x4, [x0, #864]
	ldr x5, [x0, #872]
	ldr x16, [x0, #880]
	ldr x17, [x0, #888]
	mul x9, x5, x4
	umulh x2, x5, x4
	mul x10, x16, x4
	umulh x3, x16, x4
	mul x11, x17, x4
	umulh x12, x17, x4
	adds x10, x10, x2
	mul x1, x16, x5
	umulh x2, x16, x5
	adcs x11, x11, x3
	mul x3, x17, x5
	umulh x6, x17, x5
	adc x12, x12, x7
	mul x13, x17, x16
	umulh x14, x17, x16
	adds x2, x2, x3
	mul x8, x4, x4
	adc x3, x6, x7
	adds x11, x11, x1
	umulh x4, x4, x4
	adcs x12, x12, x2
	mul x2, x5, x5
	adcs x13, x13, x3
	umulh x5, x5, x5
	adc x14, x14, x7
	adds x9, x9, x9
	mul x3, x16, x16
	adcs x10, x10, x10
	umulh x16, x16, x16
	adcs x11, x11, x11
	mul x6, x17, x17
	adcs x12, x12, x12
	umulh x17, x17, x17
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x15, x7, x7
	adds x9, x9, x4
	adcs x10, x10, x2
	adcs x11, x11, x5
	adcs x12, x12, x3
	adcs x13, x13, x16
	lsl x1, x8, #32
	adcs x14, x14, x6
	lsr x2, x8, #32
	adc x15, x15, x17
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	adcs x10, x11, x3
	adc x11, x6, x7
	adds x8, x8, x12
	adcs x9, x9, x13
	adcs x10, x10, x14
	adcs x11, x11, x15
	adc x12, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	ldr x2, [x0, #928]
	subs x8, x8, x2
	ldr x2, [x0, #936]
	sbcs x9, x9, x2
	ldr x2, [x0, #944]
	sbcs x10, x10, x2
	ldr x2, [x0, #952]
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
	str x8, [x0, #608]
	str x9, [x0, #616]
	str x10, [x0, #624]
	str x11, [x0, #632]
	ldr x8, [x0, #896]
	ldr x9, [x0, #904]
	ldr x10, [x0, #912]
	ldr x11, [x0, #920]
	adds x8, x8, x8
	adcs x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adc x12, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	str x8, [x0, #960]
	str x9, [x0, #968]
	str x10, [x0, #976]
	str x11, [x0, #984]
	ldr x8, [x0, #608]
	ldr x9, [x0, #616]
	ldr x10, [x0, #624]
	ldr x11, [x0, #632]
	ldr x2, [x0, #960]
	subs x8, x8, x2
	ldr x2, [x0, #968]
	sbcs x9, x9, x2
	ldr x2, [x0, #976]
	sbcs x10, x10, x2
	ldr x2, [x0, #984]
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
	str x8, [x0, #608]
	str x9, [x0, #616]
	str x10, [x0, #624]
	str x11, [x0, #632]
	ldr x8, [x0, #896]
	ldr x9, [x0, #904]
	ldr x10, [x0, #912]
	ldr x11, [x0, #920]
	ldr x2, [x0, #608]
	subs x8, x8, x2
	ldr x2, [x0, #616]
	sbcs x9, x9, x2
	ldr x2, [x0, #624]
	sbcs x10, x10, x2
	ldr x2, [x0, #632]
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
	orr x4, x8, x8
	orr x5, x9, x9
	orr x16, x10, x10
	orr x17, x11, x11
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #864]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #872]
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #880]
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #888]
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #896]
	str x13, [x0, #904]
	str x8, [x0, #912]
	str x9, [x0, #920]
	ldr x4, [x0, #928]
	ldr x5, [x0, #936]
	ldr x16, [x0, #944]
	ldr x17, [x0, #952]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #544]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #552]
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #560]
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #568]
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #928]
	str x13, [x0, #936]
	str x8, [x0, #944]
	str x9, [x0, #952]
	ldr x8, [x0, #896]
	ldr x9, [x0, #904]
	ldr x10, [x0, #912]
	ldr x11, [x0, #920]
	subs x8, x8, x12
	sbcs x9, x9, x13
	ldr x2, [x0, #944]
	sbcs x10, x10, x2
	ldr x2, [x0, #952]
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
	str x8, [x0, #640]
	str x9, [x0, #648]
	str x10, [x0, #656]
	str x11, [x0, #664]
	ldr x4, [x0, #832]
	ldr x5, [x0, #840]
	ldr x16, [x0, #848]
	ldr x17, [x0, #856]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #576]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #584]
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #592]
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #600]
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #672]
	str x13, [x0, #680]
	str x8, [x0, #688]
	str x9, [x0, #696]
	movz x7, #0, lsl #0
	ldr x1, [x0, #576]
	ldr x2, [x0, #584]
	orr x1, x1, x2
	ldr x2, [x0, #592]
	orr x1, x1, x2
	ldr x2, [x0, #600]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x3, x7, x7
	ldr x1, [x0, #704]
	ldr x2, [x0, #608]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #608]
	ldr x1, [x0, #712]
	ldr x2, [x0, #616]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #616]
	ldr x1, [x0, #720]
	ldr x2, [x0, #624]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #624]
	ldr x1, [x0, #728]
	ldr x2, [x0, #632]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #632]
	ldr x1, [x0, #736]
	ldr x2, [x0, #640]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #640]
	ldr x1, [x0, #744]
	ldr x2, [x0, #648]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #648]
	ldr x1, [x0, #752]
	ldr x2, [x0, #656]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #656]
	ldr x1, [x0, #760]
	ldr x2, [x0, #664]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #664]
	ldr x1, [x0, #768]
	ldr x2, [x0, #672]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #672]
	ldr x1, [x0, #776]
	ldr x2, [x0, #680]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #680]
	ldr x1, [x0, #784]
	ldr x2, [x0, #688]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #688]
	ldr x1, [x0, #792]
	ldr x2, [x0, #696]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #696]
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
	ldrb w4, [x16, #1503]
	add x2, x2, x4
	movz x7, #0, lsl #0
	ldrb w4, [x16, #1510]
	sub x3, x7, x4
	eor x2, x2, x3
	sub x2, x2, x3
	movz x9, #128, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	and x3, x3, x9
	add x2, x2, x3
	movz x7, #0, lsl #0
	movz x5, #1, lsl #0
	subs x16, x2, x5
	sbc x3, x7, x7
	ldr x1, [x0, #608]
	ldr x2, [x0, #512]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #512]
	ldr x1, [x0, #616]
	ldr x2, [x0, #520]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #520]
	ldr x1, [x0, #624]
	ldr x2, [x0, #528]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #528]
	ldr x1, [x0, #632]
	ldr x2, [x0, #536]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #536]
	ldr x1, [x0, #640]
	ldr x2, [x0, #544]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #544]
	ldr x1, [x0, #648]
	ldr x2, [x0, #552]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #552]
	ldr x1, [x0, #656]
	ldr x2, [x0, #560]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #560]
	ldr x1, [x0, #664]
	ldr x2, [x0, #568]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #568]
	ldr x1, [x0, #672]
	ldr x2, [x0, #576]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #576]
	ldr x1, [x0, #680]
	ldr x2, [x0, #584]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #584]
	ldr x1, [x0, #688]
	ldr x2, [x0, #592]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #592]
	ldr x1, [x0, #696]
	ldr x2, [x0, #600]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #600]
	add x19, x19, #1
	sub x4, x19, #37
	movz x7, #0, lsl #0
	ldr x1, [x0, #576]
	ldr x2, [x0, #584]
	orr x1, x1, x2
	ldr x2, [x0, #592]
	orr x1, x1, x2
	ldr x2, [x0, #600]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x3, x7, x7
	ldr x1, [x0, #160]
	ldr x2, [x0, #544]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #544]
	ldr x1, [x0, #168]
	ldr x2, [x0, #552]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #552]
	ldr x1, [x0, #176]
	ldr x2, [x0, #560]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #560]
	ldr x1, [x0, #184]
	ldr x2, [x0, #568]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #568]
	sub x4, x7, #1
	eor x3, x3, x4
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #544]
	orr x1, x1, x2
	str x1, [x0, #544]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #552]
	orr x1, x1, x2
	str x1, [x0, #552]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #560]
	orr x1, x1, x2
	str x1, [x0, #560]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	and x1, x1, x3
	ldr x2, [x0, #568]
	orr x1, x1, x2
	str x1, [x0, #568]
	movz x7, #0, lsl #0
	ldr x4, [x0, #576]
	ldr x5, [x0, #584]
	ldr x16, [x0, #592]
	ldr x17, [x0, #600]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #512]
	str x13, [x0, #520]
	str x8, [x0, #528]
	str x9, [x0, #536]
	ldr x4, [x0, #576]
	ldr x5, [x0, #584]
	mul x9, x5, x4
	umulh x2, x5, x4
	mul x10, x16, x4
	umulh x3, x16, x4
	mul x11, x17, x4
	umulh x12, x17, x4
	adds x10, x10, x2
	mul x1, x16, x5
	umulh x2, x16, x5
	adcs x11, x11, x3
	mul x3, x17, x5
	umulh x6, x17, x5
	adc x12, x12, x7
	mul x13, x17, x16
	umulh x14, x17, x16
	adds x2, x2, x3
	mul x8, x4, x4
	adc x3, x6, x7
	adds x11, x11, x1
	umulh x4, x4, x4
	adcs x12, x12, x2
	mul x2, x5, x5
	adcs x13, x13, x3
	umulh x5, x5, x5
	adc x14, x14, x7
	adds x9, x9, x9
	mul x3, x16, x16
	adcs x10, x10, x10
	umulh x16, x16, x16
	adcs x11, x11, x11
	mul x6, x17, x17
	adcs x12, x12, x12
	umulh x17, x17, x17
	adcs x13, x13, x13
	adcs x14, x14, x14
	adc x15, x7, x7
	adds x9, x9, x4
	adcs x10, x10, x2
	adcs x11, x11, x5
	adcs x12, x12, x3
	adcs x13, x13, x16
	lsl x1, x8, #32
	adcs x14, x14, x6
	lsr x2, x8, #32
	adc x15, x15, x17
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	lsl x1, x8, #32
	adcs x10, x11, x3
	lsr x2, x8, #32
	adc x11, x6, x7
	subs x3, x8, x1
	sbc x6, x8, x2
	adds x8, x9, x1
	adcs x9, x10, x2
	adcs x10, x11, x3
	adc x11, x6, x7
	adds x8, x8, x12
	adcs x9, x9, x13
	adcs x10, x10, x14
	adcs x11, x11, x15
	adc x12, x7, x7
	ldr x2, [x0, #64]
	subs x1, x8, x2
	ldr x2, [x0, #72]
	sbcs x3, x9, x2
	ldr x2, [x0, #80]
	sbcs x4, x10, x2
	ldr x2, [x0, #88]
	sbcs x5, x11, x2
	sbcs x2, x12, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	str x8, [x0, #800]
	str x9, [x0, #808]
	str x10, [x0, #816]
	str x11, [x0, #824]
	ldr x4, [x0, #576]
	ldr x5, [x0, #584]
	ldr x16, [x0, #592]
	ldr x17, [x0, #600]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	orr x1, x8, x8
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #808]
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #816]
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #824]
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #576]
	str x13, [x0, #584]
	str x8, [x0, #592]
	str x9, [x0, #600]
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #10, lsl #0
	ldr x2, [x0, #64]
	str x2, [x0, #2272]
	ldr x2, [x0, #72]
	str x2, [x0, #2280]
	ldr x2, [x0, #80]
	str x2, [x0, #2288]
	ldr x2, [x0, #88]
	str x2, [x0, #2296]
	str x12, [x0, #2304]
	ldr x2, [x0, #576]
	str x2, [x0, #2312]
	ldr x2, [x0, #584]
	str x2, [x0, #2320]
	ldr x2, [x0, #592]
	str x2, [x0, #2328]
	ldr x2, [x0, #600]
	str x2, [x0, #2336]
	str x12, [x0, #2344]
	str x12, [x0, #2352]
	str x12, [x0, #2360]
	str x12, [x0, #2368]
	str x12, [x0, #2376]
	str x12, [x0, #2384]
	str x12, [x0, #2392]
	str x12, [x0, #2400]
	str x12, [x0, #2408]
	str x12, [x0, #2416]
	str x12, [x0, #2424]
	str x11, [x0, #2392]
22:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #2272]
	ldr x3, [x0, #2312]
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #1, lsl #0
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x12, #0, lsl #0
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #2272]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #2512]
	ldr x2, [x0, #2280]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2520]
	ldr x2, [x0, #2288]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2528]
	ldr x2, [x0, #2296]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2536]
	ldr x2, [x0, #2304]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2312]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #2320]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #2328]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #2336]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2344]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2272]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2280]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2288]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2296]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2312]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2320]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2328]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2336]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x2, [x0, #2512]
	ldr x3, [x0, #2520]
	extr x8, x3, x2, #59
	str x8, [x0, #2432]
	ldr x2, [x0, #2520]
	ldr x3, [x0, #2528]
	extr x8, x3, x2, #59
	str x8, [x0, #2440]
	ldr x2, [x0, #2528]
	ldr x3, [x0, #2536]
	extr x8, x3, x2, #59
	str x8, [x0, #2448]
	ldr x2, [x0, #2536]
	ldr x3, [x0, #2544]
	extr x8, x3, x2, #59
	str x8, [x0, #2456]
	ldr x3, [x0, #2544]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #2464]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #2272]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #2512]
	ldr x2, [x0, #2280]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2520]
	ldr x2, [x0, #2288]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2528]
	ldr x2, [x0, #2296]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2536]
	ldr x2, [x0, #2304]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2312]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #2320]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #2328]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #2336]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2344]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2272]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2280]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2288]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2296]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2312]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2320]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2328]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2336]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x2, [x0, #2512]
	ldr x3, [x0, #2520]
	extr x8, x3, x2, #59
	str x8, [x0, #2472]
	ldr x2, [x0, #2520]
	ldr x3, [x0, #2528]
	extr x8, x3, x2, #59
	str x8, [x0, #2480]
	ldr x2, [x0, #2528]
	ldr x3, [x0, #2536]
	extr x8, x3, x2, #59
	str x8, [x0, #2488]
	ldr x2, [x0, #2536]
	ldr x3, [x0, #2544]
	extr x8, x3, x2, #59
	str x8, [x0, #2496]
	ldr x3, [x0, #2544]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #2504]
	ldr x2, [x0, #2432]
	str x2, [x0, #2272]
	ldr x2, [x0, #2440]
	str x2, [x0, #2280]
	ldr x2, [x0, #2448]
	str x2, [x0, #2288]
	ldr x2, [x0, #2456]
	str x2, [x0, #2296]
	ldr x2, [x0, #2464]
	str x2, [x0, #2304]
	ldr x2, [x0, #2472]
	str x2, [x0, #2312]
	ldr x2, [x0, #2480]
	str x2, [x0, #2320]
	ldr x2, [x0, #2488]
	str x2, [x0, #2328]
	ldr x2, [x0, #2496]
	str x2, [x0, #2336]
	ldr x2, [x0, #2504]
	str x2, [x0, #2344]
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #2352]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #2512]
	ldr x2, [x0, #2360]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2520]
	ldr x2, [x0, #2368]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2528]
	ldr x2, [x0, #2376]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2536]
	ldr x2, [x0, #2384]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2392]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #2400]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #2408]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #2416]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2424]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2352]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2360]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2368]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2376]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2392]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2400]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2408]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2416]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x2, [x0, #2512]
	movz x17, #1, lsl #0
	movk x17, #0, lsl #16
	movk x17, #0, lsl #32
	movk x17, #0, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #2544]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #2552]
	movz x10, #0, lsl #0
	ldr x2, [x0, #64]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #72]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #80]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #88]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	adds x3, x3, x10
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	adcs x3, x3, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #2520]
	str x2, [x0, #2432]
	ldr x2, [x0, #2528]
	str x2, [x0, #2440]
	ldr x2, [x0, #2536]
	str x2, [x0, #2448]
	ldr x2, [x0, #2544]
	str x2, [x0, #2456]
	ldr x2, [x0, #2552]
	str x2, [x0, #2464]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #2352]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #2512]
	ldr x2, [x0, #2360]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2520]
	ldr x2, [x0, #2368]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2528]
	ldr x2, [x0, #2376]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2536]
	ldr x2, [x0, #2384]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2392]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #2400]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #2408]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #2416]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2424]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2352]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2360]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2368]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2376]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2392]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2400]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2408]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2416]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x2, [x0, #2512]
	movz x17, #1, lsl #0
	movk x17, #0, lsl #16
	movk x17, #0, lsl #32
	movk x17, #0, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #2544]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #2552]
	movz x10, #0, lsl #0
	ldr x2, [x0, #64]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #72]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #80]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #88]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	adds x3, x3, x10
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	adcs x3, x3, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #2520]
	str x2, [x0, #2392]
	ldr x2, [x0, #2528]
	str x2, [x0, #2400]
	ldr x2, [x0, #2536]
	str x2, [x0, #2408]
	ldr x2, [x0, #2544]
	str x2, [x0, #2416]
	ldr x2, [x0, #2552]
	str x2, [x0, #2424]
	ldr x2, [x0, #2432]
	str x2, [x0, #2352]
	ldr x2, [x0, #2440]
	str x2, [x0, #2360]
	ldr x2, [x0, #2448]
	str x2, [x0, #2368]
	ldr x2, [x0, #2456]
	str x2, [x0, #2376]
	ldr x2, [x0, #2464]
	str x2, [x0, #2384]
	cbnz x19, 22b
	movz x12, #0, lsl #0
	ldr x3, [x0, #2384]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #2352]
	ldr x2, [x0, #64]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #2352]
	ldr x3, [x0, #2360]
	ldr x2, [x0, #72]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2360]
	ldr x3, [x0, #2368]
	ldr x2, [x0, #80]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2368]
	ldr x3, [x0, #2376]
	ldr x2, [x0, #88]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2376]
	ldr x3, [x0, #2384]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #2384]
	ldr x3, [x0, #2352]
	ldr x2, [x0, #64]
	subs x3, x3, x2
	str x3, [x0, #2352]
	ldr x3, [x0, #2360]
	ldr x2, [x0, #72]
	sbcs x3, x3, x2
	str x3, [x0, #2360]
	ldr x3, [x0, #2368]
	ldr x2, [x0, #80]
	sbcs x3, x3, x2
	str x3, [x0, #2368]
	ldr x3, [x0, #2376]
	ldr x2, [x0, #88]
	sbcs x3, x3, x2
	str x3, [x0, #2376]
	ldr x3, [x0, #2384]
	add x2, x12, x12
	sbcs x3, x3, x2
	str x3, [x0, #2384]
	ldr x3, [x0, #2384]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #2352]
	ldr x2, [x0, #64]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #2352]
	ldr x3, [x0, #2360]
	ldr x2, [x0, #72]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2360]
	ldr x3, [x0, #2368]
	ldr x2, [x0, #80]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2368]
	ldr x3, [x0, #2376]
	ldr x2, [x0, #88]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2376]
	ldr x3, [x0, #2384]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #2384]
	movz x12, #0, lsl #0
	ldr x3, [x0, #2272]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #0, lsl #0
	movk x2, #96, lsl #16
	movk x2, #0, lsl #32
	movk x2, #40, lsl #48
	movz x3, #65535, lsl #0
	movk x3, #65439, lsl #16
	movk x3, #65535, lsl #32
	movk x3, #65495, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2432]
	movz x2, #0, lsl #0
	movk x2, #65524, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65407, lsl #48
	movz x3, #65535, lsl #0
	movk x3, #11, lsl #16
	movk x3, #1, lsl #32
	movk x3, #128, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2440]
	movz x2, #65535, lsl #0
	movk x2, #65463, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65523, lsl #48
	movz x3, #0, lsl #0
	movk x3, #72, lsl #16
	movk x3, #0, lsl #32
	movk x3, #12, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2448]
	movz x2, #65535, lsl #0
	movk x2, #65463, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #99, lsl #48
	movz x3, #1, lsl #0
	movk x3, #72, lsl #16
	movk x3, #65535, lsl #32
	movk x3, #65435, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2456]
	movz x7, #0, lsl #0
	ldr x4, [x0, #2432]
	ldr x5, [x0, #2440]
	ldr x16, [x0, #2448]
	ldr x17, [x0, #2456]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #2352]
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #2360]
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #2368]
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #2376]
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	str x12, [x0, #992]
	str x13, [x0, #1000]
	str x8, [x0, #1008]
	str x9, [x0, #1016]
	movz x7, #0, lsl #0
	ldr x4, [x0, #992]
	ldr x5, [x0, #1000]
	ldr x16, [x0, #1008]
	ldr x17, [x0, #1016]
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
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
	lsl x2, x8, #32
	adds x9, x9, x2
	lsr x2, x8, #32
	adcs x10, x10, x2
	mul x2, x8, x6
	adcs x11, x11, x2
	umulh x2, x8, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	lsl x2, x9, #32
	adds x10, x10, x2
	lsr x2, x9, #32
	adcs x11, x11, x2
	mul x2, x9, x6
	adcs x12, x12, x2
	umulh x2, x9, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	lsl x2, x10, #32
	adds x11, x11, x2
	lsr x2, x10, #32
	adcs x12, x12, x2
	mul x2, x10, x6
	adcs x13, x13, x2
	umulh x2, x10, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	lsl x2, x11, #32
	adds x12, x12, x2
	lsr x2, x11, #32
	adcs x13, x13, x2
	mul x2, x11, x6
	adcs x8, x8, x2
	umulh x2, x11, x6
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
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
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
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
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	movz x1, #1, lsl #0
	movz x19, #10, lsl #0
	ldr x2, [x0, #96]
	str x2, [x0, #2272]
	ldr x2, [x0, #104]
	str x2, [x0, #2280]
	ldr x2, [x0, #112]
	str x2, [x0, #2288]
	ldr x2, [x0, #120]
	str x2, [x0, #2296]
	str x12, [x0, #2304]
	ldr x2, [x0, #1248]
	str x2, [x0, #2312]
	ldr x2, [x0, #1256]
	str x2, [x0, #2320]
	ldr x2, [x0, #1264]
	str x2, [x0, #2328]
	ldr x2, [x0, #1272]
	str x2, [x0, #2336]
	str x12, [x0, #2344]
	str x12, [x0, #2352]
	str x12, [x0, #2360]
	str x12, [x0, #2368]
	str x12, [x0, #2376]
	str x12, [x0, #2384]
	str x12, [x0, #2392]
	str x12, [x0, #2400]
	str x12, [x0, #2408]
	str x12, [x0, #2416]
	str x12, [x0, #2424]
	str x11, [x0, #2392]
23:
	sub x19, x19, #1
	movz x11, #1, lsl #0
	movz x12, #0, lsl #0
	ldr x2, [x0, #2272]
	ldr x3, [x0, #2312]
	movz x4, #1, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #1, lsl #0
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	orr x4, x8, x8
	orr x5, x11, x11
	orr x6, x10, x10
	orr x7, x9, x9
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x10, x10, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x9, x10, #47
	sub x9, x9, x17
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x10, x10, x17
	mul x13, x2, x8
	madd x13, x3, x11, x13
	mul x16, x2, x10
	madd x16, x3, x9, x16
	lsr x2, x13, #15
	lsr x3, x16, #15
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x10, x4
	madd x6, x9, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x10, x5
	madd x7, x9, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #32767, lsl #0
	and x8, x2, x13
	and x9, x3, x13
	movz x16, #32768, lsl #16
	add x8, x8, x16
	movz x16, #32768, lsl #32
	add x9, x9, x16
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x1, #0, #0, ne
	csel x10, x11, x10, mi
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x1, #0, #0, ne
	csel x9, x11, x9, mi
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, mi
	add x13, x1, #4
	sub x1, x1, #2
	csneg x1, x1, x13, pl
	add x12, x12, x12
	movz x13, #16384, lsl #16
	movk x13, #8192, lsl #32
	movk x13, #8192, lsl #48
	movz x17, #16384, lsl #0
	add x8, x8, x13
	add x9, x9, x13
	lsr x11, x8, #47
	sub x11, x11, x17
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x8, x8, x17
	lsr x10, x9, #47
	sub x10, x10, x17
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x9, x9, x17
	mul x13, x8, x4
	madd x13, x11, x6, x13
	mul x16, x9, x4
	madd x6, x10, x6, x16
	mul x17, x8, x5
	madd x17, x11, x7, x17
	mul x16, x9, x5
	madd x7, x10, x7, x16
	orr x4, x13, x13
	orr x5, x17, x17
	movz x13, #0, lsl #0
	sub x1, x13, x1
	sub x1, x1, #1
	movz x12, #0, lsl #0
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #2272]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #2512]
	ldr x2, [x0, #2280]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2520]
	ldr x2, [x0, #2288]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2528]
	ldr x2, [x0, #2296]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2536]
	ldr x2, [x0, #2304]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2312]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #2320]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #2328]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #2336]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2344]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2272]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2280]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2288]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2296]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2312]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2320]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2328]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2336]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x2, [x0, #2512]
	ldr x3, [x0, #2520]
	extr x8, x3, x2, #59
	str x8, [x0, #2432]
	ldr x2, [x0, #2520]
	ldr x3, [x0, #2528]
	extr x8, x3, x2, #59
	str x8, [x0, #2440]
	ldr x2, [x0, #2528]
	ldr x3, [x0, #2536]
	extr x8, x3, x2, #59
	str x8, [x0, #2448]
	ldr x2, [x0, #2536]
	ldr x3, [x0, #2544]
	extr x8, x3, x2, #59
	str x8, [x0, #2456]
	ldr x3, [x0, #2544]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #2464]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #2272]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #2512]
	ldr x2, [x0, #2280]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2520]
	ldr x2, [x0, #2288]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2528]
	ldr x2, [x0, #2296]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2536]
	ldr x2, [x0, #2304]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2312]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #2320]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #2328]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #2336]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2344]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2272]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2280]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2288]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2296]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2312]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2320]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2328]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2336]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x2, [x0, #2512]
	ldr x3, [x0, #2520]
	extr x8, x3, x2, #59
	str x8, [x0, #2472]
	ldr x2, [x0, #2520]
	ldr x3, [x0, #2528]
	extr x8, x3, x2, #59
	str x8, [x0, #2480]
	ldr x2, [x0, #2528]
	ldr x3, [x0, #2536]
	extr x8, x3, x2, #59
	str x8, [x0, #2488]
	ldr x2, [x0, #2536]
	ldr x3, [x0, #2544]
	extr x8, x3, x2, #59
	str x8, [x0, #2496]
	ldr x3, [x0, #2544]
	lsr x9, x3, #63
	sub x9, x12, x9
	extr x8, x9, x3, #59
	str x8, [x0, #2504]
	ldr x2, [x0, #2432]
	str x2, [x0, #2272]
	ldr x2, [x0, #2440]
	str x2, [x0, #2280]
	ldr x2, [x0, #2448]
	str x2, [x0, #2288]
	ldr x2, [x0, #2456]
	str x2, [x0, #2296]
	ldr x2, [x0, #2464]
	str x2, [x0, #2304]
	ldr x2, [x0, #2472]
	str x2, [x0, #2312]
	ldr x2, [x0, #2480]
	str x2, [x0, #2320]
	ldr x2, [x0, #2488]
	str x2, [x0, #2328]
	ldr x2, [x0, #2496]
	str x2, [x0, #2336]
	ldr x2, [x0, #2504]
	str x2, [x0, #2344]
	lsr x16, x4, #63
	sub x16, x12, x16
	lsr x17, x5, #63
	sub x17, x12, x17
	ldr x2, [x0, #2352]
	mul x8, x4, x2
	umulh x10, x4, x2
	str x8, [x0, #2512]
	ldr x2, [x0, #2360]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2520]
	ldr x2, [x0, #2368]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2528]
	ldr x2, [x0, #2376]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2536]
	ldr x2, [x0, #2384]
	mul x8, x4, x2
	umulh x9, x4, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2392]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #2400]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #2408]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #2416]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2424]
	mul x8, x5, x2
	umulh x9, x5, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2352]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2360]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2368]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2376]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2392]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2400]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2408]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2416]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x2, [x0, #2512]
	movz x17, #48207, lsl #0
	movk x17, #60928, lsl #16
	movk x17, #51370, lsl #32
	movk x17, #52433, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #2544]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #2552]
	movz x10, #0, lsl #0
	ldr x2, [x0, #96]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #104]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #112]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #120]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	adds x3, x3, x10
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	adcs x3, x3, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #2520]
	str x2, [x0, #2432]
	ldr x2, [x0, #2528]
	str x2, [x0, #2440]
	ldr x2, [x0, #2536]
	str x2, [x0, #2448]
	ldr x2, [x0, #2544]
	str x2, [x0, #2456]
	ldr x2, [x0, #2552]
	str x2, [x0, #2464]
	lsr x16, x6, #63
	sub x16, x12, x16
	lsr x17, x7, #63
	sub x17, x12, x17
	ldr x2, [x0, #2352]
	mul x8, x6, x2
	umulh x10, x6, x2
	str x8, [x0, #2512]
	ldr x2, [x0, #2360]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2520]
	ldr x2, [x0, #2368]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2528]
	ldr x2, [x0, #2376]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2536]
	ldr x2, [x0, #2384]
	mul x8, x6, x2
	umulh x9, x6, x2
	adds x8, x8, x10
	adc x10, x9, x12
	str x8, [x0, #2544]
	movz x10, #0, lsl #0
	ldr x2, [x0, #2392]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #2400]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #2408]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #2416]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x2, [x0, #2424]
	mul x8, x7, x2
	umulh x9, x7, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2544]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2352]
	and x2, x2, x16
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2360]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2368]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2376]
	and x2, x2, x16
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x3, [x0, #2520]
	ldr x2, [x0, #2392]
	and x2, x2, x17
	subs x3, x3, x2
	str x3, [x0, #2520]
	ldr x3, [x0, #2528]
	ldr x2, [x0, #2400]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2528]
	ldr x3, [x0, #2536]
	ldr x2, [x0, #2408]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	ldr x2, [x0, #2416]
	and x2, x2, x17
	sbcs x3, x3, x2
	str x3, [x0, #2544]
	ldr x2, [x0, #2512]
	movz x17, #48207, lsl #0
	movk x17, #60928, lsl #16
	movk x17, #51370, lsl #32
	movk x17, #52433, lsl #48
	mul x16, x2, x17
	ldr x3, [x0, #2544]
	lsr x9, x3, #63
	sub x9, x12, x9
	str x9, [x0, #2552]
	movz x10, #0, lsl #0
	ldr x2, [x0, #96]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2512]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2512]
	ldr x2, [x0, #104]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2520]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2520]
	ldr x2, [x0, #112]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2528]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2528]
	ldr x2, [x0, #120]
	mul x8, x16, x2
	umulh x9, x16, x2
	adds x8, x8, x10
	adc x9, x9, x12
	ldr x3, [x0, #2536]
	adds x3, x3, x8
	adc x10, x9, x12
	str x3, [x0, #2536]
	ldr x3, [x0, #2544]
	adds x3, x3, x10
	str x3, [x0, #2544]
	ldr x3, [x0, #2552]
	adcs x3, x3, x12
	str x3, [x0, #2552]
	ldr x2, [x0, #2520]
	str x2, [x0, #2392]
	ldr x2, [x0, #2528]
	str x2, [x0, #2400]
	ldr x2, [x0, #2536]
	str x2, [x0, #2408]
	ldr x2, [x0, #2544]
	str x2, [x0, #2416]
	ldr x2, [x0, #2552]
	str x2, [x0, #2424]
	ldr x2, [x0, #2432]
	str x2, [x0, #2352]
	ldr x2, [x0, #2440]
	str x2, [x0, #2360]
	ldr x2, [x0, #2448]
	str x2, [x0, #2368]
	ldr x2, [x0, #2456]
	str x2, [x0, #2376]
	ldr x2, [x0, #2464]
	str x2, [x0, #2384]
	cbnz x19, 23b
	movz x12, #0, lsl #0
	ldr x3, [x0, #2384]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #2352]
	ldr x2, [x0, #96]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #2352]
	ldr x3, [x0, #2360]
	ldr x2, [x0, #104]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2360]
	ldr x3, [x0, #2368]
	ldr x2, [x0, #112]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2368]
	ldr x3, [x0, #2376]
	ldr x2, [x0, #120]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2376]
	ldr x3, [x0, #2384]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #2384]
	ldr x3, [x0, #2352]
	ldr x2, [x0, #96]
	subs x3, x3, x2
	str x3, [x0, #2352]
	ldr x3, [x0, #2360]
	ldr x2, [x0, #104]
	sbcs x3, x3, x2
	str x3, [x0, #2360]
	ldr x3, [x0, #2368]
	ldr x2, [x0, #112]
	sbcs x3, x3, x2
	str x3, [x0, #2368]
	ldr x3, [x0, #2376]
	ldr x2, [x0, #120]
	sbcs x3, x3, x2
	str x3, [x0, #2376]
	ldr x3, [x0, #2384]
	add x2, x12, x12
	sbcs x3, x3, x2
	str x3, [x0, #2384]
	ldr x3, [x0, #2384]
	lsr x9, x3, #63
	sub x9, x12, x9
	ldr x3, [x0, #2352]
	ldr x2, [x0, #96]
	and x2, x2, x9
	adds x3, x3, x2
	str x3, [x0, #2352]
	ldr x3, [x0, #2360]
	ldr x2, [x0, #104]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2360]
	ldr x3, [x0, #2368]
	ldr x2, [x0, #112]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2368]
	ldr x3, [x0, #2376]
	ldr x2, [x0, #120]
	and x2, x2, x9
	adcs x3, x3, x2
	str x3, [x0, #2376]
	ldr x3, [x0, #2384]
	add x2, x12, x12
	adcs x3, x3, x2
	str x3, [x0, #2384]
	movz x12, #0, lsl #0
	ldr x3, [x0, #2272]
	lsr x9, x3, #63
	sub x9, x12, x9
	movz x2, #46200, lsl #0
	movk x2, #57457, lsl #16
	movk x2, #22743, lsl #32
	movk x2, #19242, lsl #48
	movz x3, #28889, lsl #0
	movk x3, #7153, lsl #16
	movk x3, #29163, lsl #32
	movk x3, #43151, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2432]
	movz x2, #48664, lsl #0
	movk x2, #30555, lsl #16
	movk x2, #54976, lsl #32
	movk x2, #15943, lsl #48
	movz x3, #57452, lsl #0
	movk x3, #12219, lsl #16
	movk x3, #9197, lsl #32
	movk x3, #32415, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2440]
	movz x2, #46111, lsl #0
	movk x2, #4367, lsl #16
	movk x2, #39065, lsl #32
	movk x2, #42236, lsl #48
	movz x3, #19424, lsl #0
	movk x3, #61168, lsl #16
	movk x3, #26470, lsl #32
	movk x3, #23299, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2448]
	movz x2, #56719, lsl #0
	movk x2, #37106, lsl #16
	movk x2, #9517, lsl #32
	movk x2, #19762, lsl #48
	movz x3, #8817, lsl #0
	movk x3, #28429, lsl #16
	movk x3, #56017, lsl #32
	movk x3, #45773, lsl #48
	eor x3, x3, x2
	and x3, x3, x9
	eor x2, x2, x3
	str x2, [x0, #2456]
	movz x7, #0, lsl #0
	ldr x4, [x0, #2432]
	ldr x5, [x0, #2440]
	ldr x16, [x0, #2448]
	ldr x17, [x0, #2456]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #2352]
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
	ldr x1, [x0, #2360]
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
	ldr x1, [x0, #2368]
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
	ldr x1, [x0, #2376]
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
	str x12, [x0, #992]
	str x13, [x0, #1000]
	str x8, [x0, #1008]
	str x9, [x0, #1016]
	movz x7, #0, lsl #0
	ldr x4, [x0, #384]
	ldr x5, [x0, #392]
	ldr x16, [x0, #400]
	ldr x17, [x0, #408]
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
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
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
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
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
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
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
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
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
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
	movz x6, #48207, lsl #0
	movk x6, #60928, lsl #16
	movk x6, #51370, lsl #32
	movk x6, #52433, lsl #48
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
	str x1, [x20, #24]
	ldr x1, [x0, #1224]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #16]
	ldr x1, [x0, #1232]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #8]
	ldr x1, [x0, #1240]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #0]
	ldr x1, [x0, #1440]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #56]
	ldr x1, [x0, #1448]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #48]
	ldr x1, [x0, #1456]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #40]
	ldr x1, [x0, #1464]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #32]
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
