// The functions of `src/internal/vg_ecdsa_p256_sign_k.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p256_sign_k:
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
	bl {vg_p256_comb}
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
21:
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
	cbnz x19, 21b
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
	cbnz x19, 22b
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
