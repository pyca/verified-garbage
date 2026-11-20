// The functions of `src/ecdh_brainpoolp320r1.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_brainpoolp320r1:
	add x4, x3, #0
	add x6, x2, #0
	add x3, x1, #0
	add x2, x2, #1
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
	ldr x5, [x3, #32]
	rev x5, x5
	str x5, [x0, #1304]
	ldr x5, [x3, #24]
	rev x5, x5
	str x5, [x0, #1312]
	ldr x5, [x3, #16]
	rev x5, x5
	str x5, [x0, #1320]
	ldr x5, [x3, #8]
	rev x5, x5
	str x5, [x0, #1328]
	ldr x5, [x3, #0]
	rev x5, x5
	str x5, [x0, #1336]
	ldr x5, [x1, #32]
	rev x5, x5
	str x5, [x0, #1344]
	ldr x5, [x1, #24]
	rev x5, x5
	str x5, [x0, #1352]
	ldr x5, [x1, #16]
	rev x5, x5
	str x5, [x0, #1360]
	ldr x5, [x1, #8]
	rev x5, x5
	str x5, [x0, #1368]
	ldr x5, [x1, #0]
	rev x5, x5
	str x5, [x0, #1376]
	ldr x5, [x2, #32]
	rev x5, x5
	str x5, [x0, #1384]
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #1392]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1400]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1408]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1416]
	movz x1, #11815, lsl #0
	movk x1, #61875, lsl #16
	movk x1, #4785, lsl #32
	movk x1, #64724, lsl #48
	str x1, [x0, #64]
	movz x1, #60456, lsl #0
	movk x1, #30867, lsl #16
	movk x1, #47596, lsl #32
	movk x1, #20370, lsl #48
	str x1, [x0, #72]
	movz x1, #3567, lsl #0
	movk x1, #63220, lsl #16
	movk x1, #53158, lsl #32
	movk x1, #63887, lsl #48
	str x1, [x0, #80]
	movz x1, #57445, lsl #0
	movk x1, #53761, lsl #16
	movk x1, #30814, lsl #32
	movk x1, #57660, lsl #48
	str x1, [x0, #88]
	movz x1, #20407, lsl #0
	movk x1, #14012, lsl #16
	movk x1, #18208, lsl #32
	movk x1, #54110, lsl #48
	str x1, [x0, #96]
	movz x1, #37649, lsl #0
	movk x1, #17605, lsl #16
	movk x1, #21851, lsl #32
	movk x1, #34449, lsl #48
	str x1, [x0, #104]
	movz x1, #22761, lsl #0
	movk x1, #61062, lsl #16
	movk x1, #11975, lsl #32
	movk x1, #11592, lsl #48
	str x1, [x0, #112]
	movz x1, #4771, lsl #0
	movk x1, #46735, lsl #16
	movk x1, #53157, lsl #32
	movk x1, #63887, lsl #48
	str x1, [x0, #120]
	movz x1, #57445, lsl #0
	movk x1, #53761, lsl #16
	movk x1, #30814, lsl #32
	movk x1, #57660, lsl #48
	str x1, [x0, #128]
	movz x1, #20407, lsl #0
	movk x1, #14012, lsl #16
	movk x1, #18208, lsl #32
	movk x1, #54110, lsl #48
	str x1, [x0, #136]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #184]
	movz x1, #0, lsl #0
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
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
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
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #256]
	movz x1, #53721, lsl #0
	movk x1, #3660, lsl #16
	movk x1, #60750, lsl #32
	movk x1, #811, lsl #48
	str x1, [x0, #264]
	movz x1, #5079, lsl #0
	movk x1, #34668, lsl #16
	movk x1, #17939, lsl #32
	movk x1, #45165, lsl #48
	str x1, [x0, #272]
	movz x1, #61968, lsl #0
	movk x1, #2315, lsl #16
	movk x1, #12377, lsl #32
	movk x1, #1648, lsl #48
	str x1, [x0, #280]
	movz x1, #8090, lsl #0
	movk x1, #11774, lsl #16
	movk x1, #34721, lsl #32
	movk x1, #7875, lsl #48
	str x1, [x0, #288]
	movz x1, #45128, lsl #0
	movk x1, #51523, lsl #16
	movk x1, #47327, lsl #32
	movk x1, #11425, lsl #48
	str x1, [x0, #296]
	movz x1, #13730, lsl #0
	movk x1, #3953, lsl #16
	movk x1, #62075, lsl #32
	movk x1, #8371, lsl #48
	str x1, [x0, #304]
	movz x1, #57222, lsl #0
	movk x1, #41922, lsl #16
	movk x1, #27245, lsl #32
	movk x1, #1012, lsl #48
	str x1, [x0, #312]
	movz x1, #45075, lsl #0
	movk x1, #48024, lsl #16
	movk x1, #41953, lsl #32
	movk x1, #41273, lsl #48
	str x1, [x0, #320]
	movz x1, #14047, lsl #0
	movk x1, #52715, lsl #16
	movk x1, #39144, lsl #32
	movk x1, #14901, lsl #48
	str x1, [x0, #328]
	movz x1, #40294, lsl #0
	movk x1, #52930, lsl #16
	movk x1, #47289, lsl #32
	movk x1, #18043, lsl #48
	str x1, [x0, #336]
	movz x1, #56090, lsl #0
	movk x1, #49137, lsl #16
	movk x1, #22776, lsl #32
	movk x1, #51502, lsl #48
	str x1, [x0, #344]
	movz x1, #31493, lsl #0
	movk x1, #8324, lsl #16
	movk x1, #48094, lsl #32
	movk x1, #5306, lsl #48
	str x1, [x0, #352]
	movz x1, #36601, lsl #0
	movk x1, #38493, lsl #16
	movk x1, #57818, lsl #32
	movk x1, #6230, lsl #48
	str x1, [x0, #360]
	movz x1, #269, lsl #0
	movk x1, #8861, lsl #16
	movk x1, #40050, lsl #32
	movk x1, #37242, lsl #48
	str x1, [x0, #368]
	movz x1, #21352, lsl #0
	movk x1, #10632, lsl #16
	movk x1, #45002, lsl #32
	movk x1, #37686, lsl #48
	str x1, [x0, #376]
	movz x1, #2745, lsl #0
	movk x1, #23932, lsl #16
	movk x1, #24176, lsl #32
	movk x1, #48530, lsl #48
	str x1, [x0, #384]
	movz x1, #61691, lsl #0
	movk x1, #57036, lsl #16
	movk x1, #65188, lsl #32
	movk x1, #61040, lsl #48
	str x1, [x0, #392]
	movz x1, #37790, lsl #0
	movk x1, #7421, lsl #16
	movk x1, #64560, lsl #32
	movk x1, #28714, lsl #48
	str x1, [x0, #400]
	movz x1, #8691, lsl #0
	movk x1, #48978, lsl #16
	movk x1, #60931, lsl #32
	movk x1, #22095, lsl #48
	str x1, [x0, #408]
	movz x1, #62692, lsl #0
	movk x1, #16819, lsl #16
	movk x1, #63667, lsl #32
	movk x1, #17518, lsl #48
	str x1, [x0, #416]
	movz x1, #24908, lsl #0
	movk x1, #18380, lsl #16
	movk x1, #14215, lsl #32
	movk x1, #21505, lsl #48
	str x1, [x0, #424]
	movz x1, #57977, lsl #0
	movk x1, #32798, lsl #16
	movk x1, #34311, lsl #32
	movk x1, #50815, lsl #48
	str x1, [x0, #432]
	movz x1, #3063, lsl #0
	movk x1, #44863, lsl #16
	movk x1, #17238, lsl #32
	movk x1, #21523, lsl #48
	str x1, [x0, #440]
	movz x1, #48761, lsl #0
	movk x1, #33253, lsl #16
	movk x1, #6689, lsl #32
	movk x1, #64362, lsl #48
	str x1, [x0, #448]
	movz x1, #43914, lsl #0
	movk x1, #48500, lsl #16
	movk x1, #37762, lsl #32
	movk x1, #30362, lsl #48
	str x1, [x0, #456]
	movz x1, #58573, lsl #0
	movk x1, #9491, lsl #16
	movk x1, #10719, lsl #32
	movk x1, #26525, lsl #48
	str x1, [x0, #464]
	movz x1, #26629, lsl #0
	movk x1, #57569, lsl #16
	movk x1, #27, lsl #32
	movk x1, #37315, lsl #48
	str x1, [x0, #472]
	movz x1, #50185, lsl #0
	movk x1, #44934, lsl #16
	movk x1, #12476, lsl #32
	movk x1, #34483, lsl #48
	str x1, [x0, #480]
	movz x1, #37118, lsl #0
	movk x1, #20067, lsl #16
	movk x1, #13604, lsl #32
	movk x1, #58125, lsl #48
	str x1, [x0, #488]
	movz x1, #45391, lsl #0
	movk x1, #12800, lsl #16
	movk x1, #34759, lsl #32
	movk x1, #12780, lsl #48
	str x1, [x0, #496]
	movz x1, #27887, lsl #0
	movk x1, #47930, lsl #16
	movk x1, #43684, lsl #32
	movk x1, #31086, lsl #48
	str x1, [x0, #504]
	movz x1, #42774, lsl #0
	movk x1, #4473, lsl #16
	movk x1, #53560, lsl #32
	movk x1, #53943, lsl #48
	str x1, [x0, #512]
	movz x1, #60764, lsl #0
	movk x1, #18800, lsl #16
	movk x1, #12378, lsl #32
	movk x1, #1648, lsl #48
	str x1, [x0, #520]
	movz x1, #8090, lsl #0
	movk x1, #11774, lsl #16
	movk x1, #34721, lsl #32
	movk x1, #7875, lsl #48
	str x1, [x0, #528]
	movz x1, #45128, lsl #0
	movk x1, #51523, lsl #16
	movk x1, #47327, lsl #32
	movk x1, #11425, lsl #48
	str x1, [x0, #536]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #624]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #632]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #640]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #648]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #656]
	movz x1, #53721, lsl #0
	movk x1, #3660, lsl #16
	movk x1, #60750, lsl #32
	movk x1, #811, lsl #48
	str x1, [x0, #664]
	movz x1, #5079, lsl #0
	movk x1, #34668, lsl #16
	movk x1, #17939, lsl #32
	movk x1, #45165, lsl #48
	str x1, [x0, #672]
	movz x1, #61968, lsl #0
	movk x1, #2315, lsl #16
	movk x1, #12377, lsl #32
	movk x1, #1648, lsl #48
	str x1, [x0, #680]
	movz x1, #8090, lsl #0
	movk x1, #11774, lsl #16
	movk x1, #34721, lsl #32
	movk x1, #7875, lsl #48
	str x1, [x0, #688]
	movz x1, #45128, lsl #0
	movk x1, #51523, lsl #16
	movk x1, #47327, lsl #32
	movk x1, #11425, lsl #48
	str x1, [x0, #696]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #704]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #712]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #720]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #728]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #736]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #1824]
	movz x19, #40, lsl #0
	movz x5, #1, lsl #0
20:
	sub x19, x19, #1
	add x16, x0, x19
	ldrb w1, [x16, #1304]
	lsl x17, x19, #3
	add x17, x0, x17
	and x2, x1, x5
	strb w2, [x17, #1864]
	lsr x2, x1, #1
	and x2, x2, x5
	strb w2, [x17, #1865]
	lsr x2, x1, #2
	and x2, x2, x5
	strb w2, [x17, #1866]
	lsr x2, x1, #3
	and x2, x2, x5
	strb w2, [x17, #1867]
	lsr x2, x1, #4
	and x2, x2, x5
	strb w2, [x17, #1868]
	lsr x2, x1, #5
	and x2, x2, x5
	strb w2, [x17, #1869]
	lsr x2, x1, #6
	and x2, x2, x5
	strb w2, [x17, #1870]
	lsr x2, x1, #7
	and x2, x2, x5
	strb w2, [x17, #1871]
	cbnz x19, 20b
	movz x1, #21241, lsl #0
	movk x1, #29755, lsl #16
	movk x1, #59530, lsl #32
	movk x1, #39246, lsl #48
	str x1, [x0, #1624]
	movz x1, #30959, lsl #0
	movk x1, #36969, lsl #16
	movk x1, #35469, lsl #32
	movk x1, #49735, lsl #48
	str x1, [x0, #1632]
	movz x1, #46710, lsl #0
	movk x1, #12485, lsl #16
	movk x1, #34847, lsl #32
	movk x1, #8012, lsl #48
	str x1, [x0, #1640]
	movz x1, #54994, lsl #0
	movk x1, #58900, lsl #16
	movk x1, #43364, lsl #32
	movk x1, #21589, lsl #48
	str x1, [x0, #1648]
	movz x1, #37458, lsl #0
	movk x1, #27693, lsl #16
	movk x1, #47690, lsl #32
	movk x1, #41561, lsl #48
	str x1, [x0, #1656]
	movz x1, #56090, lsl #0
	movk x1, #49137, lsl #16
	movk x1, #22776, lsl #32
	movk x1, #51502, lsl #48
	str x1, [x0, #1664]
	movz x1, #31493, lsl #0
	movk x1, #8324, lsl #16
	movk x1, #48094, lsl #32
	movk x1, #5306, lsl #48
	str x1, [x0, #1672]
	movz x1, #36601, lsl #0
	movk x1, #38493, lsl #16
	movk x1, #57818, lsl #32
	movk x1, #6230, lsl #48
	str x1, [x0, #1680]
	movz x1, #269, lsl #0
	movk x1, #8861, lsl #16
	movk x1, #40050, lsl #32
	movk x1, #37242, lsl #48
	str x1, [x0, #1688]
	movz x1, #21352, lsl #0
	movk x1, #10632, lsl #16
	movk x1, #45002, lsl #32
	movk x1, #37686, lsl #48
	str x1, [x0, #1696]
	add x2, x6, #41
	ldr x5, [x2, #32]
	rev x5, x5
	str x5, [x0, #1504]
	ldr x5, [x2, #24]
	rev x5, x5
	str x5, [x0, #1512]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1520]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1528]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1536]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	movz x5, #4, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #1824]
	and x1, x1, x2
	str x1, [x0, #1824]
	mov v28.d[0], x30
	bl {vg_brainpoolp320r1_check_point}
	umov x30, v28.d[0]
	movz x1, #13568, lsl #0
	movk x1, #23663, lsl #16
	movk x1, #58758, lsl #32
	movk x1, #25058, lsl #48
	str x1, [x0, #544]
	movz x1, #39103, lsl #0
	movk x1, #28773, lsl #16
	movk x1, #49089, lsl #32
	movk x1, #40714, lsl #48
	str x1, [x0, #552]
	movz x1, #37132, lsl #0
	movk x1, #54576, lsl #16
	movk x1, #1601, lsl #32
	movk x1, #21989, lsl #48
	str x1, [x0, #560]
	movz x1, #16987, lsl #0
	movk x1, #50131, lsl #16
	movk x1, #58520, lsl #32
	movk x1, #61942, lsl #48
	str x1, [x0, #568]
	movz x1, #23241, lsl #0
	movk x1, #3872, lsl #16
	movk x1, #33054, lsl #32
	movk x1, #4839, lsl #48
	str x1, [x0, #576]
	ldr x1, [x0, #1584]
	str x1, [x0, #624]
	ldr x1, [x0, #1592]
	str x1, [x0, #632]
	ldr x1, [x0, #1600]
	str x1, [x0, #640]
	ldr x1, [x0, #1608]
	str x1, [x0, #648]
	ldr x1, [x0, #1616]
	str x1, [x0, #656]
	ldr x1, [x0, #1784]
	str x1, [x0, #664]
	ldr x1, [x0, #1792]
	str x1, [x0, #672]
	ldr x1, [x0, #1800]
	str x1, [x0, #680]
	ldr x1, [x0, #1808]
	str x1, [x0, #688]
	ldr x1, [x0, #1816]
	str x1, [x0, #696]
	movz x1, #13568, lsl #0
	movk x1, #23663, lsl #16
	movk x1, #58758, lsl #32
	movk x1, #25058, lsl #48
	str x1, [x0, #344]
	movz x1, #39103, lsl #0
	movk x1, #28773, lsl #16
	movk x1, #49089, lsl #32
	movk x1, #40714, lsl #48
	str x1, [x0, #352]
	movz x1, #37132, lsl #0
	movk x1, #54576, lsl #16
	movk x1, #1601, lsl #32
	movk x1, #21989, lsl #48
	str x1, [x0, #360]
	movz x1, #16987, lsl #0
	movk x1, #50131, lsl #16
	movk x1, #58520, lsl #32
	movk x1, #61942, lsl #48
	str x1, [x0, #368]
	movz x1, #23241, lsl #0
	movk x1, #3872, lsl #16
	movk x1, #33054, lsl #32
	movk x1, #4839, lsl #48
	str x1, [x0, #376]
	mov v29.d[0], x30
	bl {vg_brainpoolp320r1_mul}
	umov x30, v29.d[0]
	movz x1, #56090, lsl #0
	movk x1, #49137, lsl #16
	movk x1, #22776, lsl #32
	movk x1, #51502, lsl #48
	str x1, [x0, #344]
	movz x1, #31493, lsl #0
	movk x1, #8324, lsl #16
	movk x1, #48094, lsl #32
	movk x1, #5306, lsl #48
	str x1, [x0, #352]
	movz x1, #36601, lsl #0
	movk x1, #38493, lsl #16
	movk x1, #57818, lsl #32
	movk x1, #6230, lsl #48
	str x1, [x0, #360]
	movz x1, #269, lsl #0
	movk x1, #8861, lsl #16
	movk x1, #40050, lsl #32
	movk x1, #37242, lsl #48
	str x1, [x0, #368]
	movz x1, #21352, lsl #0
	movk x1, #10632, lsl #16
	movk x1, #45002, lsl #32
	movk x1, #37686, lsl #48
	str x1, [x0, #376]
	mov v29.d[0], x30
	bl {vg_brainpoolp320r1_inv_mod_p}
	umov x30, v29.d[0]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1224]
	ldr x5, [x0, #1232]
	ldr x16, [x0, #1240]
	ldr x17, [x0, #1248]
	movz x6, #40553, lsl #0
	movk x6, #10890, lsl #16
	movk x6, #39842, lsl #32
	movk x6, #15646, lsl #48
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	ldr x1, [x0, #624]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x0, #1256]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #1256]
	umulh x2, x1, x3
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	adcs x13, x13, x7
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x14, x14, x7
	ldr x1, [x0, #632]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #1256]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #1256]
	umulh x2, x1, x3
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	adcs x14, x14, x7
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x14, x14, x2
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	adcs x8, x8, x7
	ldr x1, [x0, #640]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #1256]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #1256]
	umulh x2, x1, x3
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #96]
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #648]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #1256]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #1256]
	umulh x2, x1, x3
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
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
	adcs x14, x14, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #96]
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
	adcs x14, x14, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x1, [x0, #656]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #1256]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #1256]
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	adcs x10, x10, x7
	mul x1, x12, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x2, [x0, #64]
	subs x1, x13, x2
	ldr x2, [x0, #72]
	sbcs x3, x14, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	ldr x2, [x0, #96]
	sbcs x6, x10, x2
	sbcs x2, x11, x7
	csel x13, x1, x13, hs
	csel x14, x3, x14, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	str x13, [x0, #1424]
	str x14, [x0, #1432]
	str x8, [x0, #1440]
	str x9, [x0, #1448]
	str x10, [x0, #1456]
	movz x7, #0, lsl #0
	ldr x4, [x0, #224]
	ldr x5, [x0, #232]
	ldr x16, [x0, #240]
	ldr x17, [x0, #248]
	movz x6, #40553, lsl #0
	movk x6, #10890, lsl #16
	movk x6, #39842, lsl #32
	movk x6, #15646, lsl #48
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	ldr x1, [x0, #1424]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x0, #256]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #256]
	umulh x2, x1, x3
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	adcs x13, x13, x7
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x14, x14, x7
	ldr x1, [x0, #1432]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x0, #256]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #256]
	umulh x2, x1, x3
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	adcs x14, x14, x7
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x14, x14, x2
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	adcs x8, x8, x7
	ldr x1, [x0, #1440]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x0, #256]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #256]
	umulh x2, x1, x3
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
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
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #96]
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
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x0, #1448]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x0, #256]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #256]
	umulh x2, x1, x3
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
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
	adcs x14, x14, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #96]
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
	adcs x14, x14, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x1, [x0, #1456]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x0, #256]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #256]
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	adcs x10, x10, x7
	mul x1, x12, x6
	ldr x3, [x0, #64]
	mul x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #72]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #80]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #88]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #96]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #96]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	ldr x3, [x0, #64]
	umulh x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #72]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #80]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #88]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x2, [x0, #64]
	subs x1, x13, x2
	ldr x2, [x0, #72]
	sbcs x3, x14, x2
	ldr x2, [x0, #80]
	sbcs x4, x8, x2
	ldr x2, [x0, #88]
	sbcs x5, x9, x2
	ldr x2, [x0, #96]
	sbcs x6, x10, x2
	sbcs x2, x11, x7
	csel x13, x1, x13, hs
	csel x14, x3, x14, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	str x13, [x0, #1464]
	str x14, [x0, #1472]
	str x8, [x0, #1480]
	str x9, [x0, #1488]
	str x10, [x0, #1496]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1344]
	ldr x2, [x0, #104]
	subs x16, x1, x2
	ldr x1, [x0, #1352]
	ldr x2, [x0, #112]
	sbcs x16, x1, x2
	ldr x1, [x0, #1360]
	ldr x2, [x0, #120]
	sbcs x16, x1, x2
	ldr x1, [x0, #1368]
	ldr x2, [x0, #128]
	sbcs x16, x1, x2
	ldr x1, [x0, #1376]
	ldr x2, [x0, #136]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	add x4, x2, #0
	movz x7, #0, lsl #0
	ldr x1, [x0, #1344]
	ldr x2, [x0, #1352]
	orr x1, x1, x2
	ldr x2, [x0, #1360]
	orr x1, x1, x2
	ldr x2, [x0, #1368]
	orr x1, x1, x2
	ldr x2, [x0, #1376]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	and x2, x2, x4
	ldr x1, [x0, #1824]
	and x1, x1, x2
	str x1, [x0, #1824]
	movz x7, #0, lsl #0
	ldr x1, [x0, #704]
	ldr x2, [x0, #712]
	orr x1, x1, x2
	ldr x2, [x0, #720]
	orr x1, x1, x2
	ldr x2, [x0, #728]
	orr x1, x1, x2
	ldr x2, [x0, #736]
	orr x1, x1, x2
	subs x16, x7, x1
	sbc x2, x7, x7
	ldr x1, [x0, #1824]
	and x1, x1, x2
	str x1, [x0, #1824]
	ldr x3, [x0, #1824]
	ldr x1, [x0, #1464]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #32]
	ldr x1, [x0, #1472]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #24]
	ldr x1, [x0, #1480]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #16]
	ldr x1, [x0, #1488]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #8]
	ldr x1, [x0, #1496]
	and x1, x1, x3
	rev x1, x1
	str x1, [x20, #0]
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
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v28.2d, #0
	movi v29.2d, #0
	tst x1, x1
	add w0, w0, #0
	ret
	.p2align 6
