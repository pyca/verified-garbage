// The functions of `src/ec_p192_compressed.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p192_compress_public_key:
	add x4, x2, #0
	add x6, x1, #0
	add x3, x1, #1
	add x1, x3, #0
	add x2, x3, #0
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
	ldr x5, [x3, #16]
	rev x5, x5
	str x5, [x0, #1056]
	ldr x5, [x3, #8]
	rev x5, x5
	str x5, [x0, #1064]
	ldr x5, [x3, #0]
	rev x5, x5
	str x5, [x0, #1072]
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	str x5, [x0, #1080]
	ldr x5, [x1, #16]
	rev x5, x5
	str x5, [x0, #1088]
	ldr x5, [x1, #8]
	rev x5, x5
	str x5, [x0, #1096]
	ldr x5, [x1, #0]
	rev x5, x5
	str x5, [x0, #1104]
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	str x5, [x0, #1112]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1120]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1128]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1136]
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	str x5, [x0, #1144]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #64]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #72]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #80]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #88]
	movz x1, #10289, lsl #0
	movk x1, #46290, lsl #16
	movk x1, #51633, lsl #32
	movk x1, #5227, lsl #48
	str x1, [x0, #96]
	movz x1, #63542, lsl #0
	movk x1, #39390, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #104]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #112]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
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
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #224]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #232]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #248]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #256]
	movz x1, #65531, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #264]
	movz x1, #65532, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #280]
	movz x1, #45361, lsl #0
	movk x1, #22464, lsl #16
	movk x1, #61125, lsl #32
	movk x1, #29640, lsl #48
	str x1, [x0, #288]
	movz x1, #60361, lsl #0
	movk x1, #65187, lsl #16
	movk x1, #53963, lsl #32
	movk x1, #54946, lsl #48
	str x1, [x0, #296]
	movz x1, #27362, lsl #0
	movk x1, #6407, lsl #16
	movk x1, #52658, lsl #32
	movk x1, #29313, lsl #48
	str x1, [x0, #304]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #312]
	movz x1, #6391, lsl #0
	movk x1, #62418, lsl #16
	movk x1, #51449, lsl #32
	movk x1, #38220, lsl #48
	str x1, [x0, #320]
	movz x1, #47615, lsl #0
	movk x1, #9985, lsl #16
	movk x1, #31750, lsl #32
	movk x1, #41689, lsl #48
	str x1, [x0, #328]
	movz x1, #10505, lsl #0
	movk x1, #30417, lsl #16
	movk x1, #54263, lsl #32
	movk x1, #35403, lsl #48
	str x1, [x0, #336]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #344]
	movz x1, #43085, lsl #0
	movk x1, #27373, lsl #16
	movk x1, #15747, lsl #32
	movk x1, #27177, lsl #48
	str x1, [x0, #352]
	movz x1, #51926, lsl #0
	movk x1, #35119, lsl #16
	movk x1, #57530, lsl #32
	movk x1, #58683, lsl #48
	str x1, [x0, #360]
	movz x1, #61534, lsl #0
	movk x1, #35174, lsl #16
	movk x1, #46372, lsl #32
	movk x1, #56866, lsl #48
	str x1, [x0, #368]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #376]
	movz x1, #19495, lsl #0
	movk x1, #33555, lsl #16
	movk x1, #30474, lsl #32
	movk x1, #465, lsl #48
	str x1, [x0, #384]
	movz x1, #26751, lsl #0
	movk x1, #51887, lsl #16
	movk x1, #26977, lsl #32
	movk x1, #54940, lsl #48
	str x1, [x0, #392]
	movz x1, #55493, lsl #0
	movk x1, #52981, lsl #16
	movk x1, #37572, lsl #32
	movk x1, #4711, lsl #48
	str x1, [x0, #400]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #416]
	movz x1, #55247, lsl #0
	movk x1, #19245, lsl #16
	movk x1, #13902, lsl #32
	movk x1, #60308, lsl #48
	str x1, [x0, #424]
	movz x1, #1993, lsl #0
	movk x1, #26145, lsl #16
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
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #544]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #552]
	movz x1, #1, lsl #0
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
	movz x1, #2, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1312]
	movz x1, #3, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1320]
	movz x1, #2, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1336]
	movz x1, #45361, lsl #0
	movk x1, #22464, lsl #16
	movk x1, #61125, lsl #32
	movk x1, #29640, lsl #48
	str x1, [x0, #1344]
	movz x1, #60361, lsl #0
	movk x1, #65187, lsl #16
	movk x1, #53963, lsl #32
	movk x1, #54946, lsl #48
	str x1, [x0, #1352]
	movz x1, #27362, lsl #0
	movk x1, #6407, lsl #16
	movk x1, #52658, lsl #32
	movk x1, #29313, lsl #48
	str x1, [x0, #1360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1368]
	add x2, x6, #25
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1216]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1224]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1232]
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	str x5, [x0, #1240]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	movz x5, #4, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	mov v28.d[0], x30
	bl {vg_p192_check_point}
	umov x30, v28.d[0]
	ldr x3, [x0, #1472]
	ldr x1, [x0, #1216]
	movz x2, #1, lsl #0
	and x1, x1, x2
	add x1, x1, #2
	and x1, x1, x3
	strb w1, [x20, #0]
	ldr x1, [x0, #1120]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #17
	str x1, [x17, #0]
	ldr x1, [x0, #1128]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #9
	str x1, [x17, #0]
	ldr x1, [x0, #1136]
	and x1, x1, x3
	rev x1, x1
	add x17, x20, #1
	str x1, [x17, #0]
	ldr x1, [x0, #1144]
	and x1, x1, x3
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

vg_ec_p192_decompress_public_key:
	add x4, x2, #0
	add x6, x1, #0
	add x3, x1, #1
	add x1, x3, #0
	add x2, x3, #0
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
	ldr x5, [x3, #16]
	rev x5, x5
	str x5, [x0, #1056]
	ldr x5, [x3, #8]
	rev x5, x5
	str x5, [x0, #1064]
	ldr x5, [x3, #0]
	rev x5, x5
	str x5, [x0, #1072]
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	str x5, [x0, #1080]
	ldr x5, [x1, #16]
	rev x5, x5
	str x5, [x0, #1088]
	ldr x5, [x1, #8]
	rev x5, x5
	str x5, [x0, #1096]
	ldr x5, [x1, #0]
	rev x5, x5
	str x5, [x0, #1104]
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	str x5, [x0, #1112]
	ldr x5, [x2, #16]
	rev x5, x5
	str x5, [x0, #1120]
	ldr x5, [x2, #8]
	rev x5, x5
	str x5, [x0, #1128]
	ldr x5, [x2, #0]
	rev x5, x5
	str x5, [x0, #1136]
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	str x5, [x0, #1144]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #64]
	movz x1, #65534, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #72]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #80]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #88]
	movz x1, #10289, lsl #0
	movk x1, #46290, lsl #16
	movk x1, #51633, lsl #32
	movk x1, #5227, lsl #48
	str x1, [x0, #96]
	movz x1, #63542, lsl #0
	movk x1, #39390, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #104]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #112]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
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
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #224]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #232]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #240]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #248]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #256]
	movz x1, #65531, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #264]
	movz x1, #65532, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #272]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #280]
	movz x1, #45361, lsl #0
	movk x1, #22464, lsl #16
	movk x1, #61125, lsl #32
	movk x1, #29640, lsl #48
	str x1, [x0, #288]
	movz x1, #60361, lsl #0
	movk x1, #65187, lsl #16
	movk x1, #53963, lsl #32
	movk x1, #54946, lsl #48
	str x1, [x0, #296]
	movz x1, #27362, lsl #0
	movk x1, #6407, lsl #16
	movk x1, #52658, lsl #32
	movk x1, #29313, lsl #48
	str x1, [x0, #304]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #312]
	movz x1, #6391, lsl #0
	movk x1, #62418, lsl #16
	movk x1, #51449, lsl #32
	movk x1, #38220, lsl #48
	str x1, [x0, #320]
	movz x1, #47615, lsl #0
	movk x1, #9985, lsl #16
	movk x1, #31750, lsl #32
	movk x1, #41689, lsl #48
	str x1, [x0, #328]
	movz x1, #10505, lsl #0
	movk x1, #30417, lsl #16
	movk x1, #54263, lsl #32
	movk x1, #35403, lsl #48
	str x1, [x0, #336]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #344]
	movz x1, #43085, lsl #0
	movk x1, #27373, lsl #16
	movk x1, #15747, lsl #32
	movk x1, #27177, lsl #48
	str x1, [x0, #352]
	movz x1, #51926, lsl #0
	movk x1, #35119, lsl #16
	movk x1, #57530, lsl #32
	movk x1, #58683, lsl #48
	str x1, [x0, #360]
	movz x1, #61534, lsl #0
	movk x1, #35174, lsl #16
	movk x1, #46372, lsl #32
	movk x1, #56866, lsl #48
	str x1, [x0, #368]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #376]
	movz x1, #19495, lsl #0
	movk x1, #33555, lsl #16
	movk x1, #30474, lsl #32
	movk x1, #465, lsl #48
	str x1, [x0, #384]
	movz x1, #26751, lsl #0
	movk x1, #51887, lsl #16
	movk x1, #26977, lsl #32
	movk x1, #54940, lsl #48
	str x1, [x0, #392]
	movz x1, #55493, lsl #0
	movk x1, #52981, lsl #16
	movk x1, #37572, lsl #32
	movk x1, #4711, lsl #48
	str x1, [x0, #400]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #408]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #416]
	movz x1, #55247, lsl #0
	movk x1, #19245, lsl #16
	movk x1, #13902, lsl #32
	movk x1, #60308, lsl #48
	str x1, [x0, #424]
	movz x1, #1993, lsl #0
	movk x1, #26145, lsl #16
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
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #544]
	movz x1, #1, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #552]
	movz x1, #1, lsl #0
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
	movz x1, #2, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1312]
	movz x1, #3, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1320]
	movz x1, #2, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1328]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1336]
	movz x1, #45361, lsl #0
	movk x1, #22464, lsl #16
	movk x1, #61125, lsl #32
	movk x1, #29640, lsl #48
	str x1, [x0, #1344]
	movz x1, #60361, lsl #0
	movk x1, #65187, lsl #16
	movk x1, #53963, lsl #32
	movk x1, #54946, lsl #48
	str x1, [x0, #1352]
	movz x1, #27362, lsl #0
	movk x1, #6407, lsl #16
	movk x1, #52658, lsl #32
	movk x1, #29313, lsl #48
	str x1, [x0, #1360]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #1368]
	movz x7, #0, lsl #0
	ldrb w1, [x6, #0]
	str x1, [x0, #1088]
	movz x5, #1, lsl #0
	orr x1, x1, x5
	movz x5, #3, lsl #0
	eor x1, x1, x5
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1120]
	ldr x2, [x0, #64]
	subs x16, x1, x2
	ldr x1, [x0, #1128]
	ldr x2, [x0, #72]
	sbcs x16, x1, x2
	ldr x1, [x0, #1136]
	ldr x2, [x0, #80]
	sbcs x16, x1, x2
	ldr x1, [x0, #1144]
	ldr x2, [x0, #88]
	sbcs x16, x1, x2
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	ldr x4, [x0, #1152]
	ldr x5, [x0, #1160]
	ldr x16, [x0, #1168]
	ldr x17, [x0, #1176]
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #1376]
	str x13, [x0, #1384]
	str x8, [x0, #1392]
	str x9, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1152]
	ldr x5, [x0, #1160]
	ldr x16, [x0, #1168]
	ldr x17, [x0, #1176]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1376]
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #1384]
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #1392]
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #1400]
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #1408]
	str x13, [x0, #1416]
	str x8, [x0, #1424]
	str x9, [x0, #1432]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1152]
	ldr x5, [x0, #1160]
	ldr x16, [x0, #1168]
	ldr x17, [x0, #1176]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #256]
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #264]
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #272]
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #280]
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #1376]
	str x13, [x0, #1384]
	str x8, [x0, #1392]
	str x9, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1408]
	ldr x9, [x0, #1416]
	ldr x10, [x0, #1424]
	ldr x11, [x0, #1432]
	ldr x2, [x0, #1376]
	adds x8, x8, x2
	ldr x2, [x0, #1384]
	adcs x9, x9, x2
	ldr x2, [x0, #1392]
	adcs x10, x10, x2
	ldr x2, [x0, #1400]
	adcs x11, x11, x2
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1280]
	ldr x9, [x0, #1288]
	ldr x10, [x0, #1296]
	ldr x11, [x0, #1304]
	ldr x2, [x0, #1344]
	adds x8, x8, x2
	ldr x2, [x0, #1352]
	adcs x9, x9, x2
	ldr x2, [x0, #1360]
	adcs x10, x10, x2
	ldr x2, [x0, #1368]
	adcs x11, x11, x2
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
	str x8, [x0, #1408]
	str x9, [x0, #1416]
	str x10, [x0, #1424]
	str x11, [x0, #1432]
	ldr x1, [x0, #1408]
	str x1, [x0, #512]
	ldr x1, [x0, #1416]
	str x1, [x0, #520]
	ldr x1, [x0, #1424]
	str x1, [x0, #528]
	ldr x1, [x0, #1432]
	str x1, [x0, #536]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1408]
	ldr x5, [x0, #1416]
	ldr x16, [x0, #1424]
	ldr x17, [x0, #1432]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #768]
	str x13, [x0, #776]
	str x8, [x0, #784]
	str x9, [x0, #792]
	movz x7, #0, lsl #0
	ldr x4, [x0, #768]
	ldr x5, [x0, #776]
	ldr x16, [x0, #784]
	ldr x17, [x0, #792]
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #544]
	str x13, [x0, #552]
	str x8, [x0, #560]
	str x9, [x0, #568]
	movz x7, #0, lsl #0
	ldr x4, [x0, #768]
	ldr x5, [x0, #776]
	ldr x16, [x0, #784]
	ldr x17, [x0, #792]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x7, #0, lsl #0
	ldr x4, [x0, #768]
	ldr x5, [x0, #776]
	ldr x16, [x0, #784]
	ldr x17, [x0, #792]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #608]
	str x13, [x0, #616]
	str x8, [x0, #624]
	str x9, [x0, #632]
	movz x7, #0, lsl #0
	ldr x4, [x0, #768]
	ldr x5, [x0, #776]
	ldr x16, [x0, #784]
	ldr x17, [x0, #792]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #608]
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #616]
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #624]
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #632]
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #640]
	str x13, [x0, #648]
	str x8, [x0, #656]
	str x9, [x0, #664]
	movz x7, #0, lsl #0
	ldr x4, [x0, #768]
	ldr x5, [x0, #776]
	ldr x16, [x0, #784]
	ldr x17, [x0, #792]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #640]
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #648]
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #656]
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #664]
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	ldr x4, [x0, #768]
	ldr x5, [x0, #776]
	ldr x16, [x0, #784]
	ldr x17, [x0, #792]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #672]
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #680]
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #688]
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #696]
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #704]
	str x13, [x0, #712]
	str x8, [x0, #720]
	str x9, [x0, #728]
	movz x7, #0, lsl #0
	ldr x4, [x0, #768]
	ldr x5, [x0, #776]
	ldr x16, [x0, #784]
	ldr x17, [x0, #792]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #736]
	str x13, [x0, #744]
	str x8, [x0, #752]
	str x9, [x0, #760]
	ldr x1, [x0, #736]
	str x1, [x0, #992]
	ldr x1, [x0, #744]
	str x1, [x0, #1000]
	ldr x1, [x0, #752]
	str x1, [x0, #1008]
	ldr x1, [x0, #760]
	str x1, [x0, #1016]
	movz x19, #4, lsl #0
20:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 20b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
21:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 21b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
22:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 22b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
23:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 23b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
24:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 24b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
25:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 25b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
26:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 26b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
27:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 27b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
28:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 28b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
29:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 29b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
210:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 210b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
211:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 211b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
212:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 212b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
213:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 213b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
214:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 214b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
215:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 215b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
216:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 216b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
217:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 217b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
218:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 218b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
219:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 219b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
220:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 220b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
221:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 221b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
222:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 222b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
223:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 223b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
224:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 224b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
225:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 225b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
226:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 226b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
227:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 227b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
228:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 228b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
229:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 229b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #4, lsl #0
230:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 230b
	movz x7, #0, lsl #0
	ldr x4, [x0, #736]
	ldr x5, [x0, #744]
	ldr x16, [x0, #752]
	ldr x17, [x0, #760]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	movz x19, #62, lsl #0
231:
	sub x19, x19, #1
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	cbnz x19, 231b
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #1216]
	str x13, [x0, #1224]
	str x8, [x0, #1232]
	str x9, [x0, #1240]
	movz x7, #0, lsl #0
	ldr x8, [x0, #160]
	ldr x9, [x0, #168]
	ldr x10, [x0, #176]
	ldr x11, [x0, #184]
	ldr x2, [x0, #1216]
	subs x8, x8, x2
	ldr x2, [x0, #1224]
	sbcs x9, x9, x2
	ldr x2, [x0, #1232]
	sbcs x10, x10, x2
	ldr x2, [x0, #1240]
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
	str x8, [x0, #1248]
	str x9, [x0, #1256]
	str x10, [x0, #1264]
	str x11, [x0, #1272]
	ldr x1, [x0, #1216]
	ldr x2, [x0, #1088]
	eor x2, x2, x1
	movz x1, #1, lsl #0
	and x2, x2, x1
	movz x7, #0, lsl #0
	sub x3, x7, x2
	ldr x1, [x0, #1216]
	ldr x2, [x0, #1248]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1216]
	ldr x1, [x0, #1224]
	ldr x2, [x0, #1256]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1224]
	ldr x1, [x0, #1232]
	ldr x2, [x0, #1264]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1232]
	ldr x1, [x0, #1240]
	ldr x2, [x0, #1272]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #1240]
	movz x7, #0, lsl #0
	ldr x4, [x0, #1312]
	ldr x5, [x0, #1320]
	ldr x16, [x0, #1328]
	ldr x17, [x0, #1336]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	ldr x4, [x0, #1184]
	ldr x5, [x0, #1192]
	ldr x16, [x0, #1200]
	ldr x17, [x0, #1208]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	ldr x1, [x0, #1184]
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
	mul x2, x8, x6
	adds x9, x9, x2
	mul x2, x8, x6
	adcs x10, x10, x2
	umulh x2, x8, x6
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	umulh x2, x8, x6
	adds x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	movz x8, #0, lsl #0
	ldr x1, [x0, #1192]
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
	mul x2, x9, x6
	adds x10, x10, x2
	mul x2, x9, x6
	adcs x11, x11, x2
	umulh x2, x9, x6
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	umulh x2, x9, x6
	adds x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x0, #1200]
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
	mul x2, x10, x6
	adds x11, x11, x2
	mul x2, x10, x6
	adcs x12, x12, x2
	umulh x2, x10, x6
	adcs x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	umulh x2, x10, x6
	adds x12, x12, x2
	adcs x13, x13, x7
	adcs x8, x8, x7
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x0, #1208]
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
	mul x2, x11, x6
	adds x12, x12, x2
	mul x2, x11, x6
	adcs x13, x13, x2
	umulh x2, x11, x6
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	umulh x2, x11, x6
	adds x13, x13, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
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
	str x12, [x0, #1376]
	str x13, [x0, #1384]
	str x8, [x0, #1392]
	str x9, [x0, #1400]
	movz x7, #0, lsl #0
	ldr x8, [x0, #1376]
	ldr x9, [x0, #1384]
	ldr x10, [x0, #1392]
	ldr x11, [x0, #1400]
	ldr x2, [x0, #1408]
	subs x8, x8, x2
	ldr x2, [x0, #1416]
	sbcs x9, x9, x2
	ldr x2, [x0, #1424]
	sbcs x10, x10, x2
	ldr x2, [x0, #1432]
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
	str x8, [x0, #1280]
	str x9, [x0, #1288]
	str x10, [x0, #1296]
	str x11, [x0, #1304]
	movz x7, #0, lsl #0
	ldr x1, [x0, #1280]
	ldr x2, [x0, #1288]
	orr x1, x1, x2
	ldr x2, [x0, #1296]
	orr x1, x1, x2
	ldr x2, [x0, #1304]
	orr x1, x1, x2
	movz x5, #1, lsl #0
	subs x16, x1, x5
	sbc x2, x7, x7
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	ldr x1, [x0, #1216]
	ldr x2, [x0, #1088]
	eor x2, x2, x1
	movz x1, #1, lsl #0
	and x2, x2, x1
	movz x7, #0, lsl #0
	sub x3, x7, x2
	movz x7, #0, lsl #0
	add x2, x3, #1
	sub x2, x7, x2
	ldr x1, [x0, #1472]
	and x1, x1, x2
	str x1, [x0, #1472]
	ldr x3, [x0, #1472]
	movz x1, #4, lsl #0
	and x1, x1, x3
	strb w1, [x20, #0]
	add x6, x20, #1
	ldr x1, [x0, #1120]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #16]
	ldr x1, [x0, #1128]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #8]
	ldr x1, [x0, #1136]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #0]
	ldr x1, [x0, #1144]
	and x1, x1, x3
	ldr x1, [x0, #1216]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #40]
	ldr x1, [x0, #1224]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #32]
	ldr x1, [x0, #1232]
	and x1, x1, x3
	rev x1, x1
	str x1, [x6, #24]
	ldr x1, [x0, #1240]
	and x1, x1, x3
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
