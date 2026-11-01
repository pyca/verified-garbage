// The functions of `src/sm4_ofb.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ofb:
	sub sp, sp, #3264
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #3168]
	str x20, [x5, #3176]
	str x21, [x5, #3184]
	str x22, [x5, #3192]
	str x23, [x5, #3200]
	str x24, [x5, #3208]
	str x25, [x5, #3216]
	str x26, [x5, #3224]
	str x27, [x5, #3232]
	str x28, [x5, #3240]
	add x19, x1, #0
	add x23, x2, #0
	add x24, x3, #0
	movz x21, #37078, lsl #0
	movk x21, #65257, lsl #16
	movk x21, #57804, lsl #32
	movk x21, #46909, lsl #48
	str x21, [x5, #0]
	movz x21, #46614, lsl #0
	movk x21, #49684, lsl #16
	movk x21, #64296, lsl #32
	movk x21, #1324, lsl #48
	str x21, [x5, #8]
	movz x21, #26411, lsl #0
	movk x21, #30362, lsl #16
	movk x21, #48682, lsl #32
	movk x21, #49924, lsl #48
	str x21, [x5, #16]
	movz x21, #17578, lsl #0
	movk x21, #9747, lsl #16
	movk x21, #34377, lsl #32
	movk x21, #39174, lsl #48
	str x21, [x5, #24]
	movz x21, #17052, lsl #0
	movk x21, #62544, lsl #16
	movk x21, #61329, lsl #32
	movk x21, #31384, lsl #48
	str x21, [x5, #32]
	movz x21, #21555, lsl #0
	movk x21, #17163, lsl #16
	movk x21, #53229, lsl #32
	movk x21, #25260, lsl #48
	str x21, [x5, #40]
	movz x21, #46052, lsl #0
	movk x21, #43292, lsl #16
	movk x21, #2249, lsl #32
	movk x21, #38376, lsl #48
	str x21, [x5, #48]
	movz x21, #57216, lsl #0
	movk x21, #64148, lsl #16
	movk x21, #36725, lsl #32
	movk x21, #42559, lsl #48
	str x21, [x5, #56]
	movz x21, #1863, lsl #0
	movk x21, #64679, lsl #16
	movk x21, #29683, lsl #32
	movk x21, #47639, lsl #48
	str x21, [x5, #64]
	movz x21, #22915, lsl #0
	movk x21, #6460, lsl #16
	movk x21, #34278, lsl #32
	movk x21, #43087, lsl #48
	str x21, [x5, #72]
	movz x21, #27496, lsl #0
	movk x21, #45697, lsl #16
	movk x21, #25713, lsl #32
	movk x21, #35802, lsl #48
	str x21, [x5, #80]
	movz x21, #60408, lsl #0
	movk x21, #19215, lsl #16
	movk x21, #22128, lsl #32
	movk x21, #13725, lsl #48
	str x21, [x5, #88]
	movz x21, #9246, lsl #0
	movk x21, #24078, lsl #16
	movk x21, #22627, lsl #32
	movk x21, #41681, lsl #48
	str x21, [x5, #96]
	movz x21, #8741, lsl #0
	movk x21, #15228, lsl #16
	movk x21, #8449, lsl #32
	movk x21, #34680, lsl #48
	str x21, [x5, #104]
	movz x21, #212, lsl #0
	movk x21, #22342, lsl #16
	movk x21, #54175, lsl #32
	movk x21, #21031, lsl #48
	str x21, [x5, #112]
	movz x21, #13900, lsl #0
	movk x21, #59138, lsl #16
	movk x21, #50336, lsl #32
	movk x21, #40648, lsl #48
	str x21, [x5, #120]
	movz x21, #49130, lsl #0
	movk x21, #53898, lsl #16
	movk x21, #51008, lsl #32
	movk x21, #46392, lsl #48
	str x21, [x5, #128]
	movz x21, #63395, lsl #0
	movk x21, #52978, lsl #16
	movk x21, #25081, lsl #32
	movk x21, #41237, lsl #48
	str x21, [x5, #136]
	movz x21, #44768, lsl #0
	movk x21, #42077, lsl #16
	movk x21, #13467, lsl #32
	movk x21, #21786, lsl #48
	str x21, [x5, #144]
	movz x21, #37805, lsl #0
	movk x21, #12338, lsl #16
	movk x21, #36085, lsl #32
	movk x21, #58289, lsl #48
	str x21, [x5, #152]
	movz x21, #63005, lsl #0
	movk x21, #12002, lsl #16
	movk x21, #26242, lsl #32
	movk x21, #24778, lsl #48
	str x21, [x5, #160]
	movz x21, #10688, lsl #0
	movk x21, #43811, lsl #16
	movk x21, #21261, lsl #32
	movk x21, #28494, lsl #48
	str x21, [x5, #168]
	movz x21, #56277, lsl #0
	movk x21, #17719, lsl #16
	movk x21, #64990, lsl #32
	movk x21, #12174, lsl #48
	str x21, [x5, #176]
	movz x21, #65283, lsl #0
	movk x21, #29290, lsl #16
	movk x21, #27757, lsl #32
	movk x21, #20827, lsl #48
	str x21, [x5, #184]
	movz x21, #7053, lsl #0
	movk x21, #37551, lsl #16
	movk x21, #56763, lsl #32
	movk x21, #32700, lsl #48
	str x21, [x5, #192]
	movz x21, #55569, lsl #0
	movk x21, #16732, lsl #16
	movk x21, #4127, lsl #32
	movk x21, #55386, lsl #48
	str x21, [x5, #200]
	movz x21, #49418, lsl #0
	movk x21, #34865, lsl #16
	movk x21, #52645, lsl #32
	movk x21, #48507, lsl #48
	str x21, [x5, #208]
	movz x21, #29741, lsl #0
	movk x21, #4816, lsl #16
	movk x21, #58808, lsl #32
	movk x21, #45236, lsl #48
	str x21, [x5, #216]
	movz x21, #27017, lsl #0
	movk x21, #19095, lsl #16
	movk x21, #38412, lsl #32
	movk x21, #32375, lsl #48
	str x21, [x5, #224]
	movz x21, #47461, lsl #0
	movk x21, #2545, lsl #16
	movk x21, #28357, lsl #32
	movk x21, #33990, lsl #48
	str x21, [x5, #232]
	movz x21, #61464, lsl #0
	movk x21, #60541, lsl #16
	movk x21, #56378, lsl #32
	movk x21, #8269, lsl #48
	str x21, [x5, #240]
	movz x21, #61049, lsl #0
	movk x21, #15967, lsl #16
	movk x21, #52183, lsl #32
	movk x21, #18489, lsl #48
	str x21, [x5, #248]
	add x14, x0, #0
	add x15, x5, #256
	movz x17, #8, lsl #0
20:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 20b
	ldr x6, [x19, #0]
	str x6, [x5, #768]
	ldr x6, [x19, #8]
	str x6, [x5, #776]
	cbz x24, 21f
23:
	ldr q16, [x5, #0]
	ldr q17, [x5, #16]
	ldr q18, [x5, #32]
	ldr q19, [x5, #48]
	ldr q20, [x5, #64]
	ldr q21, [x5, #80]
	ldr q22, [x5, #96]
	ldr q23, [x5, #112]
	ldr q24, [x5, #128]
	ldr q25, [x5, #144]
	ldr q26, [x5, #160]
	ldr q27, [x5, #176]
	ldr q28, [x5, #192]
	ldr q29, [x5, #208]
	ldr q30, [x5, #224]
	ldr q31, [x5, #240]
	movz w15, #64, lsl #0
	dup v4.16b, w15
	movz w15, #128, lsl #0
	dup v5.16b, w15
	movz w15, #192, lsl #0
	dup v6.16b, w15
	ldr w6, [x5, #768]
	rev w6, w6
	ldr w7, [x5, #772]
	rev w7, w7
	ldr w8, [x5, #776]
	rev w8, w8
	ldr w9, [x5, #780]
	rev w9, w9
	ldr w10, [x5, #256]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w6, w6, w11
	ldr w10, [x5, #260]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w7, w7, w11
	ldr w10, [x5, #264]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w8, w8, w11
	ldr w10, [x5, #268]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w9, w9, w11
	ldr w10, [x5, #272]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w6, w6, w11
	ldr w10, [x5, #276]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w7, w7, w11
	ldr w10, [x5, #280]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w8, w8, w11
	ldr w10, [x5, #284]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w9, w9, w11
	ldr w10, [x5, #288]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w6, w6, w11
	ldr w10, [x5, #292]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w7, w7, w11
	ldr w10, [x5, #296]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w8, w8, w11
	ldr w10, [x5, #300]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w9, w9, w11
	ldr w10, [x5, #304]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w6, w6, w11
	ldr w10, [x5, #308]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w7, w7, w11
	ldr w10, [x5, #312]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w8, w8, w11
	ldr w10, [x5, #316]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w9, w9, w11
	ldr w10, [x5, #320]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w6, w6, w11
	ldr w10, [x5, #324]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w7, w7, w11
	ldr w10, [x5, #328]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w8, w8, w11
	ldr w10, [x5, #332]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w9, w9, w11
	ldr w10, [x5, #336]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w6, w6, w11
	ldr w10, [x5, #340]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w7, w7, w11
	ldr w10, [x5, #344]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w8, w8, w11
	ldr w10, [x5, #348]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w9, w9, w11
	ldr w10, [x5, #352]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w6, w6, w11
	ldr w10, [x5, #356]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w7, w7, w11
	ldr w10, [x5, #360]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w8, w8, w11
	ldr w10, [x5, #364]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w9, w9, w11
	ldr w10, [x5, #368]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w6, w6, w11
	ldr w10, [x5, #372]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w7, w7, w11
	ldr w10, [x5, #376]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w8, w8, w11
	ldr w10, [x5, #380]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w11, w11, w10, ror #22
	eor w11, w11, w10, ror #14
	eor w11, w11, w10, ror #8
	eor w9, w9, w11
	rev w9, w9
	str w9, [x5, #768]
	rev w8, w8
	str w8, [x5, #772]
	rev w7, w7
	str w7, [x5, #776]
	rev w6, w6
	str w6, [x5, #780]
	ldr x6, [x23, #0]
	ldr x7, [x5, #768]
	eor x6, x6, x7
	str x6, [x23, #0]
	ldr x6, [x23, #8]
	ldr x7, [x5, #776]
	eor x6, x6, x7
	str x6, [x23, #8]
	add x23, x23, #16
	sub x24, x24, #1
	cbnz x24, 23b
	b 22f
21:
22:
	ldr x6, [x5, #768]
	str x6, [x19, #0]
	ldr x6, [x5, #776]
	str x6, [x19, #8]
	ldr x19, [x5, #3168]
	ldr x20, [x5, #3176]
	ldr x21, [x5, #3184]
	ldr x22, [x5, #3192]
	ldr x23, [x5, #3200]
	ldr x24, [x5, #3208]
	ldr x25, [x5, #3216]
	ldr x26, [x5, #3224]
	ldr x27, [x5, #3232]
	ldr x28, [x5, #3240]
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
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1024
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
	add x16, sp, #1536
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
	add x16, sp, #2048
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
	add x16, sp, #2560
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
	add x16, sp, #3072
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
	add sp, sp, #3264
	ret
	.p2align 6
