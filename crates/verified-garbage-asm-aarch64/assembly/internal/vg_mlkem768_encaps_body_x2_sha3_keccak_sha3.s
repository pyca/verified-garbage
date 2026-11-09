// The functions of `src/internal/vg_mlkem768_encaps_body_x2_sha3_keccak_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_encaps_body_x2_sha3_keccak_sha3:
	str x24, [x4, #21720]
	str x30, [x4, #21728]
	str x25, [x4, #21736]
	str x26, [x4, #21744]
	str x27, [x4, #21752]
	str x28, [x4, #21760]
	add x25, x0, #0
	add x26, x2, #0
	add x27, x3, #0
	add x28, x4, #0
	movz x24, #1, lsl #0
	ldr x9, [x1, #0]
	str x9, [x28, #912]
	ldr x9, [x1, #8]
	str x9, [x28, #920]
	ldr x9, [x1, #16]
	str x9, [x28, #928]
	ldr x9, [x1, #24]
	str x9, [x28, #936]
	add x0, x28, #0
	movz x9, #0, lsl #0
	str x9, [x0, #0]
	str x9, [x0, #8]
	str x9, [x0, #16]
	str x9, [x0, #24]
	str x9, [x0, #32]
	str x9, [x0, #40]
	str x9, [x0, #48]
	str x9, [x0, #56]
	str x9, [x0, #64]
	str x9, [x0, #72]
	str x9, [x0, #80]
	str x9, [x0, #88]
	str x9, [x0, #96]
	str x9, [x0, #104]
	str x9, [x0, #112]
	str x9, [x0, #120]
	str x9, [x0, #128]
	str x9, [x0, #136]
	str x9, [x0, #144]
	str x9, [x0, #152]
	str x9, [x0, #160]
	str x9, [x0, #168]
	str x9, [x0, #176]
	str x9, [x0, #184]
	str x9, [x0, #192]
	ldr x9, [x25, #1152]
	str x9, [x28, #840]
	ldr x9, [x25, #1160]
	str x9, [x28, #848]
	ldr x9, [x25, #1168]
	str x9, [x28, #856]
	ldr x9, [x25, #1176]
	str x9, [x28, #864]
	add x2, x28, #1176
	str x19, [x2, #1800]
	str x20, [x2, #1808]
	str x21, [x2, #1816]
	str x22, [x2, #1824]
	str x23, [x2, #1832]
	str x30, [x2, #1840]
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #0, lsl #0
	movk x6, #31, lsl #16
	movz x7, #1, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
	ldr x9, [x25, #0]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x25, #8]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x25, #16]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x25, #24]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x25, #32]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x25, #40]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x25, #48]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x25, #56]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x25, #64]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x25, #72]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x25, #80]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x25, #88]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x25, #96]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x25, #104]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x25, #112]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x25, #120]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x25, #128]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x25, #136]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x25, #144]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x25, #152]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x25, #160]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x25, #168]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x25, #176]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x25, #184]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x25, #192]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x25, #200]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x25, #208]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x25, #216]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x25, #224]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x25, #232]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x25, #240]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x25, #248]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x25, #256]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x25, #264]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x25, #272]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x25, #280]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x25, #288]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x25, #296]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x25, #304]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x25, #312]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x25, #320]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x25, #328]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x25, #336]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x25, #344]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x25, #352]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x25, #360]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x25, #368]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x25, #376]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x25, #384]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x25, #392]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x25, #400]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x21, #4248, lsl #0
	add x21, x28, x21
	movz x23, #5272, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
20:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
21:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 22f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 24f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 26f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 27f
26:
27:
	b 25f
24:
25:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 28f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 210f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 211f
210:
211:
	b 29f
28:
29:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 212f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 214f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 215f
214:
215:
	b 213f
212:
213:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 216f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 218f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 219f
218:
219:
	b 217f
216:
217:
	cbz x4, 220f
	b 221f
220:
	movz x5, #0, lsl #0
221:
	b 23f
22:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
23:
	cbnz x5, 21b
	cbz x4, 222f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 223f
222:
223:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	and x22, x22, x0
	add x20, x20, #504
	add x21, x23, #0
	add x1, x1, #16
	sub x6, x1, x19
	sub x6, x6, #1712
	cbnz x6, 20b
	add x6, x22, #0
	cbz x6, 224f
	b 225f
224:
	movz x30, #1, lsl #0
226:
	add x20, x19, #400
	add x21, x19, #904
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
	movz x23, #2, lsl #0
227:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 228f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
230:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 231f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 233f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 235f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 236f
235:
236:
	b 234f
233:
234:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 237f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 239f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 240f
239:
240:
	b 238f
237:
238:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 241f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 243f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 244f
243:
244:
	b 242f
241:
242:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 245f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 247f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 248f
247:
248:
	b 246f
245:
246:
	cbz x4, 249f
	b 250f
249:
	movz x5, #0, lsl #0
250:
	b 232f
231:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
232:
	cbnz x5, 230b
	cbz x4, 251f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 252f
251:
252:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 229f
228:
	movz x0, #1, lsl #0
229:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 227b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 226b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 253f
255:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 255b
	b 254f
253:
254:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 256f
258:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 258b
	b 257f
256:
257:
225:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	add x2, x28, #1176
	str x19, [x2, #1800]
	str x20, [x2, #1808]
	str x21, [x2, #1816]
	str x22, [x2, #1824]
	str x23, [x2, #1832]
	str x30, [x2, #1840]
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #2, lsl #0
	movk x6, #31, lsl #16
	movz x7, #256, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
	ldr x9, [x25, #408]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x25, #416]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x25, #424]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x25, #432]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x25, #440]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x25, #448]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x25, #456]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x25, #464]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x25, #472]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x25, #480]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x25, #488]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x25, #496]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x25, #504]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x25, #512]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x25, #520]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x25, #528]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x25, #536]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x25, #544]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x25, #552]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x25, #560]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x25, #568]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x25, #576]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x25, #584]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x25, #592]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x25, #600]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x25, #608]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x25, #616]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x25, #624]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x25, #632]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x25, #640]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x25, #648]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x25, #656]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x25, #664]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x25, #672]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x25, #680]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x25, #688]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x25, #696]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x25, #704]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x25, #712]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x25, #720]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x25, #728]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x25, #736]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x25, #744]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x25, #752]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x25, #760]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x25, #768]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x25, #776]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x25, #784]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x25, #792]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x25, #800]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x25, #808]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x21, #6296, lsl #0
	add x21, x28, x21
	movz x23, #7320, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
259:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
260:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 261f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 263f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 265f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 266f
265:
266:
	b 264f
263:
264:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 267f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 269f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 270f
269:
270:
	b 268f
267:
268:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 271f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 273f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 274f
273:
274:
	b 272f
271:
272:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 275f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 277f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 278f
277:
278:
	b 276f
275:
276:
	cbz x4, 279f
	b 280f
279:
	movz x5, #0, lsl #0
280:
	b 262f
261:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
262:
	cbnz x5, 260b
	cbz x4, 281f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 282f
281:
282:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	and x22, x22, x0
	add x20, x20, #504
	add x21, x23, #0
	add x1, x1, #16
	sub x6, x1, x19
	sub x6, x6, #1712
	cbnz x6, 259b
	add x6, x22, #0
	cbz x6, 283f
	b 284f
283:
	movz x30, #1, lsl #0
285:
	add x20, x19, #400
	add x21, x19, #904
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
	movz x23, #2, lsl #0
286:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 287f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
289:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 290f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 292f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 294f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 295f
294:
295:
	b 293f
292:
293:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 296f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 298f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 299f
298:
299:
	b 297f
296:
297:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2100f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2102f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2103f
2102:
2103:
	b 2101f
2100:
2101:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2104f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2106f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2107f
2106:
2107:
	b 2105f
2104:
2105:
	cbz x4, 2108f
	b 2109f
2108:
	movz x5, #0, lsl #0
2109:
	b 291f
290:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
291:
	cbnz x5, 289b
	cbz x4, 2110f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2111f
2110:
2111:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 288f
287:
	movz x0, #1, lsl #0
288:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 286b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 285b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2112f
2114:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2114b
	b 2113f
2112:
2113:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2115f
2117:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2117b
	b 2116f
2115:
2116:
284:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	add x2, x28, #1176
	str x19, [x2, #1800]
	str x20, [x2, #1808]
	str x21, [x2, #1816]
	str x22, [x2, #1824]
	str x23, [x2, #1832]
	str x30, [x2, #1840]
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #257, lsl #0
	movk x6, #31, lsl #16
	movz x7, #258, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
	ldr x9, [x25, #816]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x25, #824]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x25, #832]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x25, #840]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x25, #848]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x25, #856]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x25, #864]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x25, #872]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x25, #880]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x25, #888]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x25, #896]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x25, #904]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x25, #912]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x25, #920]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x25, #928]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x25, #936]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x25, #944]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x25, #952]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x25, #960]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x25, #968]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x25, #976]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x25, #984]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x25, #992]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x25, #1000]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x25, #1008]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x25, #1016]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x25, #1024]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x25, #1032]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x25, #1040]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x25, #1048]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x25, #1056]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x25, #1064]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x25, #1072]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x25, #1080]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x25, #1088]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x25, #1096]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x25, #1104]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x25, #1112]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x25, #1120]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x25, #1128]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x25, #1136]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x25, #1144]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x25, #1152]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x25, #1160]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x25, #1168]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x25, #1176]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldrb w9, [x28, #96]
	movz x10, #6, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #96]
	ldrb w9, [x28, #135]
	movz x10, #128, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #135]
	add x2, x19, #1536
	str x30, [x2, #128]
	add x0, x19, #0
	add x1, x28, #0
	bl {vg_keccak_f1600_x3_sha3}
	ldr x30, [x19, #1664]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x21, #8344, lsl #0
	add x21, x28, x21
	movz x23, #9368, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2118:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2119:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2120f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2122f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2124f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2125f
2124:
2125:
	b 2123f
2122:
2123:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2126f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2128f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2129f
2128:
2129:
	b 2127f
2126:
2127:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2130f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2132f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2133f
2132:
2133:
	b 2131f
2130:
2131:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2134f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2136f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2137f
2136:
2137:
	b 2135f
2134:
2135:
	cbz x4, 2138f
	b 2139f
2138:
	movz x5, #0, lsl #0
2139:
	b 2121f
2120:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2121:
	cbnz x5, 2119b
	cbz x4, 2140f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2141f
2140:
2141:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	and x22, x22, x0
	add x20, x20, #504
	add x21, x23, #0
	add x1, x1, #16
	sub x6, x1, x19
	sub x6, x6, #1712
	cbnz x6, 2118b
	add x6, x22, #0
	cbz x6, 2142f
	b 2143f
2142:
	movz x30, #1, lsl #0
2144:
	add x20, x19, #400
	add x21, x19, #904
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
	movz x23, #2, lsl #0
2145:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2146f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2148:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2149f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2151f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2153f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2154f
2153:
2154:
	b 2152f
2151:
2152:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2155f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2157f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2158f
2157:
2158:
	b 2156f
2155:
2156:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2159f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2161f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2162f
2161:
2162:
	b 2160f
2159:
2160:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2163f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2165f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2166f
2165:
2166:
	b 2164f
2163:
2164:
	cbz x4, 2167f
	b 2168f
2167:
	movz x5, #0, lsl #0
2168:
	b 2150f
2149:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2150:
	cbnz x5, 2148b
	cbz x4, 2169f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2170f
2169:
2170:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2147f
2146:
	movz x0, #1, lsl #0
2147:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2145b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2144b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2171f
2173:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2173b
	b 2172f
2171:
2172:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2174f
2176:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2176b
	b 2175f
2174:
2175:
2143:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	ldr x9, [x28, #0]
	str x9, [x28, #880]
	ldr x9, [x28, #8]
	str x9, [x28, #888]
	ldr x9, [x28, #16]
	str x9, [x28, #896]
	ldr x9, [x28, #24]
	str x9, [x28, #904]
	add x0, x28, #0
	movz x9, #0, lsl #0
	str x9, [x0, #0]
	str x9, [x0, #8]
	str x9, [x0, #16]
	str x9, [x0, #24]
	str x9, [x0, #32]
	str x9, [x0, #40]
	str x9, [x0, #48]
	str x9, [x0, #56]
	str x9, [x0, #64]
	str x9, [x0, #72]
	str x9, [x0, #80]
	str x9, [x0, #88]
	str x9, [x0, #96]
	str x9, [x0, #104]
	str x9, [x0, #112]
	str x9, [x0, #120]
	str x9, [x0, #128]
	str x9, [x0, #136]
	str x9, [x0, #144]
	str x9, [x0, #152]
	str x9, [x0, #160]
	str x9, [x0, #168]
	str x9, [x0, #176]
	str x9, [x0, #184]
	str x9, [x0, #192]
	str x30, [x28, #800]
	add x2, x28, #912
	ldr x9, [x2, #0]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	add x2, x28, #920
	ldr x9, [x2, #0]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	add x2, x28, #928
	ldr x9, [x2, #0]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	add x2, x28, #936
	ldr x9, [x2, #0]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	add x2, x28, #880
	ldr x9, [x2, #0]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	add x2, x28, #888
	ldr x9, [x2, #0]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	add x2, x28, #896
	ldr x9, [x2, #0]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	add x2, x28, #904
	ldr x9, [x2, #0]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldrb w9, [x28, #64]
	movz x10, #6, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #64]
	ldrb w9, [x28, #71]
	movz x10, #128, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #71]
	add x0, x28, #0
	add x1, x28, #200
	bl {vg_keccak_f1600_sha3}
	ldr x9, [x28, #0]
	add x2, x26, #0
	str x9, [x2, #0]
	ldr x9, [x28, #8]
	add x2, x26, #8
	str x9, [x2, #0]
	ldr x9, [x28, #16]
	add x2, x26, #16
	str x9, [x2, #0]
	ldr x9, [x28, #24]
	add x2, x26, #24
	str x9, [x2, #0]
	ldr x9, [x28, #32]
	add x2, x28, #944
	str x9, [x2, #0]
	ldr x9, [x28, #40]
	add x2, x28, #952
	str x9, [x2, #0]
	ldr x9, [x28, #48]
	add x2, x28, #960
	str x9, [x2, #0]
	ldr x9, [x28, #56]
	add x2, x28, #968
	str x9, [x2, #0]
	ldr x30, [x28, #800]
	bl {vg_mlkem768_pair_prf_840_1176_4248_944_17560_6_0_3}
	add x2, x28, #1176
	str x19, [x2, #1800]
	str x20, [x2, #1808]
	str x21, [x2, #1816]
	str x22, [x2, #1824]
	str x23, [x2, #1832]
	str x30, [x2, #1840]
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #514, lsl #0
	movk x6, #31, lsl #16
	movz x7, #514, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
	movz x21, #18064, lsl #0
	add x21, x28, x21
	ldr x9, [x28, #944]
	str x9, [x19, #8]
	ldr x9, [x28, #952]
	str x9, [x19, #24]
	ldr x9, [x28, #960]
	str x9, [x19, #40]
	ldr x9, [x28, #968]
	str x9, [x19, #56]
	movz x9, #7939, lsl #0
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #104]
	movz x9, #0, lsl #0
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #136]
	movz x9, #0, lsl #0
	str x9, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #168]
	movz x9, #0, lsl #0
	str x9, [x19, #184]
	movz x9, #0, lsl #0
	str x9, [x19, #200]
	movz x9, #0, lsl #0
	str x9, [x19, #216]
	movz x9, #0, lsl #0
	str x9, [x19, #232]
	movz x9, #0, lsl #0
	str x9, [x19, #248]
	movz x9, #32768, lsl #48
	str x9, [x19, #264]
	movz x9, #0, lsl #0
	str x9, [x19, #280]
	movz x9, #0, lsl #0
	str x9, [x19, #296]
	movz x9, #0, lsl #0
	str x9, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #328]
	movz x9, #0, lsl #0
	str x9, [x19, #344]
	movz x9, #0, lsl #0
	str x9, [x19, #360]
	movz x9, #0, lsl #0
	str x9, [x19, #376]
	movz x9, #0, lsl #0
	str x9, [x19, #392]
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #944]
	str x9, [x19, #8]
	ldr x9, [x28, #952]
	str x9, [x19, #24]
	ldr x9, [x28, #960]
	str x9, [x19, #40]
	ldr x9, [x28, #968]
	str x9, [x19, #56]
	movz x9, #7940, lsl #0
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #104]
	movz x9, #0, lsl #0
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #136]
	movz x9, #0, lsl #0
	str x9, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #168]
	movz x9, #0, lsl #0
	str x9, [x19, #184]
	movz x9, #0, lsl #0
	str x9, [x19, #200]
	movz x9, #0, lsl #0
	str x9, [x19, #216]
	movz x9, #0, lsl #0
	str x9, [x19, #232]
	movz x9, #0, lsl #0
	str x9, [x19, #248]
	movz x9, #32768, lsl #48
	str x9, [x19, #264]
	movz x9, #0, lsl #0
	str x9, [x19, #280]
	movz x9, #0, lsl #0
	str x9, [x19, #296]
	movz x9, #0, lsl #0
	str x9, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #328]
	movz x9, #0, lsl #0
	str x9, [x19, #344]
	movz x9, #0, lsl #0
	str x9, [x19, #360]
	movz x9, #0, lsl #0
	str x9, [x19, #376]
	movz x9, #0, lsl #0
	str x9, [x19, #392]
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	ldr x9, [x28, #944]
	str x9, [x19, #8]
	ldr x9, [x28, #952]
	str x9, [x19, #24]
	ldr x9, [x28, #960]
	str x9, [x19, #40]
	ldr x9, [x28, #968]
	str x9, [x19, #56]
	movz x9, #7941, lsl #0
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #88]
	movz x9, #0, lsl #0
	str x9, [x19, #104]
	movz x9, #0, lsl #0
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #136]
	movz x9, #0, lsl #0
	str x9, [x19, #152]
	movz x9, #0, lsl #0
	str x9, [x19, #168]
	movz x9, #0, lsl #0
	str x9, [x19, #184]
	movz x9, #0, lsl #0
	str x9, [x19, #200]
	movz x9, #0, lsl #0
	str x9, [x19, #216]
	movz x9, #0, lsl #0
	str x9, [x19, #232]
	movz x9, #0, lsl #0
	str x9, [x19, #248]
	movz x9, #32768, lsl #48
	str x9, [x19, #264]
	movz x9, #0, lsl #0
	str x9, [x19, #280]
	movz x9, #0, lsl #0
	str x9, [x19, #296]
	movz x9, #0, lsl #0
	str x9, [x19, #312]
	movz x9, #0, lsl #0
	str x9, [x19, #328]
	movz x9, #0, lsl #0
	str x9, [x19, #344]
	movz x9, #0, lsl #0
	str x9, [x19, #360]
	movz x9, #0, lsl #0
	str x9, [x19, #376]
	movz x9, #0, lsl #0
	str x9, [x19, #392]
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	ldr x7, [x19, #8]
	str x6, [x20, #0]
	str x7, [x21, #0]
	ldr x6, [x19, #16]
	ldr x7, [x19, #24]
	str x6, [x20, #8]
	str x7, [x21, #8]
	ldr x6, [x19, #32]
	ldr x7, [x19, #40]
	str x6, [x20, #16]
	str x7, [x21, #16]
	ldr x6, [x19, #48]
	ldr x7, [x19, #56]
	str x6, [x20, #24]
	str x7, [x21, #24]
	ldr x6, [x19, #64]
	ldr x7, [x19, #72]
	str x6, [x20, #32]
	str x7, [x21, #32]
	ldr x6, [x19, #80]
	ldr x7, [x19, #88]
	str x6, [x20, #40]
	str x7, [x21, #40]
	ldr x6, [x19, #96]
	ldr x7, [x19, #104]
	str x6, [x20, #48]
	str x7, [x21, #48]
	ldr x6, [x19, #112]
	ldr x7, [x19, #120]
	str x6, [x20, #56]
	str x7, [x21, #56]
	ldr x6, [x19, #128]
	ldr x7, [x19, #136]
	str x6, [x20, #64]
	str x7, [x21, #64]
	ldr x6, [x19, #144]
	ldr x7, [x19, #152]
	str x6, [x20, #72]
	str x7, [x21, #72]
	ldr x6, [x19, #160]
	ldr x7, [x19, #168]
	str x6, [x20, #80]
	str x7, [x21, #80]
	ldr x6, [x19, #176]
	ldr x7, [x19, #184]
	str x6, [x20, #88]
	str x7, [x21, #88]
	ldr x6, [x19, #192]
	ldr x7, [x19, #200]
	str x6, [x20, #96]
	str x7, [x21, #96]
	ldr x6, [x19, #208]
	ldr x7, [x19, #216]
	str x6, [x20, #104]
	str x7, [x21, #104]
	ldr x6, [x19, #224]
	ldr x7, [x19, #232]
	str x6, [x20, #112]
	str x7, [x21, #112]
	ldr x6, [x19, #240]
	ldr x7, [x19, #248]
	str x6, [x20, #120]
	str x7, [x21, #120]
	ldr x6, [x19, #256]
	ldr x7, [x19, #264]
	str x6, [x20, #128]
	str x7, [x21, #128]
	ldr x6, [x19, #272]
	ldr x7, [x19, #280]
	str x6, [x20, #136]
	str x7, [x21, #136]
	ldr x6, [x19, #288]
	ldr x7, [x19, #296]
	str x6, [x20, #144]
	str x7, [x21, #144]
	ldr x6, [x19, #304]
	ldr x7, [x19, #312]
	str x6, [x20, #152]
	str x7, [x21, #152]
	ldr x6, [x19, #320]
	ldr x7, [x19, #328]
	str x6, [x20, #160]
	str x7, [x21, #160]
	add x20, x20, #168
	add x21, x21, #168
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x3, #12440, lsl #0
	add x3, x28, x3
	add x2, x19, #400
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2177:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2178f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2180f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2182f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2183f
2182:
2183:
	b 2181f
2180:
2181:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2184f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2186f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2187f
2186:
2187:
	b 2185f
2184:
2185:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2188f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2190f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2191f
2190:
2191:
	b 2189f
2188:
2189:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2192f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2194f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2195f
2194:
2195:
	b 2193f
2192:
2193:
	cbz x4, 2196f
	b 2197f
2196:
	movz x5, #0, lsl #0
2197:
	b 2179f
2178:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2179:
	cbnz x5, 2177b
	cbz x4, 2198f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2199f
2198:
2199:
	sub x0, x4, #1
	lsr x0, x0, #63
	add x22, x0, #0
	cbz x22, 2200f
	b 2201f
2200:
	str x22, [x19, #1848]
	str x23, [x19, #1856]
	add x2, x28, #1176
	add x19, x2, #0
	movi v0.2d, #0
	str q0, [x19, #0]
	str q0, [x19, #16]
	str q0, [x19, #32]
	str q0, [x19, #48]
	str q0, [x19, #64]
	str q0, [x19, #80]
	str q0, [x19, #96]
	str q0, [x19, #112]
	str q0, [x19, #128]
	str q0, [x19, #144]
	str q0, [x19, #160]
	str q0, [x19, #176]
	str q0, [x19, #192]
	str q0, [x19, #208]
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	str q0, [x19, #352]
	str q0, [x19, #368]
	str q0, [x19, #384]
	ldr x6, [x28, #840]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #848]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #856]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #864]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #514, lsl #0
	movk x6, #31, lsl #16
	movz x7, #514, lsl #0
	movk x7, #31, lsl #16
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #320]
	add x20, x19, #400
	add x21, x19, #904
	movz x22, #3, lsl #0
	movz x22, #5, lsl #0
2202:
	add x1, x19, #768
	add x1, x1, #768
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2_sha3}
	ldr x30, [x1, #128]
	ldr x6, [x19, #0]
	str x6, [x20, #0]
	ldr x6, [x19, #16]
	str x6, [x20, #8]
	ldr x6, [x19, #32]
	str x6, [x20, #16]
	ldr x6, [x19, #48]
	str x6, [x20, #24]
	ldr x6, [x19, #64]
	str x6, [x20, #32]
	ldr x6, [x19, #80]
	str x6, [x20, #40]
	ldr x6, [x19, #96]
	str x6, [x20, #48]
	ldr x6, [x19, #112]
	str x6, [x20, #56]
	ldr x6, [x19, #128]
	str x6, [x20, #64]
	ldr x6, [x19, #144]
	str x6, [x20, #72]
	ldr x6, [x19, #160]
	str x6, [x20, #80]
	ldr x6, [x19, #176]
	str x6, [x20, #88]
	ldr x6, [x19, #192]
	str x6, [x20, #96]
	ldr x6, [x19, #208]
	str x6, [x20, #104]
	ldr x6, [x19, #224]
	str x6, [x20, #112]
	ldr x6, [x19, #240]
	str x6, [x20, #120]
	ldr x6, [x19, #256]
	str x6, [x20, #128]
	ldr x6, [x19, #272]
	str x6, [x20, #136]
	ldr x6, [x19, #288]
	str x6, [x20, #144]
	ldr x6, [x19, #304]
	str x6, [x20, #152]
	ldr x6, [x19, #320]
	str x6, [x20, #160]
	add x20, x20, #168
	sub x22, x22, #1
	cbnz x22, 2202b
	movz x9, #256, lsl #0
	movk x9, #513, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #1284, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #2826, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	dup v17.2d, x9
	movz x9, #4095, lsl #0
	movk x9, #0, lsl #16
	movk x9, #4095, lsl #32
	movk x9, #0, lsl #48
	mov v17.d[1], x9
	movz x9, #257, lsl #0
	movk x9, #258, lsl #16
	movk x9, #260, lsl #32
	movk x9, #264, lsl #48
	dup v20.2d, x9
	movz x9, #272, lsl #0
	movk x9, #288, lsl #16
	movk x9, #320, lsl #32
	movk x9, #384, lsl #48
	mov v20.d[1], x9
	movz x9, #3329, lsl #0
	dup v19.8h, w9
	movi v21.2d, #0
	movz x9, #0, lsl #0
	str x9, [x19, #1408]
	adrp x16, {VG_MLKEM_REJ_SHUFFLE}
	add x16, x16, {VG_MLKEM_REJ_SHUFFLE}
	movz x9, #0, lsl #0
	str x9, [x19, #1240]
	movz x3, #12440, lsl #0
	add x3, x28, x3
	add x2, x19, #400
	movz x4, #256, lsl #0
	movz x5, #280, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2203:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2204f
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2206f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2208f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2209f
2208:
2209:
	b 2207f
2206:
2207:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2210f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2212f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2213f
2212:
2213:
	b 2211f
2210:
2211:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2214f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2216f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2217f
2216:
2217:
	b 2215f
2214:
2215:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 2218f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2220f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2221f
2220:
2221:
	b 2219f
2218:
2219:
	cbz x4, 2222f
	b 2223f
2222:
	movz x5, #0, lsl #0
2223:
	b 2205f
2204:
	ldr q0, [x2, #0]
	tbl v0.16b, {v0.16b}, v16.16b
	ushr v1.8h, v0.8h, #4
	bif v0.16b, v1.16b, v17.16b
	cmhi v1.8h, v19.8h, v0.8h
	and v1.16b, v1.16b, v20.16b
	addv h1, v1.8h
	umov w6, v1.s[0]
	movz x7, #255, lsl #0
	and x7, x6, x7
	lsl x7, x7, #4
	add x7, x16, x7
	ldr q2, [x7, #0]
	tbl v0.16b, {v0.16b}, v2.16b
	str q0, [x3, #0]
	lsr x6, x6, #8
	movz x7, #15, lsl #0
	and x6, x6, x7
	sub x4, x4, x6
	lsl x6, x6, #1
	add x3, x3, x6
	add x2, x2, #12
	sub x5, x5, #4
2205:
	cbnz x5, 2203b
	cbz x4, 2224f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2225f
2224:
2225:
	sub x0, x4, #1
	lsr x0, x0, #63
	and x24, x24, x0
	cbz x4, 2226f
2228:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2228b
	b 2227f
2226:
2227:
	ldr x22, [x19, #1848]
	ldr x23, [x19, #1856]
2201:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #13464, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #13464, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #17728, lsl #0
	add x0, x28, x0
	movz x1, #14488, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #14488, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #17896, lsl #0
	add x0, x28, x0
	movz x1, #15512, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #15512, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_ntt}
	movz x0, #18064, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #18232, lsl #0
	add x0, x28, x0
	movz x1, #30720, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #18400, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
2229:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x2, #13464, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #7320, lsl #0
	add x1, x28, x1
	movz x2, #14488, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #10392, lsl #0
	add x1, x28, x1
	movz x2, #15512, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 2229b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #29696, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2230:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.8h, v0.8h, v1.8h
	cmhs v3.8h, v2.8h, v16.8h
	and v3.16b, v3.16b, v16.16b
	sub v2.8h, v2.8h, v3.8h
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2230b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2231:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2231b
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #10, lsl #0
	add x2, x27, #0
	movz x3, #320, lsl #0
	bl {vg_mlkem_compress_encode}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
2232:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x2, #13464, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #8344, lsl #0
	add x1, x28, x1
	movz x2, #14488, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #11416, lsl #0
	add x1, x28, x1
	movz x2, #15512, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 2232b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #30720, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2233:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.8h, v0.8h, v1.8h
	cmhs v3.8h, v2.8h, v16.8h
	and v3.16b, v3.16b, v16.16b
	sub v2.8h, v2.8h, v3.8h
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2233b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2234:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2234b
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #10, lsl #0
	add x2, x27, #320
	movz x3, #320, lsl #0
	bl {vg_mlkem_compress_encode}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
2235:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x2, #13464, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #9368, lsl #0
	add x1, x28, x1
	movz x2, #14488, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #12440, lsl #0
	add x1, x28, x1
	movz x2, #15512, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 2235b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #31744, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2236:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.8h, v0.8h, v1.8h
	cmhs v3.8h, v2.8h, v16.8h
	and v3.16b, v3.16b, v16.16b
	sub v2.8h, v2.8h, v3.8h
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2236b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2237:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2237b
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #10, lsl #0
	add x2, x27, #640
	movz x3, #320, lsl #0
	bl {vg_mlkem_compress_encode}
	add x0, x25, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
2238:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2238b
	add x0, x25, #384
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
2239:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2239b
	add x0, x25, #768
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
2240:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	uzp1 v0.8h, v0.8h, v1.8h
	str q0, [x1, #0]
	add x0, x0, #12
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2240b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	adrp x3, {VG_MLKEM_GAMMA}
	add x3, x3, {VG_MLKEM_GAMMA}
	movz x11, #16, lsl #0
	movz x12, #0, lsl #0
2241:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #4248, lsl #0
	add x1, x28, x1
	movz x2, #13464, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #5272, lsl #0
	add x1, x28, x1
	movz x2, #14488, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	movz x1, #6296, lsl #0
	add x1, x28, x1
	movz x2, #15512, lsl #0
	add x2, x28, x2
	add x1, x1, x12
	add x2, x2, x12
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	uzp1 v6.8h, v0.8h, v1.8h
	uzp2 v7.8h, v0.8h, v1.8h
	uzp1 v19.8h, v4.8h, v5.8h
	uzp2 v20.8h, v4.8h, v5.8h
	umlal v21.4s, v6.4h, v19.4h
	umlal2 v25.4s, v6.8h, v19.8h
	umlal v22.4s, v7.4h, v20.4h
	umlal2 v26.4s, v7.8h, v20.8h
	umlal v23.4s, v6.4h, v20.4h
	umlal2 v27.4s, v6.8h, v20.8h
	umlal v23.4s, v7.4h, v19.4h
	umlal2 v27.4s, v7.8h, v19.8h
	ldr q18, [x3, #0]
	ldr q28, [x3, #16]
	sqdmulh v24.4s, v22.4s, v17.4s
	mls v22.4s, v24.4s, v16.4s
	mla v21.4s, v22.4s, v18.4s
	sqdmulh v24.4s, v21.4s, v17.4s
	mls v21.4s, v24.4s, v16.4s
	sub v24.4s, v21.4s, v16.4s
	umin v21.4s, v21.4s, v24.4s
	sqdmulh v24.4s, v23.4s, v17.4s
	mls v23.4s, v24.4s, v16.4s
	sub v24.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v24.4s
	sqdmulh v24.4s, v26.4s, v17.4s
	mls v26.4s, v24.4s, v16.4s
	mla v25.4s, v26.4s, v28.4s
	sqdmulh v24.4s, v25.4s, v17.4s
	mls v25.4s, v24.4s, v16.4s
	sub v24.4s, v25.4s, v16.4s
	umin v25.4s, v25.4s, v24.4s
	sqdmulh v24.4s, v27.4s, v17.4s
	mls v27.4s, v24.4s, v16.4s
	sub v24.4s, v27.4s, v16.4s
	umin v27.4s, v27.4s, v24.4s
	uzp1 v0.8h, v21.8h, v25.8h
	uzp1 v1.8h, v23.8h, v27.8h
	zip1 v2.8h, v0.8h, v1.8h
	zip2 v3.8h, v0.8h, v1.8h
	str q2, [x0, #0]
	str q3, [x0, #16]
	add x0, x0, #32
	add x3, x3, #32
	add x12, x12, #32
	sub x11, x11, #1
	cbnz x11, 2241b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	add x1, x28, #3224
	bl {vg_mlkem16_inv_ntt}
	movz x9, #6, lsl #0
	strb w9, [x28, #976]
	add x0, x28, #0
	movz x9, #0, lsl #0
	str x9, [x0, #0]
	str x9, [x0, #8]
	str x9, [x0, #16]
	str x9, [x0, #24]
	str x9, [x0, #32]
	str x9, [x0, #40]
	str x9, [x0, #48]
	str x9, [x0, #56]
	str x9, [x0, #64]
	str x9, [x0, #72]
	str x9, [x0, #80]
	str x9, [x0, #88]
	str x9, [x0, #96]
	str x9, [x0, #104]
	str x9, [x0, #112]
	str x9, [x0, #120]
	str x9, [x0, #128]
	str x9, [x0, #136]
	str x9, [x0, #144]
	str x9, [x0, #152]
	str x9, [x0, #160]
	str x9, [x0, #168]
	str x9, [x0, #176]
	str x9, [x0, #184]
	str x9, [x0, #192]
	str x30, [x28, #800]
	add x2, x28, #944
	ldr x9, [x2, #0]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	add x2, x28, #952
	ldr x9, [x2, #0]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	add x2, x28, #960
	ldr x9, [x2, #0]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	add x2, x28, #968
	ldr x9, [x2, #0]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	add x2, x28, #976
	ldrb w9, [x2, #0]
	ldrb w10, [x28, #32]
	eor x9, x9, x10
	strb w9, [x28, #32]
	ldrb w9, [x28, #33]
	movz x10, #31, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #33]
	ldrb w9, [x28, #135]
	movz x10, #128, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #135]
	add x0, x28, #0
	add x1, x28, #200
	bl {vg_keccak_f1600_sha3}
	ldr x9, [x28, #0]
	add x2, x28, #1048
	str x9, [x2, #0]
	ldr x9, [x28, #8]
	add x2, x28, #1056
	str x9, [x2, #0]
	ldr x9, [x28, #16]
	add x2, x28, #1064
	str x9, [x2, #0]
	ldr x9, [x28, #24]
	add x2, x28, #1072
	str x9, [x2, #0]
	ldr x9, [x28, #32]
	add x2, x28, #1080
	str x9, [x2, #0]
	ldr x9, [x28, #40]
	add x2, x28, #1088
	str x9, [x2, #0]
	ldr x9, [x28, #48]
	add x2, x28, #1096
	str x9, [x2, #0]
	ldr x9, [x28, #56]
	add x2, x28, #1104
	str x9, [x2, #0]
	ldr x9, [x28, #64]
	add x2, x28, #1112
	str x9, [x2, #0]
	ldr x9, [x28, #72]
	add x2, x28, #1120
	str x9, [x2, #0]
	ldr x9, [x28, #80]
	add x2, x28, #1128
	str x9, [x2, #0]
	ldr x9, [x28, #88]
	add x2, x28, #1136
	str x9, [x2, #0]
	ldr x9, [x28, #96]
	add x2, x28, #1144
	str x9, [x2, #0]
	ldr x9, [x28, #104]
	add x2, x28, #1152
	str x9, [x2, #0]
	ldr x9, [x28, #112]
	add x2, x28, #1160
	str x9, [x2, #0]
	ldr x9, [x28, #120]
	add x2, x28, #1168
	str x9, [x2, #0]
	ldr x30, [x28, #800]
	add x0, x28, #1048
	movz x1, #16536, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #16536, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2242:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.8h, v0.8h, v1.8h
	cmhs v3.8h, v2.8h, v16.8h
	and v3.16b, v3.16b, v16.16b
	sub v2.8h, v2.8h, v3.8h
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x11, x11, #1
	cbnz x11, 2242b
	movz x0, #17560, lsl #0
	add x0, x28, x0
	movz x1, #18584, lsl #0
	add x1, x28, x1
	movz x10, #32, lsl #0
	movi v29.2d, #0
2243:
	ldr q0, [x0, #0]
	zip1 v1.8h, v0.8h, v29.8h
	zip2 v2.8h, v0.8h, v29.8h
	str q1, [x1, #0]
	str q2, [x1, #16]
	add x0, x0, #16
	add x1, x1, #32
	sub x10, x10, #1
	cbnz x10, 2243b
	add x0, x28, #912
	movz x1, #32, lsl #0
	movz x2, #1, lsl #0
	movz x3, #16536, lsl #0
	add x3, x28, x3
	bl {vg_mlkem_decode_decompress}
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #16536, lsl #0
	add x1, x28, x1
	bl {vg_mlkem_add}
	movz x0, #18584, lsl #0
	add x0, x28, x0
	movz x1, #4, lsl #0
	add x2, x27, #960
	movz x3, #128, lsl #0
	bl {vg_mlkem_compress_encode}
	add x0, x24, #0
	ldr x24, [x28, #21720]
	ldr x30, [x28, #21728]
	ldr x25, [x28, #21736]
	ldr x26, [x28, #21744]
	ldr x27, [x28, #21752]
	ldr x28, [x28, #21760]
	ret
	.p2align 6
