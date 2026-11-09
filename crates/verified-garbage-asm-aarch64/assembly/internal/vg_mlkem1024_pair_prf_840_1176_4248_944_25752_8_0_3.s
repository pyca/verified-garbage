// The functions of `src/internal/vg_mlkem1024_pair_prf_840_1176_4248_944_25752_8_0_3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_pair_prf_840_1176_4248_944_25752_8_0_3:
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
	movz x6, #512, lsl #0
	movk x6, #31, lsl #16
	movz x7, #513, lsl #0
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
	ldr x9, [x28, #944]
	str x9, [x28, #0]
	ldr x9, [x28, #952]
	str x9, [x28, #8]
	ldr x9, [x28, #960]
	str x9, [x28, #16]
	ldr x9, [x28, #968]
	str x9, [x28, #24]
	movz x9, #7936, lsl #0
	str x9, [x28, #32]
	movz x9, #0, lsl #0
	str x9, [x28, #40]
	movz x9, #0, lsl #0
	str x9, [x28, #48]
	movz x9, #0, lsl #0
	str x9, [x28, #56]
	movz x9, #0, lsl #0
	str x9, [x28, #64]
	movz x9, #0, lsl #0
	str x9, [x28, #72]
	movz x9, #0, lsl #0
	str x9, [x28, #80]
	movz x9, #0, lsl #0
	str x9, [x28, #88]
	movz x9, #0, lsl #0
	str x9, [x28, #96]
	movz x9, #0, lsl #0
	str x9, [x28, #104]
	movz x9, #0, lsl #0
	str x9, [x28, #112]
	movz x9, #0, lsl #0
	str x9, [x28, #120]
	movz x9, #32768, lsl #48
	str x9, [x28, #128]
	movz x9, #0, lsl #0
	str x9, [x28, #136]
	movz x9, #0, lsl #0
	str x9, [x28, #144]
	movz x9, #0, lsl #0
	str x9, [x28, #152]
	movz x9, #0, lsl #0
	str x9, [x28, #160]
	movz x9, #0, lsl #0
	str x9, [x28, #168]
	movz x9, #0, lsl #0
	str x9, [x28, #176]
	movz x9, #0, lsl #0
	str x9, [x28, #184]
	movz x9, #0, lsl #0
	str x9, [x28, #192]
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
	movz x2, #25752, lsl #0
	add x2, x28, x2
	ldr x9, [x28, #0]
	str x9, [x2, #0]
	ldr x9, [x28, #8]
	str x9, [x2, #8]
	ldr x9, [x28, #16]
	str x9, [x2, #16]
	ldr x9, [x28, #24]
	str x9, [x2, #24]
	ldr x9, [x28, #32]
	str x9, [x2, #32]
	ldr x9, [x28, #40]
	str x9, [x2, #40]
	ldr x9, [x28, #48]
	str x9, [x2, #48]
	ldr x9, [x28, #56]
	str x9, [x2, #56]
	ldr x9, [x28, #64]
	str x9, [x2, #64]
	ldr x9, [x28, #72]
	str x9, [x2, #72]
	ldr x9, [x28, #80]
	str x9, [x2, #80]
	ldr x9, [x28, #88]
	str x9, [x2, #88]
	ldr x9, [x28, #96]
	str x9, [x2, #96]
	ldr x9, [x28, #104]
	str x9, [x2, #104]
	ldr x9, [x28, #112]
	str x9, [x2, #112]
	ldr x9, [x28, #120]
	str x9, [x2, #120]
	ldr x9, [x28, #944]
	str x9, [x28, #0]
	ldr x9, [x28, #952]
	str x9, [x28, #8]
	ldr x9, [x28, #960]
	str x9, [x28, #16]
	ldr x9, [x28, #968]
	str x9, [x28, #24]
	movz x9, #7937, lsl #0
	str x9, [x28, #32]
	movz x9, #0, lsl #0
	str x9, [x28, #40]
	movz x9, #0, lsl #0
	str x9, [x28, #48]
	movz x9, #0, lsl #0
	str x9, [x28, #56]
	movz x9, #0, lsl #0
	str x9, [x28, #64]
	movz x9, #0, lsl #0
	str x9, [x28, #72]
	movz x9, #0, lsl #0
	str x9, [x28, #80]
	movz x9, #0, lsl #0
	str x9, [x28, #88]
	movz x9, #0, lsl #0
	str x9, [x28, #96]
	movz x9, #0, lsl #0
	str x9, [x28, #104]
	movz x9, #0, lsl #0
	str x9, [x28, #112]
	movz x9, #0, lsl #0
	str x9, [x28, #120]
	movz x9, #32768, lsl #48
	str x9, [x28, #128]
	movz x9, #0, lsl #0
	str x9, [x28, #136]
	movz x9, #0, lsl #0
	str x9, [x28, #144]
	movz x9, #0, lsl #0
	str x9, [x28, #152]
	movz x9, #0, lsl #0
	str x9, [x28, #160]
	movz x9, #0, lsl #0
	str x9, [x28, #168]
	movz x9, #0, lsl #0
	str x9, [x28, #176]
	movz x9, #0, lsl #0
	str x9, [x28, #184]
	movz x9, #0, lsl #0
	str x9, [x28, #192]
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
	movz x2, #25920, lsl #0
	add x2, x28, x2
	ldr x9, [x28, #0]
	str x9, [x2, #0]
	ldr x9, [x28, #8]
	str x9, [x2, #8]
	ldr x9, [x28, #16]
	str x9, [x2, #16]
	ldr x9, [x28, #24]
	str x9, [x2, #24]
	ldr x9, [x28, #32]
	str x9, [x2, #32]
	ldr x9, [x28, #40]
	str x9, [x2, #40]
	ldr x9, [x28, #48]
	str x9, [x2, #48]
	ldr x9, [x28, #56]
	str x9, [x2, #56]
	ldr x9, [x28, #64]
	str x9, [x2, #64]
	ldr x9, [x28, #72]
	str x9, [x2, #72]
	ldr x9, [x28, #80]
	str x9, [x2, #80]
	ldr x9, [x28, #88]
	str x9, [x2, #88]
	ldr x9, [x28, #96]
	str x9, [x2, #96]
	ldr x9, [x28, #104]
	str x9, [x2, #104]
	ldr x9, [x28, #112]
	str x9, [x2, #112]
	ldr x9, [x28, #120]
	str x9, [x2, #120]
	ldr x9, [x28, #944]
	str x9, [x28, #0]
	ldr x9, [x28, #952]
	str x9, [x28, #8]
	ldr x9, [x28, #960]
	str x9, [x28, #16]
	ldr x9, [x28, #968]
	str x9, [x28, #24]
	movz x9, #7938, lsl #0
	str x9, [x28, #32]
	movz x9, #0, lsl #0
	str x9, [x28, #40]
	movz x9, #0, lsl #0
	str x9, [x28, #48]
	movz x9, #0, lsl #0
	str x9, [x28, #56]
	movz x9, #0, lsl #0
	str x9, [x28, #64]
	movz x9, #0, lsl #0
	str x9, [x28, #72]
	movz x9, #0, lsl #0
	str x9, [x28, #80]
	movz x9, #0, lsl #0
	str x9, [x28, #88]
	movz x9, #0, lsl #0
	str x9, [x28, #96]
	movz x9, #0, lsl #0
	str x9, [x28, #104]
	movz x9, #0, lsl #0
	str x9, [x28, #112]
	movz x9, #0, lsl #0
	str x9, [x28, #120]
	movz x9, #32768, lsl #48
	str x9, [x28, #128]
	movz x9, #0, lsl #0
	str x9, [x28, #136]
	movz x9, #0, lsl #0
	str x9, [x28, #144]
	movz x9, #0, lsl #0
	str x9, [x28, #152]
	movz x9, #0, lsl #0
	str x9, [x28, #160]
	movz x9, #0, lsl #0
	str x9, [x28, #168]
	movz x9, #0, lsl #0
	str x9, [x28, #176]
	movz x9, #0, lsl #0
	str x9, [x28, #184]
	movz x9, #0, lsl #0
	str x9, [x28, #192]
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
	movz x2, #26088, lsl #0
	add x2, x28, x2
	ldr x9, [x28, #0]
	str x9, [x2, #0]
	ldr x9, [x28, #8]
	str x9, [x2, #8]
	ldr x9, [x28, #16]
	str x9, [x2, #16]
	ldr x9, [x28, #24]
	str x9, [x2, #24]
	ldr x9, [x28, #32]
	str x9, [x2, #32]
	ldr x9, [x28, #40]
	str x9, [x2, #40]
	ldr x9, [x28, #48]
	str x9, [x2, #48]
	ldr x9, [x28, #56]
	str x9, [x2, #56]
	ldr x9, [x28, #64]
	str x9, [x2, #64]
	ldr x9, [x28, #72]
	str x9, [x2, #72]
	ldr x9, [x28, #80]
	str x9, [x2, #80]
	ldr x9, [x28, #88]
	str x9, [x2, #88]
	ldr x9, [x28, #96]
	str x9, [x2, #96]
	ldr x9, [x28, #104]
	str x9, [x2, #104]
	ldr x9, [x28, #112]
	str x9, [x2, #112]
	ldr x9, [x28, #120]
	str x9, [x2, #120]
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
	movz x21, #12440, lsl #0
	add x21, x28, x21
	movz x23, #13464, lsl #0
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
	ret
	.p2align 6
