// The functions of `src/internal/vg_mlkem1024_keygen_body_x2_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_keygen_body_x2_sha3:
	str x24, [x3, #27680]
	str x25, [x3, #27688]
	str x26, [x3, #27696]
	str x27, [x3, #27704]
	str x28, [x3, #27712]
	str x30, [x3, #27720]
	add x25, x0, #0
	add x26, x1, #0
	add x27, x2, #0
	add x28, x3, #0
	movz x24, #1, lsl #0
	movz x9, #4, lsl #0
	strb w9, [x28, #920]
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
	add x2, x25, #0
	ldr x9, [x2, #0]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	add x2, x25, #8
	ldr x9, [x2, #0]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	add x2, x25, #16
	ldr x9, [x2, #0]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	add x2, x25, #24
	ldr x9, [x2, #0]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	add x2, x28, #920
	ldrb w9, [x2, #0]
	ldrb w10, [x28, #32]
	eor x9, x9, x10
	strb w9, [x28, #32]
	ldrb w9, [x28, #33]
	movz x10, #6, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #33]
	ldrb w9, [x28, #71]
	movz x10, #128, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #71]
	add x0, x28, #0
	add x1, x28, #200
	bl {vg_keccak_f1600}
	ldr x9, [x28, #0]
	add x2, x28, #840
	str x9, [x2, #0]
	ldr x9, [x28, #8]
	add x2, x28, #848
	str x9, [x2, #0]
	ldr x9, [x28, #16]
	add x2, x28, #856
	str x9, [x2, #0]
	ldr x9, [x28, #24]
	add x2, x28, #864
	str x9, [x2, #0]
	ldr x9, [x28, #32]
	add x2, x28, #880
	str x9, [x2, #0]
	ldr x9, [x28, #40]
	add x2, x28, #888
	str x9, [x2, #0]
	ldr x9, [x28, #48]
	add x2, x28, #896
	str x9, [x2, #0]
	ldr x9, [x28, #56]
	add x2, x28, #904
	str x9, [x2, #0]
	ldr x30, [x28, #800]
	add x2, x28, #1056
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
	ldr x9, [x28, #880]
	str x9, [x28, #0]
	ldr x9, [x28, #888]
	str x9, [x28, #8]
	ldr x9, [x28, #896]
	str x9, [x28, #16]
	ldr x9, [x28, #904]
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
	movz x2, #25632, lsl #0
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
	ldr x9, [x28, #880]
	str x9, [x28, #0]
	ldr x9, [x28, #888]
	str x9, [x28, #8]
	ldr x9, [x28, #896]
	str x9, [x28, #16]
	ldr x9, [x28, #904]
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
	movz x2, #25800, lsl #0
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
	ldr x9, [x28, #880]
	str x9, [x28, #0]
	ldr x9, [x28, #888]
	str x9, [x28, #8]
	ldr x9, [x28, #896]
	str x9, [x28, #16]
	ldr x9, [x28, #904]
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
	movz x2, #25968, lsl #0
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
	movz x21, #4128, lsl #0
	add x21, x28, x21
	movz x23, #5152, lsl #0
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
	add x2, x28, #1056
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
	movz x7, #3, lsl #0
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
	ldr x9, [x28, #880]
	str x9, [x28, #0]
	ldr x9, [x28, #888]
	str x9, [x28, #8]
	ldr x9, [x28, #896]
	str x9, [x28, #16]
	ldr x9, [x28, #904]
	str x9, [x28, #24]
	movz x9, #7939, lsl #0
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
	movz x2, #26136, lsl #0
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
	ldr x9, [x28, #880]
	str x9, [x28, #0]
	ldr x9, [x28, #888]
	str x9, [x28, #8]
	ldr x9, [x28, #896]
	str x9, [x28, #16]
	ldr x9, [x28, #904]
	str x9, [x28, #24]
	movz x9, #7940, lsl #0
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
	movz x2, #26304, lsl #0
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
	ldr x9, [x28, #880]
	str x9, [x28, #0]
	ldr x9, [x28, #888]
	str x9, [x28, #8]
	ldr x9, [x28, #896]
	str x9, [x28, #16]
	ldr x9, [x28, #904]
	str x9, [x28, #24]
	movz x9, #7941, lsl #0
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
	movz x2, #26472, lsl #0
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
	movz x21, #6176, lsl #0
	add x21, x28, x21
	movz x23, #7200, lsl #0
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
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #20512, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #20512, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem16_ntt}
	movz x0, #25800, lsl #0
	add x0, x28, x0
	movz x1, #21536, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #21536, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem16_ntt}
	movz x0, #25968, lsl #0
	add x0, x28, x0
	movz x1, #22560, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #22560, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem16_ntt}
	movz x0, #26136, lsl #0
	add x0, x28, x0
	movz x1, #23584, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #23584, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem16_ntt}
	movz x0, #26304, lsl #0
	add x0, x28, x0
	movz x1, #45056, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #45056, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem16_ntt}
	movz x0, #26472, lsl #0
	add x0, x28, x0
	movz x1, #46080, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #46080, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem16_ntt}
	add x2, x28, #1056
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
	ldr x6, [x28, #880]
	dup v0.2d, x6
	str q0, [x19, #0]
	ldr x6, [x28, #888]
	dup v0.2d, x6
	str q0, [x19, #16]
	ldr x6, [x28, #896]
	dup v0.2d, x6
	str q0, [x19, #32]
	ldr x6, [x28, #904]
	dup v0.2d, x6
	str q0, [x19, #48]
	movz x6, #7942, lsl #0
	movz x7, #7943, lsl #0
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x19, #64]
	movz x6, #32768, lsl #48
	dup v0.2d, x6
	str q0, [x19, #256]
	add x20, x19, #400
	add x21, x19, #528
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
	add x0, x19, #400
	movz x1, #47104, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #47104, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem16_ntt}
	add x0, x19, #528
	movz x1, #48128, lsl #0
	add x1, x28, x1
	bl {vg_mlkem16_cbd2}
	movz x0, #48128, lsl #0
	add x0, x28, x0
	add x1, x28, #3104
	bl {vg_mlkem16_ntt}
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	movz x0, #20512, lsl #0
	add x0, x28, x0
	add x1, x27, #0
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2118:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2118b
	movz x0, #21536, lsl #0
	add x0, x28, x0
	add x1, x27, #384
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2119:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2119b
	movz x0, #22560, lsl #0
	add x0, x28, x0
	add x1, x27, #768
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2120:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2120b
	movz x0, #23584, lsl #0
	add x0, x28, x0
	add x1, x27, #1152
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2121:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2121b
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
	movz x0, #25632, lsl #0
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
2122:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #4128, lsl #0
	add x1, x28, x1
	movz x2, #20512, lsl #0
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
	movz x1, #5152, lsl #0
	add x1, x28, x1
	movz x2, #21536, lsl #0
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
	movz x1, #6176, lsl #0
	add x1, x28, x1
	movz x2, #22560, lsl #0
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
	movz x1, #7200, lsl #0
	add x1, x28, x1
	movz x2, #23584, lsl #0
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
	cbnz x11, 2122b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #45056, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2123:
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
	cbnz x11, 2123b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x26, #0
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2124:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2124b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x27, #1536
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2125:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2125b
	add x2, x28, #1056
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
	movz x6, #256, lsl #0
	movk x6, #31, lsl #16
	movz x7, #257, lsl #0
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
	ldr x9, [x26, #0]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #8]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #16]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #24]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #32]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #40]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #48]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #56]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #64]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #72]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #80]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #88]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #96]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #104]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #112]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #120]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #128]
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
	ldr x9, [x26, #136]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #144]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #152]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #160]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #168]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #176]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #184]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #192]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #200]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #208]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #216]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #224]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #232]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #240]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #248]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #256]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #264]
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
	movz x21, #8224, lsl #0
	add x21, x28, x21
	movz x23, #9248, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2126:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2127:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2128f
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
	cbz x4, 2138f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2140f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2141f
2140:
2141:
	b 2139f
2138:
2139:
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
	cbz x4, 2142f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2144f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2145f
2144:
2145:
	b 2143f
2142:
2143:
	cbz x4, 2146f
	b 2147f
2146:
	movz x5, #0, lsl #0
2147:
	b 2129f
2128:
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
2129:
	cbnz x5, 2127b
	cbz x4, 2148f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2149f
2148:
2149:
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
	cbnz x6, 2126b
	add x6, x22, #0
	cbz x6, 2150f
	b 2151f
2150:
	movz x30, #1, lsl #0
2152:
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
2153:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2154f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2156:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2157f
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
	cbz x4, 2167f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2169f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2170f
2169:
2170:
	b 2168f
2167:
2168:
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
	cbz x4, 2171f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2173f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2174f
2173:
2174:
	b 2172f
2171:
2172:
	cbz x4, 2175f
	b 2176f
2175:
	movz x5, #0, lsl #0
2176:
	b 2158f
2157:
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
2158:
	cbnz x5, 2156b
	cbz x4, 2177f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2178f
2177:
2178:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2155f
2154:
	movz x0, #1, lsl #0
2155:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2153b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2152b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2179f
2181:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2181b
	b 2180f
2179:
2180:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2182f
2184:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2184b
	b 2183f
2182:
2183:
2151:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	add x2, x28, #1056
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
	movz x6, #258, lsl #0
	movk x6, #31, lsl #16
	movz x7, #259, lsl #0
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
	movz x21, #10272, lsl #0
	add x21, x28, x21
	movz x23, #11296, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2185:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2186:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2187f
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
	cbz x4, 2189f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2191f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2192f
2191:
2192:
	b 2190f
2189:
2190:
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
	cbz x4, 2193f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2195f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2196f
2195:
2196:
	b 2194f
2193:
2194:
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
	cbz x4, 2197f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2199f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2200f
2199:
2200:
	b 2198f
2197:
2198:
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
	cbz x4, 2201f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2203f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2204f
2203:
2204:
	b 2202f
2201:
2202:
	cbz x4, 2205f
	b 2206f
2205:
	movz x5, #0, lsl #0
2206:
	b 2188f
2187:
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
2188:
	cbnz x5, 2186b
	cbz x4, 2207f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2208f
2207:
2208:
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
	cbnz x6, 2185b
	add x6, x22, #0
	cbz x6, 2209f
	b 2210f
2209:
	movz x30, #1, lsl #0
2211:
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
2212:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2213f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2215:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2216f
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
	cbz x4, 2222f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2224f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2225f
2224:
2225:
	b 2223f
2222:
2223:
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
	cbz x4, 2226f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2228f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2229f
2228:
2229:
	b 2227f
2226:
2227:
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
	cbz x4, 2230f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2232f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2233f
2232:
2233:
	b 2231f
2230:
2231:
	cbz x4, 2234f
	b 2235f
2234:
	movz x5, #0, lsl #0
2235:
	b 2217f
2216:
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
2217:
	cbnz x5, 2215b
	cbz x4, 2236f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2237f
2236:
2237:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2214f
2213:
	movz x0, #1, lsl #0
2214:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2212b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2211b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2238f
2240:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2240b
	b 2239f
2238:
2239:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2241f
2243:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2243b
	b 2242f
2241:
2242:
2210:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	movz x0, #25632, lsl #0
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
2244:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #8224, lsl #0
	add x1, x28, x1
	movz x2, #20512, lsl #0
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
	movz x1, #9248, lsl #0
	add x1, x28, x1
	movz x2, #21536, lsl #0
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
	movz x1, #10272, lsl #0
	add x1, x28, x1
	movz x2, #22560, lsl #0
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
	movz x1, #11296, lsl #0
	add x1, x28, x1
	movz x2, #23584, lsl #0
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
	cbnz x11, 2244b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #46080, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2245:
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
	cbnz x11, 2245b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x26, #384
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2246:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2246b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x27, #1920
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2247:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2247b
	add x2, x28, #1056
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
	ldr x9, [x26, #272]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #280]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #288]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #296]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #304]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #312]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #320]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #328]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #336]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #344]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #352]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #360]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #368]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #376]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #384]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #392]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #400]
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
	ldr x9, [x26, #408]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #416]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #424]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #432]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #440]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #448]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #456]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #464]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #472]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #480]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #488]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #496]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #504]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #512]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #520]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #528]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #536]
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
	ldr x9, [x26, #544]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #552]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #560]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #568]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #576]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #584]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #592]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #600]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #608]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #616]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #624]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #632]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #640]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #648]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #656]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #664]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #672]
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
	movz x21, #12320, lsl #0
	add x21, x28, x21
	movz x23, #13344, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2248:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2249:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2250f
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
	cbz x4, 2252f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2254f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2255f
2254:
2255:
	b 2253f
2252:
2253:
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
	cbz x4, 2256f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2258f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2259f
2258:
2259:
	b 2257f
2256:
2257:
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
	cbz x4, 2260f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2262f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2263f
2262:
2263:
	b 2261f
2260:
2261:
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
	cbz x4, 2264f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2266f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2267f
2266:
2267:
	b 2265f
2264:
2265:
	cbz x4, 2268f
	b 2269f
2268:
	movz x5, #0, lsl #0
2269:
	b 2251f
2250:
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
2251:
	cbnz x5, 2249b
	cbz x4, 2270f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2271f
2270:
2271:
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
	cbnz x6, 2248b
	add x6, x22, #0
	cbz x6, 2272f
	b 2273f
2272:
	movz x30, #1, lsl #0
2274:
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
2275:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2276f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2278:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2279f
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
	cbz x4, 2281f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2283f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2284f
2283:
2284:
	b 2282f
2281:
2282:
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
	cbz x4, 2285f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2287f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2288f
2287:
2288:
	b 2286f
2285:
2286:
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
	cbz x4, 2289f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2291f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2292f
2291:
2292:
	b 2290f
2289:
2290:
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
	cbz x4, 2293f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2295f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2296f
2295:
2296:
	b 2294f
2293:
2294:
	cbz x4, 2297f
	b 2298f
2297:
	movz x5, #0, lsl #0
2298:
	b 2280f
2279:
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
2280:
	cbnz x5, 2278b
	cbz x4, 2299f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2300f
2299:
2300:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2277f
2276:
	movz x0, #1, lsl #0
2277:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2275b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2274b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2301f
2303:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2303b
	b 2302f
2301:
2302:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2304f
2306:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2306b
	b 2305f
2304:
2305:
2273:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	add x2, x28, #1056
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
	movz x7, #515, lsl #0
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
	movz x21, #14368, lsl #0
	add x21, x28, x21
	movz x23, #15392, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2307:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2308:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2309f
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
	cbz x4, 2311f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2313f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2314f
2313:
2314:
	b 2312f
2311:
2312:
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
	cbz x4, 2315f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2317f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2318f
2317:
2318:
	b 2316f
2315:
2316:
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
	cbz x4, 2319f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2321f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2322f
2321:
2322:
	b 2320f
2319:
2320:
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
	cbz x4, 2323f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2325f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2326f
2325:
2326:
	b 2324f
2323:
2324:
	cbz x4, 2327f
	b 2328f
2327:
	movz x5, #0, lsl #0
2328:
	b 2310f
2309:
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
2310:
	cbnz x5, 2308b
	cbz x4, 2329f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2330f
2329:
2330:
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
	cbnz x6, 2307b
	add x6, x22, #0
	cbz x6, 2331f
	b 2332f
2331:
	movz x30, #1, lsl #0
2333:
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
2334:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2335f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2337:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2338f
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
	cbz x4, 2340f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2342f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2343f
2342:
2343:
	b 2341f
2340:
2341:
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
	cbz x4, 2344f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2346f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2347f
2346:
2347:
	b 2345f
2344:
2345:
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
	cbz x4, 2348f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2350f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2351f
2350:
2351:
	b 2349f
2348:
2349:
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
	cbz x4, 2352f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2354f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2355f
2354:
2355:
	b 2353f
2352:
2353:
	cbz x4, 2356f
	b 2357f
2356:
	movz x5, #0, lsl #0
2357:
	b 2339f
2338:
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
2339:
	cbnz x5, 2337b
	cbz x4, 2358f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2359f
2358:
2359:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2336f
2335:
	movz x0, #1, lsl #0
2336:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2334b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2333b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2360f
2362:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2362b
	b 2361f
2360:
2361:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2363f
2365:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2365b
	b 2364f
2363:
2364:
2332:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	movz x0, #25632, lsl #0
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
2366:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #12320, lsl #0
	add x1, x28, x1
	movz x2, #20512, lsl #0
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
	movz x1, #13344, lsl #0
	add x1, x28, x1
	movz x2, #21536, lsl #0
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
	movz x1, #14368, lsl #0
	add x1, x28, x1
	movz x2, #22560, lsl #0
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
	movz x1, #15392, lsl #0
	add x1, x28, x1
	movz x2, #23584, lsl #0
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
	cbnz x11, 2366b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #47104, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2367:
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
	cbnz x11, 2367b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x26, #768
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2368:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2368b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x27, #2304
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2369:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2369b
	add x2, x28, #1056
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
	movz x6, #768, lsl #0
	movk x6, #31, lsl #16
	movz x7, #769, lsl #0
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
	ldr x9, [x26, #680]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #688]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #696]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #704]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #712]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #720]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #728]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #736]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #744]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #752]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #760]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #768]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #776]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #784]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #792]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #800]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #808]
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
	ldr x9, [x26, #816]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #824]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #832]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #840]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #848]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #856]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #864]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #872]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #880]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #888]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #896]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #904]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #912]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #920]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #928]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #936]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #944]
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
	ldr x9, [x26, #952]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #960]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #968]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #976]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #984]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #992]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #1000]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #1008]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #1016]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #1024]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #1032]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #1040]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #1048]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #1056]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #1064]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #1072]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #1080]
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
	movz x21, #16416, lsl #0
	add x21, x28, x21
	movz x23, #17440, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2370:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2371:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2372f
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
	cbz x4, 2374f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2376f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2377f
2376:
2377:
	b 2375f
2374:
2375:
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
	cbz x4, 2378f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2380f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2381f
2380:
2381:
	b 2379f
2378:
2379:
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
	cbz x4, 2382f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2384f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2385f
2384:
2385:
	b 2383f
2382:
2383:
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
	cbz x4, 2386f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2388f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2389f
2388:
2389:
	b 2387f
2386:
2387:
	cbz x4, 2390f
	b 2391f
2390:
	movz x5, #0, lsl #0
2391:
	b 2373f
2372:
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
2373:
	cbnz x5, 2371b
	cbz x4, 2392f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2393f
2392:
2393:
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
	cbnz x6, 2370b
	add x6, x22, #0
	cbz x6, 2394f
	b 2395f
2394:
	movz x30, #1, lsl #0
2396:
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
2397:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2398f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2400:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2401f
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
	cbz x4, 2403f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2405f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2406f
2405:
2406:
	b 2404f
2403:
2404:
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
	cbz x4, 2407f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2409f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2410f
2409:
2410:
	b 2408f
2407:
2408:
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
	cbz x4, 2411f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2413f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2414f
2413:
2414:
	b 2412f
2411:
2412:
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
	cbz x4, 2415f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2417f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2418f
2417:
2418:
	b 2416f
2415:
2416:
	cbz x4, 2419f
	b 2420f
2419:
	movz x5, #0, lsl #0
2420:
	b 2402f
2401:
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
2402:
	cbnz x5, 2400b
	cbz x4, 2421f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2422f
2421:
2422:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2399f
2398:
	movz x0, #1, lsl #0
2399:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2397b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2396b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2423f
2425:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2425b
	b 2424f
2423:
2424:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2426f
2428:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2428b
	b 2427f
2426:
2427:
2395:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	add x2, x28, #1056
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
	movz x6, #770, lsl #0
	movk x6, #31, lsl #16
	movz x7, #771, lsl #0
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
	movz x21, #18464, lsl #0
	add x21, x28, x21
	movz x23, #19488, lsl #0
	add x23, x28, x23
	add x20, x19, #400
	add x1, x19, #1680
	movz x22, #1, lsl #0
2429:
	add x2, x20, #0
	add x3, x21, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2430:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2431f
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
	cbz x4, 2433f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2435f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2436f
2435:
2436:
	b 2434f
2433:
2434:
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
	cbz x4, 2437f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2439f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2440f
2439:
2440:
	b 2438f
2437:
2438:
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
	cbz x4, 2441f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2443f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2444f
2443:
2444:
	b 2442f
2441:
2442:
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
	cbz x4, 2445f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2447f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2448f
2447:
2448:
	b 2446f
2445:
2446:
	cbz x4, 2449f
	b 2450f
2449:
	movz x5, #0, lsl #0
2450:
	b 2432f
2431:
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
2432:
	cbnz x5, 2430b
	cbz x4, 2451f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2452f
2451:
2452:
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
	cbnz x6, 2429b
	add x6, x22, #0
	cbz x6, 2453f
	b 2454f
2453:
	movz x30, #1, lsl #0
2455:
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
2456:
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	cbz x4, 2457f
	add x2, x20, #0
	movz x5, #56, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
2459:
	sub x6, x4, #8
	lsr x6, x6, #63
	cbz x6, 2460f
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
	cbz x4, 2462f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2464f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2465f
2464:
2465:
	b 2463f
2462:
2463:
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
	cbz x4, 2466f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2468f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2469f
2468:
2469:
	b 2467f
2466:
2467:
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
	cbz x4, 2470f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2472f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2473f
2472:
2473:
	b 2471f
2470:
2471:
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
	cbz x4, 2474f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 2476f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #1
	add x3, x3, x15
	sub x4, x4, x14
	b 2477f
2476:
2477:
	b 2475f
2474:
2475:
	cbz x4, 2478f
	b 2479f
2478:
	movz x5, #0, lsl #0
2479:
	b 2461f
2460:
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
2461:
	cbnz x5, 2459b
	cbz x4, 2480f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 2481f
2480:
2481:
	sub x0, x4, #1
	lsr x0, x0, #63
	str x3, [x1, #0]
	str x4, [x1, #8]
	b 2458f
2457:
	movz x0, #1, lsl #0
2458:
	and x22, x22, x0
	add x20, x20, #504
	add x1, x1, #16
	sub x23, x23, #1
	cbnz x23, 2456b
	add x6, x22, #0
	sub x7, x6, x30
	lsr x7, x7, #63
	movz x30, #0, lsl #0
	cbnz x7, 2455b
	and x24, x24, x6
	ldr x3, [x19, #1680]
	ldr x4, [x19, #1688]
	cbz x4, 2482f
2484:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2484b
	b 2483f
2482:
2483:
	ldr x3, [x19, #1696]
	ldr x4, [x19, #1704]
	cbz x4, 2485f
2487:
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	add x3, x3, #2
	sub x4, x4, #1
	cbnz x4, 2487b
	b 2486f
2485:
2486:
2454:
	ldr x30, [x19, #1840]
	ldr x23, [x19, #1832]
	ldr x22, [x19, #1824]
	ldr x21, [x19, #1816]
	ldr x20, [x19, #1808]
	ldr x19, [x19, #1800]
	movz x0, #25632, lsl #0
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
2488:
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movz x1, #16416, lsl #0
	add x1, x28, x1
	movz x2, #20512, lsl #0
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
	movz x1, #17440, lsl #0
	add x1, x28, x1
	movz x2, #21536, lsl #0
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
	movz x1, #18464, lsl #0
	add x1, x28, x1
	movz x2, #22560, lsl #0
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
	movz x1, #19488, lsl #0
	add x1, x28, x1
	movz x2, #23584, lsl #0
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
	cbnz x11, 2488b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	movz x1, #48128, lsl #0
	add x1, x28, x1
	movz x9, #3329, lsl #0
	dup v16.8h, w9
	movz x11, #32, lsl #0
2489:
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
	cbnz x11, 2489b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x26, #1152
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2490:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2490b
	movz x0, #25632, lsl #0
	add x0, x28, x0
	add x1, x27, #2688
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movi v17.2d, #0
	movz x11, #32, lsl #0
2491:
	ldr q4, [x0, #0]
	zip1 v0.8h, v4.8h, v17.8h
	zip2 v1.8h, v4.8h, v17.8h
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #16
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 2491b
	ldr x9, [x28, #840]
	str x9, [x26, #1536]
	ldr x9, [x28, #848]
	str x9, [x26, #1544]
	ldr x9, [x28, #856]
	str x9, [x26, #1552]
	ldr x9, [x28, #864]
	str x9, [x26, #1560]
	ldr x9, [x28, #840]
	str x9, [x27, #3072]
	ldr x9, [x28, #848]
	str x9, [x27, #3080]
	ldr x9, [x28, #856]
	str x9, [x27, #3088]
	ldr x9, [x28, #864]
	str x9, [x27, #3096]
	ldr x9, [x26, #1088]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #1096]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #1104]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #1112]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #1120]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #1128]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #1136]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #1144]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #1152]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #1160]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #1168]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #1176]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #1184]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #1192]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #1200]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #1208]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #1216]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x0, x28, #0
	add x1, x28, #200
	bl {vg_keccak_f1600}
	ldr x9, [x26, #1224]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #1232]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #1240]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #1248]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #1256]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #1264]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #1272]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #1280]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #1288]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #1296]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #1304]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #1312]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #1320]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #1328]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #1336]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #1344]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #1352]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x0, x28, #0
	add x1, x28, #200
	bl {vg_keccak_f1600}
	ldr x9, [x26, #1360]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #1368]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #1376]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #1384]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #1392]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #1400]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #1408]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #1416]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #1424]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldr x9, [x26, #1432]
	ldr x10, [x28, #72]
	eor x9, x9, x10
	str x9, [x28, #72]
	ldr x9, [x26, #1440]
	ldr x10, [x28, #80]
	eor x9, x9, x10
	str x9, [x28, #80]
	ldr x9, [x26, #1448]
	ldr x10, [x28, #88]
	eor x9, x9, x10
	str x9, [x28, #88]
	ldr x9, [x26, #1456]
	ldr x10, [x28, #96]
	eor x9, x9, x10
	str x9, [x28, #96]
	ldr x9, [x26, #1464]
	ldr x10, [x28, #104]
	eor x9, x9, x10
	str x9, [x28, #104]
	ldr x9, [x26, #1472]
	ldr x10, [x28, #112]
	eor x9, x9, x10
	str x9, [x28, #112]
	ldr x9, [x26, #1480]
	ldr x10, [x28, #120]
	eor x9, x9, x10
	str x9, [x28, #120]
	ldr x9, [x26, #1488]
	ldr x10, [x28, #128]
	eor x9, x9, x10
	str x9, [x28, #128]
	add x0, x28, #0
	add x1, x28, #200
	bl {vg_keccak_f1600}
	ldr x9, [x26, #1496]
	ldr x10, [x28, #0]
	eor x9, x9, x10
	str x9, [x28, #0]
	ldr x9, [x26, #1504]
	ldr x10, [x28, #8]
	eor x9, x9, x10
	str x9, [x28, #8]
	ldr x9, [x26, #1512]
	ldr x10, [x28, #16]
	eor x9, x9, x10
	str x9, [x28, #16]
	ldr x9, [x26, #1520]
	ldr x10, [x28, #24]
	eor x9, x9, x10
	str x9, [x28, #24]
	ldr x9, [x26, #1528]
	ldr x10, [x28, #32]
	eor x9, x9, x10
	str x9, [x28, #32]
	ldr x9, [x26, #1536]
	ldr x10, [x28, #40]
	eor x9, x9, x10
	str x9, [x28, #40]
	ldr x9, [x26, #1544]
	ldr x10, [x28, #48]
	eor x9, x9, x10
	str x9, [x28, #48]
	ldr x9, [x26, #1552]
	ldr x10, [x28, #56]
	eor x9, x9, x10
	str x9, [x28, #56]
	ldr x9, [x26, #1560]
	ldr x10, [x28, #64]
	eor x9, x9, x10
	str x9, [x28, #64]
	ldrb w9, [x28, #72]
	movz x10, #6, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #72]
	ldrb w9, [x28, #135]
	movz x10, #128, lsl #0
	eor x9, x9, x10
	strb w9, [x28, #135]
	add x0, x28, #0
	add x1, x28, #200
	bl {vg_keccak_f1600}
	ldr x9, [x28, #0]
	str x9, [x27, #3104]
	ldr x9, [x28, #8]
	str x9, [x27, #3112]
	ldr x9, [x28, #16]
	str x9, [x27, #3120]
	ldr x9, [x28, #24]
	str x9, [x27, #3128]
	ldr x9, [x25, #32]
	str x9, [x27, #3136]
	ldr x9, [x25, #40]
	str x9, [x27, #3144]
	ldr x9, [x25, #48]
	str x9, [x27, #3152]
	ldr x9, [x25, #56]
	str x9, [x27, #3160]
	add x0, x24, #0
	ldr x30, [x28, #27720]
	ldr x24, [x28, #27680]
	ldr x25, [x28, #27688]
	ldr x26, [x28, #27696]
	ldr x27, [x28, #27704]
	ldr x28, [x28, #27712]
	ret
	.p2align 6
