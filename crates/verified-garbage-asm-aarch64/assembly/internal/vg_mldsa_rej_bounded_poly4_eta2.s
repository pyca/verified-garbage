// The functions of `src/internal/vg_mldsa_rej_bounded_poly4_eta2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_bounded_poly4_eta2:
	str x19, [x2, #7968]
	str x20, [x2, #7976]
	str x21, [x2, #7984]
	str x22, [x2, #7992]
	str x23, [x2, #8000]
	str x24, [x2, #8008]
	str x25, [x2, #8016]
	str x26, [x2, #8024]
	str x27, [x2, #8032]
	str x28, [x2, #8040]
	umov x8, v8.d[0]
	str x8, [x2, #8048]
	umov x8, v9.d[0]
	str x8, [x2, #8056]
	umov x8, v10.d[0]
	str x8, [x2, #8064]
	umov x8, v11.d[0]
	str x8, [x2, #8072]
	umov x8, v12.d[0]
	str x8, [x2, #8080]
	umov x8, v13.d[0]
	str x8, [x2, #8088]
	umov x8, v14.d[0]
	str x8, [x2, #8096]
	umov x8, v15.d[0]
	str x8, [x2, #8104]
	add x19, x2, #0
	add x20, x0, #0
	add x21, x1, #0
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
	str q0, [x19, #400]
	str q0, [x19, #416]
	str q0, [x19, #432]
	str q0, [x19, #448]
	str q0, [x19, #464]
	str q0, [x19, #480]
	str q0, [x19, #496]
	str q0, [x19, #512]
	str q0, [x19, #528]
	str q0, [x19, #544]
	str q0, [x19, #560]
	str q0, [x19, #576]
	str q0, [x19, #592]
	str q0, [x19, #608]
	str q0, [x19, #624]
	str q0, [x19, #640]
	str q0, [x19, #656]
	str q0, [x19, #672]
	str q0, [x19, #688]
	str q0, [x19, #704]
	str q0, [x19, #720]
	str q0, [x19, #736]
	str q0, [x19, #752]
	str q0, [x19, #768]
	str q0, [x19, #784]
	add x2, x19, #0
	add x3, x20, #0
	add x4, x3, #66
	ldr x6, [x3, #0]
	ldr x7, [x4, #0]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #0]
	ldr x6, [x3, #8]
	ldr x7, [x4, #8]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #16]
	ldr x6, [x3, #16]
	ldr x7, [x4, #16]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #32]
	ldr x6, [x3, #24]
	ldr x7, [x4, #24]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #48]
	ldr x6, [x3, #32]
	ldr x7, [x4, #32]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #64]
	ldr x6, [x3, #40]
	ldr x7, [x4, #40]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #80]
	ldr x6, [x3, #48]
	ldr x7, [x4, #48]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #96]
	ldr x6, [x3, #56]
	ldr x7, [x4, #56]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #112]
	ldrb w6, [x3, #64]
	ldrb w8, [x3, #65]
	lsl x8, x8, #8
	add x6, x6, x8
	ldrb w7, [x4, #64]
	ldrb w8, [x4, #65]
	lsl x8, x8, #8
	add x7, x7, x8
	movz x9, #31, lsl #16
	add x6, x6, x9
	add x7, x7, x9
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #128]
	movz x9, #32768, lsl #48
	dup v0.2d, x9
	str q0, [x2, #256]
	add x2, x19, #400
	add x3, x20, #132
	add x4, x3, #66
	ldr x6, [x3, #0]
	ldr x7, [x4, #0]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #0]
	ldr x6, [x3, #8]
	ldr x7, [x4, #8]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #16]
	ldr x6, [x3, #16]
	ldr x7, [x4, #16]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #32]
	ldr x6, [x3, #24]
	ldr x7, [x4, #24]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #48]
	ldr x6, [x3, #32]
	ldr x7, [x4, #32]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #64]
	ldr x6, [x3, #40]
	ldr x7, [x4, #40]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #80]
	ldr x6, [x3, #48]
	ldr x7, [x4, #48]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #96]
	ldr x6, [x3, #56]
	ldr x7, [x4, #56]
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #112]
	ldrb w6, [x3, #64]
	ldrb w8, [x3, #65]
	lsl x8, x8, #8
	add x6, x6, x8
	ldrb w7, [x4, #64]
	ldrb w8, [x4, #65]
	lsl x8, x8, #8
	add x7, x7, x8
	movz x9, #31, lsl #16
	add x6, x6, x9
	add x7, x7, x9
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #128]
	movz x9, #32768, lsl #48
	dup v0.2d, x9
	str q0, [x2, #256]
	movz x4, #256, lsl #0
	str x4, [x19, #7904]
	str x4, [x19, #7912]
	str x4, [x19, #7920]
	str x4, [x19, #7928]
	movz x6, #3340, lsl #0
	movk x6, #3854, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6000]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6008]
	movz x6, #0, lsl #0
	str x6, [x19, #6032]
	movz x6, #256, lsl #0
	movk x6, #770, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #3854, lsl #48
	str x6, [x19, #6064]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6072]
	movz x6, #1, lsl #0
	str x6, [x19, #6096]
	movz x6, #1284, lsl #0
	movk x6, #1798, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #3854, lsl #48
	str x6, [x19, #6128]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6136]
	movz x6, #1, lsl #0
	str x6, [x19, #6160]
	movz x6, #256, lsl #0
	movk x6, #770, lsl #16
	movk x6, #1284, lsl #32
	movk x6, #1798, lsl #48
	str x6, [x19, #6192]
	movz x6, #3340, lsl #0
	movk x6, #3854, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6200]
	movz x6, #2, lsl #0
	str x6, [x19, #6224]
	movz x6, #2312, lsl #0
	movk x6, #2826, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #3854, lsl #48
	str x6, [x19, #6256]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6264]
	movz x6, #1, lsl #0
	str x6, [x19, #6288]
	movz x6, #256, lsl #0
	movk x6, #770, lsl #16
	movk x6, #2312, lsl #32
	movk x6, #2826, lsl #48
	str x6, [x19, #6320]
	movz x6, #3340, lsl #0
	movk x6, #3854, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6328]
	movz x6, #2, lsl #0
	str x6, [x19, #6352]
	movz x6, #1284, lsl #0
	movk x6, #1798, lsl #16
	movk x6, #2312, lsl #32
	movk x6, #2826, lsl #48
	str x6, [x19, #6384]
	movz x6, #3340, lsl #0
	movk x6, #3854, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6392]
	movz x6, #2, lsl #0
	str x6, [x19, #6416]
	movz x6, #256, lsl #0
	movk x6, #770, lsl #16
	movk x6, #1284, lsl #32
	movk x6, #1798, lsl #48
	str x6, [x19, #6448]
	movz x6, #2312, lsl #0
	movk x6, #2826, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #3854, lsl #48
	str x6, [x19, #6456]
	movz x6, #3, lsl #0
	str x6, [x19, #6480]
	movz x6, #3340, lsl #0
	movk x6, #3854, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6512]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6520]
	movz x6, #1, lsl #0
	str x6, [x19, #6544]
	movz x6, #256, lsl #0
	movk x6, #770, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #3854, lsl #48
	str x6, [x19, #6576]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6584]
	movz x6, #2, lsl #0
	str x6, [x19, #6608]
	movz x6, #1284, lsl #0
	movk x6, #1798, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #3854, lsl #48
	str x6, [x19, #6640]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6648]
	movz x6, #2, lsl #0
	str x6, [x19, #6672]
	movz x6, #256, lsl #0
	movk x6, #770, lsl #16
	movk x6, #1284, lsl #32
	movk x6, #1798, lsl #48
	str x6, [x19, #6704]
	movz x6, #3340, lsl #0
	movk x6, #3854, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6712]
	movz x6, #3, lsl #0
	str x6, [x19, #6736]
	movz x6, #2312, lsl #0
	movk x6, #2826, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #3854, lsl #48
	str x6, [x19, #6768]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6776]
	movz x6, #2, lsl #0
	str x6, [x19, #6800]
	movz x6, #256, lsl #0
	movk x6, #770, lsl #16
	movk x6, #2312, lsl #32
	movk x6, #2826, lsl #48
	str x6, [x19, #6832]
	movz x6, #3340, lsl #0
	movk x6, #3854, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6840]
	movz x6, #3, lsl #0
	str x6, [x19, #6864]
	movz x6, #1284, lsl #0
	movk x6, #1798, lsl #16
	movk x6, #2312, lsl #32
	movk x6, #2826, lsl #48
	str x6, [x19, #6896]
	movz x6, #3340, lsl #0
	movk x6, #3854, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	str x6, [x19, #6904]
	movz x6, #3, lsl #0
	str x6, [x19, #6928]
	movz x6, #256, lsl #0
	movk x6, #770, lsl #16
	movk x6, #1284, lsl #32
	movk x6, #1798, lsl #48
	str x6, [x19, #6960]
	movz x6, #2312, lsl #0
	movk x6, #2826, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #3854, lsl #48
	str x6, [x19, #6968]
	movz x6, #4, lsl #0
	str x6, [x19, #6992]
	add x22, x19, #0
	add x23, x19, #400
	add x24, x19, #840
	add x25, x19, #1384
	add x26, x19, #1928
	add x27, x19, #2472
	movz x28, #2, lsl #0
20:
	add x1, x19, #1512
	add x1, x1, #1512
	str x30, [x1, #128]
	add x0, x22, #0
	bl {vg_keccak_f1600_x2}
	ldr x30, [x1, #128]
	ldr x6, [x22, #0]
	ldr x7, [x22, #8]
	str x6, [x24, #0]
	str x7, [x25, #0]
	ldr x6, [x22, #16]
	ldr x7, [x22, #24]
	str x6, [x24, #8]
	str x7, [x25, #8]
	ldr x6, [x22, #32]
	ldr x7, [x22, #40]
	str x6, [x24, #16]
	str x7, [x25, #16]
	ldr x6, [x22, #48]
	ldr x7, [x22, #56]
	str x6, [x24, #24]
	str x7, [x25, #24]
	ldr x6, [x22, #64]
	ldr x7, [x22, #72]
	str x6, [x24, #32]
	str x7, [x25, #32]
	ldr x6, [x22, #80]
	ldr x7, [x22, #88]
	str x6, [x24, #40]
	str x7, [x25, #40]
	ldr x6, [x22, #96]
	ldr x7, [x22, #104]
	str x6, [x24, #48]
	str x7, [x25, #48]
	ldr x6, [x22, #112]
	ldr x7, [x22, #120]
	str x6, [x24, #56]
	str x7, [x25, #56]
	ldr x6, [x22, #128]
	ldr x7, [x22, #136]
	str x6, [x24, #64]
	str x7, [x25, #64]
	ldr x6, [x22, #144]
	ldr x7, [x22, #152]
	str x6, [x24, #72]
	str x7, [x25, #72]
	ldr x6, [x22, #160]
	ldr x7, [x22, #168]
	str x6, [x24, #80]
	str x7, [x25, #80]
	ldr x6, [x22, #176]
	ldr x7, [x22, #184]
	str x6, [x24, #88]
	str x7, [x25, #88]
	ldr x6, [x22, #192]
	ldr x7, [x22, #200]
	str x6, [x24, #96]
	str x7, [x25, #96]
	ldr x6, [x22, #208]
	ldr x7, [x22, #216]
	str x6, [x24, #104]
	str x7, [x25, #104]
	ldr x6, [x22, #224]
	ldr x7, [x22, #232]
	str x6, [x24, #112]
	str x7, [x25, #112]
	ldr x6, [x22, #240]
	ldr x7, [x22, #248]
	str x6, [x24, #120]
	str x7, [x25, #120]
	ldr x6, [x22, #256]
	ldr x7, [x22, #264]
	str x6, [x24, #128]
	str x7, [x25, #128]
	add x1, x19, #1512
	add x1, x1, #1512
	str x30, [x1, #128]
	add x0, x23, #0
	bl {vg_keccak_f1600_x2}
	ldr x30, [x1, #128]
	ldr x6, [x23, #0]
	ldr x7, [x23, #8]
	str x6, [x26, #0]
	str x7, [x27, #0]
	ldr x6, [x23, #16]
	ldr x7, [x23, #24]
	str x6, [x26, #8]
	str x7, [x27, #8]
	ldr x6, [x23, #32]
	ldr x7, [x23, #40]
	str x6, [x26, #16]
	str x7, [x27, #16]
	ldr x6, [x23, #48]
	ldr x7, [x23, #56]
	str x6, [x26, #24]
	str x7, [x27, #24]
	ldr x6, [x23, #64]
	ldr x7, [x23, #72]
	str x6, [x26, #32]
	str x7, [x27, #32]
	ldr x6, [x23, #80]
	ldr x7, [x23, #88]
	str x6, [x26, #40]
	str x7, [x27, #40]
	ldr x6, [x23, #96]
	ldr x7, [x23, #104]
	str x6, [x26, #48]
	str x7, [x27, #48]
	ldr x6, [x23, #112]
	ldr x7, [x23, #120]
	str x6, [x26, #56]
	str x7, [x27, #56]
	ldr x6, [x23, #128]
	ldr x7, [x23, #136]
	str x6, [x26, #64]
	str x7, [x27, #64]
	ldr x6, [x23, #144]
	ldr x7, [x23, #152]
	str x6, [x26, #72]
	str x7, [x27, #72]
	ldr x6, [x23, #160]
	ldr x7, [x23, #168]
	str x6, [x26, #80]
	str x7, [x27, #80]
	ldr x6, [x23, #176]
	ldr x7, [x23, #184]
	str x6, [x26, #88]
	str x7, [x27, #88]
	ldr x6, [x23, #192]
	ldr x7, [x23, #200]
	str x6, [x26, #96]
	str x7, [x27, #96]
	ldr x6, [x23, #208]
	ldr x7, [x23, #216]
	str x6, [x26, #104]
	str x7, [x27, #104]
	ldr x6, [x23, #224]
	ldr x7, [x23, #232]
	str x6, [x26, #112]
	str x7, [x27, #112]
	ldr x6, [x23, #240]
	ldr x7, [x23, #248]
	str x6, [x26, #120]
	str x7, [x27, #120]
	ldr x6, [x23, #256]
	ldr x7, [x23, #264]
	str x6, [x26, #128]
	str x7, [x27, #128]
	add x24, x24, #136
	add x25, x25, #136
	add x26, x26, #136
	add x27, x27, #136
	sub x28, x28, #1
	cbnz x28, 20b
	add x24, x19, #840
	add x25, x21, #0
	add x26, x19, #3952
	add x26, x26, #3952
	movz x27, #4, lsl #0
21:
	add x2, x24, #0
	add x3, x25, #0
	ldr x4, [x26, #0]
	movz x6, #256, lsl #0
	sub x6, x6, x4
	lsl x6, x6, #2
	add x3, x3, x6
	movz x5, #272, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #2, lsl #0
	movz x11, #15, lsl #0
	movz x15, #15, lsl #0
	movz x6, #65280, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65281, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #65282, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65283, lsl #32
	movk x7, #65535, lsl #48
	dup v25.2d, x6
	mov v25.d[1], x7
	dup v23.16b, w11
	dup v22.4s, w15
	dup v21.4s, w9
	dup v20.4s, w10
	add v20.4s, v20.4s, v21.4s
	movz x6, #13, lsl #0
	dup v18.4s, w6
	movz x6, #5, lsl #0
	dup v19.4s, w6
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #2, lsl #32
	movk x6, #0, lsl #48
	movz x7, #4, lsl #0
	movk x7, #0, lsl #16
	movk x7, #8, lsl #32
	movk x7, #0, lsl #48
	dup v24.2d, x6
	mov v24.d[1], x7
	movz x0, #0, lsl #0
	movz x16, #4, lsl #0
	add x12, x19, #3000
	add x12, x12, #3000
	subs x8, x4, x16
	csel x8, x5, x0, hs
	cbz x8, 22f
24:
	ldr w6, [x2, #0]
	dup v0.4s, w6
	and v1.16b, v0.16b, v23.16b
	ushr v0.16b, v0.16b, #4
	zip1 v0.16b, v1.16b, v0.16b
	tbl v1.16b, {v0.16b}, v25.16b
	sub v2.4s, v1.4s, v22.4s
	ushr v2.4s, v2.4s, #31
	mul v2.4s, v2.4s, v24.4s
	umov x6, v2.d[0]
	umov x7, v2.d[1]
	add x6, x6, x7
	lsr x7, x6, #32
	add x6, x6, x7
	and x6, x6, x11
	lsl x6, x6, #6
	add x13, x12, x6
	ldr q6, [x13, #0]
	ldr x6, [x13, #32]
	mul v2.4s, v1.4s, v18.4s
	ushr v2.4s, v2.4s, #6
	mul v2.4s, v2.4s, v19.4s
	sub v1.4s, v1.4s, v2.4s
	sub v1.4s, v20.4s, v1.4s
	sub v2.4s, v1.4s, v21.4s
	umin v1.4s, v1.4s, v2.4s
	tbl v1.16b, {v1.16b}, v6.16b
	str q1, [x3, #0]
	lsl x7, x6, #2
	add x3, x3, x7
	sub x4, x4, x6
	add x2, x2, #2
	sub x5, x5, #2
	subs x8, x4, x16
	csel x8, x5, x0, hs
	cbnz x8, 24b
	b 23f
22:
23:
	movz x16, #10, lsl #0
	movz x17, #5, lsl #0
	mul x8, x4, x5
	cbz x8, 25f
27:
	ldrb w6, [x2, #0]
	add x2, x2, #1
	sub x5, x5, #1
	and x7, x6, x11
	cbz x4, 28f
	sub x8, x7, x15
	lsr x12, x8, #63
	add x13, x7, #0
	sub x13, x13, x16
	lsr x14, x13, #63
	madd x13, x14, x16, x13
	sub x13, x13, x17
	lsr x14, x13, #63
	madd x13, x14, x17, x13
	sub x13, x10, x13
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsl x14, x12, #2
	add x3, x3, x14
	sub x4, x4, x12
	lsr x7, x6, #4
	cbz x4, 210f
	sub x8, x7, x15
	lsr x12, x8, #63
	add x13, x7, #0
	sub x13, x13, x16
	lsr x14, x13, #63
	madd x13, x14, x16, x13
	sub x13, x13, x17
	lsr x14, x13, #63
	madd x13, x14, x17, x13
	sub x13, x10, x13
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsl x14, x12, #2
	add x3, x3, x14
	sub x4, x4, x12
	b 211f
210:
211:
	b 29f
28:
29:
	mul x8, x4, x5
	cbnz x8, 27b
	b 26f
25:
26:
	str x4, [x26, #0]
	add x24, x24, #544
	add x25, x25, #1024
	add x26, x26, #8
	sub x27, x27, #1
	cbnz x27, 21b
	ldr x27, [x19, #7904]
	ldr x6, [x19, #7912]
	orr x27, x27, x6
	ldr x6, [x19, #7920]
	orr x27, x27, x6
	ldr x6, [x19, #7928]
	orr x27, x27, x6
	cbz x27, 212f
	add x22, x19, #0
	add x23, x19, #400
	add x24, x19, #1112
	add x25, x19, #1656
	add x26, x19, #2200
	add x27, x19, #2744
	movz x28, #2, lsl #0
214:
	add x1, x19, #1512
	add x1, x1, #1512
	str x30, [x1, #128]
	add x0, x22, #0
	bl {vg_keccak_f1600_x2}
	ldr x30, [x1, #128]
	ldr x6, [x22, #0]
	ldr x7, [x22, #8]
	str x6, [x24, #0]
	str x7, [x25, #0]
	ldr x6, [x22, #16]
	ldr x7, [x22, #24]
	str x6, [x24, #8]
	str x7, [x25, #8]
	ldr x6, [x22, #32]
	ldr x7, [x22, #40]
	str x6, [x24, #16]
	str x7, [x25, #16]
	ldr x6, [x22, #48]
	ldr x7, [x22, #56]
	str x6, [x24, #24]
	str x7, [x25, #24]
	ldr x6, [x22, #64]
	ldr x7, [x22, #72]
	str x6, [x24, #32]
	str x7, [x25, #32]
	ldr x6, [x22, #80]
	ldr x7, [x22, #88]
	str x6, [x24, #40]
	str x7, [x25, #40]
	ldr x6, [x22, #96]
	ldr x7, [x22, #104]
	str x6, [x24, #48]
	str x7, [x25, #48]
	ldr x6, [x22, #112]
	ldr x7, [x22, #120]
	str x6, [x24, #56]
	str x7, [x25, #56]
	ldr x6, [x22, #128]
	ldr x7, [x22, #136]
	str x6, [x24, #64]
	str x7, [x25, #64]
	ldr x6, [x22, #144]
	ldr x7, [x22, #152]
	str x6, [x24, #72]
	str x7, [x25, #72]
	ldr x6, [x22, #160]
	ldr x7, [x22, #168]
	str x6, [x24, #80]
	str x7, [x25, #80]
	ldr x6, [x22, #176]
	ldr x7, [x22, #184]
	str x6, [x24, #88]
	str x7, [x25, #88]
	ldr x6, [x22, #192]
	ldr x7, [x22, #200]
	str x6, [x24, #96]
	str x7, [x25, #96]
	ldr x6, [x22, #208]
	ldr x7, [x22, #216]
	str x6, [x24, #104]
	str x7, [x25, #104]
	ldr x6, [x22, #224]
	ldr x7, [x22, #232]
	str x6, [x24, #112]
	str x7, [x25, #112]
	ldr x6, [x22, #240]
	ldr x7, [x22, #248]
	str x6, [x24, #120]
	str x7, [x25, #120]
	ldr x6, [x22, #256]
	ldr x7, [x22, #264]
	str x6, [x24, #128]
	str x7, [x25, #128]
	add x1, x19, #1512
	add x1, x1, #1512
	str x30, [x1, #128]
	add x0, x23, #0
	bl {vg_keccak_f1600_x2}
	ldr x30, [x1, #128]
	ldr x6, [x23, #0]
	ldr x7, [x23, #8]
	str x6, [x26, #0]
	str x7, [x27, #0]
	ldr x6, [x23, #16]
	ldr x7, [x23, #24]
	str x6, [x26, #8]
	str x7, [x27, #8]
	ldr x6, [x23, #32]
	ldr x7, [x23, #40]
	str x6, [x26, #16]
	str x7, [x27, #16]
	ldr x6, [x23, #48]
	ldr x7, [x23, #56]
	str x6, [x26, #24]
	str x7, [x27, #24]
	ldr x6, [x23, #64]
	ldr x7, [x23, #72]
	str x6, [x26, #32]
	str x7, [x27, #32]
	ldr x6, [x23, #80]
	ldr x7, [x23, #88]
	str x6, [x26, #40]
	str x7, [x27, #40]
	ldr x6, [x23, #96]
	ldr x7, [x23, #104]
	str x6, [x26, #48]
	str x7, [x27, #48]
	ldr x6, [x23, #112]
	ldr x7, [x23, #120]
	str x6, [x26, #56]
	str x7, [x27, #56]
	ldr x6, [x23, #128]
	ldr x7, [x23, #136]
	str x6, [x26, #64]
	str x7, [x27, #64]
	ldr x6, [x23, #144]
	ldr x7, [x23, #152]
	str x6, [x26, #72]
	str x7, [x27, #72]
	ldr x6, [x23, #160]
	ldr x7, [x23, #168]
	str x6, [x26, #80]
	str x7, [x27, #80]
	ldr x6, [x23, #176]
	ldr x7, [x23, #184]
	str x6, [x26, #88]
	str x7, [x27, #88]
	ldr x6, [x23, #192]
	ldr x7, [x23, #200]
	str x6, [x26, #96]
	str x7, [x27, #96]
	ldr x6, [x23, #208]
	ldr x7, [x23, #216]
	str x6, [x26, #104]
	str x7, [x27, #104]
	ldr x6, [x23, #224]
	ldr x7, [x23, #232]
	str x6, [x26, #112]
	str x7, [x27, #112]
	ldr x6, [x23, #240]
	ldr x7, [x23, #248]
	str x6, [x26, #120]
	str x7, [x27, #120]
	ldr x6, [x23, #256]
	ldr x7, [x23, #264]
	str x6, [x26, #128]
	str x7, [x27, #128]
	add x24, x24, #136
	add x25, x25, #136
	add x26, x26, #136
	add x27, x27, #136
	sub x28, x28, #1
	cbnz x28, 214b
	add x24, x19, #1112
	add x25, x21, #0
	add x26, x19, #3952
	add x26, x26, #3952
	movz x27, #4, lsl #0
215:
	add x2, x24, #0
	add x3, x25, #0
	ldr x4, [x26, #0]
	movz x6, #256, lsl #0
	sub x6, x6, x4
	lsl x6, x6, #2
	add x3, x3, x6
	movz x5, #272, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #2, lsl #0
	movz x11, #15, lsl #0
	movz x15, #15, lsl #0
	movz x6, #65280, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65281, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #65282, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #65283, lsl #32
	movk x7, #65535, lsl #48
	dup v25.2d, x6
	mov v25.d[1], x7
	dup v23.16b, w11
	dup v22.4s, w15
	dup v21.4s, w9
	dup v20.4s, w10
	add v20.4s, v20.4s, v21.4s
	movz x6, #13, lsl #0
	dup v18.4s, w6
	movz x6, #5, lsl #0
	dup v19.4s, w6
	movz x6, #1, lsl #0
	movk x6, #0, lsl #16
	movk x6, #2, lsl #32
	movk x6, #0, lsl #48
	movz x7, #4, lsl #0
	movk x7, #0, lsl #16
	movk x7, #8, lsl #32
	movk x7, #0, lsl #48
	dup v24.2d, x6
	mov v24.d[1], x7
	movz x0, #0, lsl #0
	movz x16, #4, lsl #0
	add x12, x19, #3000
	add x12, x12, #3000
	subs x8, x4, x16
	csel x8, x5, x0, hs
	cbz x8, 216f
218:
	ldr w6, [x2, #0]
	dup v0.4s, w6
	and v1.16b, v0.16b, v23.16b
	ushr v0.16b, v0.16b, #4
	zip1 v0.16b, v1.16b, v0.16b
	tbl v1.16b, {v0.16b}, v25.16b
	sub v2.4s, v1.4s, v22.4s
	ushr v2.4s, v2.4s, #31
	mul v2.4s, v2.4s, v24.4s
	umov x6, v2.d[0]
	umov x7, v2.d[1]
	add x6, x6, x7
	lsr x7, x6, #32
	add x6, x6, x7
	and x6, x6, x11
	lsl x6, x6, #6
	add x13, x12, x6
	ldr q6, [x13, #0]
	ldr x6, [x13, #32]
	mul v2.4s, v1.4s, v18.4s
	ushr v2.4s, v2.4s, #6
	mul v2.4s, v2.4s, v19.4s
	sub v1.4s, v1.4s, v2.4s
	sub v1.4s, v20.4s, v1.4s
	sub v2.4s, v1.4s, v21.4s
	umin v1.4s, v1.4s, v2.4s
	tbl v1.16b, {v1.16b}, v6.16b
	str q1, [x3, #0]
	lsl x7, x6, #2
	add x3, x3, x7
	sub x4, x4, x6
	add x2, x2, #2
	sub x5, x5, #2
	subs x8, x4, x16
	csel x8, x5, x0, hs
	cbnz x8, 218b
	b 217f
216:
217:
	movz x16, #10, lsl #0
	movz x17, #5, lsl #0
	mul x8, x4, x5
	cbz x8, 219f
221:
	ldrb w6, [x2, #0]
	add x2, x2, #1
	sub x5, x5, #1
	and x7, x6, x11
	cbz x4, 222f
	sub x8, x7, x15
	lsr x12, x8, #63
	add x13, x7, #0
	sub x13, x13, x16
	lsr x14, x13, #63
	madd x13, x14, x16, x13
	sub x13, x13, x17
	lsr x14, x13, #63
	madd x13, x14, x17, x13
	sub x13, x10, x13
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsl x14, x12, #2
	add x3, x3, x14
	sub x4, x4, x12
	lsr x7, x6, #4
	cbz x4, 224f
	sub x8, x7, x15
	lsr x12, x8, #63
	add x13, x7, #0
	sub x13, x13, x16
	lsr x14, x13, #63
	madd x13, x14, x16, x13
	sub x13, x13, x17
	lsr x14, x13, #63
	madd x13, x14, x17, x13
	sub x13, x10, x13
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsl x14, x12, #2
	add x3, x3, x14
	sub x4, x4, x12
	b 225f
224:
225:
	b 223f
222:
223:
	mul x8, x4, x5
	cbnz x8, 221b
	b 220f
219:
220:
	str x4, [x26, #0]
	add x24, x24, #544
	add x25, x25, #1024
	add x26, x26, #8
	sub x27, x27, #1
	cbnz x27, 215b
	ldr x27, [x19, #7904]
	ldr x6, [x19, #7912]
	orr x27, x27, x6
	ldr x6, [x19, #7920]
	orr x27, x27, x6
	ldr x6, [x19, #7928]
	orr x27, x27, x6
	b 213f
212:
213:
	ldr x4, [x19, #7904]
	sub x4, x4, #1
	lsr x4, x4, #63
	movz x6, #0, lsl #0
	sub w4, w6, w4
	dup v0.4s, w4
	add x3, x21, #0
	movz x5, #64, lsl #0
226:
	ldr q1, [x3, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x3, #0]
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 226b
	ldr x4, [x19, #7912]
	sub x4, x4, #1
	lsr x4, x4, #63
	movz x6, #0, lsl #0
	sub w4, w6, w4
	dup v0.4s, w4
	add x3, x21, #1024
	movz x5, #64, lsl #0
227:
	ldr q1, [x3, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x3, #0]
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 227b
	ldr x4, [x19, #7920]
	sub x4, x4, #1
	lsr x4, x4, #63
	movz x6, #0, lsl #0
	sub w4, w6, w4
	dup v0.4s, w4
	add x3, x21, #2048
	movz x5, #64, lsl #0
228:
	ldr q1, [x3, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x3, #0]
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 228b
	ldr x4, [x19, #7928]
	sub x4, x4, #1
	lsr x4, x4, #63
	movz x6, #0, lsl #0
	sub w4, w6, w4
	dup v0.4s, w4
	add x3, x21, #3072
	movz x5, #64, lsl #0
229:
	ldr q1, [x3, #0]
	and v1.16b, v1.16b, v0.16b
	str q1, [x3, #0]
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 229b
	sub x27, x27, #1
	lsr x27, x27, #63
	add x0, x27, #0
	ldr x8, [x19, #8048]
	mov v8.d[0], x8
	ldr x8, [x19, #8056]
	mov v9.d[0], x8
	ldr x8, [x19, #8064]
	mov v10.d[0], x8
	ldr x8, [x19, #8072]
	mov v11.d[0], x8
	ldr x8, [x19, #8080]
	mov v12.d[0], x8
	ldr x8, [x19, #8088]
	mov v13.d[0], x8
	ldr x8, [x19, #8096]
	mov v14.d[0], x8
	ldr x8, [x19, #8104]
	mov v15.d[0], x8
	ldr x20, [x19, #7976]
	ldr x21, [x19, #7984]
	ldr x22, [x19, #7992]
	ldr x23, [x19, #8000]
	ldr x24, [x19, #8008]
	ldr x25, [x19, #8016]
	ldr x26, [x19, #8024]
	ldr x27, [x19, #8032]
	ldr x28, [x19, #8040]
	ldr x19, [x19, #7968]
	ret
	.p2align 6
