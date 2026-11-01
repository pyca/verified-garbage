// The functions of `src/internal/vg_mldsa_rej_ntt_poly4.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_rej_ntt_poly4:
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
	add x4, x3, #34
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
	ldrb w6, [x3, #32]
	ldrb w8, [x3, #33]
	lsl x8, x8, #8
	add x6, x6, x8
	ldrb w7, [x4, #32]
	ldrb w8, [x4, #33]
	lsl x8, x8, #8
	add x7, x7, x8
	movz x9, #31, lsl #16
	add x6, x6, x9
	add x7, x7, x9
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #64]
	movz x9, #32768, lsl #48
	dup v0.2d, x9
	str q0, [x2, #320]
	add x2, x19, #400
	add x3, x20, #68
	add x4, x3, #34
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
	ldrb w6, [x3, #32]
	ldrb w8, [x3, #33]
	lsl x8, x8, #8
	add x6, x6, x8
	ldrb w7, [x4, #32]
	ldrb w8, [x4, #33]
	lsl x8, x8, #8
	add x7, x7, x8
	movz x9, #31, lsl #16
	add x6, x6, x9
	add x7, x7, x9
	dup v0.2d, x6
	mov v0.d[1], x7
	str q0, [x2, #64]
	movz x9, #32768, lsl #48
	dup v0.2d, x9
	str q0, [x2, #320]
	add x22, x19, #0
	add x23, x19, #400
	add x24, x19, #840
	add x25, x19, #1848
	add x26, x19, #2856
	add x27, x19, #3864
	movz x28, #6, lsl #0
20:
	add x1, x19, #2440
	add x1, x1, #2440
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
	ldr x6, [x22, #272]
	ldr x7, [x22, #280]
	str x6, [x24, #136]
	str x7, [x25, #136]
	ldr x6, [x22, #288]
	ldr x7, [x22, #296]
	str x6, [x24, #144]
	str x7, [x25, #144]
	ldr x6, [x22, #304]
	ldr x7, [x22, #312]
	str x6, [x24, #152]
	str x7, [x25, #152]
	ldr x6, [x22, #320]
	ldr x7, [x22, #328]
	str x6, [x24, #160]
	str x7, [x25, #160]
	add x1, x19, #2440
	add x1, x1, #2440
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
	ldr x6, [x23, #272]
	ldr x7, [x23, #280]
	str x6, [x26, #136]
	str x7, [x27, #136]
	ldr x6, [x23, #288]
	ldr x7, [x23, #296]
	str x6, [x26, #144]
	str x7, [x27, #144]
	ldr x6, [x23, #304]
	ldr x7, [x23, #312]
	str x6, [x26, #152]
	str x7, [x27, #152]
	ldr x6, [x23, #320]
	ldr x7, [x23, #328]
	str x6, [x26, #160]
	str x7, [x27, #160]
	add x24, x24, #168
	add x25, x25, #168
	add x26, x26, #168
	add x27, x27, #168
	sub x28, x28, #1
	cbnz x28, 20b
	movz x27, #1, lsl #0
	add x25, x19, #0
	add x26, x21, #0
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
21:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 21b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
22:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 23f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 24f
23:
24:
	cbnz x5, 22b
	sub x0, x4, #1
	lsr x0, x0, #63
	and x27, x27, x0
	add x25, x19, #1008
	add x26, x21, #1024
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
25:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 25b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
26:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 27f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 28f
27:
28:
	cbnz x5, 26b
	sub x0, x4, #1
	lsr x0, x0, #63
	and x27, x27, x0
	add x25, x19, #2016
	add x26, x21, #2048
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
29:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 29b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
210:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 211f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 212f
211:
212:
	cbnz x5, 210b
	sub x0, x4, #1
	lsr x0, x0, #63
	and x27, x27, x0
	add x25, x19, #3024
	add x26, x21, #3072
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
213:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 213b
	add x2, x25, #840
	add x3, x26, #0
	movz x4, #256, lsl #0
	movz x5, #336, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
	movz x10, #127, lsl #0
214:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x8, x8, x10
	lsl x8, x8, #16
	lsl x7, x7, #8
	add x11, x6, x7
	add x11, x11, x8
	cbz x4, 215f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 216f
215:
216:
	cbnz x5, 214b
	sub x0, x4, #1
	lsr x0, x0, #63
	and x27, x27, x0
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
