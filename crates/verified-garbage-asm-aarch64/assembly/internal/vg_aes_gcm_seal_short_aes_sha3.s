// The functions of `src/internal/vg_aes_gcm_seal_short_aes_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_short_aes_sha3:
	sub sp, sp, #368
	add x9, sp, #0
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x21, x0, #0
	add x22, x1, #0
	add x23, x2, #0
	add x24, x5, #0
	ldr x26, [sp, #376]
	add x25, x26, #15
	lsr x25, x25, #4
	lsl x25, x25, #4
	movi v0.2d, #0
	str q0, [x19, #224]
	str q0, [x19, #240]
	str q0, [x19, #256]
	str q0, [x19, #272]
	str q0, [x19, #288]
	str q0, [x19, #304]
	str q0, [x19, #320]
	str q0, [x19, #336]
	add x11, x19, #320
	sub x11, x11, x25
	add x12, x4, #0
	add x13, x24, #0
	cbz x13, 20f
	lsr x14, x13, #2
	cbz x14, 22f
	lsr x14, x13, #3
	cbz x14, 24f
26:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 26b
	b 25f
24:
25:
	lsr x14, x13, #2
	cbz x14, 27f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 28f
27:
28:
	cbz x13, 29f
211:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 211b
	b 210f
29:
210:
	b 23f
22:
212:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 212b
23:
	b 21f
20:
21:
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 213f
	cbz x14, 215f
	ldr x9, [x23, #0]
	ldr w10, [x23, #8]
	mov v31.d[0], x9
	mov v31.s[2], w10
	orr v0.16b, v31.16b, v31.16b
	movz w12, #256, lsl #16
	mov v0.s[3], w12
	orr v1.16b, v31.16b, v31.16b
	movz w12, #512, lsl #16
	mov v1.s[3], w12
	orr v2.16b, v31.16b, v31.16b
	movz w12, #768, lsl #16
	mov v2.s[3], w12
	orr v3.16b, v31.16b, v31.16b
	movz w12, #1024, lsl #16
	mov v3.s[3], w12
	orr v4.16b, v31.16b, v31.16b
	movz w12, #1280, lsl #16
	mov v4.s[3], w12
	orr v5.16b, v31.16b, v31.16b
	movz w12, #1536, lsl #16
	mov v5.s[3], w12
	orr v6.16b, v31.16b, v31.16b
	movz w12, #1792, lsl #16
	mov v6.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #192]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #208]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	ldr q30, [x21, #224]
	eor v0.16b, v0.16b, v30.16b
	str q0, [x19, #0]
	eor v1.16b, v1.16b, v30.16b
	str q1, [x19, #16]
	eor v2.16b, v2.16b, v30.16b
	str q2, [x19, #32]
	eor v3.16b, v3.16b, v30.16b
	str q3, [x19, #48]
	eor v4.16b, v4.16b, v30.16b
	str q4, [x19, #64]
	eor v5.16b, v5.16b, v30.16b
	str q5, [x19, #80]
	eor v6.16b, v6.16b, v30.16b
	str q6, [x19, #96]
	b 216f
215:
	ldr x9, [x23, #0]
	ldr w10, [x23, #8]
	mov v31.d[0], x9
	mov v31.s[2], w10
	orr v0.16b, v31.16b, v31.16b
	movz w12, #256, lsl #16
	mov v0.s[3], w12
	orr v1.16b, v31.16b, v31.16b
	movz w12, #512, lsl #16
	mov v1.s[3], w12
	orr v2.16b, v31.16b, v31.16b
	movz w12, #768, lsl #16
	mov v2.s[3], w12
	orr v3.16b, v31.16b, v31.16b
	movz w12, #1024, lsl #16
	mov v3.s[3], w12
	orr v4.16b, v31.16b, v31.16b
	movz w12, #1280, lsl #16
	mov v4.s[3], w12
	orr v5.16b, v31.16b, v31.16b
	movz w12, #1536, lsl #16
	mov v5.s[3], w12
	orr v6.16b, v31.16b, v31.16b
	movz w12, #1792, lsl #16
	mov v6.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	ldr q30, [x21, #192]
	eor v0.16b, v0.16b, v30.16b
	str q0, [x19, #0]
	eor v1.16b, v1.16b, v30.16b
	str q1, [x19, #16]
	eor v2.16b, v2.16b, v30.16b
	str q2, [x19, #32]
	eor v3.16b, v3.16b, v30.16b
	str q3, [x19, #48]
	eor v4.16b, v4.16b, v30.16b
	str q4, [x19, #64]
	eor v5.16b, v5.16b, v30.16b
	str q5, [x19, #80]
	eor v6.16b, v6.16b, v30.16b
	str q6, [x19, #96]
216:
	b 214f
213:
	ldr x9, [x23, #0]
	ldr w10, [x23, #8]
	mov v31.d[0], x9
	mov v31.s[2], w10
	orr v0.16b, v31.16b, v31.16b
	movz w12, #256, lsl #16
	mov v0.s[3], w12
	orr v1.16b, v31.16b, v31.16b
	movz w12, #512, lsl #16
	mov v1.s[3], w12
	orr v2.16b, v31.16b, v31.16b
	movz w12, #768, lsl #16
	mov v2.s[3], w12
	orr v3.16b, v31.16b, v31.16b
	movz w12, #1024, lsl #16
	mov v3.s[3], w12
	orr v4.16b, v31.16b, v31.16b
	movz w12, #1280, lsl #16
	mov v4.s[3], w12
	orr v5.16b, v31.16b, v31.16b
	movz w12, #1536, lsl #16
	mov v5.s[3], w12
	orr v6.16b, v31.16b, v31.16b
	movz w12, #1792, lsl #16
	mov v6.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	ldr q30, [x21, #160]
	eor v0.16b, v0.16b, v30.16b
	str q0, [x19, #0]
	eor v1.16b, v1.16b, v30.16b
	str q1, [x19, #16]
	eor v2.16b, v2.16b, v30.16b
	str q2, [x19, #32]
	eor v3.16b, v3.16b, v30.16b
	str q3, [x19, #48]
	eor v4.16b, v4.16b, v30.16b
	str q4, [x19, #64]
	eor v5.16b, v5.16b, v30.16b
	str q5, [x19, #80]
	eor v6.16b, v6.16b, v30.16b
	str q6, [x19, #96]
214:
	add x1, x19, #16
	ldr x2, [sp, #368]
	add x3, x19, #336
	sub x3, x3, x25
	cbz x7, 217f
219:
	ldr x0, [x6, #0]
	ldr x12, [x6, #8]
	add x6, x6, #16
	lsr x13, x12, #4
	movz x14, #15, lsl #0
	and x12, x12, x14
	cbz x13, 220f
222:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #0]
	str q0, [x3, #0]
	add x0, x0, #16
	add x1, x1, #16
	add x2, x2, #16
	add x3, x3, #16
	sub x13, x13, #1
	cbnz x13, 222b
	b 221f
220:
221:
	cbz x12, 223f
	lsr x14, x12, #3
	cbnz x14, 225f
	lsr x14, x12, #2
	cbnz x14, 227f
229:
	ldrb w14, [x0, #0]
	ldrb w15, [x1, #0]
	eor w14, w14, w15
	strb w14, [x2, #0]
	strb w14, [x3, #0]
	add x0, x0, #1
	add x1, x1, #1
	add x2, x2, #1
	add x3, x3, #1
	sub x12, x12, #1
	cbnz x12, 229b
	b 228f
227:
	ldr w14, [x0, #0]
	ldr w15, [x1, #0]
	eor w13, w14, w15
	sub x12, x12, #4
	add x0, x0, x12
	add x1, x1, x12
	ldr w14, [x0, #0]
	ldr w15, [x1, #0]
	eor w14, w14, w15
	str w13, [x2, #0]
	str w13, [x3, #0]
	add x2, x2, x12
	add x3, x3, x12
	str w14, [x2, #0]
	str w14, [x3, #0]
	add x0, x0, #4
	add x1, x1, #4
	add x2, x2, #4
	add x3, x3, #4
228:
	b 226f
225:
	ldr x14, [x0, #0]
	ldr x15, [x1, #0]
	eor x13, x14, x15
	sub x12, x12, #8
	add x0, x0, x12
	add x1, x1, x12
	ldr x14, [x0, #0]
	ldr x15, [x1, #0]
	eor x14, x14, x15
	str x13, [x2, #0]
	str x13, [x3, #0]
	add x2, x2, x12
	add x3, x3, x12
	str x14, [x2, #0]
	str x14, [x3, #0]
	add x0, x0, #8
	add x1, x1, #8
	add x2, x2, #8
	add x3, x3, #8
226:
	b 224f
223:
224:
	sub x7, x7, #1
	cbnz x7, 219b
	b 218f
217:
218:
	lsl x9, x24, #3
	rev x9, x9
	str x9, [x19, #336]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #344]
	add x0, x21, #240
	add x1, x19, #352
	movi v0.2d, #0
	str q0, [x1, #0]
	add x2, x19, #224
	movz x3, #8, lsl #0
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ushr v7.2d, v6.2d, #63
	shl v3.2d, v6.2d, #1
	ext v4.16b, v7.16b, v7.16b, #8
	eor v3.16b, v3.16b, v4.16b
	pmull v5.1q, v7.1d, v1.1d
	eor v24.16b, v3.16b, v5.16b
	ext v16.16b, v24.16b, v24.16b, #8
	ldr q0, [x1, #0]
	rev64 v0.16b, v0.16b
	lsr x5, x3, #3
	pmull v5.1q, v24.1d, v24.1d
	pmull2 v3.1q, v24.2d, v24.2d
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v3.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v25.16b, v5.16b, v7.16b
	ext v17.16b, v25.16b, v25.16b, #8
	pmull v5.1q, v25.1d, v24.1d
	pmull2 v3.1q, v25.2d, v24.2d
	pmull v4.1q, v25.1d, v16.1d
	pmull2 v7.1q, v25.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v26.16b, v5.16b, v7.16b
	ext v18.16b, v26.16b, v26.16b, #8
	pmull v5.1q, v25.1d, v25.1d
	pmull2 v3.1q, v25.2d, v25.2d
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v3.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v27.16b, v5.16b, v7.16b
	ext v19.16b, v27.16b, v27.16b, #8
	pmull v5.1q, v26.1d, v25.1d
	pmull2 v3.1q, v26.2d, v25.2d
	pmull v4.1q, v26.1d, v17.1d
	pmull2 v7.1q, v26.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v28.16b, v5.16b, v7.16b
	ext v20.16b, v28.16b, v28.16b, #8
	pmull v5.1q, v26.1d, v26.1d
	pmull2 v3.1q, v26.2d, v26.2d
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v3.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v29.16b, v5.16b, v7.16b
	ext v21.16b, v29.16b, v29.16b, #8
	pmull v5.1q, v27.1d, v26.1d
	pmull2 v3.1q, v27.2d, v26.2d
	pmull v4.1q, v27.1d, v18.1d
	pmull2 v7.1q, v27.2d, v18.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v30.16b, v5.16b, v7.16b
	ext v22.16b, v30.16b, v30.16b, #8
	pmull v5.1q, v27.1d, v27.1d
	pmull2 v3.1q, v27.2d, v27.2d
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v3.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v31.16b, v5.16b, v7.16b
	ext v23.16b, v31.16b, v31.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	ldr q6, [x2, #16]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v30.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v30.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v22.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v22.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #32]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v29.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v29.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v21.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v21.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #48]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v28.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v28.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v20.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v20.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #64]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v27.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v27.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v19.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v19.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #80]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v26.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v26.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v18.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v18.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #96]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #112]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #0]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	pmull v7.1q, v6.1d, v31.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v31.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v23.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v23.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	add x2, x2, #128
	sub x3, x3, #8
	lsr x5, x3, #3
	orr v16.16b, v0.16b, v0.16b
	rev64 v16.16b, v16.16b
	ldr q0, [x19, #0]
	eor v16.16b, v16.16b, v0.16b
	ldr x10, [sp, #384]
	str q16, [x10, #0]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #368
	ret
	.p2align 6
