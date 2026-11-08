// The functions of `src/internal/vg_aes_gcm_open_split_with_powers_aes_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_open_split_with_powers_aes_sha3:
	sub sp, sp, #2608
	add x16, sp, #0
	ldr x17, [sp, #2608]
	str x17, [x16, #0]
	ldr x17, [sp, #2616]
	str x17, [x16, #8]
	ldr x17, [sp, #2624]
	str x17, [x16, #16]
	ldr x17, [sp, #2632]
	str x17, [x16, #24]
	ldr x17, [sp, #2640]
	str x17, [x16, #32]
	add x17, sp, #48
	str x17, [x16, #40]
	ldr x9, [sp, #40]
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
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	add x28, x10, #0
	ldr x12, [sp, #0]
	ldr x6, [sp, #24]
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 20f
	lsr x13, x28, #4
	cbz x13, 22f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 23f
22:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
23:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 27f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
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
	b 28f
27:
28:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr q0, [x20, #48]
	str q0, [x19, #320]
	lsr x9, x26, #7
	lsl x9, x9, #7
	ldr x11, [x19, #232]
	add x11, x11, x9
	add x12, x23, x9
	sub x13, x26, x9
	cbz x13, 222f
	lsr x14, x13, #2
	cbz x14, 224f
	lsr x14, x13, #3
	cbz x14, 226f
228:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 228b
	b 227f
226:
227:
	lsr x14, x13, #2
	cbz x14, 229f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 230f
229:
230:
	cbz x13, 231f
233:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 233b
	b 232f
231:
232:
	b 225f
224:
234:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 234b
225:
	b 223f
222:
223:
	ldr x15, [x19, #232]
	lsr x9, x26, #7
	cbz x9, 235f
	ldr x5, [sp, #16]
	ldr q16, [x5, #16]
	ext v24.16b, v16.16b, v16.16b, #8
	ldr q17, [x5, #0]
	ext v25.16b, v17.16b, v17.16b, #8
	ldr q18, [x5, #48]
	ext v26.16b, v18.16b, v18.16b, #8
	ldr q19, [x5, #32]
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q20, [x5, #80]
	ext v28.16b, v20.16b, v20.16b, #8
	ldr q21, [x5, #64]
	ext v29.16b, v21.16b, v21.16b, #8
	ldr q22, [x5, #112]
	ext v30.16b, v22.16b, v22.16b, #8
	ldr q23, [x5, #96]
	ext v31.16b, v23.16b, v23.16b, #8
	str q24, [x19, #512]
	str q25, [x19, #528]
	str q26, [x19, #544]
	str q27, [x19, #560]
	str q28, [x19, #576]
	str q29, [x19, #592]
	str q30, [x19, #608]
	str q31, [x19, #624]
	eor v2.16b, v30.16b, v22.16b
	eor v3.16b, v29.16b, v21.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #640]
	eor v2.16b, v28.16b, v20.16b
	eor v3.16b, v27.16b, v19.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #656]
	eor v2.16b, v26.16b, v18.16b
	eor v3.16b, v25.16b, v17.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #672]
	eor v2.16b, v24.16b, v16.16b
	eor v3.16b, v31.16b, v23.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #688]
	ldr w10, [x20, #60]
	rev w10, w10
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	ldr q16, [x20, #16]
	rev64 v16.16b, v16.16b
	add x9, x23, #0
	lsr x11, x26, #7
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 237f
	cbz x14, 239f
241:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	ldr q0, [x20, #48]
	rev64 v21.16b, v21.16b
	mov v0.s[3], w12
	add w12, w10, #1
	ldr q22, [x9, #32]
	rev w12, w12
	ldr q1, [x20, #48]
	rev64 v22.16b, v22.16b
	mov v1.s[3], w12
	add w12, w10, #2
	ldr q23, [x19, #608]
	rev w12, w12
	ldr q2, [x20, #48]
	ldr q24, [x19, #592]
	mov v2.s[3], w12
	add w12, w10, #3
	ldr q25, [x19, #640]
	rev w12, w12
	ldr q3, [x20, #48]
	trn1 v26.2d, v21.2d, v22.2d
	mov v3.s[3], w12
	add w12, w10, #4
	trn2 v27.2d, v21.2d, v22.2d
	rev w12, w12
	ldr q4, [x20, #48]
	eor v26.16b, v26.16b, v27.16b
	mov v4.s[3], w12
	add w12, w10, #5
	pmull v28.1q, v21.1d, v23.1d
	rev w12, w12
	ldr q5, [x20, #48]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v5.s[3], w12
	add w12, w10, #6
	pmull v29.1q, v22.1d, v24.1d
	rev w12, w12
	ldr q6, [x20, #48]
	pmull2 v22.1q, v22.2d, v24.2d
	mov v6.s[3], w12
	add w12, w10, #7
	pmull v27.1q, v26.1d, v25.1d
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	pmull2 v26.1q, v26.2d, v25.2d
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v18.16b, v28.16b, v29.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v19.16b, v21.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v20.16b, v27.16b, v26.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #48]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #64]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v22.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q23, [x19, #576]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #560]
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #656]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v26.16b, v26.16b, v27.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #80]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v21.16b, v21.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q22, [x9, #96]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v22.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	ldr q23, [x19, #544]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q24, [x19, #528]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #672]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q21, [x9, #112]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v21.16b, v21.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	ldr q22, [x9, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	rev64 v22.16b, v22.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor v22.16b, v22.16b, v16.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q23, [x19, #512]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #624]
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #688]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v26.16b, v26.16b, v27.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #192]
	pmull v28.1q, v21.1d, v23.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #208]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q30, [x21, #224]
	ldr q31, [x9, #0]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	pmull v26.1q, v20.1d, v17.1d
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	ext v18.16b, v18.16b, v18.16b, #8
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x15, #0]
	str q1, [x15, #16]
	str q2, [x15, #32]
	str q3, [x15, #48]
	str q4, [x15, #64]
	str q5, [x15, #80]
	str q6, [x15, #96]
	str q7, [x15, #112]
	add x15, x15, #128
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 241b
	b 240f
239:
242:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	rev64 v21.16b, v21.16b
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	ldr q22, [x9, #32]
	add w12, w10, #1
	rev w12, w12
	rev64 v22.16b, v22.16b
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	ldr q23, [x19, #608]
	add w12, w10, #2
	rev w12, w12
	ldr q24, [x19, #592]
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	ldr q25, [x19, #640]
	add w12, w10, #3
	rev w12, w12
	trn1 v26.2d, v21.2d, v22.2d
	ldr q3, [x20, #48]
	trn2 v27.2d, v21.2d, v22.2d
	mov v3.s[3], w12
	add w12, w10, #4
	eor v26.16b, v26.16b, v27.16b
	rev w12, w12
	ldr q4, [x20, #48]
	pmull v28.1q, v21.1d, v23.1d
	mov v4.s[3], w12
	add w12, w10, #5
	pmull2 v21.1q, v21.2d, v23.2d
	rev w12, w12
	ldr q5, [x20, #48]
	pmull v29.1q, v22.1d, v24.1d
	mov v5.s[3], w12
	add w12, w10, #6
	pmull2 v22.1q, v22.2d, v24.2d
	rev w12, w12
	ldr q6, [x20, #48]
	pmull v27.1q, v26.1d, v25.1d
	mov v6.s[3], w12
	pmull2 v26.1q, v26.2d, v25.2d
	add w12, w10, #7
	rev w12, w12
	eor v18.16b, v28.16b, v29.16b
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	eor v19.16b, v21.16b, v22.16b
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v20.16b, v27.16b, v26.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q21, [x9, #48]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	rev64 v21.16b, v21.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q22, [x9, #64]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #576]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q24, [x19, #560]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #656]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	pmull2 v22.1q, v22.2d, v24.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q21, [x9, #80]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v21.16b, v21.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #96]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #544]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q24, [x19, #528]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q25, [x19, #672]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	trn2 v27.2d, v21.2d, v22.2d
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v26.16b, v26.16b, v27.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #112]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v21.16b, v21.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q22, [x9, #0]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v22.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	eor v22.16b, v22.16b, v16.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q23, [x19, #512]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q24, [x19, #624]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #688]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x21, #176]
	pmull2 v22.1q, v22.2d, v24.2d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	ldr q30, [x21, #192]
	ldr q31, [x9, #0]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	pmull v26.1q, v20.1d, v17.1d
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ext v18.16b, v18.16b, v18.16b, #8
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add w10, w10, #8
	str q0, [x15, #0]
	str q1, [x15, #16]
	str q2, [x15, #32]
	str q3, [x15, #48]
	str q4, [x15, #64]
	str q5, [x15, #80]
	str q6, [x15, #96]
	str q7, [x15, #112]
	add x15, x15, #128
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 242b
240:
	b 238f
237:
243:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	rev64 v21.16b, v21.16b
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	ldr q22, [x9, #32]
	add w12, w10, #1
	rev64 v22.16b, v22.16b
	rev w12, w12
	ldr q1, [x20, #48]
	ldr q23, [x19, #608]
	mov v1.s[3], w12
	add w12, w10, #2
	ldr q24, [x19, #592]
	rev w12, w12
	ldr q25, [x19, #640]
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	trn1 v26.2d, v21.2d, v22.2d
	add w12, w10, #3
	rev w12, w12
	trn2 v27.2d, v21.2d, v22.2d
	ldr q3, [x20, #48]
	eor v26.16b, v26.16b, v27.16b
	mov v3.s[3], w12
	add w12, w10, #4
	pmull v28.1q, v21.1d, v23.1d
	rev w12, w12
	ldr q4, [x20, #48]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v4.s[3], w12
	pmull v29.1q, v22.1d, v24.1d
	add w12, w10, #5
	rev w12, w12
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	pmull v27.1q, v26.1d, v25.1d
	add w12, w10, #6
	pmull2 v26.1q, v26.2d, v25.2d
	rev w12, w12
	ldr q6, [x20, #48]
	eor v18.16b, v28.16b, v29.16b
	mov v6.s[3], w12
	add w12, w10, #7
	eor v19.16b, v21.16b, v22.16b
	rev w12, w12
	eor v20.16b, v27.16b, v26.16b
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q21, [x9, #48]
	ldr q30, [x21, #0]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #64]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v22.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q23, [x19, #576]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q24, [x19, #560]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	ldr q25, [x19, #656]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v26.16b, v26.16b, v27.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v21.1q, v21.2d, v23.2d
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q21, [x9, #80]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	rev64 v21.16b, v21.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #96]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #544]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q24, [x19, #528]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q25, [x19, #672]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	eor v26.16b, v26.16b, v27.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v27.1q, v26.1d, v25.1d
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #112]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #0]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v22.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v22.16b, v22.16b, v16.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q23, [x19, #512]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #624]
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #688]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor v26.16b, v26.16b, v27.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v28.1q, v21.1d, v23.1d
	ldr q30, [x21, #144]
	pmull2 v21.1q, v21.2d, v23.2d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v2.16b, v30.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v7.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	ldr q30, [x21, #160]
	ldr q31, [x9, #0]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	pmull v26.1q, v19.1d, v17.1d
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	ldr q31, [x9, #64]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	pmull v26.1q, v20.1d, v17.1d
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	ext v18.16b, v18.16b, v18.16b, #8
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add w10, w10, #8
	str q0, [x15, #0]
	str q1, [x15, #16]
	str q2, [x15, #32]
	str q3, [x15, #48]
	str q4, [x15, #64]
	str q5, [x15, #80]
	str q6, [x15, #96]
	str q7, [x15, #112]
	add x15, x15, #128
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 243b
238:
	rev64 v16.16b, v16.16b
	str q16, [x20, #16]
	rev w12, w10
	str w12, [x20, #60]
	b 236f
235:
236:
	ldr x23, [x19, #232]
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x23, x23, x9
	sub x24, x26, x9
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	lsr x9, x3, #1
	cbz x9, 244f
	ldr x5, [sp, #16]
	bl {vg_ghash_with_powers_aes}
	b 245f
244:
	bl {vg_ghash_aes}
245:
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 246f
	lsr x9, x26, #4
	cbz x9, 248f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
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
	b 249f
248:
	cbz x13, 250f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 252f
	lsr x14, x13, #2
	cbz x14, 254f
	lsr x14, x13, #3
	cbz x14, 256f
258:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 258b
	b 257f
256:
257:
	lsr x14, x13, #2
	cbz x14, 259f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 260f
259:
260:
	cbz x13, 261f
263:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 263b
	b 262f
261:
262:
	b 255f
254:
264:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 264b
255:
	b 253f
252:
253:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
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
	b 251f
250:
251:
249:
	b 247f
246:
247:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	lsr x9, x28, #4
	cbz x9, 265f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 266f
265:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 267f
269:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 269b
	b 268f
267:
268:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 270f
272:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 272b
	b 271f
270:
271:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
266:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 273f
	ldr x23, [x19, #232]
	ldr x26, [x19, #240]
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x23, x23, x9
	sub x24, x26, x9
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 275f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 276f
275:
	movz x4, #0, lsl #0
276:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 277f
	lsr x9, x26, #4
	cbz x9, 279f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 280f
279:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 281f
	lsr x14, x13, #2
	cbz x14, 283f
	lsr x14, x13, #3
	cbz x14, 285f
287:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 287b
	b 286f
285:
286:
	lsr x14, x13, #2
	cbz x14, 288f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 289f
288:
289:
	cbz x13, 290f
292:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 292b
	b 291f
290:
291:
	b 284f
283:
293:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 293b
284:
	b 282f
281:
282:
280:
	b 278f
277:
278:
	b 274f
273:
	ldr q0, [x19, #320]
	str q0, [x20, #48]
	ldr x23, [x19, #232]
	ldr x26, [x19, #240]
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x24, x9, #0
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 294f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 295f
294:
	movz x4, #0, lsl #0
295:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 296f
	lsr x9, x26, #4
	cbz x9, 298f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 299f
298:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2100f
	lsr x14, x13, #2
	cbz x14, 2102f
	lsr x14, x13, #3
	cbz x14, 2104f
2106:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2106b
	b 2105f
2104:
2105:
	lsr x14, x13, #2
	cbz x14, 2107f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2108f
2107:
2108:
	cbz x13, 2109f
2111:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2111b
	b 2110f
2109:
2110:
	b 2103f
2102:
2112:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2112b
2103:
	b 2101f
2100:
2101:
299:
	b 297f
296:
297:
274:
	add x0, x27, #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
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
	add sp, sp, #2608
	ret
	.p2align 6
