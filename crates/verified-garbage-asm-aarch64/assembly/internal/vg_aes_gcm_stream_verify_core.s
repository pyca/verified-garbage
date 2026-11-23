// The functions of `src/internal/vg_aes_gcm_stream_verify_core.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_stream_verify_core:
	sub sp, sp, #2560
	add x7, sp, #0
	str x20, [x7, #136]
	str x21, [x7, #144]
	str x22, [x7, #152]
	str x23, [x7, #160]
	str x24, [x7, #168]
	str x25, [x7, #176]
	str x26, [x7, #184]
	str x27, [x7, #192]
	str x28, [x7, #200]
	str x30, [x7, #208]
	str x19, [x7, #128]
	add x19, x7, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x3, #0
	add x27, x4, #0
	add x28, x6, #0
	add x12, x5, #0
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
	cbz x27, 27f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 28f
27:
	movz x9, #15, lsl #0
	and x25, x26, x9
28:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
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
	cbz x25, 222f
	movz x3, #1, lsl #0
	b 223f
222:
	movz x3, #0, lsl #0
223:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	umov x16, v8.d[0]
	blr x16
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	umov x16, v8.d[0]
	blr x16
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
	umov x16, v9.d[0]
	blr x16
	lsr x9, x28, #4
	cbz x9, 224f
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
	b 225f
224:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 229f
231:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 231b
	b 230f
229:
230:
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
225:
	movz x0, #1, lsl #0
	sub x0, x0, x10
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
	add sp, sp, #2560
	ret
	.p2align 6
