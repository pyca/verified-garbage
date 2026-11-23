// The functions of `src/internal/vg_aes_gcm_stream_finish_core.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_stream_finish_core:
	sub sp, sp, #2560
	add x6, sp, #0
	str x20, [x6, #136]
	str x21, [x6, #144]
	str x22, [x6, #152]
	str x23, [x6, #160]
	str x24, [x6, #168]
	str x25, [x6, #176]
	str x26, [x6, #184]
	str x27, [x6, #192]
	str x28, [x6, #200]
	str x30, [x6, #208]
	str x19, [x6, #128]
	add x19, x6, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x3, #0
	add x27, x4, #0
	add x28, x5, #0
	cbz x27, 20f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 21f
20:
	movz x9, #15, lsl #0
	and x25, x26, x9
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
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
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	umov x16, v9.d[0]
	blr x16
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
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
