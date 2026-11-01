// The functions of `src/sm3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm3_init:
	movz w9, #5743, lsl #0
	movk w9, #29568, lsl #16
	str w9, [x0, #0]
	movz w9, #45753, lsl #0
	movk w9, #18708, lsl #16
	str w9, [x0, #4]
	movz w9, #17111, lsl #0
	movk w9, #5924, lsl #16
	str w9, [x0, #8]
	movz w9, #1536, lsl #0
	movk w9, #55946, lsl #16
	str w9, [x0, #12]
	movz w9, #12476, lsl #0
	movk w9, #43375, lsl #16
	str w9, [x0, #16]
	movz w9, #14506, lsl #0
	movk w9, #5681, lsl #16
	str w9, [x0, #20]
	movz w9, #61005, lsl #0
	movk w9, #58253, lsl #16
	str w9, [x0, #24]
	movz w9, #3662, lsl #0
	movk w9, #45307, lsl #16
	str w9, [x0, #28]
	ret
	.p2align 6

vg_sm3_update:
	sub sp, sp, #112
	add x4, sp, #0
	str x30, [sp, #-16]!
	str x19, [x4, #64]
	str x20, [x4, #72]
	str x21, [x4, #80]
	str x22, [x4, #88]
	str x23, [x4, #96]
	str x24, [x4, #104]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x2, #0
	add x22, x3, #0
	movz x9, #63, lsl #0
	and x23, x1, x9
	cbz x22, 20f
22:
	movz x10, #0, lsl #0
	cbz x23, 23f
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 25f
	b 26f
25:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 27f
	b 28f
27:
	add x11, x22, #0
28:
26:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 29f
211:
	ldr x9, [x21, #0]
	add x12, x19, x23
	str x9, [x12, #32]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 211b
	b 210f
29:
210:
	cbz x11, 212f
214:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #32]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 214b
	b 213f
212:
213:
	sub x9, x23, #64
	cbz x9, 215f
	b 216f
215:
	add x1, x19, #32
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
216:
	b 24f
23:
	lsr x9, x22, #6
	cbz x9, 217f
	add x1, x21, #0
	lsr x10, x22, #6
	lsl x9, x10, #6
	add x21, x21, x9
	sub x22, x22, x9
	b 218f
217:
	movz x11, #64, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #6
	cbz x9, 219f
	b 220f
219:
	add x9, x22, x23
	lsr x9, x9, #6
	cbz x9, 221f
	b 222f
221:
	add x11, x22, #0
222:
220:
	sub x22, x22, x11
	lsr x13, x11, #3
	cbz x13, 223f
225:
	ldr x9, [x21, #0]
	add x12, x19, x23
	str x9, [x12, #32]
	add x21, x21, #8
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 225b
	b 224f
223:
224:
	cbz x11, 226f
228:
	ldrb w9, [x21, #0]
	add x12, x19, x23
	strb w9, [x12, #32]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 228b
	b 227f
226:
227:
	sub x9, x23, #64
	cbz x9, 229f
	b 230f
229:
	add x1, x19, #32
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sm3_compress}
	b 232f
231:
232:
	cbnz x22, 22b
	b 21f
20:
21:
	ldr x19, [x20, #64]
	ldr x21, [x20, #80]
	ldr x22, [x20, #88]
	ldr x23, [x20, #96]
	ldr x24, [x20, #104]
	ldr x20, [x20, #72]
	ldr x30, [sp], #16
	add sp, sp, #112
	ret
	.p2align 6

vg_sm3_finalize:
	sub sp, sp, #112
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #64]
	str x20, [x3, #72]
	str x21, [x3, #80]
	str x22, [x3, #88]
	str x23, [x3, #96]
	str x24, [x3, #104]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #63, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #32]
	add x23, x23, #1
	add x24, x23, #7
	lsr x24, x24, #6
20:
	movz x11, #64, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #56, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #32]
	add x23, x23, #8
	sub x11, x11, #8
	lsr x13, x11, #3
	cbnz x13, 25b
	b 24f
23:
24:
	cbz x11, 26f
28:
	add x12, x19, x23
	strb w9, [x12, #32]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #88]
210:
	add x1, x19, #32
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sm3_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	ldr w9, [x19, #20]
	rev w9, w9
	str w9, [x21, #20]
	ldr w9, [x19, #24]
	rev w9, w9
	str w9, [x21, #24]
	ldr w9, [x19, #28]
	rev w9, w9
	str w9, [x21, #28]
	ldr x19, [x20, #64]
	ldr x21, [x20, #80]
	ldr x22, [x20, #88]
	ldr x23, [x20, #96]
	ldr x24, [x20, #104]
	ldr x20, [x20, #72]
	ldr x30, [sp], #16
	add sp, sp, #112
	ret
	.p2align 6
