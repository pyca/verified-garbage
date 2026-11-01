// The functions of `src/internal/vg_sha512_update_scratch_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_update_scratch_sha3:
	.arch_extension sha3
	str x30, [sp, #-16]!
	str x19, [x4, #640]
	str x20, [x4, #648]
	str x21, [x4, #656]
	str x22, [x4, #664]
	str x23, [x4, #672]
	str x24, [x4, #680]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x2, #0
	add x22, x3, #0
	movz x9, #127, lsl #0
	and x23, x1, x9
	cbz x22, 20f
22:
	movz x10, #0, lsl #0
	cbz x23, 23f
	movz x11, #128, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #7
	cbz x9, 25f
	b 26f
25:
	add x9, x22, x23
	lsr x9, x9, #7
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
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 214b
	b 213f
212:
213:
	sub x9, x23, #128
	cbz x9, 215f
	b 216f
215:
	add x1, x19, #64
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
216:
	b 24f
23:
	lsr x9, x22, #7
	cbz x9, 217f
	add x1, x21, #0
	lsr x10, x22, #7
	lsl x9, x10, #7
	add x21, x21, x9
	sub x22, x22, x9
	b 218f
217:
	movz x11, #128, lsl #0
	sub x11, x11, x23
	lsr x9, x22, #7
	cbz x9, 219f
	b 220f
219:
	add x9, x22, x23
	lsr x9, x9, #7
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
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x21, x21, #1
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 228b
	b 227f
226:
227:
	sub x9, x23, #128
	cbz x9, 229f
	b 230f
229:
	add x1, x19, #64
	movz x23, #0, lsl #0
	movz x10, #1, lsl #0
230:
218:
24:
	cbz x10, 231f
	add x0, x19, #0
	add x2, x10, #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	b 232f
231:
232:
	cbnz x22, 22b
	b 21f
20:
21:
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	ret
	.arch_extension nosha3
	.p2align 6
