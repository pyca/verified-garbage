// The functions of `src/sha256.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha224_init:
	adrp x9, {VG_SHA224_H0}
	add x9, x9, {VG_SHA224_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	ret
	.p2align 6

vg_sha256_init:
	adrp x9, {VG_SHA256_H0}
	add x9, x9, {VG_SHA256_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	ret
	.p2align 6

vg_sha224_finalize:
	sub sp, sp, #608
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #112]
	str x20, [x3, #120]
	str x21, [x3, #128]
	str x22, [x3, #136]
	str x23, [x3, #144]
	str x24, [x3, #152]
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
	bl {vg_sha256_compress}
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
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.p2align 6

vg_sha224_digest:
	sub sp, sp, #272
	add x10, sp, #208
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	adrp x9, {VG_SHA224_H0}
	add x9, x9, {VG_SHA224_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #32
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	movz x9, #63, lsl #0
	and x28, x25, x9
	lsr x13, x28, #4
	cbz x13, 22f
24:
	ldp x9, x10, [x27, #0]
	stp x9, x10, [x12, #0]
	add x27, x27, #16
	add x12, x12, #16
	sub x13, x13, #1
	cbnz x13, 24b
	b 23f
22:
23:
	movz x9, #15, lsl #0
	and x11, x28, x9
	cbz x11, 25f
	lsr x9, x25, #4
	cbz x9, 27f
	add x13, x27, x11
	sub x13, x13, #16
	movz x9, #128, lsl #0
	ldr q0, [x13, #0]
	movi v1.2d, #0
	mov v1.d[0], x9
	movz x6, #4368, lsl #0
	movk x6, #4882, lsl #16
	movk x6, #5396, lsl #32
	movk x6, #5910, lsl #48
	movz x7, #6424, lsl #0
	movk x7, #6938, lsl #16
	movk x7, #7452, lsl #32
	movk x7, #7966, lsl #48
	mov v2.d[0], x6
	mov v2.d[1], x7
	dup v3.16b, w11
	sub v2.16b, v2.16b, v3.16b
	tbl v4.16b, {v0.16b, v1.16b}, v2.16b
	str q4, [x12, #0]
	b 28f
27:
29:
	ldrb w9, [x27, #0]
	strb w9, [x12, #0]
	add x27, x27, #1
	add x12, x12, #1
	sub x11, x11, #1
	cbnz x11, 29b
	movz x9, #128, lsl #0
	strb w9, [x12, #0]
28:
	b 26f
25:
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x12, #0]
26:
	add x9, x28, #8
	lsr x9, x9, #6
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	movz x9, #0, lsl #0
	add x12, sp, #32
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #88]
	add x12, sp, #80
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	add x19, sp, #0
	add x21, x26, #0
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
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	add x16, sp, #208
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #272
	ret
	.p2align 6

vg_sha224_finalize_sha2:
	.arch_extension sha2
	sub sp, sp, #608
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #112]
	str x20, [x3, #120]
	str x21, [x3, #128]
	str x22, [x3, #136]
	str x23, [x3, #144]
	str x24, [x3, #152]
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
	bl {vg_sha256_compress_sha2}
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
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha224_digest_sha2:
	.arch_extension sha2
	sub sp, sp, #272
	add x10, sp, #208
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	adrp x9, {VG_SHA224_H0}
	add x9, x9, {VG_SHA224_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #32
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	movz x9, #63, lsl #0
	and x28, x25, x9
	lsr x13, x28, #4
	cbz x13, 22f
24:
	ldp x9, x10, [x27, #0]
	stp x9, x10, [x12, #0]
	add x27, x27, #16
	add x12, x12, #16
	sub x13, x13, #1
	cbnz x13, 24b
	b 23f
22:
23:
	movz x9, #15, lsl #0
	and x11, x28, x9
	cbz x11, 25f
	lsr x9, x25, #4
	cbz x9, 27f
	add x13, x27, x11
	sub x13, x13, #16
	movz x9, #128, lsl #0
	ldr q0, [x13, #0]
	movi v1.2d, #0
	mov v1.d[0], x9
	movz x6, #4368, lsl #0
	movk x6, #4882, lsl #16
	movk x6, #5396, lsl #32
	movk x6, #5910, lsl #48
	movz x7, #6424, lsl #0
	movk x7, #6938, lsl #16
	movk x7, #7452, lsl #32
	movk x7, #7966, lsl #48
	mov v2.d[0], x6
	mov v2.d[1], x7
	dup v3.16b, w11
	sub v2.16b, v2.16b, v3.16b
	tbl v4.16b, {v0.16b, v1.16b}, v2.16b
	str q4, [x12, #0]
	b 28f
27:
29:
	ldrb w9, [x27, #0]
	strb w9, [x12, #0]
	add x27, x27, #1
	add x12, x12, #1
	sub x11, x11, #1
	cbnz x11, 29b
	movz x9, #128, lsl #0
	strb w9, [x12, #0]
28:
	b 26f
25:
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x12, #0]
26:
	add x9, x28, #8
	lsr x9, x9, #6
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	movz x9, #0, lsl #0
	add x12, sp, #32
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #88]
	add x12, sp, #80
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	add x19, sp, #0
	add x21, x26, #0
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
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	add x16, sp, #208
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #272
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha256_update:
	sub sp, sp, #608
	add x4, sp, #0
	str x30, [sp, #-16]!
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x23, [x4, #144]
	str x24, [x4, #152]
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
	bl {vg_sha256_compress}
	b 232f
231:
232:
	cbnz x22, 22b
	b 21f
20:
21:
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.p2align 6

vg_sha256_finalize:
	sub sp, sp, #608
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #112]
	str x20, [x3, #120]
	str x21, [x3, #128]
	str x22, [x3, #136]
	str x23, [x3, #144]
	str x24, [x3, #152]
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
	bl {vg_sha256_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.p2align 6

vg_sha256_digest:
	sub sp, sp, #272
	add x10, sp, #208
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	adrp x9, {VG_SHA256_H0}
	add x9, x9, {VG_SHA256_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #32
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	movz x9, #63, lsl #0
	and x28, x25, x9
	lsr x13, x28, #4
	cbz x13, 22f
24:
	ldp x9, x10, [x27, #0]
	stp x9, x10, [x12, #0]
	add x27, x27, #16
	add x12, x12, #16
	sub x13, x13, #1
	cbnz x13, 24b
	b 23f
22:
23:
	movz x9, #15, lsl #0
	and x11, x28, x9
	cbz x11, 25f
	lsr x9, x25, #4
	cbz x9, 27f
	add x13, x27, x11
	sub x13, x13, #16
	movz x9, #128, lsl #0
	ldr q0, [x13, #0]
	movi v1.2d, #0
	mov v1.d[0], x9
	movz x6, #4368, lsl #0
	movk x6, #4882, lsl #16
	movk x6, #5396, lsl #32
	movk x6, #5910, lsl #48
	movz x7, #6424, lsl #0
	movk x7, #6938, lsl #16
	movk x7, #7452, lsl #32
	movk x7, #7966, lsl #48
	mov v2.d[0], x6
	mov v2.d[1], x7
	dup v3.16b, w11
	sub v2.16b, v2.16b, v3.16b
	tbl v4.16b, {v0.16b, v1.16b}, v2.16b
	str q4, [x12, #0]
	b 28f
27:
29:
	ldrb w9, [x27, #0]
	strb w9, [x12, #0]
	add x27, x27, #1
	add x12, x12, #1
	sub x11, x11, #1
	cbnz x11, 29b
	movz x9, #128, lsl #0
	strb w9, [x12, #0]
28:
	b 26f
25:
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x12, #0]
26:
	add x9, x28, #8
	lsr x9, x9, #6
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	movz x9, #0, lsl #0
	add x12, sp, #32
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #88]
	add x12, sp, #80
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress}
	add x19, sp, #0
	add x21, x26, #0
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	add x16, sp, #208
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #272
	ret
	.p2align 6

vg_sha256_update_sha2:
	.arch_extension sha2
	sub sp, sp, #608
	add x4, sp, #0
	str x30, [sp, #-16]!
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x23, [x4, #144]
	str x24, [x4, #152]
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
	bl {vg_sha256_compress_sha2}
	b 232f
231:
232:
	cbnz x22, 22b
	b 21f
20:
21:
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha256_finalize_sha2:
	.arch_extension sha2
	sub sp, sp, #608
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #112]
	str x20, [x3, #120]
	str x21, [x3, #128]
	str x22, [x3, #136]
	str x23, [x3, #144]
	str x24, [x3, #152]
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
	bl {vg_sha256_compress_sha2}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ldr x30, [sp], #16
	add sp, sp, #608
	ret
	.arch_extension nosha2
	.p2align 6

vg_sha256_digest_sha2:
	.arch_extension sha2
	sub sp, sp, #272
	add x10, sp, #208
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	adrp x9, {VG_SHA256_H0}
	add x9, x9, {VG_SHA256_H0}
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	str q0, [x0, #0]
	str q1, [x0, #16]
	lsr x28, x25, #6
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	lsl x9, x28, #6
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #32
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	movz x9, #63, lsl #0
	and x28, x25, x9
	lsr x13, x28, #4
	cbz x13, 22f
24:
	ldp x9, x10, [x27, #0]
	stp x9, x10, [x12, #0]
	add x27, x27, #16
	add x12, x12, #16
	sub x13, x13, #1
	cbnz x13, 24b
	b 23f
22:
23:
	movz x9, #15, lsl #0
	and x11, x28, x9
	cbz x11, 25f
	lsr x9, x25, #4
	cbz x9, 27f
	add x13, x27, x11
	sub x13, x13, #16
	movz x9, #128, lsl #0
	ldr q0, [x13, #0]
	movi v1.2d, #0
	mov v1.d[0], x9
	movz x6, #4368, lsl #0
	movk x6, #4882, lsl #16
	movk x6, #5396, lsl #32
	movk x6, #5910, lsl #48
	movz x7, #6424, lsl #0
	movk x7, #6938, lsl #16
	movk x7, #7452, lsl #32
	movk x7, #7966, lsl #48
	mov v2.d[0], x6
	mov v2.d[1], x7
	dup v3.16b, w11
	sub v2.16b, v2.16b, v3.16b
	tbl v4.16b, {v0.16b, v1.16b}, v2.16b
	str q4, [x12, #0]
	b 28f
27:
29:
	ldrb w9, [x27, #0]
	strb w9, [x12, #0]
	add x27, x27, #1
	add x12, x12, #1
	sub x11, x11, #1
	cbnz x11, 29b
	movz x9, #128, lsl #0
	strb w9, [x12, #0]
28:
	b 26f
25:
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x12, #0]
26:
	add x9, x28, #8
	lsr x9, x9, #6
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	movz x9, #0, lsl #0
	add x12, sp, #32
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #88]
	add x12, sp, #80
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #32
	movz x2, #1, lsl #0
	add x3, sp, #96
	bl {vg_sha256_compress_sha2}
	add x19, sp, #0
	add x21, x26, #0
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	add x16, sp, #208
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #272
	ret
	.arch_extension nosha2
	.p2align 6
