// The functions of `src/sha512.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha384_init:
	movz x9, #40664, lsl #0
	movk x9, #49413, lsl #16
	movk x9, #40285, lsl #32
	movk x9, #52155, lsl #48
	str x9, [x0, #0]
	movz x9, #54535, lsl #0
	movk x9, #13948, lsl #16
	movk x9, #10538, lsl #32
	movk x9, #25242, lsl #48
	str x9, [x0, #8]
	movz x9, #56599, lsl #0
	movk x9, #12400, lsl #16
	movk x9, #346, lsl #32
	movk x9, #37209, lsl #48
	str x9, [x0, #16]
	movz x9, #22841, lsl #0
	movk x9, #63246, lsl #16
	movk x9, #60632, lsl #32
	movk x9, #5423, lsl #48
	str x9, [x0, #24]
	movz x9, #2865, lsl #0
	movk x9, #65472, lsl #16
	movk x9, #9831, lsl #32
	movk x9, #26419, lsl #48
	str x9, [x0, #32]
	movz x9, #5393, lsl #0
	movk x9, #26712, lsl #16
	movk x9, #19079, lsl #32
	movk x9, #36532, lsl #48
	str x9, [x0, #40]
	movz x9, #36775, lsl #0
	movk x9, #25849, lsl #16
	movk x9, #11789, lsl #32
	movk x9, #56076, lsl #48
	str x9, [x0, #48]
	movz x9, #20388, lsl #0
	movk x9, #48890, lsl #16
	movk x9, #18461, lsl #32
	movk x9, #18357, lsl #48
	str x9, [x0, #56]
	ret
	.p2align 6

vg_sha512_init:
	movz x9, #51464, lsl #0
	movk x9, #62396, lsl #16
	movk x9, #58983, lsl #32
	movk x9, #27145, lsl #48
	str x9, [x0, #0]
	movz x9, #42811, lsl #0
	movk x9, #33994, lsl #16
	movk x9, #44677, lsl #32
	movk x9, #47975, lsl #48
	str x9, [x0, #8]
	movz x9, #63531, lsl #0
	movk x9, #65172, lsl #16
	movk x9, #62322, lsl #32
	movk x9, #15470, lsl #48
	str x9, [x0, #16]
	movz x9, #14065, lsl #0
	movk x9, #24349, lsl #16
	movk x9, #62778, lsl #32
	movk x9, #42319, lsl #48
	str x9, [x0, #24]
	movz x9, #33489, lsl #0
	movk x9, #44518, lsl #16
	movk x9, #21119, lsl #32
	movk x9, #20750, lsl #48
	str x9, [x0, #32]
	movz x9, #27679, lsl #0
	movk x9, #11070, lsl #16
	movk x9, #26764, lsl #32
	movk x9, #39685, lsl #48
	str x9, [x0, #40]
	movz x9, #48491, lsl #0
	movk x9, #64321, lsl #16
	movk x9, #55723, lsl #32
	movk x9, #8067, lsl #48
	str x9, [x0, #48]
	movz x9, #8569, lsl #0
	movk x9, #4990, lsl #16
	movk x9, #52505, lsl #32
	movk x9, #23520, lsl #48
	str x9, [x0, #56]
	ret
	.p2align 6

vg_sha512_224_init:
	movz x9, #19874, lsl #0
	movk x9, #6484, lsl #16
	movk x9, #14280, lsl #32
	movk x9, #35901, lsl #48
	str x9, [x0, #0]
	movz x9, #54486, lsl #0
	movk x9, #35292, lsl #16
	movk x9, #39270, lsl #32
	movk x9, #29665, lsl #48
	str x9, [x0, #8]
	movz x9, #40066, lsl #0
	movk x9, #13055, lsl #16
	movk x9, #47022, lsl #32
	movk x9, #7674, lsl #48
	str x9, [x0, #16]
	movz x9, #40911, lsl #0
	movk x9, #22575, lsl #16
	movk x9, #54548, lsl #32
	movk x9, #26525, lsl #48
	str x9, [x0, #24]
	movz x9, #19880, lsl #0
	movk x9, #31700, lsl #16
	movk x9, #11113, lsl #32
	movk x9, #3949, lsl #48
	str x9, [x0, #32]
	movz x9, #35138, lsl #0
	movk x9, #1220, lsl #16
	movk x9, #28531, lsl #32
	movk x9, #30691, lsl #48
	str x9, [x0, #40]
	movz x9, #14024, lsl #0
	movk x9, #27165, lsl #16
	movk x9, #34216, lsl #32
	movk x9, #16285, lsl #48
	str x9, [x0, #48]
	movz x9, #37537, lsl #0
	movk x9, #37334, lsl #16
	movk x9, #59053, lsl #32
	movk x9, #4370, lsl #48
	str x9, [x0, #56]
	ret
	.p2align 6

vg_sha512_256_init:
	movz x9, #63276, lsl #0
	movk x9, #64555, lsl #16
	movk x9, #8596, lsl #32
	movk x9, #8753, lsl #48
	str x9, [x0, #0]
	movz x9, #25794, lsl #0
	movk x9, #51276, lsl #16
	movk x9, #24483, lsl #32
	movk x9, #40789, lsl #48
	str x9, [x0, #8]
	movz x9, #45393, lsl #0
	movk x9, #28499, lsl #16
	movk x9, #47211, lsl #32
	movk x9, #9107, lsl #48
	str x9, [x0, #16]
	movz x9, #60093, lsl #0
	movk x9, #22848, lsl #16
	movk x9, #30489, lsl #32
	movk x9, #38456, lsl #48
	str x9, [x0, #24]
	movz x9, #65507, lsl #0
	movk x9, #43150, lsl #16
	movk x9, #16098, lsl #32
	movk x9, #38440, lsl #48
	str x9, [x0, #32]
	movz x9, #14738, lsl #0
	movk x9, #21382, lsl #16
	movk x9, #7717, lsl #32
	movk x9, #48734, lsl #48
	str x9, [x0, #40]
	movz x9, #47274, lsl #0
	movk x9, #11397, lsl #16
	movk x9, #39420, lsl #32
	movk x9, #11009, lsl #48
	str x9, [x0, #48]
	movz x9, #11426, lsl #0
	movk x9, #33221, lsl #16
	movk x9, #11740, lsl #32
	movk x9, #3767, lsl #48
	str x9, [x0, #56]
	ret
	.p2align 6

vg_sha384_finalize:
	sub sp, sp, #1376
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	str x22, [x3, #664]
	str x23, [x3, #672]
	str x24, [x3, #680]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #127, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	add x24, x23, #15
	lsr x24, x24, #7
20:
	movz x11, #128, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #112, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
210:
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	add sp, sp, #1376
	ret
	.p2align 6

vg_sha384_digest:
	sub sp, sp, #896
	add x10, sp, #832
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz x9, #40664, lsl #0
	movk x9, #49413, lsl #16
	movk x9, #40285, lsl #32
	movk x9, #52155, lsl #48
	movz x10, #54535, lsl #0
	movk x10, #13948, lsl #16
	movk x10, #10538, lsl #32
	movk x10, #25242, lsl #48
	stp x9, x10, [x0, #0]
	movz x9, #56599, lsl #0
	movk x9, #12400, lsl #16
	movk x9, #346, lsl #32
	movk x9, #37209, lsl #48
	movz x10, #22841, lsl #0
	movk x10, #63246, lsl #16
	movk x10, #60632, lsl #32
	movk x10, #5423, lsl #48
	stp x9, x10, [x0, #16]
	movz x9, #2865, lsl #0
	movk x9, #65472, lsl #16
	movk x9, #9831, lsl #32
	movk x9, #26419, lsl #48
	movz x10, #5393, lsl #0
	movk x10, #26712, lsl #16
	movk x10, #19079, lsl #32
	movk x10, #36532, lsl #48
	stp x9, x10, [x0, #32]
	movz x9, #36775, lsl #0
	movk x9, #25849, lsl #16
	movk x9, #11789, lsl #32
	movk x9, #56076, lsl #48
	movz x10, #20388, lsl #0
	movk x10, #48890, lsl #16
	movk x10, #18461, lsl #32
	movk x10, #18357, lsl #48
	stp x9, x10, [x0, #48]
	lsr x28, x25, #7
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	lsl x9, x28, #7
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	movz x9, #127, lsl #0
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
	add x9, x28, #16
	lsr x9, x9, #7
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x12, sp, #176
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	add x19, sp, #0
	add x21, x26, #0
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	add x16, sp, #832
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #896
	ret
	.p2align 6

vg_sha384_finalize_sha3:
	.arch_extension sha3
	sub sp, sp, #1376
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	str x22, [x3, #664]
	str x23, [x3, #672]
	str x24, [x3, #680]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #127, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	add x24, x23, #15
	lsr x24, x24, #7
20:
	movz x11, #128, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #112, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
210:
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	add sp, sp, #1376
	ret
	.arch_extension nosha3
	.p2align 6

vg_sha384_digest_sha3:
	.arch_extension sha3
	sub sp, sp, #896
	add x10, sp, #832
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz x9, #40664, lsl #0
	movk x9, #49413, lsl #16
	movk x9, #40285, lsl #32
	movk x9, #52155, lsl #48
	movz x10, #54535, lsl #0
	movk x10, #13948, lsl #16
	movk x10, #10538, lsl #32
	movk x10, #25242, lsl #48
	stp x9, x10, [x0, #0]
	movz x9, #56599, lsl #0
	movk x9, #12400, lsl #16
	movk x9, #346, lsl #32
	movk x9, #37209, lsl #48
	movz x10, #22841, lsl #0
	movk x10, #63246, lsl #16
	movk x10, #60632, lsl #32
	movk x10, #5423, lsl #48
	stp x9, x10, [x0, #16]
	movz x9, #2865, lsl #0
	movk x9, #65472, lsl #16
	movk x9, #9831, lsl #32
	movk x9, #26419, lsl #48
	movz x10, #5393, lsl #0
	movk x10, #26712, lsl #16
	movk x10, #19079, lsl #32
	movk x10, #36532, lsl #48
	stp x9, x10, [x0, #32]
	movz x9, #36775, lsl #0
	movk x9, #25849, lsl #16
	movk x9, #11789, lsl #32
	movk x9, #56076, lsl #48
	movz x10, #20388, lsl #0
	movk x10, #48890, lsl #16
	movk x10, #18461, lsl #32
	movk x10, #18357, lsl #48
	stp x9, x10, [x0, #48]
	lsr x28, x25, #7
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	lsl x9, x28, #7
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	movz x9, #127, lsl #0
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
	add x9, x28, #16
	lsr x9, x9, #7
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x12, sp, #176
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	add x19, sp, #0
	add x21, x26, #0
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	add x16, sp, #832
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #896
	ret
	.arch_extension nosha3
	.p2align 6

vg_sha512_update:
	sub sp, sp, #1376
	add x4, sp, #0
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
	bl {vg_sha512_compress}
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
	add sp, sp, #1376
	ret
	.p2align 6

vg_sha512_finalize:
	sub sp, sp, #1376
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	str x22, [x3, #664]
	str x23, [x3, #672]
	str x24, [x3, #680]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #127, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	add x24, x23, #15
	lsr x24, x24, #7
20:
	movz x11, #128, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #112, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
210:
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	add sp, sp, #1376
	ret
	.p2align 6

vg_sha512_digest:
	sub sp, sp, #896
	add x10, sp, #832
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz x9, #51464, lsl #0
	movk x9, #62396, lsl #16
	movk x9, #58983, lsl #32
	movk x9, #27145, lsl #48
	movz x10, #42811, lsl #0
	movk x10, #33994, lsl #16
	movk x10, #44677, lsl #32
	movk x10, #47975, lsl #48
	stp x9, x10, [x0, #0]
	movz x9, #63531, lsl #0
	movk x9, #65172, lsl #16
	movk x9, #62322, lsl #32
	movk x9, #15470, lsl #48
	movz x10, #14065, lsl #0
	movk x10, #24349, lsl #16
	movk x10, #62778, lsl #32
	movk x10, #42319, lsl #48
	stp x9, x10, [x0, #16]
	movz x9, #33489, lsl #0
	movk x9, #44518, lsl #16
	movk x9, #21119, lsl #32
	movk x9, #20750, lsl #48
	movz x10, #27679, lsl #0
	movk x10, #11070, lsl #16
	movk x10, #26764, lsl #32
	movk x10, #39685, lsl #48
	stp x9, x10, [x0, #32]
	movz x9, #48491, lsl #0
	movk x9, #64321, lsl #16
	movk x9, #55723, lsl #32
	movk x9, #8067, lsl #48
	movz x10, #8569, lsl #0
	movk x10, #4990, lsl #16
	movk x10, #52505, lsl #32
	movk x10, #23520, lsl #48
	stp x9, x10, [x0, #48]
	lsr x28, x25, #7
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	lsl x9, x28, #7
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	movz x9, #127, lsl #0
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
	add x9, x28, #16
	lsr x9, x9, #7
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x12, sp, #176
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	add x19, sp, #0
	add x21, x26, #0
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	add x16, sp, #832
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #896
	ret
	.p2align 6

vg_sha512_update_sha3:
	.arch_extension sha3
	sub sp, sp, #1376
	add x4, sp, #0
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
	add sp, sp, #1376
	ret
	.arch_extension nosha3
	.p2align 6

vg_sha512_finalize_sha3:
	.arch_extension sha3
	sub sp, sp, #1376
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	str x22, [x3, #664]
	str x23, [x3, #672]
	str x24, [x3, #680]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #127, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	add x24, x23, #15
	lsr x24, x24, #7
20:
	movz x11, #128, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #112, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
210:
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	add sp, sp, #1376
	ret
	.arch_extension nosha3
	.p2align 6

vg_sha512_digest_sha3:
	.arch_extension sha3
	sub sp, sp, #896
	add x10, sp, #832
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz x9, #51464, lsl #0
	movk x9, #62396, lsl #16
	movk x9, #58983, lsl #32
	movk x9, #27145, lsl #48
	movz x10, #42811, lsl #0
	movk x10, #33994, lsl #16
	movk x10, #44677, lsl #32
	movk x10, #47975, lsl #48
	stp x9, x10, [x0, #0]
	movz x9, #63531, lsl #0
	movk x9, #65172, lsl #16
	movk x9, #62322, lsl #32
	movk x9, #15470, lsl #48
	movz x10, #14065, lsl #0
	movk x10, #24349, lsl #16
	movk x10, #62778, lsl #32
	movk x10, #42319, lsl #48
	stp x9, x10, [x0, #16]
	movz x9, #33489, lsl #0
	movk x9, #44518, lsl #16
	movk x9, #21119, lsl #32
	movk x9, #20750, lsl #48
	movz x10, #27679, lsl #0
	movk x10, #11070, lsl #16
	movk x10, #26764, lsl #32
	movk x10, #39685, lsl #48
	stp x9, x10, [x0, #32]
	movz x9, #48491, lsl #0
	movk x9, #64321, lsl #16
	movk x9, #55723, lsl #32
	movk x9, #8067, lsl #48
	movz x10, #8569, lsl #0
	movk x10, #4990, lsl #16
	movk x10, #52505, lsl #32
	movk x10, #23520, lsl #48
	stp x9, x10, [x0, #48]
	lsr x28, x25, #7
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	lsl x9, x28, #7
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	movz x9, #127, lsl #0
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
	add x9, x28, #16
	lsr x9, x9, #7
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x12, sp, #176
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	add x19, sp, #0
	add x21, x26, #0
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	add x16, sp, #832
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #896
	ret
	.arch_extension nosha3
	.p2align 6

vg_sha512_224_finalize:
	sub sp, sp, #1376
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	str x22, [x3, #664]
	str x23, [x3, #672]
	str x24, [x3, #680]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #127, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	add x24, x23, #15
	lsr x24, x24, #7
20:
	movz x11, #128, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #112, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
210:
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr w9, [x19, #28]
	rev w9, w9
	str w9, [x21, #24]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	add sp, sp, #1376
	ret
	.p2align 6

vg_sha512_224_digest:
	sub sp, sp, #896
	add x10, sp, #832
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz x9, #19874, lsl #0
	movk x9, #6484, lsl #16
	movk x9, #14280, lsl #32
	movk x9, #35901, lsl #48
	movz x10, #54486, lsl #0
	movk x10, #35292, lsl #16
	movk x10, #39270, lsl #32
	movk x10, #29665, lsl #48
	stp x9, x10, [x0, #0]
	movz x9, #40066, lsl #0
	movk x9, #13055, lsl #16
	movk x9, #47022, lsl #32
	movk x9, #7674, lsl #48
	movz x10, #40911, lsl #0
	movk x10, #22575, lsl #16
	movk x10, #54548, lsl #32
	movk x10, #26525, lsl #48
	stp x9, x10, [x0, #16]
	movz x9, #19880, lsl #0
	movk x9, #31700, lsl #16
	movk x9, #11113, lsl #32
	movk x9, #3949, lsl #48
	movz x10, #35138, lsl #0
	movk x10, #1220, lsl #16
	movk x10, #28531, lsl #32
	movk x10, #30691, lsl #48
	stp x9, x10, [x0, #32]
	movz x9, #14024, lsl #0
	movk x9, #27165, lsl #16
	movk x9, #34216, lsl #32
	movk x9, #16285, lsl #48
	movz x10, #37537, lsl #0
	movk x10, #37334, lsl #16
	movk x10, #59053, lsl #32
	movk x10, #4370, lsl #48
	stp x9, x10, [x0, #48]
	lsr x28, x25, #7
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	lsl x9, x28, #7
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	movz x9, #127, lsl #0
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
	add x9, x28, #16
	lsr x9, x9, #7
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x12, sp, #176
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	add x19, sp, #0
	add x21, x26, #0
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr w9, [x19, #28]
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
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	add x16, sp, #832
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #896
	ret
	.p2align 6

vg_sha512_224_finalize_sha3:
	.arch_extension sha3
	sub sp, sp, #1376
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	str x22, [x3, #664]
	str x23, [x3, #672]
	str x24, [x3, #680]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #127, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	add x24, x23, #15
	lsr x24, x24, #7
20:
	movz x11, #128, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #112, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
210:
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr w9, [x19, #28]
	rev w9, w9
	str w9, [x21, #24]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	add sp, sp, #1376
	ret
	.arch_extension nosha3
	.p2align 6

vg_sha512_224_digest_sha3:
	.arch_extension sha3
	sub sp, sp, #896
	add x10, sp, #832
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz x9, #19874, lsl #0
	movk x9, #6484, lsl #16
	movk x9, #14280, lsl #32
	movk x9, #35901, lsl #48
	movz x10, #54486, lsl #0
	movk x10, #35292, lsl #16
	movk x10, #39270, lsl #32
	movk x10, #29665, lsl #48
	stp x9, x10, [x0, #0]
	movz x9, #40066, lsl #0
	movk x9, #13055, lsl #16
	movk x9, #47022, lsl #32
	movk x9, #7674, lsl #48
	movz x10, #40911, lsl #0
	movk x10, #22575, lsl #16
	movk x10, #54548, lsl #32
	movk x10, #26525, lsl #48
	stp x9, x10, [x0, #16]
	movz x9, #19880, lsl #0
	movk x9, #31700, lsl #16
	movk x9, #11113, lsl #32
	movk x9, #3949, lsl #48
	movz x10, #35138, lsl #0
	movk x10, #1220, lsl #16
	movk x10, #28531, lsl #32
	movk x10, #30691, lsl #48
	stp x9, x10, [x0, #32]
	movz x9, #14024, lsl #0
	movk x9, #27165, lsl #16
	movk x9, #34216, lsl #32
	movk x9, #16285, lsl #48
	movz x10, #37537, lsl #0
	movk x10, #37334, lsl #16
	movk x10, #59053, lsl #32
	movk x10, #4370, lsl #48
	stp x9, x10, [x0, #48]
	lsr x28, x25, #7
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	lsl x9, x28, #7
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	movz x9, #127, lsl #0
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
	add x9, x28, #16
	lsr x9, x9, #7
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x12, sp, #176
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	add x19, sp, #0
	add x21, x26, #0
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr w9, [x19, #28]
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
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	add x16, sp, #832
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #896
	ret
	.arch_extension nosha3
	.p2align 6

vg_sha512_256_finalize:
	sub sp, sp, #1376
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	str x22, [x3, #664]
	str x23, [x3, #672]
	str x24, [x3, #680]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #127, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	add x24, x23, #15
	lsr x24, x24, #7
20:
	movz x11, #128, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #112, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
210:
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	add sp, sp, #1376
	ret
	.p2align 6

vg_sha512_256_digest:
	sub sp, sp, #896
	add x10, sp, #832
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz x9, #63276, lsl #0
	movk x9, #64555, lsl #16
	movk x9, #8596, lsl #32
	movk x9, #8753, lsl #48
	movz x10, #25794, lsl #0
	movk x10, #51276, lsl #16
	movk x10, #24483, lsl #32
	movk x10, #40789, lsl #48
	stp x9, x10, [x0, #0]
	movz x9, #45393, lsl #0
	movk x9, #28499, lsl #16
	movk x9, #47211, lsl #32
	movk x9, #9107, lsl #48
	movz x10, #60093, lsl #0
	movk x10, #22848, lsl #16
	movk x10, #30489, lsl #32
	movk x10, #38456, lsl #48
	stp x9, x10, [x0, #16]
	movz x9, #65507, lsl #0
	movk x9, #43150, lsl #16
	movk x9, #16098, lsl #32
	movk x9, #38440, lsl #48
	movz x10, #14738, lsl #0
	movk x10, #21382, lsl #16
	movk x10, #7717, lsl #32
	movk x10, #48734, lsl #48
	stp x9, x10, [x0, #32]
	movz x9, #47274, lsl #0
	movk x9, #11397, lsl #16
	movk x9, #39420, lsl #32
	movk x9, #11009, lsl #48
	movz x10, #11426, lsl #0
	movk x10, #33221, lsl #16
	movk x10, #11740, lsl #32
	movk x10, #3767, lsl #48
	stp x9, x10, [x0, #48]
	lsr x28, x25, #7
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	lsl x9, x28, #7
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	movz x9, #127, lsl #0
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
	add x9, x28, #16
	lsr x9, x9, #7
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x12, sp, #176
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress}
	add x19, sp, #0
	add x21, x26, #0
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	add x16, sp, #832
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #896
	ret
	.p2align 6

vg_sha512_256_finalize_sha3:
	.arch_extension sha3
	sub sp, sp, #1376
	add x3, sp, #0
	str x30, [sp, #-16]!
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	str x22, [x3, #664]
	str x23, [x3, #672]
	str x24, [x3, #680]
	add x19, x0, #0
	add x20, x3, #0
	add x21, x2, #0
	add x22, x1, #0
	movz x9, #127, lsl #0
	and x23, x22, x9
	movz x9, #128, lsl #0
	add x12, x19, x23
	strb w9, [x12, #64]
	add x23, x23, #1
	add x24, x23, #15
	lsr x24, x24, #7
20:
	movz x11, #128, lsl #0
	cbz x24, 21f
	b 22f
21:
	movz x11, #112, lsl #0
22:
	movz x9, #0, lsl #0
	sub x11, x11, x23
	lsr x13, x11, #3
	cbz x13, 23f
25:
	add x12, x19, x23
	str x9, [x12, #64]
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
	strb w9, [x12, #64]
	add x23, x23, #1
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
27:
	cbz x24, 29f
	b 210f
29:
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
210:
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	movz x23, #0, lsl #0
	sub x24, x24, #1
	cbz x24, 20b
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ldr x30, [sp], #16
	add sp, sp, #1376
	ret
	.arch_extension nosha3
	.p2align 6

vg_sha512_256_digest_sha3:
	.arch_extension sha3
	sub sp, sp, #896
	add x10, sp, #832
	stp x19, x21, [x10, #0]
	stp x22, x25, [x10, #16]
	stp x26, x27, [x10, #32]
	stp x28, x30, [x10, #48]
	add x25, x1, #0
	add x26, x2, #0
	add x27, x0, #0
	add x0, sp, #0
	movz x9, #63276, lsl #0
	movk x9, #64555, lsl #16
	movk x9, #8596, lsl #32
	movk x9, #8753, lsl #48
	movz x10, #25794, lsl #0
	movk x10, #51276, lsl #16
	movk x10, #24483, lsl #32
	movk x10, #40789, lsl #48
	stp x9, x10, [x0, #0]
	movz x9, #45393, lsl #0
	movk x9, #28499, lsl #16
	movk x9, #47211, lsl #32
	movk x9, #9107, lsl #48
	movz x10, #60093, lsl #0
	movk x10, #22848, lsl #16
	movk x10, #30489, lsl #32
	movk x10, #38456, lsl #48
	stp x9, x10, [x0, #16]
	movz x9, #65507, lsl #0
	movk x9, #43150, lsl #16
	movk x9, #16098, lsl #32
	movk x9, #38440, lsl #48
	movz x10, #14738, lsl #0
	movk x10, #21382, lsl #16
	movk x10, #7717, lsl #32
	movk x10, #48734, lsl #48
	stp x9, x10, [x0, #32]
	movz x9, #47274, lsl #0
	movk x9, #11397, lsl #16
	movk x9, #39420, lsl #32
	movk x9, #11009, lsl #48
	movz x10, #11426, lsl #0
	movk x10, #33221, lsl #16
	movk x10, #11740, lsl #32
	movk x10, #3767, lsl #48
	stp x9, x10, [x0, #48]
	lsr x28, x25, #7
	cbz x28, 20f
	add x0, sp, #0
	add x1, x27, #0
	add x2, x28, #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	lsl x9, x28, #7
	add x27, x27, x9
	b 21f
20:
21:
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	movz x9, #127, lsl #0
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
	add x9, x28, #16
	lsr x9, x9, #7
	cbz x9, 210f
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	movz x9, #0, lsl #0
	add x12, sp, #64
	stp x9, x9, [x12, #0]
	stp x9, x9, [x12, #16]
	stp x9, x9, [x12, #32]
	stp x9, x9, [x12, #48]
	stp x9, x9, [x12, #64]
	stp x9, x9, [x12, #80]
	stp x9, x9, [x12, #96]
	stp x9, x9, [x12, #112]
	b 211f
210:
211:
	add x19, sp, #0
	add x22, x25, #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x12, sp, #176
	ldr x9, [x12, #0]
	ldr x10, [x12, #8]
	stp x9, x10, [x12, #0]
	add x0, sp, #0
	add x1, sp, #64
	movz x2, #1, lsl #0
	add x3, sp, #192
	bl {vg_sha512_compress_sha3}
	add x19, sp, #0
	add x21, x26, #0
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	add x16, sp, #0
	movz x17, #0, lsl #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	add x16, sp, #832
	ldp x19, x21, [x16, #0]
	ldp x22, x25, [x16, #16]
	ldp x26, x27, [x16, #32]
	ldp x28, x30, [x16, #48]
	add sp, sp, #896
	ret
	.arch_extension nosha3
	.p2align 6
