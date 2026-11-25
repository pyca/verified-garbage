// The functions of `src/sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha3_224_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #144, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_224_finalize_sha3:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #144, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x19, #0
	movz x1, #144, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #28, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_256_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_256_finalize_sha3:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x19, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #32, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_384_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #104, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_384_finalize_sha3:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #104, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x19, #0
	movz x1, #104, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #48, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_512_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #72, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_512_finalize_sha3:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #72, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x19, #0
	movz x1, #72, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #64, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_shake128_update_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake128_finalize_sha3:
	sub sp, sp, #640
	add x2, sp, #0
	add x4, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600_sha3}
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake128_squeeze_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
27:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 27b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake256_finalize_sha3:
	sub sp, sp, #640
	add x2, sp, #0
	add x4, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600_sha3}
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	movz x0, #0, lsl #0
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake256_squeeze_sha3:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	mov v10.d[1], x1
	mov v11.d[1], x1
	mov v12.d[1], x1
	mov v13.d[1], x1
	mov v14.d[1], x1
	mov v15.d[1], x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
27:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 27b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_224_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #144, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_224_finalize:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #144, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch}
	add x0, x19, #0
	movz x1, #144, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #28, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_256_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_256_finalize:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch}
	add x0, x19, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #32, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_384_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #104, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_384_finalize:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #104, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch}
	add x0, x19, #0
	movz x1, #104, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #48, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_sha3_512_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #72, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_sha3_512_finalize:
	sub sp, sp, #672
	add x3, sp, #0
	str x30, [x3, #664]
	str x19, [x3, #640]
	str x20, [x3, #648]
	str x21, [x3, #656]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x3, #0
	add x2, x1, #0
	movz x1, #72, lsl #0
	movz x3, #6, lsl #0
	add x4, x21, #0
	bl {vg_keccak_pad_scratch}
	add x0, x19, #0
	movz x1, #72, lsl #0
	movz x2, #0, lsl #0
	add x3, x20, #0
	movz x4, #64, lsl #0
	add x5, x21, #0
	bl {vg_keccak_squeeze_scratch}
	ldr x30, [x21, #664]
	ldr x19, [x21, #640]
	ldr x20, [x21, #648]
	ldr x21, [x21, #656]
	add sp, sp, #672
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #688
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	add sp, sp, #688
	ret
	.p2align 6

vg_shake128_update:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
215:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 215b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake128_finalize:
	sub sp, sp, #640
	add x2, sp, #0
	add x4, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	movz x3, #31, lsl #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600}
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake128_squeeze:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #168, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
27:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 27b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake256_finalize:
	sub sp, sp, #640
	add x2, sp, #0
	add x4, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	str x30, [sp, #-16]!
	add x9, x0, x2
	ldrb w10, [x9, #0]
	eor x10, x10, x3
	strb w10, [x9, #0]
	add x9, x0, x1
	sub x9, x9, #1
	ldrb w10, [x9, #0]
	movz x11, #128, lsl #0
	eor x10, x10, x11
	strb w10, [x9, #0]
	add x1, x4, #0
	bl {vg_keccak_f1600}
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
20:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 20b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6

vg_shake256_squeeze:
	sub sp, sp, #640
	add x4, sp, #0
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	add x2, x1, #0
	movz x1, #136, lsl #0
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 20f
22:
	sub x9, x22, x21
	cbz x9, 23f
	b 24f
23:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600}
24:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 25f
	add x10, x19, x22
	ldrb w9, [x10, #0]
	strb w9, [x23, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	b 26f
25:
	add x10, x19, x22
	ldr x9, [x10, #0]
	str x9, [x23, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
26:
	cbnz x24, 22b
	b 21f
20:
21:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	add sp, sp, #640
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	sub sp, sp, #656
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #10, lsl #0
27:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 27b
	str q31, [x9, #0]
	add sp, sp, #656
	ret
	.p2align 6
