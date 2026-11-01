// The functions of `src/internal/vg_mldsa_expand_mask_poly_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_expand_mask_poly_sha3:
	.arch_extension sha3
	str x25, [x3, #2016]
	str x26, [x3, #2024]
	str x27, [x3, #2032]
	str x30, [x3, #2040]
	add x25, x3, #0
	add x26, x2, #0
	add w27, w1, #0
	add x3, x0, #0
	movz x4, #66, lsl #0
	movz x9, #0, lsl #0
	str x9, [x25, #0]
	str x9, [x25, #8]
	str x9, [x25, #16]
	str x9, [x25, #24]
	str x9, [x25, #32]
	str x9, [x25, #40]
	str x9, [x25, #48]
	str x9, [x25, #56]
	str x9, [x25, #64]
	str x9, [x25, #72]
	str x9, [x25, #80]
	str x9, [x25, #88]
	str x9, [x25, #96]
	str x9, [x25, #104]
	str x9, [x25, #112]
	str x9, [x25, #120]
	str x9, [x25, #128]
	str x9, [x25, #136]
	str x9, [x25, #144]
	str x9, [x25, #152]
	str x9, [x25, #160]
	str x9, [x25, #168]
	str x9, [x25, #176]
	str x9, [x25, #184]
	str x9, [x25, #192]
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x5, x25, #200
	bl {vg_keccak_absorb_scratch_sha3}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch_sha3}
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #640, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch_sha3}
	lsr x9, x27, #18
	cbz x9, 20f
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #15, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
22:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	ldrb w11, [x2, #9]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #20
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #40
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #60
	lsl x13, x7, #4
	add x12, x12, x13
	lsl x13, x11, #12
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #10
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 22b
	b 21f
20:
	add x2, x25, #840
	add x3, x26, #0
	movz x5, #64, lsl #0
	movz x8, #3, lsl #16
	movk x8, #65535, lsl #0
	movz x9, #57345, lsl #0
	movk x9, #127, lsl #16
23:
	ldr x6, [x2, #0]
	ldrb w7, [x2, #8]
	and x12, x6, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #0]
	lsr x12, x6, #18
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #4]
	lsr x12, x6, #36
	and x12, x12, x8
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #8]
	lsr x12, x6, #54
	lsl x13, x7, #10
	add x12, x12, x13
	sub x13, x27, x12
	lsr x14, x13, #63
	madd x13, x14, x9, x13
	str w13, [x3, #12]
	add x2, x2, #9
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 23b
21:
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	ret
	.arch_extension nosha3
	.p2align 6
