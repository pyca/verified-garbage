// The functions of `src/internal/vg_mldsa_sample_in_ball.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_sample_in_ball:
	str x25, [x4, #2016]
	str x26, [x4, #2024]
	str x27, [x4, #2032]
	str x30, [x4, #2040]
	add x25, x4, #0
	add x26, x3, #0
	add w27, w2, #0
	add x3, x0, #0
	add x4, x1, #0
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
	bl {vg_keccak_absorb_scratch}
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x3, #31, lsl #0
	add x4, x25, #200
	bl {vg_keccak_pad_scratch}
	add x0, x25, #0
	movz x1, #136, lsl #0
	movz x2, #0, lsl #0
	add x3, x25, #840
	movz x4, #272, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x26, #0
	movz x4, #256, lsl #0
20:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 20b
	ldr x9, [x25, #840]
	movz x10, #256, lsl #0
	sub x10, x10, x27
	add x11, x27, #0
	add x2, x25, #848
	movz x5, #264, lsl #0
	movz x12, #57345, lsl #0
	movk x12, #127, lsl #16
	sub x12, x12, #2
	movz x15, #1, lsl #0
21:
	cbz x11, 22f
	ldrb w6, [x2, #0]
	sub x7, x10, x6
	lsr x7, x7, #63
	cbnz x7, 24f
	lsl x8, x6, #2
	add x8, x26, x8
	lsl x13, x10, #2
	add x13, x26, x13
	ldr w14, [x8, #0]
	str w14, [x13, #0]
	and x14, x9, x15
	madd x14, x14, x12, x15
	str w14, [x8, #0]
	lsr x9, x9, #1
	add x10, x10, #1
	sub x11, x11, #1
	b 25f
24:
25:
	b 23f
22:
23:
	add x2, x2, #1
	sub x5, x5, #1
	cbnz x5, 21b
	lsr x0, x10, #8
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	ret
	.p2align 6
