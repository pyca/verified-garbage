// The functions of `src/internal/vg_mldsa_sample_in_ball_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_sample_in_ball_sha3:
	.arch_extension sha3
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
	movz x4, #136, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch_sha3}
	movi v0.2d, #0
	str q0, [x26, #0]
	str q0, [x26, #16]
	str q0, [x26, #32]
	str q0, [x26, #48]
	str q0, [x26, #64]
	str q0, [x26, #80]
	str q0, [x26, #96]
	str q0, [x26, #112]
	str q0, [x26, #128]
	str q0, [x26, #144]
	str q0, [x26, #160]
	str q0, [x26, #176]
	str q0, [x26, #192]
	str q0, [x26, #208]
	str q0, [x26, #224]
	str q0, [x26, #240]
	str q0, [x26, #256]
	str q0, [x26, #272]
	str q0, [x26, #288]
	str q0, [x26, #304]
	str q0, [x26, #320]
	str q0, [x26, #336]
	str q0, [x26, #352]
	str q0, [x26, #368]
	str q0, [x26, #384]
	str q0, [x26, #400]
	str q0, [x26, #416]
	str q0, [x26, #432]
	str q0, [x26, #448]
	str q0, [x26, #464]
	str q0, [x26, #480]
	str q0, [x26, #496]
	str q0, [x26, #512]
	str q0, [x26, #528]
	str q0, [x26, #544]
	str q0, [x26, #560]
	str q0, [x26, #576]
	str q0, [x26, #592]
	str q0, [x26, #608]
	str q0, [x26, #624]
	str q0, [x26, #640]
	str q0, [x26, #656]
	str q0, [x26, #672]
	str q0, [x26, #688]
	str q0, [x26, #704]
	str q0, [x26, #720]
	str q0, [x26, #736]
	str q0, [x26, #752]
	str q0, [x26, #768]
	str q0, [x26, #784]
	str q0, [x26, #800]
	str q0, [x26, #816]
	str q0, [x26, #832]
	str q0, [x26, #848]
	str q0, [x26, #864]
	str q0, [x26, #880]
	str q0, [x26, #896]
	str q0, [x26, #912]
	str q0, [x26, #928]
	str q0, [x26, #944]
	str q0, [x26, #960]
	str q0, [x26, #976]
	str q0, [x26, #992]
	str q0, [x26, #1008]
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
	movz x5, #128, lsl #0
	cbz x11, 20f
22:
	ldrb w6, [x2, #0]
	sub x7, x10, x6
	lsr x7, x7, #63
	cbnz x7, 23f
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
	b 24f
23:
24:
	add x2, x2, #1
	sub x5, x5, #1
	cbz x11, 25f
	b 26f
25:
	movz x5, #0, lsl #0
26:
	cbnz x5, 22b
	b 21f
20:
21:
	cbz x11, 27f
	str x9, [x25, #1800]
	str x10, [x25, #1808]
	str x11, [x25, #1816]
	add x2, x0, #0
	add x0, x25, #0
	movz x1, #136, lsl #0
	add x3, x25, #840
	movz x4, #136, lsl #0
	add x5, x25, #200
	bl {vg_keccak_squeeze_scratch_sha3}
	ldr x9, [x25, #1800]
	ldr x10, [x25, #1808]
	ldr x11, [x25, #1816]
	add x2, x25, #840
	movz x5, #136, lsl #0
	movz x12, #57345, lsl #0
	movk x12, #127, lsl #16
	sub x12, x12, #2
	movz x15, #1, lsl #0
	cbz x11, 29f
211:
	ldrb w6, [x2, #0]
	sub x7, x10, x6
	lsr x7, x7, #63
	cbnz x7, 212f
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
	b 213f
212:
213:
	add x2, x2, #1
	sub x5, x5, #1
	cbz x11, 214f
	b 215f
214:
	movz x5, #0, lsl #0
215:
	cbnz x5, 211b
	b 210f
29:
210:
	b 28f
27:
28:
	lsr x0, x10, #8
	ldr x30, [x25, #2040]
	ldr x26, [x25, #2024]
	ldr x27, [x25, #2032]
	ldr x25, [x25, #2016]
	ret
	.arch_extension nosha3
	.p2align 6
