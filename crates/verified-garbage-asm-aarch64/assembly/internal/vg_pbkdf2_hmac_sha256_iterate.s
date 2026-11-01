// The functions of `src/internal/vg_pbkdf2_hmac_sha256_iterate.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha256_iterate:
	add w2, w2, #0
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x23, [x4, #144]
	str x24, [x4, #152]
	str x30, [x4, #160]
	add x19, x4, #168
	add x20, x4, #0
	add x21, x4, #200
	add x23, x3, #0
	add x24, x2, #0
	ldr w9, [x1, #0]
	str w9, [x21, #0]
	ldr w9, [x1, #4]
	str w9, [x21, #4]
	ldr w9, [x1, #8]
	str w9, [x21, #8]
	ldr w9, [x1, #12]
	str w9, [x21, #12]
	ldr w9, [x1, #16]
	str w9, [x21, #16]
	ldr w9, [x1, #20]
	str w9, [x21, #20]
	ldr w9, [x1, #24]
	str w9, [x21, #24]
	ldr w9, [x1, #28]
	str w9, [x21, #28]
	movz x9, #128, lsl #0
	str w9, [x21, #32]
	movz x9, #0, lsl #0
	str w9, [x21, #36]
	str w9, [x21, #40]
	str w9, [x21, #44]
	str w9, [x21, #48]
	str w9, [x21, #52]
	movz x22, #96, lsl #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #88]
	add x22, x0, #0
	cbz x24, 20f
22:
	ldr w9, [x22, #0]
	str w9, [x19, #0]
	ldr w9, [x22, #4]
	str w9, [x19, #4]
	ldr w9, [x22, #8]
	str w9, [x19, #8]
	ldr w9, [x22, #12]
	str w9, [x19, #12]
	ldr w9, [x22, #16]
	str w9, [x19, #16]
	ldr w9, [x22, #20]
	str w9, [x19, #20]
	ldr w9, [x22, #24]
	str w9, [x19, #24]
	ldr w9, [x22, #28]
	str w9, [x19, #28]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha256_compress}
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	ldr w9, [x22, #96]
	str w9, [x19, #0]
	ldr w9, [x22, #100]
	str w9, [x19, #4]
	ldr w9, [x22, #104]
	str w9, [x19, #8]
	ldr w9, [x22, #108]
	str w9, [x19, #12]
	ldr w9, [x22, #112]
	str w9, [x19, #16]
	ldr w9, [x22, #116]
	str w9, [x19, #20]
	ldr w9, [x22, #120]
	str w9, [x19, #24]
	ldr w9, [x22, #124]
	str w9, [x19, #28]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha256_compress}
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	ldr w9, [x21, #0]
	ldr w10, [x23, #0]
	eor x9, x9, x10
	str w9, [x23, #0]
	ldr w9, [x21, #4]
	ldr w10, [x23, #4]
	eor x9, x9, x10
	str w9, [x23, #4]
	ldr w9, [x21, #8]
	ldr w10, [x23, #8]
	eor x9, x9, x10
	str w9, [x23, #8]
	ldr w9, [x21, #12]
	ldr w10, [x23, #12]
	eor x9, x9, x10
	str w9, [x23, #12]
	ldr w9, [x21, #16]
	ldr w10, [x23, #16]
	eor x9, x9, x10
	str w9, [x23, #16]
	ldr w9, [x21, #20]
	ldr w10, [x23, #20]
	eor x9, x9, x10
	str w9, [x23, #20]
	ldr w9, [x21, #24]
	ldr w10, [x23, #24]
	eor x9, x9, x10
	str w9, [x23, #24]
	ldr w9, [x21, #28]
	ldr w10, [x23, #28]
	eor x9, x9, x10
	str w9, [x23, #28]
	sub x24, x24, #1
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x30, [x20, #160]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ret
	.p2align 6
