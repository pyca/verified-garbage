// The functions of `src/internal/vg_scrypt_romix.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_romix:
	str x19, [x4, #128]
	str x20, [x4, #136]
	str x22, [x4, #144]
	str x23, [x4, #152]
	str x24, [x4, #160]
	str x30, [x4, #168]
	str x21, [x4, #176]
	add x19, x0, #0
	add x20, x2, #0
	add x21, x4, #0
	lsl x22, x1, #7
	add x9, x1, #0
	movz x10, #1, lsl #0
	add x11, x3, x3
20:
	add x9, x9, x9
	add x10, x10, x10
	sub x12, x9, x11
	cbnz x12, 20b
	lsr x10, x10, #1
	str x10, [x21, #184]
	add x23, x10, #0
	add x24, x20, #0
21:
	add x9, x19, #0
	add x10, x24, #0
	lsr x11, x22, #3
22:
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	ldr q2, [x9, #32]
	ldr q3, [x9, #48]
	str q0, [x10, #0]
	str q1, [x10, #16]
	str q2, [x10, #32]
	str q3, [x10, #48]
	add x9, x9, #64
	add x10, x10, #64
	sub x11, x11, #8
	cbnz x11, 22b
	add x0, x24, #0
	lsr x1, x22, #7
	add x2, x19, #0
	add x3, x1, #0
	add x4, x21, #0
	bl {vg_scrypt_blockmix}
	add x24, x24, x22
	sub x23, x23, #1
	cbnz x23, 21b
	ldr x23, [x21, #184]
	sub x24, x23, #1
23:
	add x9, x19, x22
	sub x9, x9, #64
	ldr x9, [x9, #0]
	and x9, x9, x24
	madd x10, x9, x22, x20
	add x9, x19, #0
	add x11, x21, #192
	lsr x12, x22, #3
24:
	ldr q0, [x9, #0]
	ldr q1, [x9, #16]
	ldr q2, [x9, #32]
	ldr q3, [x9, #48]
	ldr q4, [x10, #0]
	ldr q5, [x10, #16]
	ldr q6, [x10, #32]
	ldr q7, [x10, #48]
	eor v0.16b, v0.16b, v4.16b
	eor v1.16b, v1.16b, v5.16b
	eor v2.16b, v2.16b, v6.16b
	eor v3.16b, v3.16b, v7.16b
	str q0, [x11, #0]
	str q1, [x11, #16]
	str q2, [x11, #32]
	str q3, [x11, #48]
	add x9, x9, #64
	add x10, x10, #64
	add x11, x11, #64
	sub x12, x12, #8
	cbnz x12, 24b
	add x0, x21, #192
	lsr x1, x22, #7
	add x2, x19, #0
	add x3, x1, #0
	add x4, x21, #0
	bl {vg_scrypt_blockmix}
	sub x23, x23, #1
	cbnz x23, 23b
	ldr x19, [x21, #128]
	ldr x20, [x21, #136]
	ldr x22, [x21, #144]
	ldr x23, [x21, #152]
	ldr x24, [x21, #160]
	ldr x30, [x21, #168]
	ldr x21, [x21, #176]
	ret
	.p2align 6
