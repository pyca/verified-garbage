// The functions of `src/internal/vg_sm4_ctr32_sm4.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ctr32_sm4:
	sub sp, sp, #224
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #128]
	str x20, [x5, #136]
	str x21, [x5, #144]
	str x22, [x5, #152]
	str x23, [x5, #160]
	str x24, [x5, #168]
	str x25, [x5, #176]
	str x26, [x5, #184]
	str x27, [x5, #192]
	str x28, [x5, #200]
	ldr x6, [x1, #0]
	rev x6, x6
	ldr x7, [x1, #8]
	rev x7, x7
	str x6, [x5, #208]
	str x7, [x5, #216]
	add w10, w7, w3
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x10
	rev x6, x6
	rev x7, x7
	str x7, [x1, #8]
	str x6, [x1, #0]
	add x23, x2, #0
	add x24, x3, #0
	cbz x24, 20f
22:
	ldr x6, [x5, #208]
	ldr x7, [x5, #216]
	movz x9, #1, lsl #0
	rev x8, x6
	str x8, [x5, #0]
	rev x8, x7
	str x8, [x5, #8]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #16]
	rev x8, x7
	str x8, [x5, #24]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #32]
	rev x8, x7
	str x8, [x5, #40]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #48]
	rev x8, x7
	str x8, [x5, #56]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #64]
	rev x8, x7
	str x8, [x5, #72]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #80]
	rev x8, x7
	str x8, [x5, #88]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #96]
	rev x8, x7
	str x8, [x5, #104]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	rev x8, x6
	str x8, [x5, #112]
	rev x8, x7
	str x8, [x5, #120]
	add w8, w7, w9
	lsr x7, x7, #32
	lsl x7, x7, #32
	add x7, x7, x8
	str x6, [x5, #208]
	str x7, [x5, #216]
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	ldr q0, [x5, #0]
	ldr q1, [x5, #16]
	ldr q2, [x5, #32]
	ldr q3, [x5, #48]
	ldr q4, [x5, #64]
	ldr q5, [x5, #80]
	ldr q6, [x5, #96]
	ldr q7, [x5, #112]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	rev32 v2.16b, v2.16b
	rev32 v3.16b, v3.16b
	rev32 v4.16b, v4.16b
	rev32 v5.16b, v5.16b
	rev32 v6.16b, v6.16b
	rev32 v7.16b, v7.16b
	sm4e v0.4s, v16.4s
	sm4e v1.4s, v16.4s
	sm4e v2.4s, v16.4s
	sm4e v3.4s, v16.4s
	sm4e v4.4s, v16.4s
	sm4e v5.4s, v16.4s
	sm4e v6.4s, v16.4s
	sm4e v7.4s, v16.4s
	sm4e v0.4s, v17.4s
	sm4e v1.4s, v17.4s
	sm4e v2.4s, v17.4s
	sm4e v3.4s, v17.4s
	sm4e v4.4s, v17.4s
	sm4e v5.4s, v17.4s
	sm4e v6.4s, v17.4s
	sm4e v7.4s, v17.4s
	sm4e v0.4s, v18.4s
	sm4e v1.4s, v18.4s
	sm4e v2.4s, v18.4s
	sm4e v3.4s, v18.4s
	sm4e v4.4s, v18.4s
	sm4e v5.4s, v18.4s
	sm4e v6.4s, v18.4s
	sm4e v7.4s, v18.4s
	sm4e v0.4s, v19.4s
	sm4e v1.4s, v19.4s
	sm4e v2.4s, v19.4s
	sm4e v3.4s, v19.4s
	sm4e v4.4s, v19.4s
	sm4e v5.4s, v19.4s
	sm4e v6.4s, v19.4s
	sm4e v7.4s, v19.4s
	sm4e v0.4s, v20.4s
	sm4e v1.4s, v20.4s
	sm4e v2.4s, v20.4s
	sm4e v3.4s, v20.4s
	sm4e v4.4s, v20.4s
	sm4e v5.4s, v20.4s
	sm4e v6.4s, v20.4s
	sm4e v7.4s, v20.4s
	sm4e v0.4s, v21.4s
	sm4e v1.4s, v21.4s
	sm4e v2.4s, v21.4s
	sm4e v3.4s, v21.4s
	sm4e v4.4s, v21.4s
	sm4e v5.4s, v21.4s
	sm4e v6.4s, v21.4s
	sm4e v7.4s, v21.4s
	sm4e v0.4s, v22.4s
	sm4e v1.4s, v22.4s
	sm4e v2.4s, v22.4s
	sm4e v3.4s, v22.4s
	sm4e v4.4s, v22.4s
	sm4e v5.4s, v22.4s
	sm4e v6.4s, v22.4s
	sm4e v7.4s, v22.4s
	sm4e v0.4s, v23.4s
	sm4e v1.4s, v23.4s
	sm4e v2.4s, v23.4s
	sm4e v3.4s, v23.4s
	sm4e v4.4s, v23.4s
	sm4e v5.4s, v23.4s
	sm4e v6.4s, v23.4s
	sm4e v7.4s, v23.4s
	rev64 v0.16b, v0.16b
	ext v0.16b, v0.16b, v0.16b, #8
	rev64 v1.16b, v1.16b
	ext v1.16b, v1.16b, v1.16b, #8
	rev64 v2.16b, v2.16b
	ext v2.16b, v2.16b, v2.16b, #8
	rev64 v3.16b, v3.16b
	ext v3.16b, v3.16b, v3.16b, #8
	rev64 v4.16b, v4.16b
	ext v4.16b, v4.16b, v4.16b, #8
	rev64 v5.16b, v5.16b
	ext v5.16b, v5.16b, v5.16b, #8
	rev64 v6.16b, v6.16b
	ext v6.16b, v6.16b, v6.16b, #8
	rev64 v7.16b, v7.16b
	ext v7.16b, v7.16b, v7.16b, #8
	str q0, [x5, #0]
	str q1, [x5, #16]
	str q2, [x5, #32]
	str q3, [x5, #48]
	str q4, [x5, #64]
	str q5, [x5, #80]
	str q6, [x5, #96]
	str q7, [x5, #112]
	lsr x13, x24, #3
	cbnz x13, 23f
	add x16, x24, #0
	b 24f
23:
	movz x16, #8, lsl #0
24:
	add x14, x5, #0
	add x14, x14, #0
	add x15, x23, #0
	add x17, x16, #0
25:
	ldr x8, [x14, #0]
	ldr x9, [x15, #0]
	eor x8, x8, x9
	str x8, [x15, #0]
	ldr x8, [x14, #8]
	ldr x9, [x15, #8]
	eor x8, x8, x9
	str x8, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 25b
	add x23, x15, #0
	sub x24, x24, x16
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x19, [x5, #128]
	ldr x20, [x5, #136]
	ldr x21, [x5, #144]
	ldr x22, [x5, #152]
	ldr x23, [x5, #160]
	ldr x24, [x5, #168]
	ldr x25, [x5, #176]
	ldr x26, [x5, #184]
	ldr x27, [x5, #192]
	ldr x28, [x5, #200]
	movz x17, #0, lsl #0
	add x16, sp, #0
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
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	add sp, sp, #224
	ret
	.p2align 6
