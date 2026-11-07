// The functions of `src/internal/vg_cmac_aes_update_aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_update_aes:
	lsr x9, x4, #1
	cbnz x9, 20f
	str x19, [x5, #2064]
	str x20, [x5, #2072]
	str x21, [x5, #2080]
	str x22, [x5, #2088]
	str x23, [x5, #2096]
	str x30, [x5, #2104]
	str x24, [x5, #2112]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	cbz x23, 22f
24:
	ldr x9, [x21, #0]
	ldr x10, [x22, #0]
	eor x9, x9, x10
	str x9, [x24, #2048]
	ldr x9, [x21, #8]
	ldr x10, [x22, #8]
	eor x9, x9, x10
	str x9, [x24, #2056]
	movz x9, #0, lsl #0
	str x9, [x21, #0]
	str x9, [x21, #8]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x24, #2048
	add x3, x21, #0
	movz x4, #1, lsl #0
	add x5, x24, #0
	bl {vg_aes_ctr32_aes}
	add x22, x22, #16
	sub x23, x23, #1
	cbnz x23, 24b
	b 23f
22:
23:
	ldr x19, [x24, #2064]
	ldr x20, [x24, #2072]
	ldr x21, [x24, #2080]
	ldr x22, [x24, #2088]
	ldr x23, [x24, #2096]
	ldr x30, [x24, #2104]
	ldr x24, [x24, #2112]
21:
	ret
20:
	cbz x4, 25f
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	ldr q24, [x0, #128]
	ldr q25, [x0, #144]
	ldr q26, [x0, #160]
	ldr q27, [x0, #176]
	ldr q28, [x0, #192]
	lsl x9, x1, #4
	add x9, x0, x9
	ldr q30, [x9, #0]
	sub x9, x9, #16
	ldr q29, [x9, #0]
	sub x6, x1, #10
	sub x7, x1, #12
	ldr q0, [x2, #0]
	eor v31.16b, v16.16b, v30.16b
	eor v0.16b, v0.16b, v30.16b
	cbz x6, 27f
	cbz x7, 29f
211:
	ldr q1, [x3, #0]
	eor v1.16b, v1.16b, v31.16b
	aese v0.16b, v1.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v27.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v28.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v29.16b
	add x3, x3, #16
	sub x4, x4, #1
	cbnz x4, 211b
	b 210f
29:
212:
	ldr q1, [x3, #0]
	eor v1.16b, v1.16b, v31.16b
	aese v0.16b, v1.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v29.16b
	add x3, x3, #16
	sub x4, x4, #1
	cbnz x4, 212b
210:
	b 28f
27:
213:
	ldr q1, [x3, #0]
	eor v1.16b, v1.16b, v31.16b
	aese v0.16b, v1.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v29.16b
	add x3, x3, #16
	sub x4, x4, #1
	cbnz x4, 213b
28:
	eor v0.16b, v0.16b, v30.16b
	str q0, [x2, #0]
	b 26f
25:
26:
	b 21b
	.p2align 6
