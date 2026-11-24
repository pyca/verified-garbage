// The functions of `src/internal/vg_aes_gcm_seal_batches_aes_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_seal_batches_aes_sha3:
	ldr w10, [x20, #60]
	rev w10, w10
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	ldr q16, [x20, #16]
	rev64 v16.16b, v16.16b
	add x9, x23, #0
	lsr x11, x26, #7
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 20f
	cbz x14, 22f
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #192]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #208]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #224]
	ldr q31, [x15, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x15, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x15, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x15, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x15, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x15, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x15, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x15, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	sub x11, x11, #1
	cbz x11, 24f
26:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	ldr q0, [x20, #48]
	rev64 v21.16b, v21.16b
	mov v0.s[3], w12
	add w12, w10, #1
	ldr q22, [x9, #32]
	rev w12, w12
	ldr q1, [x20, #48]
	rev64 v22.16b, v22.16b
	mov v1.s[3], w12
	add w12, w10, #2
	ldr q23, [x19, #608]
	rev w12, w12
	ldr q2, [x20, #48]
	ldr q24, [x19, #592]
	mov v2.s[3], w12
	add w12, w10, #3
	ldr q25, [x19, #640]
	rev w12, w12
	ldr q3, [x20, #48]
	trn1 v26.2d, v21.2d, v22.2d
	mov v3.s[3], w12
	add w12, w10, #4
	trn2 v27.2d, v21.2d, v22.2d
	rev w12, w12
	ldr q4, [x20, #48]
	eor v26.16b, v26.16b, v27.16b
	mov v4.s[3], w12
	add w12, w10, #5
	pmull v28.1q, v21.1d, v23.1d
	rev w12, w12
	ldr q5, [x20, #48]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v5.s[3], w12
	add w12, w10, #6
	pmull v29.1q, v22.1d, v24.1d
	rev w12, w12
	ldr q6, [x20, #48]
	pmull2 v22.1q, v22.2d, v24.2d
	mov v6.s[3], w12
	add w12, w10, #7
	pmull v27.1q, v26.1d, v25.1d
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	pmull2 v26.1q, v26.2d, v25.2d
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v18.16b, v28.16b, v29.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v19.16b, v21.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v20.16b, v27.16b, v26.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #48]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #64]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v22.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q23, [x19, #576]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #560]
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #656]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v26.16b, v26.16b, v27.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #80]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v21.16b, v21.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q22, [x9, #96]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v22.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	ldr q23, [x19, #544]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q24, [x19, #528]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #672]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q21, [x9, #112]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v21.16b, v21.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	ldr q22, [x9, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	rev64 v22.16b, v22.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor v22.16b, v22.16b, v16.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q23, [x19, #512]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #624]
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #688]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v26.16b, v26.16b, v27.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #192]
	pmull v28.1q, v21.1d, v23.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #208]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q30, [x21, #224]
	ldr q31, [x15, #128]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x15, #144]
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x15, #160]
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x15, #176]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x15, #192]
	pmull v26.1q, v20.1d, v17.1d
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x15, #208]
	ext v18.16b, v18.16b, v18.16b, #8
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x15, #224]
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x15, #240]
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #128]
	str q1, [x9, #144]
	str q2, [x9, #160]
	str q3, [x9, #176]
	str q4, [x9, #192]
	str q5, [x9, #208]
	str q6, [x9, #224]
	str q7, [x9, #240]
	add x15, x15, #128
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 26b
	b 25f
24:
25:
	ldr q21, [x9, #16]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #32]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #608]
	ldr q24, [x19, #592]
	ldr q25, [x19, #640]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v28.16b, v29.16b
	eor v19.16b, v21.16b, v22.16b
	eor v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #48]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #64]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #656]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #80]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #96]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #672]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #0]
	rev64 v22.16b, v22.16b
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #512]
	ldr q24, [x19, #624]
	ldr q25, [x19, #688]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x15, x15, #128
	add x9, x9, #128
	b 23f
22:
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #192]
	ldr q31, [x15, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x15, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x15, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x15, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x15, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x15, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x15, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x15, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	sub x11, x11, #1
	cbz x11, 27f
29:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	rev64 v21.16b, v21.16b
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	ldr q22, [x9, #32]
	add w12, w10, #1
	rev w12, w12
	rev64 v22.16b, v22.16b
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	ldr q23, [x19, #608]
	add w12, w10, #2
	rev w12, w12
	ldr q24, [x19, #592]
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	ldr q25, [x19, #640]
	add w12, w10, #3
	rev w12, w12
	trn1 v26.2d, v21.2d, v22.2d
	ldr q3, [x20, #48]
	trn2 v27.2d, v21.2d, v22.2d
	mov v3.s[3], w12
	add w12, w10, #4
	eor v26.16b, v26.16b, v27.16b
	rev w12, w12
	ldr q4, [x20, #48]
	pmull v28.1q, v21.1d, v23.1d
	mov v4.s[3], w12
	add w12, w10, #5
	pmull2 v21.1q, v21.2d, v23.2d
	rev w12, w12
	ldr q5, [x20, #48]
	pmull v29.1q, v22.1d, v24.1d
	mov v5.s[3], w12
	add w12, w10, #6
	pmull2 v22.1q, v22.2d, v24.2d
	rev w12, w12
	ldr q6, [x20, #48]
	pmull v27.1q, v26.1d, v25.1d
	mov v6.s[3], w12
	pmull2 v26.1q, v26.2d, v25.2d
	add w12, w10, #7
	rev w12, w12
	eor v18.16b, v28.16b, v29.16b
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	eor v19.16b, v21.16b, v22.16b
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v20.16b, v27.16b, v26.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q21, [x9, #48]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	rev64 v21.16b, v21.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q22, [x9, #64]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #576]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q24, [x19, #560]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #656]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	pmull2 v22.1q, v22.2d, v24.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q21, [x9, #80]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v21.16b, v21.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #96]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #544]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q24, [x19, #528]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q25, [x19, #672]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	trn2 v27.2d, v21.2d, v22.2d
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v26.16b, v26.16b, v27.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #112]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v21.16b, v21.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q22, [x9, #0]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v22.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	eor v22.16b, v22.16b, v16.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q23, [x19, #512]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q24, [x19, #624]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #688]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x21, #176]
	pmull2 v22.1q, v22.2d, v24.2d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	ldr q30, [x21, #192]
	ldr q31, [x15, #128]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x15, #144]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q31, [x15, #160]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	ldr q31, [x15, #176]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q31, [x15, #192]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	pmull v26.1q, v20.1d, v17.1d
	ldr q31, [x15, #208]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ext v18.16b, v18.16b, v18.16b, #8
	ldr q31, [x15, #224]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x15, #240]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add w10, w10, #8
	str q0, [x9, #128]
	str q1, [x9, #144]
	str q2, [x9, #160]
	str q3, [x9, #176]
	str q4, [x9, #192]
	str q5, [x9, #208]
	str q6, [x9, #224]
	str q7, [x9, #240]
	add x15, x15, #128
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 29b
	b 28f
27:
28:
	ldr q21, [x9, #16]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #32]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #608]
	ldr q24, [x19, #592]
	ldr q25, [x19, #640]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v28.16b, v29.16b
	eor v19.16b, v21.16b, v22.16b
	eor v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #48]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #64]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #656]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #80]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #96]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #672]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #0]
	rev64 v22.16b, v22.16b
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #512]
	ldr q24, [x19, #624]
	ldr q25, [x19, #688]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x15, x15, #128
	add x9, x9, #128
23:
	b 21f
20:
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #160]
	ldr q31, [x15, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x15, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x15, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x15, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x15, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x15, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x15, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x15, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	sub x11, x11, #1
	cbz x11, 210f
212:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	rev64 v21.16b, v21.16b
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	ldr q22, [x9, #32]
	add w12, w10, #1
	rev64 v22.16b, v22.16b
	rev w12, w12
	ldr q1, [x20, #48]
	ldr q23, [x19, #608]
	mov v1.s[3], w12
	add w12, w10, #2
	ldr q24, [x19, #592]
	rev w12, w12
	ldr q25, [x19, #640]
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	trn1 v26.2d, v21.2d, v22.2d
	add w12, w10, #3
	rev w12, w12
	trn2 v27.2d, v21.2d, v22.2d
	ldr q3, [x20, #48]
	eor v26.16b, v26.16b, v27.16b
	mov v3.s[3], w12
	add w12, w10, #4
	pmull v28.1q, v21.1d, v23.1d
	rev w12, w12
	ldr q4, [x20, #48]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v4.s[3], w12
	pmull v29.1q, v22.1d, v24.1d
	add w12, w10, #5
	rev w12, w12
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	pmull v27.1q, v26.1d, v25.1d
	add w12, w10, #6
	pmull2 v26.1q, v26.2d, v25.2d
	rev w12, w12
	ldr q6, [x20, #48]
	eor v18.16b, v28.16b, v29.16b
	mov v6.s[3], w12
	add w12, w10, #7
	eor v19.16b, v21.16b, v22.16b
	rev w12, w12
	eor v20.16b, v27.16b, v26.16b
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q21, [x9, #48]
	ldr q30, [x21, #0]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #64]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v22.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q23, [x19, #576]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q24, [x19, #560]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	ldr q25, [x19, #656]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v26.16b, v26.16b, v27.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v21.1q, v21.2d, v23.2d
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q21, [x9, #80]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	rev64 v21.16b, v21.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #96]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #544]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q24, [x19, #528]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q25, [x19, #672]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	eor v26.16b, v26.16b, v27.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v27.1q, v26.1d, v25.1d
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #112]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #0]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v22.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v22.16b, v22.16b, v16.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q23, [x19, #512]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #624]
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #688]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor v26.16b, v26.16b, v27.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v28.1q, v21.1d, v23.1d
	ldr q30, [x21, #144]
	pmull2 v21.1q, v21.2d, v23.2d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v2.16b, v30.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v7.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	ldr q30, [x21, #160]
	ldr q31, [x15, #128]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x15, #144]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	pmull v26.1q, v19.1d, v17.1d
	ldr q31, [x15, #160]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q31, [x15, #176]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	ldr q31, [x15, #192]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x15, #208]
	pmull v26.1q, v20.1d, v17.1d
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x15, #224]
	ext v18.16b, v18.16b, v18.16b, #8
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x15, #240]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add w10, w10, #8
	str q0, [x9, #128]
	str q1, [x9, #144]
	str q2, [x9, #160]
	str q3, [x9, #176]
	str q4, [x9, #192]
	str q5, [x9, #208]
	str q6, [x9, #224]
	str q7, [x9, #240]
	add x15, x15, #128
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 212b
	b 211f
210:
211:
	ldr q21, [x9, #16]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #32]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #608]
	ldr q24, [x19, #592]
	ldr q25, [x19, #640]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v28.16b, v29.16b
	eor v19.16b, v21.16b, v22.16b
	eor v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #48]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #64]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #656]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #80]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #96]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #672]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #0]
	rev64 v22.16b, v22.16b
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #512]
	ldr q24, [x19, #624]
	ldr q25, [x19, #688]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x15, x15, #128
	add x9, x9, #128
21:
	rev64 v16.16b, v16.16b
	str q16, [x20, #16]
	rev w12, w10
	str w12, [x20, #60]
	ret
	.p2align 6
