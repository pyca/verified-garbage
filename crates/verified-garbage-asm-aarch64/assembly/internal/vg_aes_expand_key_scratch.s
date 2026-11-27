// The functions of `src/internal/vg_aes_expand_key_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch:
	adrp x6, {VG_AES_SBOX}
	add x6, x6, {VG_AES_SBOX}
	ldr q16, [x6, #0]
	ldr q17, [x6, #16]
	ldr q18, [x6, #32]
	ldr q19, [x6, #48]
	ldr q20, [x6, #64]
	ldr q21, [x6, #80]
	ldr q22, [x6, #96]
	ldr q23, [x6, #112]
	ldr q24, [x6, #128]
	ldr q25, [x6, #144]
	ldr q26, [x6, #160]
	ldr q27, [x6, #176]
	ldr q28, [x6, #192]
	ldr q29, [x6, #208]
	ldr q30, [x6, #224]
	ldr q31, [x6, #240]
	ldr q4, [x6, #256]
	ldr q5, [x6, #272]
	ldr q6, [x6, #288]
	ldr q7, [x6, #304]
	add x5, x3, #0
	str x19, [x5, #384]
	str x20, [x5, #392]
	str x21, [x5, #400]
	str x22, [x5, #408]
	str x23, [x5, #416]
	str x24, [x5, #424]
	str x25, [x5, #432]
	str x26, [x5, #440]
	str x27, [x5, #448]
	str x28, [x5, #456]
	add x4, x1, #0
20:
	ldr x6, [x0, #0]
	str x6, [x2, #0]
	add x0, x0, #8
	add x2, x2, #8
	sub x4, x4, #8
	cbnz x4, 20b
	lsr x6, x6, #32
	sub x0, x2, x1
	lsr x3, x1, #2
	movz x1, #0, lsl #0
	add x4, x3, x3
	add x4, x4, x3
	add x4, x4, #28
	movz x7, #1, lsl #0
	str x7, [x5, #472]
21:
	cbz x1, 22f
	sub x7, x1, #4
	sub x8, x3, #8
	orr x7, x7, x8
	cbz x7, 24f
	b 25f
24:
	mov v0.d[0], x6
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x6, v0.d[0]
25:
	b 23f
22:
	mov v0.d[0], x6
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x6, v0.d[0]
	ror w6, w6, #8
	ldr x7, [x5, #472]
	eor w6, w6, w7
	lsr x8, x7, #7
	movz x9, #27, lsl #0
	mul x8, x8, x9
	lsl x7, x7, #1
	eor x7, x7, x8
	movz x9, #255, lsl #0
	and x7, x7, x9
	str x7, [x5, #472]
23:
	ldr w7, [x0, #0]
	eor w6, w6, w7
	str w6, [x2, #0]
	add x0, x0, #4
	add x2, x2, #4
	add x1, x1, #1
	sub x7, x1, x3
	cbz x7, 26f
	b 27f
26:
	movz x1, #0, lsl #0
27:
	sub x4, x4, #1
	cbnz x4, 21b
	ldr x19, [x5, #384]
	ldr x20, [x5, #392]
	ldr x21, [x5, #400]
	ldr x22, [x5, #408]
	ldr x23, [x5, #416]
	ldr x24, [x5, #424]
	ldr x25, [x5, #432]
	ldr x26, [x5, #440]
	ldr x27, [x5, #448]
	ldr x28, [x5, #456]
	ret
	.p2align 6
