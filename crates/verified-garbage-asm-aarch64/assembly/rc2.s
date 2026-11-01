// The functions of `src/rc2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	sub sp, sp, #576
	add x6, sp, #0
	sub x8, x1, #1
	lsr x8, x8, #7
	cbnz x8, 20f
	sub x8, x2, #1
	lsr x8, x8, #10
	cbnz x8, 22f
	sub x8, x4, #8
	cbnz x8, 24f
	str x30, [sp, #-16]!
	ldr x8, [x3, #0]
	str x8, [x5, #128]
	add x3, x5, #0
	add x4, x6, #0
	bl {vg_rc2_expand_key}
	movz x0, #0, lsl #0
	ldr x30, [sp], #16
	b 25f
24:
	movz x0, #3, lsl #0
25:
	b 23f
22:
	movz x0, #2, lsl #0
23:
	b 21f
20:
	movz x0, #1, lsl #0
21:
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
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #576
	ret
	.p2align 6

vg_rc2_cbc_encrypt_update:
	sub sp, sp, #576
	add x6, sp, #0
	cbz x5, 20f
	str x30, [sp, #-16]!
	add x10, x0, #0
	add x11, x4, #0
	add x12, x1, #0
	cbz x12, 22f
24:
	ldrb w9, [x10, #136]
	strb w9, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 24b
	b 23f
22:
23:
	sub x12, x5, x1
	cbz x12, 25f
27:
	ldrb w9, [x2, #0]
	strb w9, [x11, #0]
	add x2, x2, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 27b
	b 26f
25:
26:
	add x3, x3, x1
	sub x3, x3, x5
	add x10, x0, #0
	cbz x3, 28f
210:
	ldrb w9, [x2, #0]
	strb w9, [x10, #136]
	add x2, x2, #1
	add x10, x10, #1
	sub x3, x3, #1
	cbnz x3, 210b
	b 29f
28:
29:
	add x1, x0, #128
	add x2, x4, #0
	lsr x3, x5, #3
	add x4, x6, #0
	bl {vg_rc2_cbc_encrypt}
	ldr x30, [sp], #16
	b 21f
20:
	add x8, x0, x1
	cbz x3, 211f
213:
	ldrb w9, [x2, #0]
	strb w9, [x8, #136]
	add x2, x2, #1
	add x8, x8, #1
	sub x3, x3, #1
	cbnz x3, 213b
	b 212f
211:
212:
21:
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
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #576
	ret
	.p2align 6

vg_rc2_cbc_decrypt_update:
	sub sp, sp, #576
	add x6, sp, #0
	cbz x5, 20f
	str x30, [sp, #-16]!
	add x10, x0, #0
	add x11, x4, #0
	add x12, x1, #0
	cbz x12, 22f
24:
	ldrb w9, [x10, #136]
	strb w9, [x11, #0]
	add x10, x10, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 24b
	b 23f
22:
23:
	sub x12, x5, x1
	cbz x12, 25f
27:
	ldrb w9, [x2, #0]
	strb w9, [x11, #0]
	add x2, x2, #1
	add x11, x11, #1
	sub x12, x12, #1
	cbnz x12, 27b
	b 26f
25:
26:
	add x3, x3, x1
	sub x3, x3, x5
	add x10, x0, #0
	cbz x3, 28f
210:
	ldrb w9, [x2, #0]
	strb w9, [x10, #136]
	add x2, x2, #1
	add x10, x10, #1
	sub x3, x3, #1
	cbnz x3, 210b
	b 29f
28:
29:
	add x1, x0, #128
	add x2, x4, #0
	lsr x3, x5, #3
	add x4, x6, #0
	bl {vg_rc2_cbc_decrypt}
	ldr x30, [sp], #16
	b 21f
20:
	add x8, x0, x1
	cbz x3, 211f
213:
	ldrb w9, [x2, #0]
	strb w9, [x8, #136]
	add x2, x2, #1
	add x8, x8, #1
	sub x3, x3, #1
	cbnz x3, 213b
	b 212f
211:
212:
21:
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
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #576
	ret
	.p2align 6

vg_rc2_cbc_encrypt:
	str x23, [x4, #264]
	str x24, [x4, #272]
	str x30, [x4, #280]
	add x23, x1, #0
	add x24, x3, #0
	add x1, x2, #0
	add x2, x4, #0
	cbz x24, 20f
22:
	ldr x8, [x1, #0]
	ldr x9, [x23, #0]
	eor x8, x8, x9
	str x8, [x1, #0]
	bl {vg_rc2_encrypt_block}
	ldr x8, [x1, #0]
	str x8, [x23, #0]
	add x1, x1, #8
	sub x24, x24, #1
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x23, [x2, #264]
	ldr x24, [x2, #272]
	ldr x30, [x2, #280]
	ret
	.p2align 6

vg_rc2_cbc_decrypt:
	str x23, [x4, #264]
	str x24, [x4, #272]
	str x30, [x4, #280]
	add x23, x1, #0
	add x24, x3, #0
	add x1, x2, #0
	add x2, x4, #0
	lsr x10, x24, #3
	cbz x10, 20f
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x9, #65535, lsl #0
	dup v6.4s, w9
	ldr x11, [x23, #0]
22:
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q2, [x1, #32]
	ldr q3, [x1, #48]
	movz x6, #256, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #2312, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #4368, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #6424, lsl #32
	movk x7, #65535, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v24.16b, {v0.16b, v1.16b}, v4.16b
	tbl v28.16b, {v2.16b, v3.16b}, v4.16b
	movz x6, #770, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #2826, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #4882, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #6938, lsl #32
	movk x7, #65535, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v25.16b, {v0.16b, v1.16b}, v4.16b
	tbl v29.16b, {v2.16b, v3.16b}, v4.16b
	movz x6, #1284, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #5396, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #7452, lsl #32
	movk x7, #65535, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v26.16b, {v0.16b, v1.16b}, v4.16b
	tbl v30.16b, {v2.16b, v3.16b}, v4.16b
	movz x6, #1798, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #3854, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #5910, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #7966, lsl #32
	movk x7, #65535, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v27.16b, {v0.16b, v1.16b}, v4.16b
	tbl v31.16b, {v2.16b, v3.16b}, v4.16b
	dup v7.4s, v23.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v26.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v27.4s, v27.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v30.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v31.4s, v31.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v25.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v26.4s, v26.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v29.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v30.4s, v30.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v24.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v25.4s, v25.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v28.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v29.4s, v29.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v27.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v24.4s, v24.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v31.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v28.4s, v28.4s, v0.4s
	dup v7.4s, v21.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v26.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v27.4s, v27.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v30.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v31.4s, v31.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v25.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v26.4s, v26.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v29.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v30.4s, v30.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v24.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v25.4s, v25.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v28.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v29.4s, v29.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v27.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v24.4s, v24.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v31.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v28.4s, v28.4s, v0.4s
	dup v7.4s, v18.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	movz x6, #256, lsl #0
	movk x6, #4368, lsl #16
	movk x6, #8480, lsl #32
	movk x6, #12592, lsl #48
	movz x7, #1284, lsl #0
	movk x7, #5396, lsl #16
	movk x7, #9508, lsl #32
	movk x7, #13620, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v0.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v4.16b
	tbl v2.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v4.16b
	movz x6, #2312, lsl #0
	movk x6, #6424, lsl #16
	movk x6, #10536, lsl #32
	movk x6, #14648, lsl #48
	movz x7, #3340, lsl #0
	movk x7, #7452, lsl #16
	movk x7, #11564, lsl #32
	movk x7, #15676, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v1.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v4.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v4.16b
	ldr x9, [x1, #0]
	mov v4.d[0], x11
	mov v4.d[1], x9
	add x12, x1, #8
	ldr q5, [x12, #0]
	eor v0.16b, v0.16b, v4.16b
	eor v1.16b, v1.16b, v5.16b
	ldr q4, [x12, #16]
	ldr q5, [x12, #32]
	eor v2.16b, v2.16b, v4.16b
	eor v3.16b, v3.16b, v5.16b
	ldr x11, [x1, #56]
	str q0, [x1, #0]
	str q1, [x1, #16]
	str q2, [x1, #32]
	str q3, [x1, #48]
	add x1, x1, #64
	sub x10, x10, #1
	cbnz x10, 22b
	str x11, [x23, #0]
	b 21f
20:
21:
	lsl x24, x24, #61
	lsr x24, x24, #61
	cbz x24, 23f
25:
	ldr x8, [x1, #0]
	str x8, [x2, #256]
	bl {vg_rc2_decrypt_block}
	ldr x8, [x1, #0]
	ldr x9, [x23, #0]
	eor x8, x8, x9
	str x8, [x1, #0]
	ldr x8, [x2, #256]
	str x8, [x23, #0]
	add x1, x1, #8
	sub x24, x24, #1
	cbnz x24, 25b
	b 24f
23:
24:
	ldr x23, [x2, #264]
	ldr x24, [x2, #272]
	ldr x30, [x2, #280]
	ret
	.p2align 6

vg_rc2_expand_key:
	str x23, [x4, #0]
	str x24, [x4, #8]
	str x19, [x4, #16]
	str x20, [x4, #24]
	str x21, [x4, #32]
	str x22, [x4, #40]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x22, x2, #0
	movz x23, #0, lsl #0
20:
	add x9, x19, x23
	ldrb w8, [x9, #0]
	add x9, x21, x23
	strb w8, [x9, #0]
	add x23, x23, #1
	sub x10, x23, x20
	cbnz x10, 20b
	sub x10, x23, #128
	cbnz x10, 21f
	b 22f
21:
23:
	add x9, x21, x23
	sub x9, x9, #1
	ldrb w8, [x9, #0]
	sub x5, x23, x20
	add x9, x21, x5
	ldrb w3, [x9, #0]
	add x8, x8, x3
	movz x6, #30937, lsl #0
	movk x6, #50425, lsl #16
	movk x6, #56601, lsl #32
	movk x6, #60853, lsl #48
	movz x7, #59688, lsl #0
	movk x7, #31229, lsl #16
	movk x7, #41034, lsl #32
	movk x7, #40408, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #32454, lsl #0
	movk x6, #33591, lsl #16
	movk x6, #30251, lsl #32
	movk x6, #36435, lsl #48
	movz x7, #19554, lsl #0
	movk x7, #34916, lsl #16
	movk x7, #35652, lsl #32
	movk x7, #41723, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #39447, lsl #0
	movk x6, #62809, lsl #16
	movk x6, #45959, lsl #32
	movk x6, #4943, lsl #48
	movz x7, #17761, lsl #0
	movk x7, #36205, lsl #16
	movk x7, #33033, lsl #32
	movk x7, #12925, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #36797, lsl #0
	movk x6, #60224, lsl #16
	movk x6, #46982, lsl #32
	movk x6, #2939, lsl #48
	movz x7, #38384, lsl #0
	movk x7, #8737, lsl #16
	movk x7, #27484, lsl #32
	movk x7, #33358, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #54868, lsl #0
	movk x6, #37733, lsl #16
	movk x6, #24782, lsl #32
	movk x6, #7346, lsl #48
	movz x7, #22131, lsl #0
	movk x7, #5312, lsl #16
	movk x7, #36007, lsl #32
	movk x7, #56561, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #29970, lsl #0
	movk x6, #8138, lsl #16
	movk x6, #48699, lsl #32
	movk x6, #53732, lsl #48
	movz x7, #15682, lsl #0
	movk x7, #12500, lsl #16
	movk x7, #15523, lsl #32
	movk x7, #9910, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #49007, lsl #0
	movk x6, #55822, lsl #16
	movk x6, #26950, lsl #32
	movk x6, #22279, lsl #48
	movz x7, #61991, lsl #0
	movk x7, #39709, lsl #16
	movk x7, #38076, lsl #32
	movk x7, #835, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #4600, lsl #0
	movk x6, #63175, lsl #16
	movk x6, #61328, lsl #32
	movk x6, #59198, lsl #48
	movz x7, #49926, lsl #0
	movk x7, #12245, lsl #16
	movk x7, #26312, lsl #32
	movk x7, #55070, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #59400, lsl #0
	movk x6, #57066, lsl #16
	movk x6, #21120, lsl #32
	movk x6, #63470, lsl #48
	movz x7, #43652, lsl #0
	movk x7, #44146, lsl #16
	movk x7, #19765, lsl #32
	movk x7, #10858, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #6806, lsl #0
	movk x6, #29138, lsl #16
	movk x6, #5466, lsl #32
	movk x6, #29769, lsl #48
	movz x7, #40779, lsl #0
	movk x7, #24272, lsl #16
	movk x7, #6148, lsl #32
	movk x7, #60580, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #57538, lsl #0
	movk x6, #28225, lsl #16
	movk x6, #20751, lsl #32
	movk x6, #52427, lsl #48
	movz x7, #37156, lsl #0
	movk x7, #20655, lsl #16
	movk x7, #62625, lsl #32
	movk x7, #14704, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #31897, lsl #0
	movk x6, #34106, lsl #16
	movk x6, #47139, lsl #32
	movk x6, #31412, lsl #48
	movz x7, #764, lsl #0
	movk x7, #23350, lsl #16
	movk x7, #21797, lsl #32
	movk x7, #12695, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #23853, lsl #0
	movk x6, #39162, lsl #16
	movk x6, #35555, lsl #32
	movk x6, #44690, lsl #48
	movz x7, #57093, lsl #0
	movk x7, #4137, lsl #16
	movk x7, #27751, lsl #32
	movk x7, #51642, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #211, lsl #0
	movk x6, #53222, lsl #16
	movk x6, #40673, lsl #32
	movk x6, #11432, lsl #48
	movz x7, #5731, lsl #0
	movk x7, #16129, lsl #16
	movk x7, #57944, lsl #32
	movk x7, #43401, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14349, lsl #0
	movk x6, #6964, lsl #16
	movk x6, #13227, lsl #32
	movk x6, #45311, lsl #48
	movz x7, #18619, lsl #0
	movk x7, #24332, lsl #16
	movk x7, #45497, lsl #32
	movk x7, #11981, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #62405, lsl #0
	movk x6, #18395, lsl #16
	movk x6, #42469, lsl #32
	movk x6, #30620, lsl #48
	movz x7, #42506, lsl #0
	movk x7, #26656, lsl #16
	movk x7, #32766, lsl #32
	movk x7, #44481, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	dup v0.16b, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	movz x6, #128, lsl #0
	dup v5.16b, w6
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov w8, v0.s[0]
	lsl x8, x8, #56
	lsr x8, x8, #56
	add x9, x21, x23
	strb w8, [x9, #0]
	add x23, x23, #1
	sub x10, x23, #128
	cbnz x10, 23b
22:
	add x24, x22, #7
	lsr x24, x24, #3
	movz x23, #128, lsl #0
	sub x23, x23, x24
	add x5, x22, #0
	lsl x5, x5, #61
	lsr x5, x5, #61
	movz x2, #255, lsl #0
	sub x10, x5, #1
	cbz x10, 24f
	b 25f
24:
	movz x2, #1, lsl #0
25:
	sub x10, x5, #2
	cbz x10, 26f
	b 27f
26:
	movz x2, #3, lsl #0
27:
	sub x10, x5, #3
	cbz x10, 28f
	b 29f
28:
	movz x2, #7, lsl #0
29:
	sub x10, x5, #4
	cbz x10, 210f
	b 211f
210:
	movz x2, #15, lsl #0
211:
	sub x10, x5, #5
	cbz x10, 212f
	b 213f
212:
	movz x2, #31, lsl #0
213:
	sub x10, x5, #6
	cbz x10, 214f
	b 215f
214:
	movz x2, #63, lsl #0
215:
	sub x10, x5, #7
	cbz x10, 216f
	b 217f
216:
	movz x2, #127, lsl #0
217:
	add x9, x21, x23
	ldrb w8, [x9, #0]
	and x8, x8, x2
	movz x6, #30937, lsl #0
	movk x6, #50425, lsl #16
	movk x6, #56601, lsl #32
	movk x6, #60853, lsl #48
	movz x7, #59688, lsl #0
	movk x7, #31229, lsl #16
	movk x7, #41034, lsl #32
	movk x7, #40408, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #32454, lsl #0
	movk x6, #33591, lsl #16
	movk x6, #30251, lsl #32
	movk x6, #36435, lsl #48
	movz x7, #19554, lsl #0
	movk x7, #34916, lsl #16
	movk x7, #35652, lsl #32
	movk x7, #41723, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #39447, lsl #0
	movk x6, #62809, lsl #16
	movk x6, #45959, lsl #32
	movk x6, #4943, lsl #48
	movz x7, #17761, lsl #0
	movk x7, #36205, lsl #16
	movk x7, #33033, lsl #32
	movk x7, #12925, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #36797, lsl #0
	movk x6, #60224, lsl #16
	movk x6, #46982, lsl #32
	movk x6, #2939, lsl #48
	movz x7, #38384, lsl #0
	movk x7, #8737, lsl #16
	movk x7, #27484, lsl #32
	movk x7, #33358, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #54868, lsl #0
	movk x6, #37733, lsl #16
	movk x6, #24782, lsl #32
	movk x6, #7346, lsl #48
	movz x7, #22131, lsl #0
	movk x7, #5312, lsl #16
	movk x7, #36007, lsl #32
	movk x7, #56561, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #29970, lsl #0
	movk x6, #8138, lsl #16
	movk x6, #48699, lsl #32
	movk x6, #53732, lsl #48
	movz x7, #15682, lsl #0
	movk x7, #12500, lsl #16
	movk x7, #15523, lsl #32
	movk x7, #9910, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #49007, lsl #0
	movk x6, #55822, lsl #16
	movk x6, #26950, lsl #32
	movk x6, #22279, lsl #48
	movz x7, #61991, lsl #0
	movk x7, #39709, lsl #16
	movk x7, #38076, lsl #32
	movk x7, #835, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #4600, lsl #0
	movk x6, #63175, lsl #16
	movk x6, #61328, lsl #32
	movk x6, #59198, lsl #48
	movz x7, #49926, lsl #0
	movk x7, #12245, lsl #16
	movk x7, #26312, lsl #32
	movk x7, #55070, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #59400, lsl #0
	movk x6, #57066, lsl #16
	movk x6, #21120, lsl #32
	movk x6, #63470, lsl #48
	movz x7, #43652, lsl #0
	movk x7, #44146, lsl #16
	movk x7, #19765, lsl #32
	movk x7, #10858, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #6806, lsl #0
	movk x6, #29138, lsl #16
	movk x6, #5466, lsl #32
	movk x6, #29769, lsl #48
	movz x7, #40779, lsl #0
	movk x7, #24272, lsl #16
	movk x7, #6148, lsl #32
	movk x7, #60580, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #57538, lsl #0
	movk x6, #28225, lsl #16
	movk x6, #20751, lsl #32
	movk x6, #52427, lsl #48
	movz x7, #37156, lsl #0
	movk x7, #20655, lsl #16
	movk x7, #62625, lsl #32
	movk x7, #14704, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #31897, lsl #0
	movk x6, #34106, lsl #16
	movk x6, #47139, lsl #32
	movk x6, #31412, lsl #48
	movz x7, #764, lsl #0
	movk x7, #23350, lsl #16
	movk x7, #21797, lsl #32
	movk x7, #12695, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #23853, lsl #0
	movk x6, #39162, lsl #16
	movk x6, #35555, lsl #32
	movk x6, #44690, lsl #48
	movz x7, #57093, lsl #0
	movk x7, #4137, lsl #16
	movk x7, #27751, lsl #32
	movk x7, #51642, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #211, lsl #0
	movk x6, #53222, lsl #16
	movk x6, #40673, lsl #32
	movk x6, #11432, lsl #48
	movz x7, #5731, lsl #0
	movk x7, #16129, lsl #16
	movk x7, #57944, lsl #32
	movk x7, #43401, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14349, lsl #0
	movk x6, #6964, lsl #16
	movk x6, #13227, lsl #32
	movk x6, #45311, lsl #48
	movz x7, #18619, lsl #0
	movk x7, #24332, lsl #16
	movk x7, #45497, lsl #32
	movk x7, #11981, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #62405, lsl #0
	movk x6, #18395, lsl #16
	movk x6, #42469, lsl #32
	movk x6, #30620, lsl #48
	movz x7, #42506, lsl #0
	movk x7, #26656, lsl #16
	movk x7, #32766, lsl #32
	movk x7, #44481, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	dup v0.16b, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	movz x6, #128, lsl #0
	dup v5.16b, w6
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov w8, v0.s[0]
	lsl x8, x8, #56
	lsr x8, x8, #56
	add x9, x21, x23
	strb w8, [x9, #0]
	add x10, x23, #0
	cbnz x10, 218f
	b 219f
218:
220:
	sub x23, x23, #1
	add x9, x21, x23
	add x9, x9, #1
	ldrb w8, [x9, #0]
	add x5, x23, x24
	add x9, x21, x5
	ldrb w3, [x9, #0]
	eor x8, x8, x3
	movz x6, #30937, lsl #0
	movk x6, #50425, lsl #16
	movk x6, #56601, lsl #32
	movk x6, #60853, lsl #48
	movz x7, #59688, lsl #0
	movk x7, #31229, lsl #16
	movk x7, #41034, lsl #32
	movk x7, #40408, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #32454, lsl #0
	movk x6, #33591, lsl #16
	movk x6, #30251, lsl #32
	movk x6, #36435, lsl #48
	movz x7, #19554, lsl #0
	movk x7, #34916, lsl #16
	movk x7, #35652, lsl #32
	movk x7, #41723, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #39447, lsl #0
	movk x6, #62809, lsl #16
	movk x6, #45959, lsl #32
	movk x6, #4943, lsl #48
	movz x7, #17761, lsl #0
	movk x7, #36205, lsl #16
	movk x7, #33033, lsl #32
	movk x7, #12925, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #36797, lsl #0
	movk x6, #60224, lsl #16
	movk x6, #46982, lsl #32
	movk x6, #2939, lsl #48
	movz x7, #38384, lsl #0
	movk x7, #8737, lsl #16
	movk x7, #27484, lsl #32
	movk x7, #33358, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #54868, lsl #0
	movk x6, #37733, lsl #16
	movk x6, #24782, lsl #32
	movk x6, #7346, lsl #48
	movz x7, #22131, lsl #0
	movk x7, #5312, lsl #16
	movk x7, #36007, lsl #32
	movk x7, #56561, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #29970, lsl #0
	movk x6, #8138, lsl #16
	movk x6, #48699, lsl #32
	movk x6, #53732, lsl #48
	movz x7, #15682, lsl #0
	movk x7, #12500, lsl #16
	movk x7, #15523, lsl #32
	movk x7, #9910, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #49007, lsl #0
	movk x6, #55822, lsl #16
	movk x6, #26950, lsl #32
	movk x6, #22279, lsl #48
	movz x7, #61991, lsl #0
	movk x7, #39709, lsl #16
	movk x7, #38076, lsl #32
	movk x7, #835, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #4600, lsl #0
	movk x6, #63175, lsl #16
	movk x6, #61328, lsl #32
	movk x6, #59198, lsl #48
	movz x7, #49926, lsl #0
	movk x7, #12245, lsl #16
	movk x7, #26312, lsl #32
	movk x7, #55070, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #59400, lsl #0
	movk x6, #57066, lsl #16
	movk x6, #21120, lsl #32
	movk x6, #63470, lsl #48
	movz x7, #43652, lsl #0
	movk x7, #44146, lsl #16
	movk x7, #19765, lsl #32
	movk x7, #10858, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #6806, lsl #0
	movk x6, #29138, lsl #16
	movk x6, #5466, lsl #32
	movk x6, #29769, lsl #48
	movz x7, #40779, lsl #0
	movk x7, #24272, lsl #16
	movk x7, #6148, lsl #32
	movk x7, #60580, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #57538, lsl #0
	movk x6, #28225, lsl #16
	movk x6, #20751, lsl #32
	movk x6, #52427, lsl #48
	movz x7, #37156, lsl #0
	movk x7, #20655, lsl #16
	movk x7, #62625, lsl #32
	movk x7, #14704, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #31897, lsl #0
	movk x6, #34106, lsl #16
	movk x6, #47139, lsl #32
	movk x6, #31412, lsl #48
	movz x7, #764, lsl #0
	movk x7, #23350, lsl #16
	movk x7, #21797, lsl #32
	movk x7, #12695, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #23853, lsl #0
	movk x6, #39162, lsl #16
	movk x6, #35555, lsl #32
	movk x6, #44690, lsl #48
	movz x7, #57093, lsl #0
	movk x7, #4137, lsl #16
	movk x7, #27751, lsl #32
	movk x7, #51642, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #211, lsl #0
	movk x6, #53222, lsl #16
	movk x6, #40673, lsl #32
	movk x6, #11432, lsl #48
	movz x7, #5731, lsl #0
	movk x7, #16129, lsl #16
	movk x7, #57944, lsl #32
	movk x7, #43401, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14349, lsl #0
	movk x6, #6964, lsl #16
	movk x6, #13227, lsl #32
	movk x6, #45311, lsl #48
	movz x7, #18619, lsl #0
	movk x7, #24332, lsl #16
	movk x7, #45497, lsl #32
	movk x7, #11981, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #62405, lsl #0
	movk x6, #18395, lsl #16
	movk x6, #42469, lsl #32
	movk x6, #30620, lsl #48
	movz x7, #42506, lsl #0
	movk x7, #26656, lsl #16
	movk x7, #32766, lsl #32
	movk x7, #44481, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	dup v0.16b, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	movz x6, #128, lsl #0
	dup v5.16b, w6
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov w8, v0.s[0]
	lsl x8, x8, #56
	lsr x8, x8, #56
	add x9, x21, x23
	strb w8, [x9, #0]
	add x10, x23, #0
	cbnz x10, 220b
219:
	ldr x23, [x4, #0]
	ldr x24, [x4, #8]
	ldr x19, [x4, #16]
	ldr x20, [x4, #24]
	ldr x21, [x4, #32]
	ldr x22, [x4, #40]
	ret
	.p2align 6

vg_rc2_encrypt_block:
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	movz x9, #65535, lsl #0
	ldr x8, [x1, #0]
	add x19, x8, #0
	lsr x19, x19, #0
	lsl x19, x19, #48
	lsr x19, x19, #48
	add x20, x8, #0
	lsr x20, x20, #16
	lsl x20, x20, #48
	lsr x20, x20, #48
	add x21, x8, #0
	lsr x21, x21, #32
	lsl x21, x21, #48
	lsr x21, x21, #48
	add x22, x8, #0
	lsr x22, x22, #48
	lsl x22, x22, #48
	lsr x22, x22, #48
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #0]
	ldrb w5, [x0, #1]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #2]
	ldrb w5, [x0, #3]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #4]
	ldrb w5, [x0, #5]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #6]
	ldrb w5, [x0, #7]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #8]
	ldrb w5, [x0, #9]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #10]
	ldrb w5, [x0, #11]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #12]
	ldrb w5, [x0, #13]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #14]
	ldrb w5, [x0, #15]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #16]
	ldrb w5, [x0, #17]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #18]
	ldrb w5, [x0, #19]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #20]
	ldrb w5, [x0, #21]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #22]
	ldrb w5, [x0, #23]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #24]
	ldrb w5, [x0, #25]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #26]
	ldrb w5, [x0, #27]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #28]
	ldrb w5, [x0, #29]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #30]
	ldrb w5, [x0, #31]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #32]
	ldrb w5, [x0, #33]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #34]
	ldrb w5, [x0, #35]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #36]
	ldrb w5, [x0, #37]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #38]
	ldrb w5, [x0, #39]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	add x8, x22, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	add x19, x19, x8
	and x19, x19, x9
	add x8, x19, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	add x20, x20, x8
	and x20, x20, x9
	add x8, x20, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	add x21, x21, x8
	and x21, x21, x9
	add x8, x21, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	add x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #40]
	ldrb w5, [x0, #41]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #42]
	ldrb w5, [x0, #43]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #44]
	ldrb w5, [x0, #45]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #46]
	ldrb w5, [x0, #47]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #48]
	ldrb w5, [x0, #49]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #50]
	ldrb w5, [x0, #51]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #52]
	ldrb w5, [x0, #53]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #54]
	ldrb w5, [x0, #55]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #56]
	ldrb w5, [x0, #57]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #58]
	ldrb w5, [x0, #59]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #60]
	ldrb w5, [x0, #61]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #62]
	ldrb w5, [x0, #63]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #64]
	ldrb w5, [x0, #65]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #66]
	ldrb w5, [x0, #67]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #68]
	ldrb w5, [x0, #69]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #70]
	ldrb w5, [x0, #71]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #72]
	ldrb w5, [x0, #73]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #74]
	ldrb w5, [x0, #75]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #76]
	ldrb w5, [x0, #77]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #78]
	ldrb w5, [x0, #79]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #80]
	ldrb w5, [x0, #81]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #82]
	ldrb w5, [x0, #83]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #84]
	ldrb w5, [x0, #85]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #86]
	ldrb w5, [x0, #87]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	add x8, x22, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	add x19, x19, x8
	and x19, x19, x9
	add x8, x19, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	add x20, x20, x8
	and x20, x20, x9
	add x8, x20, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	add x21, x21, x8
	and x21, x21, x9
	add x8, x21, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	add x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #88]
	ldrb w5, [x0, #89]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #90]
	ldrb w5, [x0, #91]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #92]
	ldrb w5, [x0, #93]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #94]
	ldrb w5, [x0, #95]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #96]
	ldrb w5, [x0, #97]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #98]
	ldrb w5, [x0, #99]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #100]
	ldrb w5, [x0, #101]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #102]
	ldrb w5, [x0, #103]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #104]
	ldrb w5, [x0, #105]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #106]
	ldrb w5, [x0, #107]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #108]
	ldrb w5, [x0, #109]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #110]
	ldrb w5, [x0, #111]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #112]
	ldrb w5, [x0, #113]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #114]
	ldrb w5, [x0, #115]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #116]
	ldrb w5, [x0, #117]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #118]
	ldrb w5, [x0, #119]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #120]
	ldrb w5, [x0, #121]
	ror x5, x5, #56
	orr x4, x4, x5
	add x19, x19, x4
	add x19, x19, x6
	add x19, x19, x7
	and x19, x19, x9
	lsl x8, x19, #1
	lsr x19, x19, #15
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #122]
	ldrb w5, [x0, #123]
	ror x5, x5, #56
	orr x4, x4, x5
	add x20, x20, x4
	add x20, x20, x6
	add x20, x20, x7
	and x20, x20, x9
	lsl x8, x20, #2
	lsr x20, x20, #14
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #124]
	ldrb w5, [x0, #125]
	ror x5, x5, #56
	orr x4, x4, x5
	add x21, x21, x4
	add x21, x21, x6
	add x21, x21, x7
	and x21, x21, x9
	lsl x8, x21, #3
	lsr x21, x21, #13
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #126]
	ldrb w5, [x0, #127]
	ror x5, x5, #56
	orr x4, x4, x5
	add x22, x22, x4
	add x22, x22, x6
	add x22, x22, x7
	and x22, x22, x9
	lsl x8, x22, #5
	lsr x22, x22, #11
	orr x22, x22, x8
	and x22, x22, x9
	add x8, x19, #0
	ror x3, x20, #48
	orr x8, x8, x3
	ror x3, x21, #32
	orr x8, x8, x3
	ror x3, x22, #16
	orr x8, x8, x3
	str x8, [x1, #0]
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ret
	.p2align 6

vg_rc2_decrypt_block:
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	movz x9, #65535, lsl #0
	ldr x8, [x1, #0]
	add x19, x8, #0
	lsr x19, x19, #0
	lsl x19, x19, #48
	lsr x19, x19, #48
	add x20, x8, #0
	lsr x20, x20, #16
	lsl x20, x20, #48
	lsr x20, x20, #48
	add x21, x8, #0
	lsr x21, x21, #32
	lsl x21, x21, #48
	lsr x21, x21, #48
	add x22, x8, #0
	lsr x22, x22, #48
	lsl x22, x22, #48
	lsr x22, x22, #48
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #126]
	ldrb w5, [x0, #127]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #124]
	ldrb w5, [x0, #125]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #122]
	ldrb w5, [x0, #123]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #120]
	ldrb w5, [x0, #121]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #118]
	ldrb w5, [x0, #119]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #116]
	ldrb w5, [x0, #117]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #114]
	ldrb w5, [x0, #115]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #112]
	ldrb w5, [x0, #113]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #110]
	ldrb w5, [x0, #111]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #108]
	ldrb w5, [x0, #109]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #106]
	ldrb w5, [x0, #107]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #104]
	ldrb w5, [x0, #105]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #102]
	ldrb w5, [x0, #103]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #100]
	ldrb w5, [x0, #101]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #98]
	ldrb w5, [x0, #99]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #96]
	ldrb w5, [x0, #97]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #94]
	ldrb w5, [x0, #95]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #92]
	ldrb w5, [x0, #93]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #90]
	ldrb w5, [x0, #91]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #88]
	ldrb w5, [x0, #89]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	add x8, x21, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x22, x22, x8
	and x22, x22, x9
	add x8, x20, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x21, x21, x8
	and x21, x21, x9
	add x8, x19, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x20, x20, x8
	and x20, x20, x9
	add x8, x22, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x19, x19, x8
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #86]
	ldrb w5, [x0, #87]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #84]
	ldrb w5, [x0, #85]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #82]
	ldrb w5, [x0, #83]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #80]
	ldrb w5, [x0, #81]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #78]
	ldrb w5, [x0, #79]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #76]
	ldrb w5, [x0, #77]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #74]
	ldrb w5, [x0, #75]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #72]
	ldrb w5, [x0, #73]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #70]
	ldrb w5, [x0, #71]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #68]
	ldrb w5, [x0, #69]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #66]
	ldrb w5, [x0, #67]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #64]
	ldrb w5, [x0, #65]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #62]
	ldrb w5, [x0, #63]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #60]
	ldrb w5, [x0, #61]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #58]
	ldrb w5, [x0, #59]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #56]
	ldrb w5, [x0, #57]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #54]
	ldrb w5, [x0, #55]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #52]
	ldrb w5, [x0, #53]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #50]
	ldrb w5, [x0, #51]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #48]
	ldrb w5, [x0, #49]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #46]
	ldrb w5, [x0, #47]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #44]
	ldrb w5, [x0, #45]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #42]
	ldrb w5, [x0, #43]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #40]
	ldrb w5, [x0, #41]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	add x8, x21, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x22, x22, x8
	and x22, x22, x9
	add x8, x20, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x21, x21, x8
	and x21, x21, x9
	add x8, x19, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x20, x20, x8
	and x20, x20, x9
	add x8, x22, #0
	lsl x8, x8, #58
	lsr x8, x8, #58
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x3, #514, lsl #0
	movz x6, #256, lsl #0
	madd x8, x8, x3, x6
	dup v0.4s, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	umov w8, v0.s[0]
	lsl x8, x8, #48
	lsr x8, x8, #48
	sub x19, x19, x8
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #38]
	ldrb w5, [x0, #39]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #36]
	ldrb w5, [x0, #37]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #34]
	ldrb w5, [x0, #35]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #32]
	ldrb w5, [x0, #33]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #30]
	ldrb w5, [x0, #31]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #28]
	ldrb w5, [x0, #29]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #26]
	ldrb w5, [x0, #27]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #24]
	ldrb w5, [x0, #25]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #22]
	ldrb w5, [x0, #23]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #20]
	ldrb w5, [x0, #21]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #18]
	ldrb w5, [x0, #19]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #16]
	ldrb w5, [x0, #17]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #14]
	ldrb w5, [x0, #15]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #12]
	ldrb w5, [x0, #13]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #10]
	ldrb w5, [x0, #11]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #8]
	ldrb w5, [x0, #9]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	lsl x8, x22, #11
	lsr x22, x22, #5
	orr x22, x22, x8
	and x22, x22, x9
	and x6, x21, x20
	bic x7, x19, x21, ror #0
	ldrb w4, [x0, #6]
	ldrb w5, [x0, #7]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x22, x22, x4
	sub x22, x22, x6
	sub x22, x22, x7
	and x22, x22, x9
	lsl x8, x21, #13
	lsr x21, x21, #3
	orr x21, x21, x8
	and x21, x21, x9
	and x6, x20, x19
	bic x7, x22, x20, ror #0
	ldrb w4, [x0, #4]
	ldrb w5, [x0, #5]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x21, x21, x4
	sub x21, x21, x6
	sub x21, x21, x7
	and x21, x21, x9
	lsl x8, x20, #14
	lsr x20, x20, #2
	orr x20, x20, x8
	and x20, x20, x9
	and x6, x19, x22
	bic x7, x21, x19, ror #0
	ldrb w4, [x0, #2]
	ldrb w5, [x0, #3]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x20, x20, x4
	sub x20, x20, x6
	sub x20, x20, x7
	and x20, x20, x9
	lsl x8, x19, #15
	lsr x19, x19, #1
	orr x19, x19, x8
	and x19, x19, x9
	and x6, x22, x21
	bic x7, x20, x22, ror #0
	ldrb w4, [x0, #0]
	ldrb w5, [x0, #1]
	ror x5, x5, #56
	orr x4, x4, x5
	sub x19, x19, x4
	sub x19, x19, x6
	sub x19, x19, x7
	and x19, x19, x9
	add x8, x19, #0
	ror x3, x20, #48
	orr x8, x8, x3
	ror x3, x21, #32
	orr x8, x8, x3
	ror x3, x22, #16
	orr x8, x8, x3
	str x8, [x1, #0]
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ret
	.p2align 6
