// The functions of `src/internal/vg_camellia_ctr_core.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ctr_core:
	sub sp, sp, #3344
	add x5, sp, #0
	add x5, x5, #0
	str x19, [x5, #3248]
	str x20, [x5, #3256]
	str x21, [x5, #3264]
	str x22, [x5, #3272]
	str x23, [x5, #3280]
	str x24, [x5, #3288]
	str x25, [x5, #3296]
	str x26, [x5, #3304]
	str x27, [x5, #3312]
	str x28, [x5, #3320]
	ldr x6, [x2, #0]
	rev x6, x6
	ldr x7, [x2, #8]
	rev x7, x7
	str x6, [x5, #3328]
	str x7, [x5, #3336]
	movz x10, #0, lsl #0
	adds x7, x7, x4
	adc x6, x6, x10
	rev x6, x6
	rev x7, x7
	str x7, [x2, #8]
	str x6, [x2, #0]
	add x23, x3, #0
	add x24, x4, #0
	dup v28.2d, x30
	dup v27.2d, x5
	dup v29.2d, x23
	dup v30.2d, x24
	dup v26.2d, x1
	movz x2, #0, lsl #0
	add x3, x5, #0
	movz x4, #406, lsl #0
	bl {vg_camellia_prepare_keys}
	umov x5, v27.d[0]
	umov x30, v28.d[0]
	umov x23, v29.d[0]
	umov x24, v30.d[0]
	umov x4, v26.d[0]
	cbz x24, 20f
22:
	ldr x6, [x5, #3328]
	ldr x7, [x5, #3336]
	movz x9, #1, lsl #0
	movz x10, #0, lsl #0
	rev x8, x6
	str x8, [x5, #3024]
	rev x8, x7
	str x8, [x5, #3032]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #3040]
	rev x8, x7
	str x8, [x5, #3048]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #3056]
	rev x8, x7
	str x8, [x5, #3064]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #3072]
	rev x8, x7
	str x8, [x5, #3080]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #3088]
	rev x8, x7
	str x8, [x5, #3096]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #3104]
	rev x8, x7
	str x8, [x5, #3112]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #3120]
	rev x8, x7
	str x8, [x5, #3128]
	adds x7, x7, x9
	adc x6, x6, x10
	rev x8, x6
	str x8, [x5, #3136]
	rev x8, x7
	str x8, [x5, #3144]
	adds x7, x7, x9
	adc x6, x6, x10
	str x6, [x5, #3328]
	str x7, [x5, #3336]
	dup v28.2d, x30
	dup v27.2d, x5
	dup v29.2d, x23
	dup v30.2d, x24
	dup v26.2d, x4
	add x0, x4, #0
	add x1, x5, #0
	movz x2, #406, lsl #0
	bl {vg_camellia_crypt_prepared}
	umov x5, v27.d[0]
	umov x30, v28.d[0]
	umov x23, v29.d[0]
	umov x24, v30.d[0]
	umov x4, v26.d[0]
	lsr x13, x24, #3
	cbnz x13, 23f
	add x16, x24, #0
	b 24f
23:
	movz x16, #8, lsl #0
24:
	add x14, x5, #0
	add x14, x14, #3024
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
	ldr x19, [x5, #3248]
	ldr x20, [x5, #3256]
	ldr x21, [x5, #3264]
	ldr x22, [x5, #3272]
	ldr x23, [x5, #3280]
	ldr x24, [x5, #3288]
	ldr x25, [x5, #3296]
	ldr x26, [x5, #3304]
	ldr x27, [x5, #3312]
	ldr x28, [x5, #3320]
	add sp, sp, #3344
	ret
	.p2align 6
