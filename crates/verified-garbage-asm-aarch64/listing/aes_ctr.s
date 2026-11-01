// The functions of `src/aes_ctr.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr_aes:
	.arch_extension aes
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
	cbz x23, 20f
22:
	ldr w9, [x21, #12]
	rev w9, w9
	movz x10, #1, lsl #32
	sub x10, x10, x9
	subs x11, x23, x10
	csel x10, x10, x23, hs
	str x10, [x24, #2048]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	add x3, x22, #0
	add x4, x10, #0
	add x5, x24, #0
	bl {vg_aes_ctr32_aes}
	ldr x9, [x24, #2048]
	sub x23, x23, x9
	lsl x9, x9, #4
	add x22, x22, x9
	ldr w9, [x21, #12]
	cbz w9, 23f
	b 24f
23:
	ldr x9, [x21, #8]
	rev x9, x9
	ldr x10, [x21, #0]
	rev x10, x10
	movz x11, #1, lsl #32
	movz x12, #0, lsl #0
	adds x9, x9, x11
	adc x10, x10, x12
	rev x9, x9
	rev x10, x10
	str x9, [x21, #8]
	str x10, [x21, #0]
24:
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x24, #2064]
	ldr x20, [x24, #2072]
	ldr x21, [x24, #2080]
	ldr x22, [x24, #2088]
	ldr x23, [x24, #2096]
	ldr x30, [x24, #2104]
	ldr x24, [x24, #2112]
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_ctr:
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
	cbz x23, 20f
22:
	ldr w9, [x21, #12]
	rev w9, w9
	movz x10, #1, lsl #32
	sub x10, x10, x9
	subs x11, x23, x10
	csel x10, x10, x23, hs
	str x10, [x24, #2048]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	add x3, x22, #0
	add x4, x10, #0
	add x5, x24, #0
	bl {vg_aes_ctr32}
	ldr x9, [x24, #2048]
	sub x23, x23, x9
	lsl x9, x9, #4
	add x22, x22, x9
	ldr w9, [x21, #12]
	cbz w9, 23f
	b 24f
23:
	ldr x9, [x21, #8]
	rev x9, x9
	ldr x10, [x21, #0]
	rev x10, x10
	movz x11, #1, lsl #32
	movz x12, #0, lsl #0
	adds x9, x9, x11
	adc x10, x10, x12
	rev x9, x9
	rev x10, x10
	str x9, [x21, #8]
	str x10, [x21, #0]
24:
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x24, #2064]
	ldr x20, [x24, #2072]
	ldr x21, [x24, #2080]
	ldr x22, [x24, #2088]
	ldr x23, [x24, #2096]
	ldr x30, [x24, #2104]
	ldr x24, [x24, #2112]
	ret
	.p2align 6
