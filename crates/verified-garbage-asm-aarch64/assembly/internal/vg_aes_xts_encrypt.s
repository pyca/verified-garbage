// The functions of `src/internal/vg_aes_xts_encrypt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_encrypt:
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
	ldr x9, [x21, #0]
	str x9, [x24, #2048]
	ldr x9, [x21, #8]
	str x9, [x24, #2056]
	add x14, x22, #0
	add x15, x23, #0
22:
	ldr x9, [x22, #0]
	ldr x10, [x21, #0]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x21, #8]
	eor x9, x9, x10
	str x9, [x22, #8]
	ldr x9, [x21, #0]
	ldr x10, [x21, #8]
	adds x9, x9, x9
	adcs x10, x10, x10
	movz x11, #135, lsl #0
	movz x12, #0, lsl #0
	csel x11, x11, x12, hs
	eor x9, x9, x11
	str x9, [x21, #0]
	str x10, [x21, #8]
	add x22, x22, #16
	sub x23, x23, #1
	cbnz x23, 22b
	add x22, x14, #0
	add x23, x15, #0
	ldr x9, [x24, #2048]
	str x9, [x21, #0]
	ldr x9, [x24, #2056]
	str x9, [x21, #8]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x22, #0
	add x3, x23, #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
23:
	ldr x9, [x22, #0]
	ldr x10, [x21, #0]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x21, #8]
	eor x9, x9, x10
	str x9, [x22, #8]
	ldr x9, [x21, #0]
	ldr x10, [x21, #8]
	adds x9, x9, x9
	adcs x10, x10, x10
	movz x11, #135, lsl #0
	movz x12, #0, lsl #0
	csel x11, x11, x12, hs
	eor x9, x9, x11
	str x9, [x21, #0]
	str x10, [x21, #8]
	add x22, x22, #16
	sub x23, x23, #1
	cbnz x23, 23b
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
