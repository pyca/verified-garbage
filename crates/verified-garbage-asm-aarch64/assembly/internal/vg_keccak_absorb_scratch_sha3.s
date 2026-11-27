// The functions of `src/internal/vg_keccak_absorb_scratch_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_absorb_scratch_sha3:
	str x30, [sp, #-16]!
	str x19, [x5, #512]
	str x20, [x5, #520]
	str x21, [x5, #528]
	str x22, [x5, #536]
	str x23, [x5, #544]
	str x24, [x5, #552]
	add x19, x0, #0
	add x20, x5, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x3, #0
	add x24, x4, #0
	cbnz x22, 20f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 22f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 23f
22:
23:
	b 21f
20:
21:
	cbz x24, 24f
26:
	movz x10, #7, lsl #0
	and x10, x22, x10
	sub x11, x24, #8
	lsr x11, x11, #63
	orr x10, x10, x11
	cbz x10, 27f
	ldrb w9, [x23, #0]
	add x10, x19, x22
	ldrb w11, [x10, #0]
	eor x9, x9, x11
	strb w9, [x10, #0]
	add x23, x23, #1
	add x22, x22, #1
	sub x24, x24, #1
	sub x9, x22, x21
	b 28f
27:
	ldr x9, [x23, #0]
	add x10, x19, x22
	ldr x11, [x10, #0]
	eor x9, x9, x11
	str x9, [x10, #0]
	add x23, x23, #8
	add x22, x22, #8
	sub x24, x24, #8
	sub x9, x22, x21
28:
	cbz x9, 29f
	b 210f
29:
	movz x22, #0, lsl #0
	add x0, x19, #0
	add x1, x20, #0
	bl {vg_keccak_f1600_sha3}
210:
	cbnz x22, 211f
	sub x9, x24, x21
	lsr x9, x9, #63
	cbnz x9, 213f
	add x0, x19, #0
	add x1, x21, #0
	add x2, x23, #0
	add x3, x24, #0
	add x4, x20, #0
	bl {vg_keccak_absorb_blocks_sha3}
	sub x9, x24, x0
	add x23, x23, x9
	add x24, x0, #0
	b 214f
213:
214:
	b 212f
211:
212:
	cbnz x24, 26b
	b 25f
24:
25:
	add x0, x22, #0
	ldr x19, [x20, #512]
	ldr x21, [x20, #528]
	ldr x22, [x20, #536]
	ldr x23, [x20, #544]
	ldr x24, [x20, #552]
	ldr x20, [x20, #520]
	ldr x30, [sp], #16
	ret
	.p2align 6
