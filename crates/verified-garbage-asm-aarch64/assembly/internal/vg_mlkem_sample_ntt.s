// The functions of `src/internal/vg_mlkem_sample_ntt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sample_ntt:
	str x25, [x2, #1680]
	str x26, [x2, #1688]
	str x30, [x2, #1696]
	str x24, [x2, #1704]
	add x24, x0, #0
	add x25, x1, #0
	add x26, x2, #0
	movz x9, #0, lsl #0
	str x9, [x2, #840]
	str x9, [x2, #848]
	str x9, [x2, #856]
	str x9, [x2, #864]
	str x9, [x2, #872]
	str x9, [x2, #880]
	str x9, [x2, #888]
	str x9, [x2, #896]
	str x9, [x2, #904]
	str x9, [x2, #912]
	str x9, [x2, #920]
	str x9, [x2, #928]
	str x9, [x2, #936]
	str x9, [x2, #944]
	str x9, [x2, #952]
	str x9, [x2, #960]
	str x9, [x2, #968]
	str x9, [x2, #976]
	str x9, [x2, #984]
	str x9, [x2, #992]
	str x9, [x2, #1000]
	str x9, [x2, #1008]
	str x9, [x2, #1016]
	str x9, [x2, #1024]
	str x9, [x2, #1032]
	add x3, x0, #0
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	movz x4, #34, lsl #0
	add x5, x26, #1040
	bl {vg_keccak_absorb_scratch}
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #34, lsl #0
	movz x3, #31, lsl #0
	add x4, x26, #1040
	bl {vg_keccak_pad_scratch}
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x26, #0
	movz x4, #504, lsl #0
	add x5, x26, #1040
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x25, #0
	movz x4, #256, lsl #0
20:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 20b
	add x2, x26, #0
	add x3, x25, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
21:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 22f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 24f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 25f
24:
25:
	b 23f
22:
23:
	cbnz x5, 21b
	cbz x4, 26f
	add x0, x24, #0
	add x1, x25, #0
	add x2, x26, #0
	ldr x30, [x26, #1696]
	ldr x24, [x26, #1704]
	ldr x25, [x26, #1680]
	ldr x26, [x26, #1688]
	str x25, [x2, #1680]
	str x26, [x2, #1688]
	str x30, [x2, #1696]
	str x24, [x2, #1704]
	add x24, x0, #0
	add x25, x1, #0
	add x26, x2, #0
	movz x9, #0, lsl #0
	str x9, [x2, #840]
	str x9, [x2, #848]
	str x9, [x2, #856]
	str x9, [x2, #864]
	str x9, [x2, #872]
	str x9, [x2, #880]
	str x9, [x2, #888]
	str x9, [x2, #896]
	str x9, [x2, #904]
	str x9, [x2, #912]
	str x9, [x2, #920]
	str x9, [x2, #928]
	str x9, [x2, #936]
	str x9, [x2, #944]
	str x9, [x2, #952]
	str x9, [x2, #960]
	str x9, [x2, #968]
	str x9, [x2, #976]
	str x9, [x2, #984]
	str x9, [x2, #992]
	str x9, [x2, #1000]
	str x9, [x2, #1008]
	str x9, [x2, #1016]
	str x9, [x2, #1024]
	str x9, [x2, #1032]
	add x3, x0, #0
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	movz x4, #34, lsl #0
	add x5, x26, #1040
	bl {vg_keccak_absorb_scratch}
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #34, lsl #0
	movz x3, #31, lsl #0
	add x4, x26, #1040
	bl {vg_keccak_pad_scratch}
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x26, #0
	movz x4, #840, lsl #0
	add x5, x26, #1040
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x25, #0
	movz x4, #256, lsl #0
28:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 28b
	add x2, x26, #0
	add x3, x25, #0
	movz x4, #256, lsl #0
	movz x5, #280, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
	ldr x30, [x26, #1696]
	ldr x24, [x26, #1704]
	ldr x25, [x26, #1680]
	ldr x26, [x26, #1688]
29:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 210f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 212f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 213f
212:
213:
	b 211f
210:
211:
	cbnz x5, 29b
	cbz x4, 214f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 215f
214:
215:
	sub x0, x4, #1
	lsr x0, x0, #63
	b 27f
26:
	movz x0, #1, lsl #0
	ldr x30, [x26, #1696]
	ldr x24, [x26, #1704]
	ldr x25, [x26, #1680]
	ldr x26, [x26, #1688]
27:
	ret
	.p2align 6
