// The functions of `src/internal/vg_slhdsa_shake_thash4_n16.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_slhdsa_shake_thash4_n16:
	str x19, [x4, #936]
	str x20, [x4, #944]
	str x21, [x4, #952]
	str x22, [x4, #960]
	str x23, [x4, #968]
	str x24, [x4, #976]
	str x25, [x4, #984]
	str x26, [x4, #992]
	str x27, [x4, #1000]
	add x19, x4, #0
	add x20, x0, #0
	add x21, x20, x1
	add x22, x21, x1
	add x23, x22, x1
	movz x24, #0, lsl #0
	add x25, x2, #0
	add x26, x19, #0
	movz x27, #17, lsl #0
	movi v16.2d, #0
	str q16, [x19, #0]
	str q16, [x19, #16]
	str q16, [x19, #32]
	str q16, [x19, #48]
	str q16, [x19, #64]
	str q16, [x19, #80]
	str q16, [x19, #96]
	str q16, [x19, #112]
	str q16, [x19, #128]
	str q16, [x19, #144]
	str q16, [x19, #160]
	str q16, [x19, #176]
	str q16, [x19, #192]
	str q16, [x19, #208]
	str q16, [x19, #224]
	str q16, [x19, #240]
	str q16, [x19, #256]
	str q16, [x19, #272]
	str q16, [x19, #288]
	str q16, [x19, #304]
	str q16, [x19, #320]
	str q16, [x19, #336]
	str q16, [x19, #352]
	str q16, [x19, #368]
	str q16, [x19, #384]
	str q16, [x19, #400]
	str q16, [x19, #416]
	str q16, [x19, #432]
	str q16, [x19, #448]
	str q16, [x19, #464]
	str q16, [x19, #480]
	str q16, [x19, #496]
	str q16, [x19, #512]
	str q16, [x19, #528]
	str q16, [x19, #544]
	str q16, [x19, #560]
	str q16, [x19, #576]
	str q16, [x19, #592]
	str q16, [x19, #608]
	str q16, [x19, #624]
	str q16, [x19, #640]
	str q16, [x19, #656]
	str q16, [x19, #672]
	str q16, [x19, #688]
	str q16, [x19, #704]
	str q16, [x19, #720]
	str q16, [x19, #736]
	str q16, [x19, #752]
	str q16, [x19, #768]
	str q16, [x19, #784]
20:
	add x9, x20, x24
	ldr x9, [x9, #0]
	add x10, x21, x24
	ldr x10, [x10, #0]
	ldp x11, x12, [x26, #0]
	eor x11, x11, x9
	eor x12, x12, x10
	stp x11, x12, [x26, #0]
	add x9, x22, x24
	ldr x9, [x9, #0]
	add x10, x23, x24
	ldr x10, [x10, #0]
	ldp x11, x12, [x26, #400]
	eor x11, x11, x9
	eor x12, x12, x10
	stp x11, x12, [x26, #400]
	add x24, x24, #8
	add x26, x26, #16
	sub x25, x25, #8
	sub x27, x27, #1
	cbz x27, 21f
	b 22f
21:
	add x1, x19, #400
	add x1, x1, #400
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2}
	ldr x30, [x19, #928]
	add x9, x19, #400
	add x1, x19, #400
	add x1, x1, #400
	str x30, [x1, #128]
	add x0, x9, #0
	bl {vg_keccak_f1600_x2}
	ldr x30, [x19, #928]
	add x26, x19, #0
	movz x27, #17, lsl #0
22:
	cbnz x25, 20b
	movz x10, #31, lsl #0
	ldr x9, [x26, #0]
	eor x9, x9, x10
	str x9, [x26, #0]
	ldr x9, [x26, #8]
	eor x9, x9, x10
	str x9, [x26, #8]
	ldr x9, [x26, #400]
	eor x9, x9, x10
	str x9, [x26, #400]
	ldr x9, [x26, #408]
	eor x9, x9, x10
	str x9, [x26, #408]
	movz x10, #32768, lsl #48
	ldr x9, [x19, #256]
	eor x9, x9, x10
	str x9, [x19, #256]
	ldr x9, [x19, #264]
	eor x9, x9, x10
	str x9, [x19, #264]
	ldr x9, [x19, #656]
	eor x9, x9, x10
	str x9, [x19, #656]
	ldr x9, [x19, #664]
	eor x9, x9, x10
	str x9, [x19, #664]
	add x1, x19, #400
	add x1, x1, #400
	str x30, [x1, #128]
	add x0, x19, #0
	bl {vg_keccak_f1600_x2}
	ldr x30, [x19, #928]
	add x9, x19, #400
	add x1, x19, #400
	add x1, x1, #400
	str x30, [x1, #128]
	add x0, x9, #0
	bl {vg_keccak_f1600_x2}
	ldr x30, [x19, #928]
	ldp x9, x10, [x19, #0]
	str x9, [x20, #48]
	str x10, [x21, #48]
	ldp x9, x10, [x19, #16]
	str x9, [x20, #56]
	str x10, [x21, #56]
	ldp x9, x10, [x19, #400]
	str x9, [x22, #48]
	str x10, [x23, #48]
	ldp x9, x10, [x19, #416]
	str x9, [x22, #56]
	str x10, [x23, #56]
	ldr x20, [x19, #944]
	ldr x21, [x19, #952]
	ldr x22, [x19, #960]
	ldr x23, [x19, #968]
	ldr x24, [x19, #976]
	ldr x25, [x19, #984]
	ldr x26, [x19, #992]
	ldr x27, [x19, #1000]
	ldr x19, [x19, #936]
	ret
	.p2align 6
