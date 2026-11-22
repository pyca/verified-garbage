// The functions of `src/internal/vg_hmac_md5_init_any_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_init_any_scratch:
	str x19, [x4, #384]
	str x20, [x4, #392]
	str x21, [x4, #400]
	str x22, [x4, #408]
	str x24, [x4, #416]
	str x30, [x4, #424]
	str x23, [x4, #432]
	add x23, x4, #0
	add x19, x2, #0
	add x20, x3, #0
	add x21, x0, #0
	add x22, x1, #0
	lsr x9, x20, #6
	cbz x9, 20f
	sub x9, x20, #64
	cbz x9, 22f
	add x0, x23, #704
	bl {vg_md5_init}
	add x0, x23, #704
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_md5_update_scratch}
	add x0, x23, #704
	add x1, x20, #0
	add x2, x23, #816
	add x3, x23, #0
	bl {vg_md5_finalize_scratch}
	add x2, x23, #816
	movz x3, #16, lsl #0
	b 23f
22:
	add x2, x19, #0
	add x3, x20, #0
23:
	b 21f
20:
	add x2, x19, #0
	add x3, x20, #0
21:
	add x0, x21, #0
	add x1, x22, #0
	add x4, x23, #0
	bl {vg_hmac_md5_init_scratch}
	ldr x19, [x23, #384]
	ldr x20, [x23, #392]
	ldr x21, [x23, #400]
	ldr x22, [x23, #408]
	ldr x24, [x23, #416]
	ldr x30, [x23, #424]
	ldr x23, [x23, #432]
	ret
	.p2align 6
