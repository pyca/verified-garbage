// The functions of `src/internal/vg_hmac_sha224_init_any_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha224_init_any_scratch:
	str x19, [x4, #832]
	str x20, [x4, #840]
	str x21, [x4, #848]
	str x22, [x4, #856]
	str x24, [x4, #864]
	str x30, [x4, #872]
	str x23, [x4, #880]
	add x23, x4, #0
	add x19, x2, #0
	add x20, x3, #0
	add x21, x0, #0
	add x22, x1, #0
	lsr x9, x20, #6
	cbz x9, 20f
	sub x9, x20, #64
	cbz x9, 22f
	add x0, x23, #1200
	bl {vg_sha224_init}
	add x0, x23, #1200
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha256_update_scratch}
	add x0, x23, #1200
	add x1, x20, #0
	add x2, x23, #1352
	add x3, x23, #0
	bl {vg_sha256_finalize_scratch}
	add x2, x23, #1352
	movz x3, #28, lsl #0
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
	bl {vg_hmac_sha224_init_scratch}
	ldr x19, [x23, #832]
	ldr x20, [x23, #840]
	ldr x21, [x23, #848]
	ldr x22, [x23, #856]
	ldr x24, [x23, #864]
	ldr x30, [x23, #872]
	ldr x23, [x23, #880]
	ret
	.p2align 6
