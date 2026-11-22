// The functions of `src/internal/vg_hmac_sha384_init_any_scratch_sha512.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha384_init_any_scratch_sha512:
	str x19, [x4, #1872]
	str x20, [x4, #1880]
	str x21, [x4, #1888]
	str x22, [x4, #1896]
	str x24, [x4, #1904]
	str x30, [x4, #1912]
	str x23, [x4, #1920]
	add x23, x4, #0
	add x19, x2, #0
	add x20, x3, #0
	add x21, x0, #0
	add x22, x1, #0
	lsr x9, x20, #7
	cbz x9, 20f
	sub x9, x20, #128
	cbz x9, 22f
	add x0, x23, #2528
	bl {vg_sha384_init}
	add x0, x23, #2528
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha512_update_scratch_sha512}
	add x0, x23, #2528
	add x1, x20, #0
	add x2, x23, #2816
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch_sha512}
	add x2, x23, #2816
	movz x3, #48, lsl #0
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
	bl {vg_hmac_sha384_init_scratch_sha512}
	ldr x19, [x23, #1872]
	ldr x20, [x23, #1880]
	ldr x21, [x23, #1888]
	ldr x22, [x23, #1896]
	ldr x24, [x23, #1904]
	ldr x30, [x23, #1912]
	ldr x23, [x23, #1920]
	ret
	.p2align 6
