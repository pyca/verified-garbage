// The functions of `src/internal/vg_hmac_sha1_init_any_scratch_sha2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_init_any_scratch_sha2:
	str x19, [x4, #448]
	str x20, [x4, #456]
	str x21, [x4, #464]
	str x22, [x4, #472]
	str x24, [x4, #480]
	str x30, [x4, #488]
	str x23, [x4, #496]
	add x23, x4, #0
	add x19, x2, #0
	add x20, x3, #0
	add x21, x0, #0
	add x22, x1, #0
	lsr x9, x20, #6
	cbz x9, 20f
	sub x9, x20, #64
	cbz x9, 22f
	add x0, x23, #780
	bl {vg_sha1_init}
	add x0, x23, #780
	movz x1, #0, lsl #0
	add x2, x19, #0
	add x3, x20, #0
	add x4, x23, #0
	bl {vg_sha1_update_scratch_sha2}
	add x0, x23, #780
	add x1, x20, #0
	add x2, x23, #904
	add x3, x23, #0
	bl {vg_sha1_finalize_scratch_sha2}
	add x2, x23, #904
	movz x3, #20, lsl #0
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
	bl {vg_hmac_sha1_init_scratch_sha2}
	ldr x19, [x23, #448]
	ldr x20, [x23, #456]
	ldr x21, [x23, #464]
	ldr x22, [x23, #472]
	ldr x24, [x23, #480]
	ldr x30, [x23, #488]
	ldr x23, [x23, #496]
	ret
	.p2align 6
