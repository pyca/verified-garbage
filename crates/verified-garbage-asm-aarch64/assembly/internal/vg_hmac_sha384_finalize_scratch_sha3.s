// The functions of `src/internal/vg_hmac_sha384_finalize_scratch_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha384_finalize_scratch_sha3:
	.arch_extension sha3
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x23, x4, #0
	add x1, x2, #0
	add x2, x23, #744
	add x3, x23, #0
	bl {vg_sha512_finalize_scratch_sha3}
	ldp x9, x10, [x20, #0]
	stp x9, x10, [x19, #0]
	ldp x9, x10, [x20, #16]
	stp x9, x10, [x19, #16]
	ldp x9, x10, [x20, #32]
	stp x9, x10, [x19, #32]
	ldp x9, x10, [x20, #48]
	stp x9, x10, [x19, #48]
	ldr x9, [x23, #744]
	ldr x10, [x23, #752]
	stp x9, x10, [x19, #64]
	ldr x9, [x23, #760]
	ldr x10, [x23, #768]
	stp x9, x10, [x19, #80]
	ldr x9, [x23, #776]
	ldr x10, [x23, #784]
	stp x9, x10, [x19, #96]
	add x24, x21, #0
	add x21, x19, #64
	add x20, x23, #0
	movz x9, #128, lsl #0
	movz x10, #0, lsl #0
	stp x9, x10, [x21, #48]
	stp x10, x10, [x21, #64]
	stp x10, x10, [x21, #80]
	stp x10, x10, [x21, #96]
	movz x22, #176, lsl #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress_sha3}
	ldr x9, [x19, #0]
	rev x9, x9
	str x9, [x21, #0]
	ldr x9, [x19, #8]
	rev x9, x9
	str x9, [x21, #8]
	ldr x9, [x19, #16]
	rev x9, x9
	str x9, [x21, #16]
	ldr x9, [x19, #24]
	rev x9, x9
	str x9, [x21, #24]
	ldr x9, [x19, #32]
	rev x9, x9
	str x9, [x21, #32]
	ldr x9, [x19, #40]
	rev x9, x9
	str x9, [x21, #40]
	ldr x9, [x19, #48]
	rev x9, x9
	str x9, [x21, #48]
	ldr x9, [x19, #56]
	rev x9, x9
	str x9, [x21, #56]
	ldp x9, x10, [x21, #0]
	stp x9, x10, [x24, #0]
	ldp x9, x10, [x21, #16]
	stp x9, x10, [x24, #16]
	ldp x9, x10, [x21, #32]
	stp x9, x10, [x24, #32]
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	ret
	.arch_extension nosha3
	.p2align 6
