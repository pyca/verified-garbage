// The functions of `src/internal/vg_hmac_sha1_finalize_scratch_sha2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_finalize_scratch_sha2:
	.arch_extension sha2
	str x19, [x4, #160]
	str x20, [x4, #168]
	str x21, [x4, #176]
	str x22, [x4, #184]
	str x24, [x4, #192]
	str x30, [x4, #200]
	str x23, [x4, #208]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x23, x4, #0
	add x1, x2, #0
	add x2, x23, #216
	add x3, x23, #0
	bl {vg_sha1_finalize_scratch_sha2}
	ldr w9, [x20, #0]
	str w9, [x19, #0]
	ldr w9, [x20, #4]
	str w9, [x19, #4]
	ldr w9, [x20, #8]
	str w9, [x19, #8]
	ldr w9, [x20, #12]
	str w9, [x19, #12]
	ldr w9, [x20, #16]
	str w9, [x19, #16]
	ldr w9, [x23, #216]
	str w9, [x19, #20]
	ldr w9, [x23, #220]
	str w9, [x19, #24]
	ldr w9, [x23, #224]
	str w9, [x19, #28]
	ldr w9, [x23, #228]
	str w9, [x19, #32]
	ldr w9, [x23, #232]
	str w9, [x19, #36]
	add x24, x21, #0
	add x21, x19, #20
	add x20, x23, #0
	movz x9, #128, lsl #0
	str w9, [x21, #20]
	movz x9, #0, lsl #0
	str w9, [x21, #24]
	str w9, [x21, #28]
	str w9, [x21, #32]
	str w9, [x21, #36]
	str w9, [x21, #40]
	str w9, [x21, #44]
	str w9, [x21, #48]
	str w9, [x21, #52]
	movz x22, #84, lsl #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	add x12, x19, #76
	str x9, [x12, #0]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress_sha2}
	add x21, x24, #0
	ldr w9, [x19, #0]
	rev w9, w9
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	rev w9, w9
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	rev w9, w9
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	rev w9, w9
	str w9, [x21, #12]
	ldr w9, [x19, #16]
	rev w9, w9
	str w9, [x21, #16]
	ldr x19, [x23, #160]
	ldr x20, [x23, #168]
	ldr x21, [x23, #176]
	ldr x22, [x23, #184]
	ldr x24, [x23, #192]
	ldr x30, [x23, #200]
	ldr x23, [x23, #208]
	ret
	.arch_extension nosha2
	.p2align 6
