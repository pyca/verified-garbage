// The functions of `src/internal/vg_pbkdf2_hmac_sha384_iterate.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha384_iterate:
	add w2, w2, #0
	str x19, [x4, #640]
	str x20, [x4, #648]
	str x21, [x4, #656]
	str x22, [x4, #664]
	str x23, [x4, #672]
	str x24, [x4, #680]
	str x30, [x4, #688]
	add x19, x4, #696
	add x20, x4, #0
	add x21, x4, #760
	add x23, x3, #0
	add x24, x2, #0
	ldr w9, [x1, #0]
	str w9, [x21, #0]
	ldr w9, [x1, #4]
	str w9, [x21, #4]
	ldr w9, [x1, #8]
	str w9, [x21, #8]
	ldr w9, [x1, #12]
	str w9, [x21, #12]
	ldr w9, [x1, #16]
	str w9, [x21, #16]
	ldr w9, [x1, #20]
	str w9, [x21, #20]
	ldr w9, [x1, #24]
	str w9, [x21, #24]
	ldr w9, [x1, #28]
	str w9, [x21, #28]
	ldr w9, [x1, #32]
	str w9, [x21, #32]
	ldr w9, [x1, #36]
	str w9, [x21, #36]
	ldr w9, [x1, #40]
	str w9, [x21, #40]
	ldr w9, [x1, #44]
	str w9, [x21, #44]
	movz x9, #128, lsl #0
	str w9, [x21, #48]
	movz x9, #0, lsl #0
	str w9, [x21, #52]
	str w9, [x21, #56]
	str w9, [x21, #60]
	str w9, [x21, #64]
	str w9, [x21, #68]
	str w9, [x21, #72]
	str w9, [x21, #76]
	str w9, [x21, #80]
	str w9, [x21, #84]
	str w9, [x21, #88]
	str w9, [x21, #92]
	str w9, [x21, #96]
	str w9, [x21, #100]
	str w9, [x21, #104]
	str w9, [x21, #108]
	movz x22, #176, lsl #0
	lsr x9, x22, #61
	rev x9, x9
	str x9, [x19, #176]
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	rev x9, x9
	str x9, [x19, #184]
	add x22, x0, #0
	cbz x24, 20f
22:
	ldr w9, [x22, #0]
	str w9, [x19, #0]
	ldr w9, [x22, #4]
	str w9, [x19, #4]
	ldr w9, [x22, #8]
	str w9, [x19, #8]
	ldr w9, [x22, #12]
	str w9, [x19, #12]
	ldr w9, [x22, #16]
	str w9, [x19, #16]
	ldr w9, [x22, #20]
	str w9, [x19, #20]
	ldr w9, [x22, #24]
	str w9, [x19, #24]
	ldr w9, [x22, #28]
	str w9, [x19, #28]
	ldr w9, [x22, #32]
	str w9, [x19, #32]
	ldr w9, [x22, #36]
	str w9, [x19, #36]
	ldr w9, [x22, #40]
	str w9, [x19, #40]
	ldr w9, [x22, #44]
	str w9, [x19, #44]
	ldr w9, [x22, #48]
	str w9, [x19, #48]
	ldr w9, [x22, #52]
	str w9, [x19, #52]
	ldr w9, [x22, #56]
	str w9, [x19, #56]
	ldr w9, [x22, #60]
	str w9, [x19, #60]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
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
	movz x9, #128, lsl #0
	str w9, [x21, #48]
	movz x9, #0, lsl #0
	str w9, [x21, #52]
	str w9, [x21, #56]
	str w9, [x21, #60]
	ldr w9, [x22, #192]
	str w9, [x19, #0]
	ldr w9, [x22, #196]
	str w9, [x19, #4]
	ldr w9, [x22, #200]
	str w9, [x19, #8]
	ldr w9, [x22, #204]
	str w9, [x19, #12]
	ldr w9, [x22, #208]
	str w9, [x19, #16]
	ldr w9, [x22, #212]
	str w9, [x19, #20]
	ldr w9, [x22, #216]
	str w9, [x19, #24]
	ldr w9, [x22, #220]
	str w9, [x19, #28]
	ldr w9, [x22, #224]
	str w9, [x19, #32]
	ldr w9, [x22, #228]
	str w9, [x19, #36]
	ldr w9, [x22, #232]
	str w9, [x19, #40]
	ldr w9, [x22, #236]
	str w9, [x19, #44]
	ldr w9, [x22, #240]
	str w9, [x19, #48]
	ldr w9, [x22, #244]
	str w9, [x19, #52]
	ldr w9, [x22, #248]
	str w9, [x19, #56]
	ldr w9, [x22, #252]
	str w9, [x19, #60]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
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
	movz x9, #128, lsl #0
	str w9, [x21, #48]
	movz x9, #0, lsl #0
	str w9, [x21, #52]
	str w9, [x21, #56]
	str w9, [x21, #60]
	ldr w9, [x21, #0]
	ldr w10, [x23, #0]
	eor x9, x9, x10
	str w9, [x23, #0]
	ldr w9, [x21, #4]
	ldr w10, [x23, #4]
	eor x9, x9, x10
	str w9, [x23, #4]
	ldr w9, [x21, #8]
	ldr w10, [x23, #8]
	eor x9, x9, x10
	str w9, [x23, #8]
	ldr w9, [x21, #12]
	ldr w10, [x23, #12]
	eor x9, x9, x10
	str w9, [x23, #12]
	ldr w9, [x21, #16]
	ldr w10, [x23, #16]
	eor x9, x9, x10
	str w9, [x23, #16]
	ldr w9, [x21, #20]
	ldr w10, [x23, #20]
	eor x9, x9, x10
	str w9, [x23, #20]
	ldr w9, [x21, #24]
	ldr w10, [x23, #24]
	eor x9, x9, x10
	str w9, [x23, #24]
	ldr w9, [x21, #28]
	ldr w10, [x23, #28]
	eor x9, x9, x10
	str w9, [x23, #28]
	ldr w9, [x21, #32]
	ldr w10, [x23, #32]
	eor x9, x9, x10
	str w9, [x23, #32]
	ldr w9, [x21, #36]
	ldr w10, [x23, #36]
	eor x9, x9, x10
	str w9, [x23, #36]
	ldr w9, [x21, #40]
	ldr w10, [x23, #40]
	eor x9, x9, x10
	str w9, [x23, #40]
	ldr w9, [x21, #44]
	ldr w10, [x23, #44]
	eor x9, x9, x10
	str w9, [x23, #44]
	sub x24, x24, #1
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x30, [x20, #688]
	ldr x19, [x20, #640]
	ldr x21, [x20, #656]
	ldr x22, [x20, #664]
	ldr x23, [x20, #672]
	ldr x24, [x20, #680]
	ldr x20, [x20, #648]
	ret
	.p2align 6
