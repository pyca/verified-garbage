// The functions of `src/internal/vg_pbkdf2_hmac_sha1_iterate.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha1_iterate:
	add w2, w2, #0
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x23, [x4, #144]
	str x24, [x4, #152]
	str x30, [x4, #160]
	add x19, x4, #168
	add x20, x4, #0
	add x21, x4, #188
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
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
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
	ldr w9, [x22, #84]
	str w9, [x19, #0]
	ldr w9, [x22, #88]
	str w9, [x19, #4]
	ldr w9, [x22, #92]
	str w9, [x19, #8]
	ldr w9, [x22, #96]
	str w9, [x19, #12]
	ldr w9, [x22, #100]
	str w9, [x19, #16]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha1_compress}
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
	sub x24, x24, #1
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x30, [x20, #160]
	ldr x19, [x20, #112]
	ldr x21, [x20, #128]
	ldr x22, [x20, #136]
	ldr x23, [x20, #144]
	ldr x24, [x20, #152]
	ldr x20, [x20, #120]
	ret
	.p2align 6
