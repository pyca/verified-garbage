// The functions of `src/internal/vg_hmac_md5_init_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_init_scratch:
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x24, [x4, #144]
	str x30, [x4, #152]
	str x23, [x4, #160]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x4, #0
	add x24, x3, #0
	add x0, x19, #0
	bl {vg_md5_init}
	add x0, x21, #0
	bl {vg_md5_init}
	movz w14, #13878, lsl #0
	movk w14, #13878, lsl #16
	str w14, [x19, #16]
	str w14, [x19, #20]
	str w14, [x19, #24]
	str w14, [x19, #28]
	str w14, [x19, #32]
	str w14, [x19, #36]
	str w14, [x19, #40]
	str w14, [x19, #44]
	str w14, [x19, #48]
	str w14, [x19, #52]
	str w14, [x19, #56]
	str w14, [x19, #60]
	str w14, [x19, #64]
	str w14, [x19, #68]
	str w14, [x19, #72]
	str w14, [x19, #76]
	movz x10, #0, lsl #0
	cbz x24, 20f
22:
	add x13, x22, x10
	ldrb w9, [x13, #0]
	eor x9, x9, x14
	add x12, x19, x10
	strb w9, [x12, #16]
	add x10, x10, #1
	sub x11, x24, x10
	cbnz x11, 22b
	b 21f
20:
21:
	movz w15, #27242, lsl #0
	movk w15, #27242, lsl #16
	ldr w9, [x19, #16]
	eor x9, x9, x15
	str w9, [x21, #16]
	ldr w9, [x19, #20]
	eor x9, x9, x15
	str w9, [x21, #20]
	ldr w9, [x19, #24]
	eor x9, x9, x15
	str w9, [x21, #24]
	ldr w9, [x19, #28]
	eor x9, x9, x15
	str w9, [x21, #28]
	ldr w9, [x19, #32]
	eor x9, x9, x15
	str w9, [x21, #32]
	ldr w9, [x19, #36]
	eor x9, x9, x15
	str w9, [x21, #36]
	ldr w9, [x19, #40]
	eor x9, x9, x15
	str w9, [x21, #40]
	ldr w9, [x19, #44]
	eor x9, x9, x15
	str w9, [x21, #44]
	ldr w9, [x19, #48]
	eor x9, x9, x15
	str w9, [x21, #48]
	ldr w9, [x19, #52]
	eor x9, x9, x15
	str w9, [x21, #52]
	ldr w9, [x19, #56]
	eor x9, x9, x15
	str w9, [x21, #56]
	ldr w9, [x19, #60]
	eor x9, x9, x15
	str w9, [x21, #60]
	ldr w9, [x19, #64]
	eor x9, x9, x15
	str w9, [x21, #64]
	ldr w9, [x19, #68]
	eor x9, x9, x15
	str w9, [x21, #68]
	ldr w9, [x19, #72]
	eor x9, x9, x15
	str w9, [x21, #72]
	ldr w9, [x19, #76]
	eor x9, x9, x15
	str w9, [x21, #76]
	add x1, x19, #16
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_md5_compress}
	add x19, x21, #0
	add x1, x21, #16
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_md5_compress}
	ldr x19, [x23, #112]
	ldr x20, [x23, #120]
	ldr x21, [x23, #128]
	ldr x22, [x23, #136]
	ldr x24, [x23, #144]
	ldr x30, [x23, #152]
	ldr x23, [x23, #160]
	ret
	.p2align 6
