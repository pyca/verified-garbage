// The functions of `src/internal/vg_hmac_sha384_init_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha384_init_scratch:
	str x19, [x4, #688]
	str x20, [x4, #696]
	str x21, [x4, #704]
	str x22, [x4, #712]
	str x24, [x4, #720]
	str x30, [x4, #728]
	str x23, [x4, #736]
	add x19, x0, #0
	add x20, x4, #0
	add x21, x1, #0
	add x22, x2, #0
	add x23, x4, #0
	add x24, x3, #0
	add x0, x19, #0
	bl {vg_sha384_init}
	add x0, x21, #0
	bl {vg_sha384_init}
	movz w14, #13878, lsl #0
	movk w14, #13878, lsl #16
	str w14, [x19, #64]
	str w14, [x19, #68]
	str w14, [x19, #72]
	str w14, [x19, #76]
	str w14, [x19, #80]
	str w14, [x19, #84]
	str w14, [x19, #88]
	str w14, [x19, #92]
	str w14, [x19, #96]
	str w14, [x19, #100]
	str w14, [x19, #104]
	str w14, [x19, #108]
	str w14, [x19, #112]
	str w14, [x19, #116]
	str w14, [x19, #120]
	str w14, [x19, #124]
	str w14, [x19, #128]
	str w14, [x19, #132]
	str w14, [x19, #136]
	str w14, [x19, #140]
	str w14, [x19, #144]
	str w14, [x19, #148]
	str w14, [x19, #152]
	str w14, [x19, #156]
	str w14, [x19, #160]
	str w14, [x19, #164]
	str w14, [x19, #168]
	str w14, [x19, #172]
	str w14, [x19, #176]
	str w14, [x19, #180]
	str w14, [x19, #184]
	str w14, [x19, #188]
	movz x10, #0, lsl #0
	cbz x24, 20f
22:
	add x13, x22, x10
	ldrb w9, [x13, #0]
	eor x9, x9, x14
	add x12, x19, x10
	strb w9, [x12, #64]
	add x10, x10, #1
	sub x11, x24, x10
	cbnz x11, 22b
	b 21f
20:
21:
	movz w15, #27242, lsl #0
	movk w15, #27242, lsl #16
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
	ldr w9, [x19, #80]
	eor x9, x9, x15
	str w9, [x21, #80]
	ldr w9, [x19, #84]
	eor x9, x9, x15
	str w9, [x21, #84]
	ldr w9, [x19, #88]
	eor x9, x9, x15
	str w9, [x21, #88]
	ldr w9, [x19, #92]
	eor x9, x9, x15
	str w9, [x21, #92]
	ldr w9, [x19, #96]
	eor x9, x9, x15
	str w9, [x21, #96]
	ldr w9, [x19, #100]
	eor x9, x9, x15
	str w9, [x21, #100]
	ldr w9, [x19, #104]
	eor x9, x9, x15
	str w9, [x21, #104]
	ldr w9, [x19, #108]
	eor x9, x9, x15
	str w9, [x21, #108]
	ldr w9, [x19, #112]
	eor x9, x9, x15
	str w9, [x21, #112]
	ldr w9, [x19, #116]
	eor x9, x9, x15
	str w9, [x21, #116]
	ldr w9, [x19, #120]
	eor x9, x9, x15
	str w9, [x21, #120]
	ldr w9, [x19, #124]
	eor x9, x9, x15
	str w9, [x21, #124]
	ldr w9, [x19, #128]
	eor x9, x9, x15
	str w9, [x21, #128]
	ldr w9, [x19, #132]
	eor x9, x9, x15
	str w9, [x21, #132]
	ldr w9, [x19, #136]
	eor x9, x9, x15
	str w9, [x21, #136]
	ldr w9, [x19, #140]
	eor x9, x9, x15
	str w9, [x21, #140]
	ldr w9, [x19, #144]
	eor x9, x9, x15
	str w9, [x21, #144]
	ldr w9, [x19, #148]
	eor x9, x9, x15
	str w9, [x21, #148]
	ldr w9, [x19, #152]
	eor x9, x9, x15
	str w9, [x21, #152]
	ldr w9, [x19, #156]
	eor x9, x9, x15
	str w9, [x21, #156]
	ldr w9, [x19, #160]
	eor x9, x9, x15
	str w9, [x21, #160]
	ldr w9, [x19, #164]
	eor x9, x9, x15
	str w9, [x21, #164]
	ldr w9, [x19, #168]
	eor x9, x9, x15
	str w9, [x21, #168]
	ldr w9, [x19, #172]
	eor x9, x9, x15
	str w9, [x21, #172]
	ldr w9, [x19, #176]
	eor x9, x9, x15
	str w9, [x21, #176]
	ldr w9, [x19, #180]
	eor x9, x9, x15
	str w9, [x21, #180]
	ldr w9, [x19, #184]
	eor x9, x9, x15
	str w9, [x21, #184]
	ldr w9, [x19, #188]
	eor x9, x9, x15
	str w9, [x21, #188]
	add x1, x19, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	add x19, x21, #0
	add x1, x21, #64
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_sha512_compress}
	ldr x19, [x23, #688]
	ldr x20, [x23, #696]
	ldr x21, [x23, #704]
	ldr x22, [x23, #712]
	ldr x24, [x23, #720]
	ldr x30, [x23, #728]
	ldr x23, [x23, #736]
	ret
	.p2align 6
