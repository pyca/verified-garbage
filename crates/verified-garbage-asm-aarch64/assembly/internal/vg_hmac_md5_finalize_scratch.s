// The functions of `src/internal/vg_hmac_md5_finalize_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_finalize_scratch:
	str x19, [x4, #112]
	str x20, [x4, #120]
	str x21, [x4, #128]
	str x22, [x4, #136]
	str x24, [x4, #144]
	str x30, [x4, #152]
	str x23, [x4, #160]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x23, x4, #0
	add x1, x2, #0
	add x2, x23, #168
	add x3, x23, #0
	bl {vg_md5_finalize_scratch}
	ldr w9, [x20, #0]
	str w9, [x19, #0]
	ldr w9, [x20, #4]
	str w9, [x19, #4]
	ldr w9, [x20, #8]
	str w9, [x19, #8]
	ldr w9, [x20, #12]
	str w9, [x19, #12]
	ldr w9, [x23, #168]
	str w9, [x19, #16]
	ldr w9, [x23, #172]
	str w9, [x19, #20]
	ldr w9, [x23, #176]
	str w9, [x19, #24]
	ldr w9, [x23, #180]
	str w9, [x19, #28]
	add x24, x21, #0
	add x21, x19, #16
	add x20, x23, #0
	movz x9, #128, lsl #0
	str w9, [x21, #16]
	movz x9, #0, lsl #0
	str w9, [x21, #20]
	str w9, [x21, #24]
	str w9, [x21, #28]
	str w9, [x21, #32]
	str w9, [x21, #36]
	str w9, [x21, #40]
	str w9, [x21, #44]
	str w9, [x21, #48]
	str w9, [x21, #52]
	movz x22, #80, lsl #0
	add x9, x22, x22
	add x9, x9, x9
	add x9, x9, x9
	str x9, [x19, #72]
	add x1, x21, #0
	add x0, x19, #0
	movz x2, #1, lsl #0
	add x3, x20, #0
	bl {vg_md5_compress}
	add x21, x24, #0
	ldr w9, [x19, #0]
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	str w9, [x21, #12]
	ldr x19, [x23, #112]
	ldr x20, [x23, #120]
	ldr x21, [x23, #128]
	ldr x22, [x23, #136]
	ldr x24, [x23, #144]
	ldr x30, [x23, #152]
	ldr x23, [x23, #160]
	ret
	.p2align 6
