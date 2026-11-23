// The functions of `src/internal/vg_aes_gcm_init_core.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_init_core:
	sub sp, sp, #2560
	add x3, sp, #0
	str x20, [x3, #136]
	str x21, [x3, #144]
	str x22, [x3, #152]
	str x23, [x3, #160]
	str x24, [x3, #168]
	str x25, [x3, #176]
	str x26, [x3, #184]
	str x27, [x3, #192]
	str x28, [x3, #200]
	str x30, [x3, #208]
	str x19, [x3, #128]
	add x19, x3, #0
	add x21, x2, #0
	lsr x22, x1, #2
	add x22, x22, #6
	add x3, x19, #512
	bl {vg_aes_expand_key_scratch}
	movz x9, #0, lsl #0
	str x9, [x21, #240]
	str x9, [x21, #248]
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x3, x21, #240
	movz x4, #1, lsl #0
	add x5, x19, #512
	umov x16, v9.d[0]
	blr x16
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.p2align 6
