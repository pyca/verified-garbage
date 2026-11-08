// The functions of `src/mlkem1024.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_keygen:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x3, [sp, #8]
	bl {vg_mlkem1024_keygen_body}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_encaps:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x4, [sp, #8]
	bl {vg_mlkem1024_encaps_body}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_encaps_h:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x5, [sp, #8]
	bl {vg_mlkem1024_encaps_h_body}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_decaps:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x3, [sp, #8]
	bl {vg_mlkem1024_decaps_body}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_keygen_x2_sha3:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x3, [sp, #8]
	bl {vg_mlkem1024_keygen_body_x2_sha3}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_encaps_x2_sha3:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x4, [sp, #8]
	bl {vg_mlkem1024_encaps_body_x2_sha3}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_encaps_h_x2_sha3:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x5, [sp, #8]
	bl {vg_mlkem1024_encaps_h_body_x2_sha3}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_decaps_x2_sha3:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x3, [sp, #8]
	bl {vg_mlkem1024_decaps_body_x2_sha3}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_keygen_x2_sha3_keccak_sha3:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x3, [sp, #8]
	bl {vg_mlkem1024_keygen_body_x2_sha3_keccak_sha3}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_encaps_x2_sha3_keccak_sha3:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x4, [sp, #8]
	bl {vg_mlkem1024_encaps_body_x2_sha3_keccak_sha3}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_encaps_h_x2_sha3_keccak_sha3:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x5, [sp, #8]
	bl {vg_mlkem1024_encaps_h_body_x2_sha3_keccak_sha3}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_decaps_x2_sha3_keccak_sha3:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x3, [sp, #8]
	bl {vg_mlkem1024_decaps_body_x2_sha3_keccak_sha3}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #49152, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_mlkem1024_check_ek:
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movi v19.2d, #0
	movz x11, #128, lsl #0
20:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	cmhs v2.4s, v2.4s, v18.4s
	cmhs v3.4s, v3.4s, v18.4s
	orr v19.16b, v19.16b, v2.16b
	orr v19.16b, v19.16b, v3.16b
	add x0, x0, #12
	sub x11, x11, #1
	cbnz x11, 20b
	uaddlv d20, v19.4s
	umov x9, v20.d[0]
	sub x0, x9, #1
	lsr x0, x0, #63
	ret
	.p2align 6
