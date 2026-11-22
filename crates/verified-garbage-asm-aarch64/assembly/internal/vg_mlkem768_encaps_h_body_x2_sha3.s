// The functions of `src/internal/vg_mlkem768_encaps_h_body_x2_sha3.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_encaps_h_body_x2_sha3:
	sub sp, sp, #16
	umov x16, v8.d[0]
	str x30, [sp, #0]
	str x16, [sp, #8]
	adrp x16, {vg_keccak_f1600}
	add x16, x16, {vg_keccak_f1600}
	mov v8.d[0], x16
	bl {vg_mlkem768_encaps_h_core_x2_sha3}
	ldr x16, [sp, #8]
	mov v8.d[0], x16
	ldr x30, [sp, #0]
	add sp, sp, #16
	ret
	.p2align 6
