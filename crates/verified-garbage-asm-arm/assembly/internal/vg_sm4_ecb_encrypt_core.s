// The functions of `src/internal/vg_sm4_ecb_encrypt_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ecb_encrypt_core:
	push {r4, lr}
	mov r4, lr
	mov r3, #0
	bl {vg_sm4_ecb}
	mov lr, r4
	ldr r4, [sp], #8
	bx lr
