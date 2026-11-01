// The functions of `src/internal/vg_keccak_pad_scratch.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_pad_scratch:
	ldr r12, [sp, #0]
	str lr, [r12, #512]
	add r2, r0, r2
	ldrb lr, [r2, #0]
	eor lr, lr, r3
	strb lr, [r2, #0]
	add r2, r0, r1
	sub r2, r2, #1
	ldrb lr, [r2, #0]
	eor lr, lr, #128
	strb lr, [r2, #0]
	mov r1, r12
	bl {vg_keccak_f1600}
	ldr lr, [r1, #512]
	bx lr
