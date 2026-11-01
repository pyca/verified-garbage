// The functions of `src/internal/vg_mlkem_add.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_add:
	mov r2, #256
20:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	add r3, r3, r12
	sub r3, r3, #3328
	sub r3, r3, #1
	lsr r12, r3, #31
	add r3, r3, r12
	add r3, r3, r12, lsl #8
	add r3, r3, r12, lsl #10
	add r3, r3, r12, lsl #11
	str r3, [r0, #0]
	add r0, r0, #4
	add r1, r1, #4
	subs r2, r2, #1
	bne 20b
	bx lr
