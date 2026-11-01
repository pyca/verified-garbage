// The functions of `src/internal/vg_mldsa_power2round.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_power2round:
	push {r4}
	mov r3, #256
20:
	ldr r12, [r0, #0]
	add r12, r12, #4096
	sub r12, r12, #1
	lsr r4, r12, #13
	str r4, [r1, #0]
	lsl r12, r12, #19
	lsr r12, r12, #19
	sub r12, r12, #4096
	add r12, r12, #1
	lsr r4, r12, #31
	add r12, r12, r4, lsl #23
	sub r12, r12, r4, lsl #13
	add r12, r12, r4
	str r12, [r2, #0]
	add r0, r0, #4
	add r1, r1, #4
	add r2, r2, #4
	subs r3, r3, #1
	bne 20b
	ldr r4, [sp], #4
	bx lr
