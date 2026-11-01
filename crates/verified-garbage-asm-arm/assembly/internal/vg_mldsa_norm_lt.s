// The functions of `src/internal/vg_mldsa_norm_lt.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_norm_lt:
	push {r4}
	mov r4, #0
	mov r2, #256
20:
	ldr r3, [r0, #0]
	movw r12, #57345
	movt r12, #127
	sub r12, r12, r3
	cmp r3, r1
	mov r3, #0
	adc r3, r3, #0
	cmp r12, r1
	mov r12, #0
	adc r12, r12, #0
	and r3, r3, r12
	orr r4, r4, r3
	add r0, r0, #4
	subs r2, r2, #1
	bne 20b
	mov r0, #1
	sub r0, r0, r4
	ldr r4, [sp], #4
	bx lr
