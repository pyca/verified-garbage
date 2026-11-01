// The functions of `src/internal/vg_mldsa_multiply_add_ntt.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_add_ntt:
	push {r4}
	push {r5}
	push {r6}
	push {r7}
	push {r8}
	push {r9}
	movw r4, #57345
	movt r4, #127
	mov r3, #256
20:
	ldr r12, [r1, #0]
	lsr r5, r12, #14
	lsl r6, r12, #18
	lsr r6, r6, #25
	lsl r7, r12, #25
	lsr r7, r7, #25
	ldr r8, [r2, #0]
	mul r9, r8, r5
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r6
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r7
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	ldr r8, [r0, #0]
	add r9, r9, r8
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	sub r9, r9, r4
	lsr r12, r9, #31
	mul r12, r12, r4
	add r9, r9, r12
	str r9, [r0, #0]
	add r0, r0, #4
	add r1, r1, #4
	add r2, r2, #4
	subs r3, r3, #1
	bne 20b
	ldr r9, [sp], #4
	ldr r8, [sp], #4
	ldr r7, [sp], #4
	ldr r6, [sp], #4
	ldr r5, [sp], #4
	ldr r4, [sp], #4
	bx lr
