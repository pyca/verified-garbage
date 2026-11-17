// The functions of `src/internal/vg_mldsa_multiply_ntt.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_ntt:
	push {r4}
	push {r5}
	push {r6}
	push {r7}
	push {r8}
	push {r9}
	movw r4, #8191
	movt r4, #65408
	movw r5, #57345
	movt r5, #127
	mov r3, #256
20:
	ldr r8, [r1, #0]
	ldr r6, [r2, #0]
	add r7, r6, r6, lsr #10
	lsr r7, r7, #7
	lsr r12, r8, #8
	mul r12, r12, r7
	lsr r12, r12, #8
	mul r9, r8, r6
	mla r9, r12, r4, r9
	lsr r12, r9, #23
	mla r9, r12, r4, r9
	sub r9, r9, r5
	lsr r12, r9, #31
	mla r9, r12, r5, r9
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
