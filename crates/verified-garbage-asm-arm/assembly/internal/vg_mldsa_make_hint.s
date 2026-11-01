// The functions of `src/internal/vg_mldsa_make_hint.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_make_hint:
	push {r4}
	push {r5}
	push {r6}
	cmp r2, #95232
	mov r4, #0
	beq 20f
	mov r2, #256
22:
	ldr r5, [r1, #0]
	add r5, r5, #127
	lsr r5, r5, #7
	movw r12, #1025
	mul r5, r5, r12
	add r5, r5, #2097152
	lsr r5, r5, #22
	sub r5, r5, #16
	lsr r12, r5, #31
	add r5, r5, r12, lsl #4
	ldr r6, [r1, #0]
	ldr r12, [r0, #0]
	add r6, r6, r12
	sub r6, r6, #8388608
	add r6, r6, #8192
	sub r6, r6, #1
	lsr r12, r6, #31
	add r6, r6, r12, lsl #23
	sub r6, r6, r12, lsl #13
	add r6, r6, r12
	add r6, r6, #127
	lsr r6, r6, #7
	movw r12, #1025
	mul r6, r6, r12
	add r6, r6, #2097152
	lsr r6, r6, #22
	sub r6, r6, #16
	lsr r12, r6, #31
	add r6, r6, r12, lsl #4
	eor r6, r6, r5
	add r6, r6, #63
	lsr r6, r6, #6
	str r6, [r3, #0]
	add r4, r4, r6
	add r0, r0, #4
	add r1, r1, #4
	add r3, r3, #4
	subs r2, r2, #1
	bne 22b
	b 21f
20:
	mov r2, #256
23:
	ldr r5, [r1, #0]
	add r5, r5, #127
	lsr r5, r5, #7
	movw r12, #11275
	mul r5, r5, r12
	add r5, r5, #8388608
	lsr r5, r5, #24
	sub r5, r5, #44
	lsr r12, r5, #31
	add r5, r5, r12, lsl #5
	add r5, r5, r12, lsl #3
	add r5, r5, r12, lsl #2
	ldr r6, [r1, #0]
	ldr r12, [r0, #0]
	add r6, r6, r12
	sub r6, r6, #8388608
	add r6, r6, #8192
	sub r6, r6, #1
	lsr r12, r6, #31
	add r6, r6, r12, lsl #23
	sub r6, r6, r12, lsl #13
	add r6, r6, r12
	add r6, r6, #127
	lsr r6, r6, #7
	movw r12, #11275
	mul r6, r6, r12
	add r6, r6, #8388608
	lsr r6, r6, #24
	sub r6, r6, #44
	lsr r12, r6, #31
	add r6, r6, r12, lsl #5
	add r6, r6, r12, lsl #3
	add r6, r6, r12, lsl #2
	eor r6, r6, r5
	add r6, r6, #63
	lsr r6, r6, #6
	str r6, [r3, #0]
	add r4, r4, r6
	add r0, r0, #4
	add r1, r1, #4
	add r3, r3, #4
	subs r2, r2, #1
	bne 23b
21:
	mov r0, r4
	ldr r6, [sp], #4
	ldr r5, [sp], #4
	ldr r4, [sp], #4
	bx lr
