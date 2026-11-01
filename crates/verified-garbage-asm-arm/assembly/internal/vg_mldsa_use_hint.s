// The functions of `src/internal/vg_mldsa_use_hint.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_use_hint:
	push {r4}
	push {r5}
	push {r6}
	cmp r2, #95232
	beq 20f
	mov r2, #256
22:
	ldr r12, [r1, #0]
	add r12, r12, #127
	lsr r12, r12, #7
	movw r4, #1025
	mul r12, r12, r4
	add r12, r12, #2097152
	lsr r12, r12, #22
	movw r4, #65024
	movt r4, #7
	mul r4, r4, r12
	ldr r5, [r1, #0]
	cmp r4, r5
	mov r4, #0
	adc r4, r4, #0
	mov r5, #1
	sub r5, r5, r4, lsl #1
	ldr r4, [r0, #0]
	mov r6, #0
	sub r6, r6, r4
	orr r6, r6, r4
	lsr r6, r6, #31
	mul r5, r5, r6
	add r12, r12, r5
	add r12, r12, #16
	sub r12, r12, #16
	lsr r4, r12, #31
	add r12, r12, r4, lsl #4
	sub r12, r12, #16
	lsr r4, r12, #31
	add r12, r12, r4, lsl #4
	str r12, [r3, #0]
	add r0, r0, #4
	add r1, r1, #4
	add r3, r3, #4
	subs r2, r2, #1
	bne 22b
	b 21f
20:
	mov r2, #256
23:
	ldr r12, [r1, #0]
	add r12, r12, #127
	lsr r12, r12, #7
	movw r4, #11275
	mul r12, r12, r4
	add r12, r12, #8388608
	lsr r12, r12, #24
	movw r4, #59392
	movt r4, #2
	mul r4, r4, r12
	ldr r5, [r1, #0]
	cmp r4, r5
	mov r4, #0
	adc r4, r4, #0
	mov r5, #1
	sub r5, r5, r4, lsl #1
	ldr r4, [r0, #0]
	mov r6, #0
	sub r6, r6, r4
	orr r6, r6, r4
	lsr r6, r6, #31
	mul r5, r5, r6
	add r12, r12, r5
	add r12, r12, #44
	sub r12, r12, #44
	lsr r4, r12, #31
	add r12, r12, r4, lsl #5
	add r12, r12, r4, lsl #3
	add r12, r12, r4, lsl #2
	sub r12, r12, #44
	lsr r4, r12, #31
	add r12, r12, r4, lsl #5
	add r12, r12, r4, lsl #3
	add r12, r12, r4, lsl #2
	str r12, [r3, #0]
	add r0, r0, #4
	add r1, r1, #4
	add r3, r3, #4
	subs r2, r2, #1
	bne 23b
21:
	ldr r6, [sp], #4
	ldr r5, [sp], #4
	ldr r4, [sp], #4
	bx lr
