// The functions of `src/internal/vg_dsa_context_3.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_context_3:
	mov r12, r0
	str r4, [r12, #544]
	str r5, [r12, #548]
	str r6, [r12, #552]
	str r7, [r12, #556]
	str r8, [r12, #560]
	str r9, [r12, #564]
	str r10, [r12, #568]
	str lr, [r12, #572]
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r10, #448
	add r10, r12, r10
	movw r9, #472
	add r9, r12, r9
	mov r7, #0
20:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 20b
	movw r10, #448
	add r10, r12, r10
	mov r4, #1
	str r4, [r10, #0]
	movw r10, #480
	add r10, r12, r10
	movw r9, #504
	add r9, r12, r9
	mov r7, #0
21:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 21b
	movw r10, #480
	add r10, r12, r10
	mov r4, #1
	str r4, [r10, #0]
	movw lr, #384
22:
	movw r6, #65535
	mov r3, #0
	movw r10, #480
	add r10, r12, r10
	movw r0, #480
	add r0, r12, r0
	movw r8, #320
	add r8, r12, r8
	movw r9, #504
	add r9, r12, r9
23:
	ldr r7, [r10, #0]
	ldr r2, [r0, #0]
	and r4, r7, r6
	and r5, r2, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #0]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r2, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #4]
	lsr r3, r4, #16
	add r10, r10, #4
	add r0, r0, #4
	add r8, r8, #8
	cmp r10, r9
	bne 23b
	str r3, [r8, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #320
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #288
	add r8, r12, r8
	movw r9, #280
	add r9, r12, r9
24:
	ldr r7, [r1, #0]
	ldr r5, [r10, #0]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r2, r5, r6
	ldr r5, [r10, #4]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r2, r2, r5, lsl #16
	str r2, [r8, #0]
	add r10, r10, #8
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 24b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #320
	add r10, r12, r10
	movw r8, #288
	add r8, r12, r8
	movw r1, #480
	add r1, r12, r1
	movw r9, #312
	add r9, r12, r9
25:
	ldr r5, [r10, #0]
	ldr r7, [r10, #4]
	orr r5, r5, r7, lsl #16
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #8
	add r8, r8, #4
	add r1, r1, #4
	cmp r8, r9
	bne 25b
	subs lr, lr, #1
	bne 22b
	ldr r4, [r12, #544]
	ldr r5, [r12, #548]
	ldr r6, [r12, #552]
	ldr r7, [r12, #556]
	ldr r8, [r12, #560]
	ldr r9, [r12, #564]
	ldr r10, [r12, #568]
	ldr lr, [r12, #572]
	bx lr
