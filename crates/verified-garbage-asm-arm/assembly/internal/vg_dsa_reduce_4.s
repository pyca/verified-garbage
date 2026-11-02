// The functions of `src/internal/vg_dsa_reduce_4.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_reduce_4:
	mov r12, r0
	str r4, [r12, #8]
	str r5, [r12, #12]
	str r6, [r12, #16]
	str r7, [r12, #20]
	str r8, [r12, #24]
	str r9, [r12, #28]
	str r10, [r12, #32]
	str r11, [r12, #36]
	str lr, [r12, #40]
	mov r11, r2
	str r3, [r12, #44]
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
	ldr lr, [r12, #44]
	add lr, lr, r11
	movw r10, #616
	add r10, r12, r10
	movw r9, #648
	add r9, r12, r9
	mov r7, #0
20:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 20b
	movw r10, #656
	add r10, r12, r10
	movw r9, #688
	add r9, r12, r9
	mov r7, #0
21:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 21b
	cmp r11, lr
	beq 22f
24:
	ldrb r4, [r11, #0]
	movw r10, #656
	add r10, r12, r10
	str r4, [r10, #0]
	movw r0, #8
25:
	mov r1, r0
	movw r6, #65535
	mov r3, #0
	movw r10, #616
	add r10, r12, r10
	movw r0, #616
	add r0, r12, r0
	movw r8, #336
	add r8, r12, r8
	movw r9, #648
	add r9, r12, r9
26:
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
	bne 26b
	str r3, [r8, #0]
	mov r0, r1
	movw r6, #65535
	mov r3, #1
	movw r10, #336
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #296
	add r8, r12, r8
	movw r9, #288
	add r9, r12, r9
27:
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
	bne 27b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #336
	add r10, r12, r10
	movw r8, #296
	add r8, r12, r8
	movw r1, #616
	add r1, r12, r1
	movw r9, #328
	add r9, r12, r9
28:
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
	bne 28b
	subs r0, r0, #1
	bne 25b
	movw r6, #65535
	mov r3, #0
	movw r10, #616
	add r10, r12, r10
	movw r0, #656
	add r0, r12, r0
	movw r8, #336
	add r8, r12, r8
	movw r9, #648
	add r9, r12, r9
29:
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
	bne 29b
	str r3, [r8, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #336
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #296
	add r8, r12, r8
	movw r9, #288
	add r9, r12, r9
210:
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
	bne 210b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #336
	add r10, r12, r10
	movw r8, #296
	add r8, r12, r8
	movw r1, #616
	add r1, r12, r1
	movw r9, #328
	add r9, r12, r9
211:
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
	bne 211b
	add r11, r11, #1
	cmp r11, lr
	bne 24b
	b 23f
22:
23:
	ldr r4, [r12, #8]
	ldr r5, [r12, #12]
	ldr r6, [r12, #16]
	ldr r7, [r12, #20]
	ldr r8, [r12, #24]
	ldr r9, [r12, #28]
	ldr r10, [r12, #32]
	ldr r11, [r12, #36]
	ldr lr, [r12, #40]
	bx lr
