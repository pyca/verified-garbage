// The functions of `src/aes_ctr.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr:
	ldr r12, [sp, #4]
	str r4, [r12, #2064]
	str r5, [r12, #2068]
	str r6, [r12, #2072]
	str r7, [r12, #2076]
	str r8, [r12, #2080]
	str r9, [r12, #2084]
	str lr, [r12, #2092]
	str r10, [r12, #2088]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	ldr r8, [sp, #0]
	mov r10, r12
	cmp r8, #0
	beq 20f
22:
	ldr r0, [r6, #12]
	rev r0, r0
	mvn r0, r0
	sub r1, r8, #1
	subs r2, r1, r0
	mov r2, #0
	adc r2, r2, #0
	mov r3, #0
	sub r2, r3, r2
	eor r3, r1, r0
	and r3, r3, r2
	eor r1, r1, r3
	add r9, r1, #1
	mov r0, r4
	mov r1, r5
	mov r2, r6
	mov r3, r7
	mov r12, r9
	mov lr, r10
	push {r12, lr}
	bl {vg_aes_ctr32}
	ldr r12, [sp], #8
	sub r8, r8, r9
	add r7, r7, r9, lsl #4
	ldr r0, [r6, #12]
	cmp r0, #0
	beq 23f
	b 24f
23:
	ldr r0, [r6, #8]
	rev r0, r0
	ldr r1, [r6, #4]
	rev r1, r1
	ldr r2, [r6, #0]
	rev r2, r2
	adds r0, r0, #1
	mov r12, #0
	adc r12, r12, #0
	adds r1, r1, r12
	adc r2, r2, #0
	rev r0, r0
	str r0, [r6, #8]
	rev r1, r1
	str r1, [r6, #4]
	rev r2, r2
	str r2, [r6, #0]
24:
	cmp r8, #0
	bne 22b
	b 21f
20:
21:
	ldr r4, [r10, #2064]
	ldr r5, [r10, #2068]
	ldr r6, [r10, #2072]
	ldr r7, [r10, #2076]
	ldr r8, [r10, #2080]
	ldr r9, [r10, #2084]
	ldr lr, [r10, #2092]
	ldr r10, [r10, #2088]
	sub sp, sp, #8
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	add sp, sp, #8
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_aes_ctr_final:
	sub sp, sp, #72
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #72]
	str lr, [r12, #0]
	ldr lr, [sp, #76]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	ldr r12, [sp, #8]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r8, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	ldr r8, [sp, #0]
	ldr r10, [sp, #4]
	lsr r12, r8, #4
	and r8, r8, #15
	add r7, r3, r12, lsl #4
	mov lr, r10
	push {r12, lr}
	bl {vg_aes_ctr_entry}
	ldr r12, [sp], #8
	cmp r8, #0
	beq 20f
	ldr r12, [sp, #8]
	mov r0, #0
	str r0, [r12, #40]
	str r0, [r12, #44]
	str r0, [r12, #48]
	str r0, [r12, #52]
	mov r0, r4
	mov r1, r5
	mov r2, r6
	add r3, r12, #40
	mov r12, #1
	mov lr, r10
	push {r12, lr}
	bl {vg_aes_ctr_entry}
	ldr r12, [sp], #8
	ldr r12, [sp, #8]
	add r0, r12, #40
	mov r6, r7
	mov r7, r8
22:
	ldrb r9, [r6, #0]
	ldrb r10, [r0, #0]
	eor r9, r9, r10
	strb r9, [r6, #0]
	add r0, r0, #1
	add r6, r6, #1
	subs r7, r7, #1
	bne 22b
	b 21f
20:
21:
	ldr r12, [sp, #8]
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r8, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	add r12, sp, #16
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	add sp, sp, #72
	sub sp, sp, #88
	add r12, sp, #0
	mov r2, #0
	mov r3, #2
23:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 23b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #88
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
