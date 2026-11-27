// The functions of `src/internal/vg_rsa_mont_double_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_mont_double_umaal:
	push {r0, r4, r5, r6, r7, r8, r9, r10, r11, lr}
	ldr r12, [sp, #40]
	add r2, r0, r2, lsl #3
	ldr r10, [r2, #64]
	add r3, r0, r3, lsl #3
	ldr r8, [r3, #64]
	add r12, r0, r12, lsl #3
	ldr r9, [r12, #64]
	ldr r5, [r0, #88]
	ldr r6, [r0, #80]
	ldr r7, [r0, #48]
	add r7, r7, r7
	ldr r11, [r0, #64]
	ldr r12, [r0, #56]
	str r7, [r5, #0]
	str r9, [r5, #4]
	str r11, [r5, #8]
	str r12, [r5, #12]
	str r8, [r5, #16]
	str r7, [r5, #20]
	str r10, [r5, #24]
	str r6, [r5, #28]
	mov r0, r6
	mov lr, r7
	add lr, lr, #2
	mov r3, #0
20:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 20b
	mov r0, r5
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r0, [r0, #28]
	mov r11, #0
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
	and r2, lr, #1
	cmp r2, #0
	bne 21f
	b 22f
21:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
	adc r4, r4, r5, lsr #16
	adds r3, r3, r7, lsl #16
	adc r4, r4, r7, lsr #16
	ldr r5, [r0, #0]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
22:
	cmp lr, #0
	bne 23f
	b 24f
23:
	orr r9, r1, r10, lsl #16
25:
	ldr r2, [r12, #0]
	ldr r3, [r0, #0]
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	ldr r2, [r12, #4]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	subs lr, lr, #2
	bne 25b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
24:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #16
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
26:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 26b
	ldr r1, [r10, #0]
	mov r2, r11
	subs r3, r1, r2
	mov r11, #0
	adc r11, r11, #0
	eor r11, r11, #1
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
27:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 27b
	ldr r4, [sp, #4]
	ldr r5, [sp, #8]
	ldr r6, [sp, #12]
	ldr r7, [sp, #16]
	ldr r8, [sp, #20]
	ldr r9, [sp, #24]
	ldr r10, [sp, #28]
	ldr r11, [sp, #32]
	ldr lr, [sp, #36]
	ldr r12, [sp], #40
	bx lr
