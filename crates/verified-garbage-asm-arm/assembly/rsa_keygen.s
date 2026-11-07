// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_generate_init:
	str r4, [r0, #12]
	str r5, [r0, #20]
	mov r4, #0
	mov r5, #0
	cmp r3, #0
	beq 20f
22:
	ldrb r12, [r2, #0]
	orr r5, r5, r4, lsr #24
	lsl r4, r4, #8
	add r4, r4, r12
	add r2, r2, #1
	subs r3, r3, #1
	bne 22b
	b 21f
20:
21:
	cmp r1, #512
	mov r3, #0
	adc r3, r3, #0
	movw r12, #8193
	cmp r1, r12
	mov r12, #0
	adc r12, r12, #0
	sub r3, r3, r12
	and r12, r4, #1
	cmp r4, #3
	mov r2, #0
	adc r2, r2, #0
	and r12, r12, r2
	subs r2, r5, #1
	mov r2, #0
	adc r2, r2, #0
	bic r12, r12, r2
	mov r5, #2
	sub r5, r5, r3
	mul r5, r5, r12
	and r12, r12, r3
	mov r3, #0
	sub r12, r3, r12
	lsr r2, r1, #7
	lsl r2, r2, #3
	str r3, [r0, #4]
	str r3, [r0, #28]
	str r3, [r0, #32]
	str r3, [r0, #36]
	str r3, [r0, #44]
	str r3, [r0, #48]
	mov r1, #4
	and r1, r1, r12
	str r1, [r0, #40]
	and r1, r2, r12
	str r1, [r0, #8]
	lsl r1, r2, #15
	add r1, r1, r2
	and r1, r1, r12
	str r1, [r0, #16]
	lsl r1, r2, #5
	and r1, r1, r12
	str r1, [r0, #24]
	rev r1, r4
	and r1, r1, r12
	str r1, [r0, #52]
	eor r1, r4, #3
	subs r1, r1, #1
	mov r1, #0
	adc r1, r1, #0
	lsl r3, r2, #3
	add r3, r3, r2, lsl #4
	mul r1, r1, r3
	lsl r3, r2, #6
	sub r3, r3, r1
	and r3, r3, r12
	str r3, [r0, #0]
	mov r1, r5
	ldr r4, [r0, #12]
	ldr r5, [r0, #20]
	mov r2, #0
	str r2, [r0, #12]
	str r2, [r0, #20]
	mov r0, r1
	bx lr

vg_rsa_generate:
	push {r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	ldr r9, [sp, #52]
	mov r4, r0
	mov r6, r2
	mov r7, r3
	ldr r5, [r9, #8]
	mov r8, #0
	mov r11, #4
	ldr r0, [r9, #48]
	ldr r1, [r9, #52]
	eor r1, r1, #50331648
	orr r0, r0, r1
	subs r0, r0, #1
	mov r0, #0
	adc r0, r0, #0
	lsl r1, r5, #3
	add r1, r1, r5, lsl #4
	mul r0, r0, r1
	lsl r10, r5, #6
	sub r10, r10, r0
	mov r0, r4
	lsl lr, r5, #2
	mov r2, #0
20:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 20b
	add r0, r4, r5, lsl #2
	add r0, r0, r5
	lsl lr, r5, #2
	mov r2, #0
21:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 21b
22:
	sub sp, sp, #32
	add lr, sp, #0
	mov r12, #8
	str r12, [lr, #0]
	ldr r12, [lr, #72]
	sub r12, r12, #1
	cmp r12, r8
	mov r0, #0
	adc r0, r0, #0
	mul r12, r0, r8
	add r12, r7, r12
	str r12, [lr, #12]
	ldr r12, [lr, #72]
	sub r12, r12, r8
	str r12, [lr, #16]
	ldr r12, [lr, #76]
	str r12, [lr, #20]
	ldr r12, [lr, #80]
	str r12, [lr, #24]
	str r9, [lr, #28]
	add r0, r4, r5, lsl #2
	str r0, [lr, #4]
	ldr r12, [r9, #32]
	mul r12, r12, r5
	str r12, [lr, #8]
	add r0, r0, r12
	mov r1, r5
	mov r2, r6
	add r3, r9, #48
	bl {vg_rsa_prime_search}
	add sp, sp, #32
	ldr r12, [r6, #0]
	add r8, r8, r12
	cmp r0, #0
	beq 23f
	cmp r0, #3
	beq 25f
	cmp r12, #0
	beq 27f
	ldr r12, [r9, #32]
	cmp r12, #0
	beq 29f
	sub sp, sp, #56
	add lr, sp, #0
	mov r0, r4
	lsl r1, r5, #1
	add r2, r0, r1
	mov r3, r1
	add r12, r2, r1
	str r12, [lr, #0]
	str r5, [lr, #4]
	add r12, r12, r5
	str r12, [lr, #8]
	str r5, [lr, #12]
	add r12, r12, r5
	str r12, [lr, #16]
	str r5, [lr, #20]
	add r12, r12, r5
	str r12, [lr, #24]
	str r5, [lr, #28]
	add r12, r12, r5
	str r12, [lr, #32]
	str r5, [lr, #36]
	add r12, r9, #48
	str r12, [lr, #40]
	mov r12, #8
	str r12, [lr, #44]
	ldr r12, [lr, #100]
	str r12, [lr, #48]
	ldr r12, [lr, #104]
	str r12, [lr, #52]
	bl {vg_rsa_keygen_key}
	add sp, sp, #56
	cmp r0, #1
	beq 211f
	cmp r0, #2
	beq 213f
	mov r0, r4
	lsl lr, r5, #3
	add lr, lr, r5
	mov r2, #0
215:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 215b
	mov r12, #0
	str r12, [r9, #32]
	str r12, [r9, #36]
	str r12, [r9, #40]
	str r12, [r9, #44]
	mov r11, #2
	b 214f
213:
	mov r12, #0
	str r10, [r9, #0]
	str r12, [r9, #4]
	str r12, [r9, #36]
	mov r12, #0
	str r12, [r9, #32]
	mov r11, #4
214:
	b 212f
211:
	mov r12, #0
	str r12, [r9, #32]
	str r12, [r9, #36]
	str r12, [r9, #40]
	str r12, [r9, #44]
	mov r11, #1
212:
	b 210f
29:
	mov r12, #0
	str r10, [r9, #0]
	str r12, [r9, #4]
	str r12, [r9, #36]
	mov r12, #1
	str r12, [r9, #32]
	mov r11, #4
210:
	b 28f
27:
	mov r0, r4
	lsl lr, r5, #3
	add lr, lr, r5
	mov r2, #0
216:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 216b
	mov r12, #0
	str r12, [r9, #32]
	str r12, [r9, #36]
	str r12, [r9, #40]
	str r12, [r9, #44]
	mov r11, #3
28:
	b 26f
25:
	ldr r0, [r9, #40]
	ldr r1, [r9, #44]
	cmp r0, #2
	mov r0, #0
	adc r0, r0, #0
	orr r0, r0, r1
	cmp r0, #0
	beq 217f
	ldr r0, [r9, #40]
	ldr r1, [r9, #44]
	subs r0, r0, #1
	mov r2, #0
	adc r2, r2, #0
	add r1, r1, r2
	sub r1, r1, #1
	str r0, [r9, #40]
	str r1, [r9, #44]
	mov r12, #0
	str r10, [r9, #0]
	str r12, [r9, #4]
	str r12, [r9, #36]
	mov r12, #0
	str r12, [r9, #32]
	mov r11, #4
	b 218f
217:
	mov r0, r4
	lsl lr, r5, #3
	add lr, lr, r5
	mov r2, #0
219:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 219b
	mov r12, #0
	str r12, [r9, #32]
	str r12, [r9, #36]
	str r12, [r9, #40]
	str r12, [r9, #44]
	mov r11, #3
218:
26:
	b 24f
23:
	mov r11, #0
24:
	cmp r11, #4
	beq 22b
	str r8, [r6, #0]
	mov r0, #0
	str r0, [r6, #4]
	mov r0, r11
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr r7, [sp, #12]
	ldr r8, [sp, #16]
	ldr r9, [sp, #20]
	ldr r10, [sp, #24]
	ldr r11, [sp, #28]
	ldr lr, [sp, #36]
	ldr r4, [sp], #40
	bx lr

vg_rsa_generate_umaal:
	push {r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	ldr r9, [sp, #52]
	mov r4, r0
	mov r6, r2
	mov r7, r3
	ldr r5, [r9, #8]
	mov r8, #0
	mov r11, #4
	ldr r0, [r9, #48]
	ldr r1, [r9, #52]
	eor r1, r1, #50331648
	orr r0, r0, r1
	subs r0, r0, #1
	mov r0, #0
	adc r0, r0, #0
	lsl r1, r5, #3
	add r1, r1, r5, lsl #4
	mul r0, r0, r1
	lsl r10, r5, #6
	sub r10, r10, r0
	mov r0, r4
	lsl lr, r5, #2
	mov r2, #0
20:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 20b
	add r0, r4, r5, lsl #2
	add r0, r0, r5
	lsl lr, r5, #2
	mov r2, #0
21:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 21b
22:
	sub sp, sp, #32
	add lr, sp, #0
	mov r12, #8
	str r12, [lr, #0]
	ldr r12, [lr, #72]
	sub r12, r12, #1
	cmp r12, r8
	mov r0, #0
	adc r0, r0, #0
	mul r12, r0, r8
	add r12, r7, r12
	str r12, [lr, #12]
	ldr r12, [lr, #72]
	sub r12, r12, r8
	str r12, [lr, #16]
	ldr r12, [lr, #76]
	str r12, [lr, #20]
	ldr r12, [lr, #80]
	str r12, [lr, #24]
	str r9, [lr, #28]
	add r0, r4, r5, lsl #2
	str r0, [lr, #4]
	ldr r12, [r9, #32]
	mul r12, r12, r5
	str r12, [lr, #8]
	add r0, r0, r12
	mov r1, r5
	mov r2, r6
	add r3, r9, #48
	bl {vg_rsa_prime_search_umaal}
	add sp, sp, #32
	ldr r12, [r6, #0]
	add r8, r8, r12
	cmp r0, #0
	beq 23f
	cmp r0, #3
	beq 25f
	cmp r12, #0
	beq 27f
	ldr r12, [r9, #32]
	cmp r12, #0
	beq 29f
	sub sp, sp, #56
	add lr, sp, #0
	mov r0, r4
	lsl r1, r5, #1
	add r2, r0, r1
	mov r3, r1
	add r12, r2, r1
	str r12, [lr, #0]
	str r5, [lr, #4]
	add r12, r12, r5
	str r12, [lr, #8]
	str r5, [lr, #12]
	add r12, r12, r5
	str r12, [lr, #16]
	str r5, [lr, #20]
	add r12, r12, r5
	str r12, [lr, #24]
	str r5, [lr, #28]
	add r12, r12, r5
	str r12, [lr, #32]
	str r5, [lr, #36]
	add r12, r9, #48
	str r12, [lr, #40]
	mov r12, #8
	str r12, [lr, #44]
	ldr r12, [lr, #100]
	str r12, [lr, #48]
	ldr r12, [lr, #104]
	str r12, [lr, #52]
	bl {vg_rsa_keygen_key}
	add sp, sp, #56
	cmp r0, #1
	beq 211f
	cmp r0, #2
	beq 213f
	mov r0, r4
	lsl lr, r5, #3
	add lr, lr, r5
	mov r2, #0
215:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 215b
	mov r12, #0
	str r12, [r9, #32]
	str r12, [r9, #36]
	str r12, [r9, #40]
	str r12, [r9, #44]
	mov r11, #2
	b 214f
213:
	mov r12, #0
	str r10, [r9, #0]
	str r12, [r9, #4]
	str r12, [r9, #36]
	mov r12, #0
	str r12, [r9, #32]
	mov r11, #4
214:
	b 212f
211:
	mov r12, #0
	str r12, [r9, #32]
	str r12, [r9, #36]
	str r12, [r9, #40]
	str r12, [r9, #44]
	mov r11, #1
212:
	b 210f
29:
	mov r12, #0
	str r10, [r9, #0]
	str r12, [r9, #4]
	str r12, [r9, #36]
	mov r12, #1
	str r12, [r9, #32]
	mov r11, #4
210:
	b 28f
27:
	mov r0, r4
	lsl lr, r5, #3
	add lr, lr, r5
	mov r2, #0
216:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 216b
	mov r12, #0
	str r12, [r9, #32]
	str r12, [r9, #36]
	str r12, [r9, #40]
	str r12, [r9, #44]
	mov r11, #3
28:
	b 26f
25:
	ldr r0, [r9, #40]
	ldr r1, [r9, #44]
	cmp r0, #2
	mov r0, #0
	adc r0, r0, #0
	orr r0, r0, r1
	cmp r0, #0
	beq 217f
	ldr r0, [r9, #40]
	ldr r1, [r9, #44]
	subs r0, r0, #1
	mov r2, #0
	adc r2, r2, #0
	add r1, r1, r2
	sub r1, r1, #1
	str r0, [r9, #40]
	str r1, [r9, #44]
	mov r12, #0
	str r10, [r9, #0]
	str r12, [r9, #4]
	str r12, [r9, #36]
	mov r12, #0
	str r12, [r9, #32]
	mov r11, #4
	b 218f
217:
	mov r0, r4
	lsl lr, r5, #3
	add lr, lr, r5
	mov r2, #0
219:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 219b
	mov r12, #0
	str r12, [r9, #32]
	str r12, [r9, #36]
	str r12, [r9, #40]
	str r12, [r9, #44]
	mov r11, #3
218:
26:
	b 24f
23:
	mov r11, #0
24:
	cmp r11, #4
	beq 22b
	str r8, [r6, #0]
	mov r0, #0
	str r0, [r6, #4]
	mov r0, r11
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr r7, [sp, #12]
	ldr r8, [sp, #16]
	ldr r9, [sp, #20]
	ldr r10, [sp, #24]
	ldr r11, [sp, #28]
	ldr lr, [sp, #36]
	ldr r4, [sp], #40
	bx lr
