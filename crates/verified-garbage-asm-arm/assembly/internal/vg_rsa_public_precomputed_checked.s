// The functions of `src/internal/vg_rsa_public_precomputed_checked.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precomputed_checked:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	add r12, sp, #0
	str r0, [r12, #4]
	ldr r0, [sp, #72]
	str r0, [r12, #0]
	str r1, [r12, #12]
	ldr r1, [sp, #56]
	ldr lr, [sp, #60]
	mov r3, #0
	mov r4, #0
20:
	ldrb r7, [r1, #0]
	lsr r5, r3, #24
	lsl r4, r4, #8
	add r4, r4, r5
	lsl r3, r3, #8
	add r3, r3, r7
	lsr r5, r4, #1
	subs r5, r5, #0
	beq 21f
	mov r4, #2
	b 22f
21:
22:
	add r1, r1, #1
	subs lr, lr, #1
	bne 20b
	lsr r5, r4, #1
	and r7, r3, #1
	eor r7, r7, #1
	orr r5, r5, r7
	subs r5, r5, #0
	beq 23f
	mov r7, #0
	b 24f
23:
	eor r5, r3, #1
	orr r5, r5, r4
	subs r5, r5, #0
	beq 25f
	mov r7, #1
	b 26f
25:
	mov r7, #0
26:
24:
	subs r7, r7, #0
	beq 27f
	ldr r4, [sp, #8]
	ldr r6, [sp, #12]
	add r7, r6, #7
	lsr r7, r7, #3
	mov r3, #0
	str r7, [r0, #48]
	str r3, [r0, #52]
	mov r8, r0
	add r5, r7, #2
	lsl r5, r5, #3
	add r4, r0, #256
	add r0, r0, #64
	mov lr, #8
29:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 29b
	mov r0, r8
	ldr r4, [sp, #8]
	ldr r6, [sp, #12]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
	mov r2, r0
	mov r0, r1
	mov r1, r2
210:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 210b
	mov r0, r5
	ldr r1, [r0, #48]
	lsl r1, r1, #3
	add r4, r4, r1
	mov r2, #4
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
	mov r2, r0
	mov r0, r1
	mov r1, r2
211:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 211b
	mov r0, r5
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
212:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 212b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r10, [r0, #120]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
213:
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
	bne 213b
	ldr r0, [sp, #0]
	add r12, sp, #48
	str r11, [r12, #0]
	ldr r10, [r0, #96]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
214:
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
	bne 214b
	ldr r0, [sp, #0]
	add r12, sp, #48
	ldr r1, [r12, #0]
	and r11, r11, r1
	str r11, [r12, #0]
	ldr r1, [r0, #64]
	ldrb r1, [r1, #0]
	ldr r11, [sp, #48]
	and r1, r1, #1
	and r11, r11, r1
	subs r11, r11, #0
	beq 215f
	mov r12, r0
	ldr r0, [r0, #64]
	ldr r2, [r0, #0]
	ldr r11, [r0, #4]
	mov r1, r2
	mov r10, r11
	ldr r2, [r0, #0]
	ldr r11, [r0, #4]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r6, #2
	subs r2, r6, r3
	mov r5, #0
	adc r5, r5, #0
	eor r5, r5, #1
	mov r11, #0
	sub r11, r11, r4
	sub r11, r11, r5
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r1, r3
	mov r10, r4
	ldr r2, [r0, #0]
	ldr r11, [r0, #4]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r6, #2
	subs r2, r6, r3
	mov r5, #0
	adc r5, r5, #0
	eor r5, r5, #1
	mov r11, #0
	sub r11, r11, r4
	sub r11, r11, r5
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r1, r3
	mov r10, r4
	ldr r2, [r0, #0]
	ldr r11, [r0, #4]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r6, #2
	subs r2, r6, r3
	mov r5, #0
	adc r5, r5, #0
	eor r5, r5, #1
	mov r11, #0
	sub r11, r11, r4
	sub r11, r11, r5
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r1, r3
	mov r10, r4
	ldr r2, [r0, #0]
	ldr r11, [r0, #4]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r6, #2
	subs r2, r6, r3
	mov r5, #0
	adc r5, r5, #0
	eor r5, r5, #1
	mov r11, #0
	sub r11, r11, r4
	sub r11, r11, r5
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r1, r3
	mov r10, r4
	ldr r2, [r0, #0]
	ldr r11, [r0, #4]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r6, #2
	subs r2, r6, r3
	mov r5, #0
	adc r5, r5, #0
	eor r5, r5, #1
	mov r11, #0
	sub r11, r11, r4
	sub r11, r11, r5
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	mul r5, r1, r11
	mul r6, r2, r10
	add r4, r4, r5
	add r4, r4, r6
	mov r1, r3
	mov r10, r4
	mov r3, r1
	mov r4, r10
	mov r6, #0
	subs r2, r6, r3
	mov r5, #0
	adc r5, r5, #0
	eor r5, r5, #1
	mov r11, #0
	sub r11, r11, r4
	sub r11, r11, r5
	str r2, [r12, #56]
	str r11, [r12, #60]
	mov r0, r12
	ldr r4, [sp, #64]
	ldr r6, [sp, #12]
	mov r2, #1
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
217:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 217b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
218:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 218b
	ldr r0, [sp, #0]
	ldr r10, [r0, #72]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
219:
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
	bne 219b
	ldr r0, [sp, #0]
	add r12, sp, #48
	str r11, [r12, #0]
	ldr r1, [sp, #56]
	ldr r2, [sp, #60]
	str r1, [r0, #128]
	str r2, [r0, #132]
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
220:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 220b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	mov r2, #6
	mov r3, #4
	mov r12, #7
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
221:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 221b
	mov r0, r5
222:
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
	bne 223f
	b 224f
223:
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
224:
	cmp lr, #0
	bne 225f
	b 226f
225:
227:
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
	ldr r2, [r12, #4]
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	subs lr, lr, #2
	bne 227b
226:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr lr, [r0, #16]
	ldr r12, [r0, #24]
	ldr r1, [r0, #28]
	ldr r0, [r0, #44]
	ldr r2, [r0, #0]
	mul r1, r1, r2
	mov r11, #0
	ldr r2, [r12, #0]
	ldr r10, [r0, #0]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	adds r3, r3, r10
	adc r4, r4, #0
	adds r3, r3, r11
	adc r4, r4, #0
	mov r11, r4
	add r12, r12, #4
	subs lr, lr, #1
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
228:
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 228b
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
	mov r3, #0
	str r3, [r0, #0]
	add r0, r0, #12
	ldr r4, [r0, #16]
	add r4, r4, #4
	str r4, [r0, #16]
	ldr lr, [r0, #20]
	subs lr, lr, #1
	str lr, [r0, #20]
	bne 222b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
229:
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
	bne 229b
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
230:
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
	bne 230b
	ldr r0, [sp, #0]
	mov r2, #5
	mov r3, #1
	mov r12, #4
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
231:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 231b
	mov r0, r5
232:
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
	bne 233f
	b 234f
233:
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
234:
	cmp lr, #0
	bne 235f
	b 236f
235:
237:
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
	ldr r2, [r12, #4]
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	subs lr, lr, #2
	bne 237b
236:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr lr, [r0, #16]
	ldr r12, [r0, #24]
	ldr r1, [r0, #28]
	ldr r0, [r0, #44]
	ldr r2, [r0, #0]
	mul r1, r1, r2
	mov r11, #0
	ldr r2, [r12, #0]
	ldr r10, [r0, #0]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	adds r3, r3, r10
	adc r4, r4, #0
	adds r3, r3, r11
	adc r4, r4, #0
	mov r11, r4
	add r12, r12, #4
	subs lr, lr, #1
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
238:
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 238b
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
	mov r3, #0
	str r3, [r0, #0]
	add r0, r0, #12
	ldr r4, [r0, #16]
	add r4, r4, #4
	str r4, [r0, #16]
	ldr lr, [r0, #20]
	subs lr, lr, #1
	str lr, [r0, #20]
	bne 232b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
239:
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
	bne 239b
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
240:
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
	bne 240b
	ldr r0, [sp, #0]
241:
	ldr r2, [r0, #128]
	ldrb r1, [r2, #0]
	str r1, [r0, #200]
	mov r1, #8
	str r1, [r0, #192]
242:
	mov r2, #6
	mov r3, #6
	mov r12, #6
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
	str r7, [r6, #0]
	str r10, [r6, #4]
	str r8, [r6, #8]
	str r8, [r6, #12]
	sub r1, r7, #1
	str r1, [r6, #16]
	add r1, r6, #28
	str r1, [r6, #20]
	add r0, r6, #24
	lsl lr, r7, #1
	add lr, lr, #2
	mov r3, #0
243:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 243b
244:
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r2, [r0, #12]
	ldr lr, [r0, #16]
	ldr r3, [r0, #20]
	add r4, r3, #8
	str r4, [r0, #20]
	add r12, r2, #4
	str r12, [r0, #12]
	mov r0, r3
	mov r11, #0
	ldr r1, [r2, #0]
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
	and r2, lr, #1
	cmp r2, #0
	bne 245f
	b 246f
245:
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
246:
	cmp lr, #0
	bne 247f
	b 248f
247:
249:
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
	ldr r2, [r12, #4]
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	subs lr, lr, #2
	bne 249b
248:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 244b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
250:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 250b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
251:
	ldr r1, [r12, #0]
	mov r2, r1
	ldr r10, [r0, #0]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	adds r3, r3, r10
	adc r4, r4, #0
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	ldr r10, [r0, #4]
	adds r4, r4, r10
	mov r11, #0
	adc r11, r11, #0
	str r4, [r0, #4]
	add r0, r0, #8
	add r12, r12, #4
	subs lr, lr, #1
	bne 251b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
252:
	ldr r0, [sp, #0]
	ldr r12, [r0, #64]
	ldr r1, [r0, #56]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	ldr r2, [r0, #20]
	add r3, r2, #4
	str r3, [r0, #20]
	mov r0, r2
	ldr r2, [r0, #0]
	mul r1, r1, r2
	mov r11, #0
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
	and r2, lr, #1
	cmp r2, #0
	bne 253f
	b 254f
253:
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
254:
	cmp lr, #0
	bne 255f
	b 256f
255:
257:
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
	ldr r2, [r12, #4]
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	subs lr, lr, #2
	bne 257b
256:
	orr r1, r1, r10, lsl #16
	ldr r2, [sp, #0]
	ldr r2, [r2, #80]
	ldr r3, [r0, #0]
	ldr r4, [r2, #12]
	adds r3, r3, r11
	mov r5, #0
	adc r5, r5, #0
	adds r3, r3, r4
	adc r5, r5, #0
	str r3, [r0, #0]
	str r5, [r2, #12]
	mov r0, r2
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 252b
	ldr r0, [sp, #0]
	ldr r12, [r0, #64]
	ldr r0, [r0, #80]
	ldr r7, [r0, #0]
	ldr r9, [r0, #4]
	ldr r3, [r0, #12]
	add r10, r0, r7, lsl #3
	str r3, [r10, #24]
	add r10, r0, r7, lsl #2
	add r10, r10, #24
	mov lr, r7
	mov r11, #0
258:
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
	bne 258b
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
259:
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
	bne 259b
	ldr r0, [sp, #0]
	ldr r1, [r0, #200]
	lsr r1, r1, #7
	and r1, r1, #1
	subs r1, r1, #0
	bne 260f
	b 261f
260:
	mov r2, #6
	mov r3, #6
	mov r12, #5
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
262:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 262b
	mov r0, r5
263:
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
	bne 264f
	b 265f
264:
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
265:
	cmp lr, #0
	bne 266f
	b 267f
266:
268:
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
	ldr r2, [r12, #4]
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	subs lr, lr, #2
	bne 268b
267:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr lr, [r0, #16]
	ldr r12, [r0, #24]
	ldr r1, [r0, #28]
	ldr r0, [r0, #44]
	ldr r2, [r0, #0]
	mul r1, r1, r2
	mov r11, #0
	ldr r2, [r12, #0]
	ldr r10, [r0, #0]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	adds r3, r3, r10
	adc r4, r4, #0
	adds r3, r3, r11
	adc r4, r4, #0
	mov r11, r4
	add r12, r12, #4
	subs lr, lr, #1
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
269:
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 269b
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
	mov r3, #0
	str r3, [r0, #0]
	add r0, r0, #12
	ldr r4, [r0, #16]
	add r4, r4, #4
	str r4, [r0, #16]
	ldr lr, [r0, #20]
	subs lr, lr, #1
	str lr, [r0, #20]
	bne 263b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
270:
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
	bne 270b
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
271:
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
	bne 271b
	ldr r0, [sp, #0]
261:
	ldr r1, [r0, #200]
	add r1, r1, r1
	str r1, [r0, #200]
	ldr r1, [r0, #192]
	subs r1, r1, #1
	str r1, [r0, #192]
	bne 242b
	ldr r1, [r0, #128]
	add r1, r1, #1
	str r1, [r0, #128]
	ldr r1, [r0, #132]
	subs r1, r1, #1
	str r1, [r0, #132]
	bne 241b
	mov r2, #6
	mov r3, #6
	mov r12, #7
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
272:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 272b
	mov r0, r5
273:
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
	bne 274f
	b 275f
274:
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
275:
	cmp lr, #0
	bne 276f
	b 277f
276:
278:
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
	ldr r2, [r12, #4]
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	subs lr, lr, #2
	bne 278b
277:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr lr, [r0, #16]
	ldr r12, [r0, #24]
	ldr r1, [r0, #28]
	ldr r0, [r0, #44]
	ldr r2, [r0, #0]
	mul r1, r1, r2
	mov r11, #0
	ldr r2, [r12, #0]
	ldr r10, [r0, #0]
	movw r9, #65535
	and r3, r1, r9
	lsr r4, r1, #16
	and r5, r2, r9
	lsr r6, r2, #16
	mul r7, r3, r5
	mul r8, r4, r5
	add r8, r8, r7, lsr #16
	and r5, r8, r9
	mul r4, r4, r6
	add r4, r4, r8, lsr #16
	mul r3, r3, r6
	add r3, r3, r5
	add r4, r4, r3, lsr #16
	and r7, r7, r9
	add r3, r7, r3, lsl #16
	adds r3, r3, r10
	adc r4, r4, #0
	adds r3, r3, r11
	adc r4, r4, #0
	mov r11, r4
	add r12, r12, #4
	subs lr, lr, #1
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
279:
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 279b
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	add r0, r0, #8
	mov r3, #0
	str r3, [r0, #0]
	add r0, r0, #12
	ldr r4, [r0, #16]
	add r4, r4, #4
	str r4, [r0, #16]
	ldr lr, [r0, #20]
	subs lr, lr, #1
	str lr, [r0, #20]
	bne 273b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
280:
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
	bne 280b
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
281:
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
	bne 281b
	ldr r0, [sp, #0]
	mov r2, #6
	ldr r4, [sp, #4]
	ldr r6, [sp, #12]
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	mov lr, r6
	add r1, r1, r6
	sub r1, r1, #1
	mov r0, r4
282:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 282b
	mov r0, r5
	mov r0, r4
	mov lr, r6
	ldr r4, [sp, #48]
	mov r2, #0
	sub r2, r2, r4
283:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 283b
	mov r0, r4
	b 216f
215:
	ldr r0, [sp, #4]
	ldr lr, [sp, #12]
	mov r2, #0
284:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 284b
	mov r0, #0
216:
	b 28f
27:
	ldr r0, [sp, #4]
	ldr lr, [sp, #12]
	mov r2, #0
285:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 285b
	mov r0, #0
28:
	ldr r4, [sp, #16]
	ldr r5, [sp, #20]
	ldr r6, [sp, #24]
	ldr r7, [sp, #28]
	ldr r8, [sp, #32]
	ldr r9, [sp, #36]
	ldr r10, [sp, #40]
	ldr r11, [sp, #44]
	ldr lr, [sp, #52]
	ldr r12, [sp], #56
	bx lr
