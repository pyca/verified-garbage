// The functions of `src/internal/vg_rsa_private_crt.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_crt:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	add r12, sp, #0
	str r0, [r12, #4]
	ldr r0, [sp, #104]
	str r0, [r12, #0]
	mov r4, r2
	mov r6, r3
	ldrb r1, [r4, #0]
	add r2, r4, r6
	sub r2, r2, #1
	ldrb r2, [r2, #0]
	sub r7, r1, #1
	lsr r7, r7, #31
	sub r9, r6, #64
	lsl r9, r9, #8
	add r9, r9, r1
	sub r9, r9, #128
	lsr r9, r9, #31
	and r2, r2, #1
	eor r2, r2, #1
	orr r7, r7, r2
	orr r7, r7, r9
	subs r7, r7, #0
	beq 20f
	ldr r0, [sp, #4]
	ldr lr, [sp, #12]
	mov r2, #0
22:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 22b
	mov r0, #0
	b 21f
20:
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
23:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 23b
	mov r0, r8
	ldr r7, [r0, #48]
	lsl r1, r7, #7
	add r1, r1, #512
	mov r2, r0
	add r2, r2, r1
	str r2, [r0, #224]
	add r2, r2, r1
	str r2, [r0, #228]
	add r2, r2, r1
	str r2, [r0, #232]
	lsl r1, r7, #4
	add r1, r1, #8
	add r2, r2, r1
	str r2, [r0, #236]
	add r2, r2, r1
	str r2, [r0, #240]
	ldr r7, [r0, #48]
	ldr r2, [r0, #224]
	str r0, [r2, #216]
	mov r0, r2
	mov r3, #0
	str r7, [r0, #48]
	str r3, [r0, #52]
	mov r8, r0
	add r5, r7, #2
	lsl r5, r5, #3
	add r4, r0, #256
	add r0, r0, #64
	mov lr, #8
24:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 24b
	mov r0, r8
	ldr r0, [r0, #216]
	ldr r7, [r0, #48]
	ldr r2, [r0, #228]
	str r0, [r2, #216]
	mov r0, r2
	mov r3, #0
	str r7, [r0, #48]
	str r3, [r0, #52]
	mov r8, r0
	add r5, r7, #2
	lsl r5, r5, #3
	add r4, r0, #256
	add r0, r0, #64
	mov lr, #8
25:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 25b
	mov r0, r8
	ldr r0, [r0, #216]
	ldr r4, [sp, #8]
	ldr r6, [sp, #12]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
26:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 26b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
27:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 27b
	ldr r0, [sp, #0]
	add r12, sp, #8
	str r0, [r12, #0]
	ldr r4, [sp, #56]
	ldr r6, [sp, #12]
	mov r2, #1
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
28:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 28b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
29:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 29b
	ldr r0, [sp, #0]
	ldr r10, [r0, #72]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
210:
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
	bne 210b
	ldr r0, [sp, #0]
	add r12, sp, #48
	str r11, [r12, #0]
	ldr r0, [r0, #224]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r4, [sp, #64]
	ldr r6, [sp, #68]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
211:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 211b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
212:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 212b
	ldr r0, [sp, #0]
	ldr r4, [sp, #96]
	ldr r6, [sp, #100]
	mov r2, #1
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
213:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 213b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
214:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 214b
	ldr r0, [sp, #0]
	ldr r10, [r0, #72]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
215:
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
	bne 215b
	ldr r0, [sp, #0]
	add r12, sp, #48
	ldr r1, [r12, #0]
	and r11, r11, r1
	str r11, [r12, #0]
	ldr r0, [sp, #8]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [r0, #228]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r4, [sp, #72]
	ldr r6, [sp, #76]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
216:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 216b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
217:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 217b
	ldr r0, [sp, #0]
	ldr r0, [sp, #8]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #2
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #232]
218:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 218b
	ldr r0, [sp, #0]
	ldr r1, [r0, #224]
	ldr r1, [r1, #64]
	str r1, [r0, #128]
	ldr r1, [r0, #228]
	ldr r1, [r1, #64]
	str r1, [r0, #132]
	ldr r1, [r0, #232]
	str r1, [r0, #136]
	ldr r1, [r0, #48]
	add r1, r1, r1
	str r1, [r0, #140]
	str r1, [r0, #144]
219:
	ldr r12, [r0, #132]
	ldr lr, [r0, #144]
	ldr r1, [r0, #128]
	ldr r1, [r1, #0]
	mov r11, #0
	ldr r0, [r0, #136]
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
	and r2, lr, #1
	cmp r2, #0
	bne 220f
	b 221f
220:
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
221:
	cmp lr, #0
	bne 222f
	b 223f
222:
224:
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
	bne 224b
223:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [r0, #128]
	add r1, r1, #4
	str r1, [r0, #128]
	ldr r1, [r0, #136]
	add r1, r1, #4
	str r1, [r0, #136]
	ldr r1, [r0, #140]
	subs r1, r1, #1
	str r1, [r0, #140]
	bne 219b
	ldr lr, [r0, #48]
	lsl lr, lr, #2
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #240]
225:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 225b
	ldr r0, [sp, #0]
	ldr r4, [r0, #240]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
226:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 226b
	mov r0, r5
	ldr r10, [r0, #232]
	ldr r12, [r0, #240]
	ldr lr, [r0, #48]
	lsl lr, lr, #2
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #236]
	mov r8, lr
	mov r11, #0
227:
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
	bne 227b
	mov r6, r11
	mov r7, r10
	mov r10, r12
	mov r12, r7
	sub r0, r0, r8, lsl #2
	sub r10, r10, r8, lsl #2
	sub r12, r12, r8, lsl #2
	mov lr, r8
	mov r11, #0
228:
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
	bne 228b
	orr r11, r11, r6
	eor r11, r11, #1
	ldr r0, [sp, #0]
	add r12, sp, #48
	ldr r1, [r12, #0]
	and r11, r11, r1
	str r11, [r12, #0]
	ldr r0, [r0, #224]
	add r12, sp, #0
	str r0, [r12, #0]
	add r12, sp, #48
	ldr r11, [r12, #0]
	str r11, [r0, #212]
	mov r2, #7
	mov r5, #3
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
229:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 229b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r11, [r0, #212]
	ldr r10, [r0, #120]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #64]
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
	mov r2, #4
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
231:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 231b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	mov r2, #7
	mov r5, #2
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
232:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 232b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
233:
	mov r2, #4
	mov r3, #7
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
234:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 234b
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
	bne 235f
	b 236f
235:
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
236:
	cmp lr, #0
	bne 237f
	b 238f
237:
239:
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
	bne 239b
238:
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
240:
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
	bne 240b
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
241:
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
	bne 241b
	ldr r0, [sp, #0]
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 233b
	mov r2, #4
	mov r3, #4
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
242:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 242b
243:
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
	bne 244f
	b 245f
244:
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
245:
	cmp lr, #0
	bne 246f
	b 247f
246:
248:
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
	bne 248b
247:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 243b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
249:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 249b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
250:
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
	bne 250b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
251:
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
	bne 252f
	b 253f
252:
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
253:
	cmp lr, #0
	bne 254f
	b 255f
254:
256:
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
	bne 256b
255:
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
	bne 251b
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
257:
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
	bne 257b
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
258:
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
	bne 258b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
259:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 259b
260:
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
	bne 261f
	b 262f
261:
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
262:
	cmp lr, #0
	bne 263f
	b 264f
263:
265:
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
	bne 265b
264:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 260b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
266:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 266b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
267:
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
	bne 267b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
268:
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
	bne 269f
	b 270f
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
	ldr r5, [r0, #0]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
270:
	cmp lr, #0
	bne 271f
	b 272f
271:
273:
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
	bne 273b
272:
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
	bne 268b
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
274:
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
	bne 274b
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
275:
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
	bne 275b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
276:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 276b
277:
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
	bne 278f
	b 279f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
279:
	cmp lr, #0
	bne 280f
	b 281f
280:
282:
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
	bne 282b
281:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 277b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
283:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 283b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
284:
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
	bne 284b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
285:
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
	bne 286f
	b 287f
286:
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
287:
	cmp lr, #0
	bne 288f
	b 289f
288:
290:
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
	bne 290b
289:
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
	bne 285b
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
291:
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
	bne 291b
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
292:
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
	bne 292b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
293:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 293b
294:
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
	bne 295f
	b 296f
295:
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
296:
	cmp lr, #0
	bne 297f
	b 298f
297:
299:
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
	bne 299b
298:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 294b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2100:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2100b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2101:
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
	bne 2101b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2102:
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
	bne 2103f
	b 2104f
2103:
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
2104:
	cmp lr, #0
	bne 2105f
	b 2106f
2105:
2107:
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
	bne 2107b
2106:
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
	bne 2102b
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
2108:
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
	bne 2108b
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
2109:
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
	bne 2109b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2110:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2110b
2111:
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
	bne 2112f
	b 2113f
2112:
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
2113:
	cmp lr, #0
	bne 2114f
	b 2115f
2114:
2116:
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
	bne 2116b
2115:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2111b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2117:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2117b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2118:
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
	bne 2118b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2119:
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
	bne 2120f
	b 2121f
2120:
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
2121:
	cmp lr, #0
	bne 2122f
	b 2123f
2122:
2124:
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
	bne 2124b
2123:
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
	bne 2119b
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
2125:
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
	bne 2125b
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
2126:
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
	bne 2126b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2127:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2127b
2128:
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
	bne 2129f
	b 2130f
2129:
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
2130:
	cmp lr, #0
	bne 2131f
	b 2132f
2131:
2133:
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
	bne 2133b
2132:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2128b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2134:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2134b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2135:
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
	bne 2135b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2136:
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
	bne 2137f
	b 2138f
2137:
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
2138:
	cmp lr, #0
	bne 2139f
	b 2140f
2139:
2141:
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
	bne 2141b
2140:
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
	bne 2136b
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
2142:
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
	bne 2142b
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
2143:
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
	bne 2143b
	ldr r0, [sp, #0]
	ldr r4, [sp, #56]
	ldr r6, [sp, #12]
	mov r2, #1
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
2144:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2144b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2145:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2145b
	ldr r0, [sp, #0]
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2146:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2146b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	mov r2, #1
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
2147:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2147b
	mov r0, r5
2148:
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
	bne 2149f
	b 2150f
2149:
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
2150:
	cmp lr, #0
	bne 2151f
	b 2152f
2151:
2153:
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
	bne 2153b
2152:
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
2154:
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
	bne 2154b
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
	bne 2148b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2155:
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
	bne 2155b
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
2156:
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
	bne 2156b
	ldr r0, [sp, #0]
	mov r2, #1
	mov r3, #1
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
2157:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2157b
	mov r0, r5
2158:
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
	bne 2159f
	b 2160f
2159:
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
2160:
	cmp lr, #0
	bne 2161f
	b 2162f
2161:
2163:
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
	bne 2163b
2162:
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
2164:
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
	bne 2164b
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
	bne 2158b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2165:
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
	bne 2165b
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
2166:
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
	bne 2166b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #112]
2167:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2167b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r0, [r1, #240]
	ldr r2, [r1, #48]
	lsl r2, r2, #4
	add r2, r2, #8
	add r0, r0, r2
	ldr r7, [sp, #68]
	add r7, r7, #7
	lsr r7, r7, #3
	sub r1, r7, #2
	lsr r1, r1, #31
	add r7, r7, r1
	mov r3, #0
	str r7, [r0, #48]
	str r3, [r0, #52]
	mov r8, r0
	add r5, r7, #2
	lsl r5, r5, #3
	add r4, r0, #256
	add r0, r0, #64
	mov lr, #8
2168:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 2168b
	mov r0, r8
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r4, [sp, #64]
	ldr r6, [sp, #68]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
2169:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2169b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2170:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2170b
	ldr r0, [sp, #0]
	add r12, sp, #48
	ldr r11, [r12, #0]
	str r11, [r0, #212]
	mov r2, #7
	mov r5, #3
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2171:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2171b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r11, [r0, #212]
	ldr r10, [r0, #120]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #64]
	mov r4, #0
	sub r4, r4, r11
2172:
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
	bne 2172b
	ldr r0, [sp, #0]
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
	mov r2, #4
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2173:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2173b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	mov r2, #7
	mov r5, #2
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2174:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2174b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
2175:
	mov r2, #4
	mov r3, #7
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
2176:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2176b
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
	bne 2177f
	b 2178f
2177:
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
2178:
	cmp lr, #0
	bne 2179f
	b 2180f
2179:
2181:
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
	bne 2181b
2180:
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
2182:
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
	bne 2182b
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
2183:
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
	bne 2183b
	ldr r0, [sp, #0]
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 2175b
	mov r2, #4
	mov r3, #4
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
2184:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2184b
2185:
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
	bne 2186f
	b 2187f
2186:
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
2187:
	cmp lr, #0
	bne 2188f
	b 2189f
2188:
2190:
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
	bne 2190b
2189:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2185b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2191:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2191b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2192:
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
	bne 2192b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2193:
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
	bne 2194f
	b 2195f
2194:
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
2195:
	cmp lr, #0
	bne 2196f
	b 2197f
2196:
2198:
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
	bne 2198b
2197:
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
	bne 2193b
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
2199:
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
	bne 2199b
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
2200:
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
	bne 2200b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2201:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2201b
2202:
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
	bne 2203f
	b 2204f
2203:
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
2204:
	cmp lr, #0
	bne 2205f
	b 2206f
2205:
2207:
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
	bne 2207b
2206:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2202b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2208:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2208b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2209:
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
	bne 2209b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2210:
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
	bne 2211f
	b 2212f
2211:
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
2212:
	cmp lr, #0
	bne 2213f
	b 2214f
2213:
2215:
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
	bne 2215b
2214:
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
	bne 2210b
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
2216:
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
	bne 2216b
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
2217:
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
	bne 2217b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2218:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2218b
2219:
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
	bne 2220f
	b 2221f
2220:
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
2221:
	cmp lr, #0
	bne 2222f
	b 2223f
2222:
2224:
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
	bne 2224b
2223:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2219b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2225:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2225b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2226:
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
	bne 2226b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2227:
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
	bne 2228f
	b 2229f
2228:
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
2229:
	cmp lr, #0
	bne 2230f
	b 2231f
2230:
2232:
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
	bne 2232b
2231:
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
	bne 2227b
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
2233:
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
	bne 2233b
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
2234:
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
	bne 2234b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2235:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2235b
2236:
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
	bne 2237f
	b 2238f
2237:
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
2238:
	cmp lr, #0
	bne 2239f
	b 2240f
2239:
2241:
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
	bne 2241b
2240:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2236b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2242:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2242b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2243:
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
	bne 2243b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2244:
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
	bne 2245f
	b 2246f
2245:
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
2246:
	cmp lr, #0
	bne 2247f
	b 2248f
2247:
2249:
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
	bne 2249b
2248:
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
	bne 2244b
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
2250:
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
	bne 2250b
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
2251:
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
	bne 2251b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2252:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2252b
2253:
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
	bne 2254f
	b 2255f
2254:
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
2255:
	cmp lr, #0
	bne 2256f
	b 2257f
2256:
2258:
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
	bne 2258b
2257:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2253b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2259:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2259b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2260:
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
	bne 2260b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2261:
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
	bne 2262f
	b 2263f
2262:
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
2263:
	cmp lr, #0
	bne 2264f
	b 2265f
2264:
2266:
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
	bne 2266b
2265:
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
	bne 2261b
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
2267:
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
	bne 2267b
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
2268:
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
	bne 2268b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2269:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2269b
2270:
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
	bne 2271f
	b 2272f
2271:
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
2272:
	cmp lr, #0
	bne 2273f
	b 2274f
2273:
2275:
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
	bne 2275b
2274:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2270b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2276:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2276b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2277:
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
	bne 2277b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2278:
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
	bne 2279f
	b 2280f
2279:
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
2280:
	cmp lr, #0
	bne 2281f
	b 2282f
2281:
2283:
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
	bne 2283b
2282:
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
	bne 2278b
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
2284:
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
	bne 2284b
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
2285:
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
	bne 2285b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #72]
	ldr r4, [r0, #72]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2286:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2286b
	mov r0, r5
	ldr r1, [sp, #80]
	ldr r2, [sp, #84]
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
2287:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2287b
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
2288:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2288b
	mov r0, r5
2289:
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
	bne 2290f
	b 2291f
2290:
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
2291:
	cmp lr, #0
	bne 2292f
	b 2293f
2292:
2294:
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
	bne 2294b
2293:
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
2295:
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
	bne 2295b
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
	bne 2289b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2296:
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
	bne 2296b
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
2297:
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
	bne 2297b
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
2298:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2298b
	mov r0, r5
2299:
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
	bne 2300f
	b 2301f
2300:
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
2301:
	cmp lr, #0
	bne 2302f
	b 2303f
2302:
2304:
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
	bne 2304b
2303:
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
2305:
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
	bne 2305b
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
	bne 2299b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2306:
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
	bne 2306b
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
2307:
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
	bne 2307b
	ldr r0, [sp, #0]
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
	mov r11, #1
	ldr r12, [r0, #112]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #220]
	mov r10, r0
	mov r4, #0
	sub r4, r4, r11
2308:
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
	bne 2308b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	mov r11, #1
	ldr r12, [r0, #104]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #220]
	mov r10, r0
	mov r4, #0
	sub r4, r4, r11
2309:
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
	bne 2309b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	mov r11, #1
	ldr r10, [r0, #72]
	ldr r12, [r0, #104]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r4, #0
	sub r4, r4, r11
2310:
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
	bne 2310b
	ldr r0, [sp, #0]
2311:
	mov r2, #1
	mov r3, #1
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
2312:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2312b
	mov r0, r5
2313:
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
	bne 2314f
	b 2315f
2314:
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
2315:
	cmp lr, #0
	bne 2316f
	b 2317f
2316:
2318:
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
	bne 2318b
2317:
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
2319:
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
	bne 2319b
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
	bne 2313b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2320:
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
	bne 2320b
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
2321:
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
	bne 2321b
	ldr r0, [sp, #0]
	mov r11, #1
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #220]
	mov r10, r0
	mov r4, #0
	sub r4, r4, r11
2322:
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
	bne 2322b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	bne 2311b
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
2323:
	ldr r2, [r0, #128]
	ldrb r1, [r2, #0]
	str r1, [r0, #200]
	mov r1, #8
	str r1, [r0, #192]
2324:
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
2325:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2325b
2326:
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
	bne 2327f
	b 2328f
2327:
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
2328:
	cmp lr, #0
	bne 2329f
	b 2330f
2329:
2331:
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
	bne 2331b
2330:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2326b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2332:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2332b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2333:
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
	bne 2333b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2334:
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
	bne 2335f
	b 2336f
2335:
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
2336:
	cmp lr, #0
	bne 2337f
	b 2338f
2337:
2339:
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
	bne 2339b
2338:
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
	bne 2334b
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
2340:
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
	bne 2340b
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
2341:
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
	bne 2341b
	ldr r0, [sp, #0]
	ldr r1, [r0, #200]
	lsr r1, r1, #7
	and r1, r1, #1
	ldr r2, [r0, #196]
	add r2, r1, r2, lsl #1
	str r2, [r0, #196]
	ldr r1, [r0, #204]
	add r1, r1, #1
	str r1, [r0, #204]
	cmp r1, #3
	beq 2342f
	b 2343f
2342:
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
2344:
	ldr r1, [r0, #196]
	ldr r2, [r0, #228]
	eor r11, r1, r2
	sub r11, r11, #1
	lsr r11, r11, #31
	ldr r10, [r0, #72]
	ldr r12, [r0, #220]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r4, #0
	sub r4, r4, r11
2345:
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
	bne 2345b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	bne 2344b
	mov r2, #6
	mov r3, #6
	mov r12, #1
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
2346:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2346b
	mov r0, r5
2347:
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
	bne 2348f
	b 2349f
2348:
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
2349:
	cmp lr, #0
	bne 2350f
	b 2351f
2350:
2352:
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
	bne 2352b
2351:
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
2353:
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
	bne 2353b
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
	bne 2347b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2354:
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
	bne 2354b
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
2355:
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
	bne 2355b
	ldr r0, [sp, #0]
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
2343:
	ldr r1, [r0, #200]
	add r1, r1, r1
	str r1, [r0, #200]
	ldr r1, [r0, #192]
	subs r1, r1, #1
	str r1, [r0, #192]
	bne 2324b
	ldr r1, [r0, #128]
	add r1, r1, #1
	str r1, [r0, #128]
	ldr r1, [r0, #132]
	subs r1, r1, #1
	str r1, [r0, #132]
	bne 2323b
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
2356:
	ldr r1, [r0, #196]
	ldr r2, [r0, #228]
	eor r11, r1, r2
	sub r11, r11, #1
	lsr r11, r11, #31
	ldr r10, [r0, #72]
	ldr r12, [r0, #220]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r4, #0
	sub r4, r4, r11
2357:
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
	bne 2357b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	bne 2356b
	mov r2, #6
	mov r3, #6
	mov r12, #1
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
2358:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2358b
	mov r0, r5
2359:
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
	bne 2360f
	b 2361f
2360:
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
2361:
	cmp lr, #0
	bne 2362f
	b 2363f
2362:
2364:
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
	bne 2364b
2363:
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
2365:
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
	bne 2365b
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
	bne 2359b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2366:
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
	bne 2366b
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
2367:
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
	bne 2367b
	ldr r0, [sp, #0]
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
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
2368:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2368b
	mov r0, r5
2369:
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
	bne 2370f
	b 2371f
2370:
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
2371:
	cmp lr, #0
	bne 2372f
	b 2373f
2372:
2374:
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
	bne 2374b
2373:
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
2375:
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
	bne 2375b
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
	bne 2369b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2376:
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
	bne 2376b
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
2377:
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
	bne 2377b
	ldr r0, [sp, #0]
	mov r1, r0
	ldr r0, [sp, #8]
	ldr r0, [r0, #224]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r4, [r0, #112]
	mov r0, r1
	mov r2, #6
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2378:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2378b
	mov r0, r5
	ldr r0, [sp, #0]
	ldr r0, [sp, #8]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [r0, #228]
	add r12, sp, #0
	str r0, [r12, #0]
	add r12, sp, #48
	ldr r11, [r12, #0]
	str r11, [r0, #212]
	mov r2, #7
	mov r5, #3
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2379:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2379b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r11, [r0, #212]
	ldr r10, [r0, #120]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #64]
	mov r4, #0
	sub r4, r4, r11
2380:
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
	bne 2380b
	ldr r0, [sp, #0]
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
	mov r2, #4
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2381:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2381b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	mov r2, #7
	mov r5, #2
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2382:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2382b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
2383:
	mov r2, #4
	mov r3, #7
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
2384:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2384b
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
	bne 2385f
	b 2386f
2385:
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
2386:
	cmp lr, #0
	bne 2387f
	b 2388f
2387:
2389:
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
	bne 2389b
2388:
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
2390:
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
	bne 2390b
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
2391:
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
	bne 2391b
	ldr r0, [sp, #0]
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 2383b
	mov r2, #4
	mov r3, #4
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
2392:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2392b
2393:
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
	bne 2394f
	b 2395f
2394:
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
2395:
	cmp lr, #0
	bne 2396f
	b 2397f
2396:
2398:
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
	bne 2398b
2397:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2393b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2399:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2399b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2400:
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
	bne 2400b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2401:
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
	bne 2402f
	b 2403f
2402:
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
2403:
	cmp lr, #0
	bne 2404f
	b 2405f
2404:
2406:
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
	bne 2406b
2405:
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
	bne 2401b
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
2407:
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
	bne 2407b
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
2408:
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
	bne 2408b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2409:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2409b
2410:
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
	bne 2411f
	b 2412f
2411:
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
2412:
	cmp lr, #0
	bne 2413f
	b 2414f
2413:
2415:
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
	bne 2415b
2414:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2410b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2416:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2416b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2417:
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
	bne 2417b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2418:
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
	bne 2419f
	b 2420f
2419:
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
2420:
	cmp lr, #0
	bne 2421f
	b 2422f
2421:
2423:
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
	bne 2423b
2422:
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
	bne 2418b
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
2424:
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
	bne 2424b
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
2425:
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
	bne 2425b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2426:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2426b
2427:
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
	bne 2428f
	b 2429f
2428:
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
2429:
	cmp lr, #0
	bne 2430f
	b 2431f
2430:
2432:
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
	bne 2432b
2431:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2427b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2433:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2433b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2434:
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
	bne 2434b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2435:
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
	bne 2436f
	b 2437f
2436:
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
2437:
	cmp lr, #0
	bne 2438f
	b 2439f
2438:
2440:
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
	bne 2440b
2439:
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
	bne 2435b
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
2441:
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
	bne 2441b
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
2442:
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
	bne 2442b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2443:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2443b
2444:
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
	bne 2445f
	b 2446f
2445:
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
2446:
	cmp lr, #0
	bne 2447f
	b 2448f
2447:
2449:
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
	bne 2449b
2448:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2444b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2450:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2450b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2451:
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
	bne 2451b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2452:
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
	bne 2453f
	b 2454f
2453:
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
2454:
	cmp lr, #0
	bne 2455f
	b 2456f
2455:
2457:
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
	bne 2457b
2456:
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
	bne 2452b
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
2458:
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
	bne 2458b
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
2459:
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
	bne 2459b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2460:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2460b
2461:
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
	bne 2462f
	b 2463f
2462:
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
2463:
	cmp lr, #0
	bne 2464f
	b 2465f
2464:
2466:
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
	bne 2466b
2465:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2461b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2467:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2467b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2468:
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
	bne 2468b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2469:
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
	bne 2470f
	b 2471f
2470:
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
2471:
	cmp lr, #0
	bne 2472f
	b 2473f
2472:
2474:
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
	bne 2474b
2473:
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
	bne 2469b
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
2475:
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
	bne 2475b
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
2476:
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
	bne 2476b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2477:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2477b
2478:
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
	bne 2479f
	b 2480f
2479:
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
2480:
	cmp lr, #0
	bne 2481f
	b 2482f
2481:
2483:
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
	bne 2483b
2482:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2478b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2484:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2484b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2485:
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
	bne 2485b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2486:
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
	bne 2487f
	b 2488f
2487:
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
2488:
	cmp lr, #0
	bne 2489f
	b 2490f
2489:
2491:
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
	bne 2491b
2490:
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
	bne 2486b
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
2492:
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
	bne 2492b
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
2493:
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
	bne 2493b
	ldr r0, [sp, #0]
	ldr r4, [sp, #56]
	ldr r6, [sp, #12]
	mov r2, #1
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
2494:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2494b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2495:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2495b
	ldr r0, [sp, #0]
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2496:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2496b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	mov r2, #1
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
2497:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2497b
	mov r0, r5
2498:
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
	bne 2499f
	b 2500f
2499:
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
2500:
	cmp lr, #0
	bne 2501f
	b 2502f
2501:
2503:
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
	bne 2503b
2502:
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
2504:
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
	bne 2504b
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
	bne 2498b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2505:
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
	bne 2505b
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
2506:
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
	bne 2506b
	ldr r0, [sp, #0]
	mov r2, #1
	mov r3, #1
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
2507:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2507b
	mov r0, r5
2508:
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
	bne 2509f
	b 2510f
2509:
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
2510:
	cmp lr, #0
	bne 2511f
	b 2512f
2511:
2513:
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
	bne 2513b
2512:
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
2514:
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
	bne 2514b
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
	bne 2508b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2515:
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
	bne 2515b
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
2516:
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
	bne 2516b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #112]
2517:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2517b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r0, [r1, #240]
	ldr r2, [r1, #48]
	lsl r2, r2, #4
	add r2, r2, #8
	add r0, r0, r2
	ldr r7, [sp, #76]
	add r7, r7, #7
	lsr r7, r7, #3
	sub r1, r7, #2
	lsr r1, r1, #31
	add r7, r7, r1
	mov r3, #0
	str r7, [r0, #48]
	str r3, [r0, #52]
	mov r8, r0
	add r5, r7, #2
	lsl r5, r5, #3
	add r4, r0, #256
	add r0, r0, #64
	mov lr, #8
2518:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 2518b
	mov r0, r8
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r4, [sp, #72]
	ldr r6, [sp, #76]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
2519:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2519b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2520:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2520b
	ldr r0, [sp, #0]
	add r12, sp, #48
	ldr r11, [r12, #0]
	str r11, [r0, #212]
	mov r2, #7
	mov r5, #3
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2521:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2521b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r11, [r0, #212]
	ldr r10, [r0, #120]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #64]
	mov r4, #0
	sub r4, r4, r11
2522:
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
	bne 2522b
	ldr r0, [sp, #0]
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
	mov r2, #4
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2523:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2523b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	mov r2, #7
	mov r5, #2
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2524:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2524b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
2525:
	mov r2, #4
	mov r3, #7
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
2526:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2526b
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
	bne 2527f
	b 2528f
2527:
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
2528:
	cmp lr, #0
	bne 2529f
	b 2530f
2529:
2531:
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
	bne 2531b
2530:
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
2532:
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
	bne 2532b
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
2533:
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
	bne 2533b
	ldr r0, [sp, #0]
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 2525b
	mov r2, #4
	mov r3, #4
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
2534:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2534b
2535:
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
	bne 2536f
	b 2537f
2536:
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
2537:
	cmp lr, #0
	bne 2538f
	b 2539f
2538:
2540:
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
	bne 2540b
2539:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2535b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2541:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2541b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2542:
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
	bne 2542b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2543:
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
	bne 2544f
	b 2545f
2544:
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
2545:
	cmp lr, #0
	bne 2546f
	b 2547f
2546:
2548:
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
	bne 2548b
2547:
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
	bne 2543b
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
2549:
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
	bne 2549b
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
2550:
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
	bne 2550b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2551:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2551b
2552:
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
	bne 2553f
	b 2554f
2553:
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
2554:
	cmp lr, #0
	bne 2555f
	b 2556f
2555:
2557:
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
	bne 2557b
2556:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2552b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2558:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2558b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2559:
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
	bne 2559b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2560:
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
	bne 2561f
	b 2562f
2561:
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
2562:
	cmp lr, #0
	bne 2563f
	b 2564f
2563:
2565:
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
	bne 2565b
2564:
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
	bne 2560b
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
2566:
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
	bne 2566b
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
2567:
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
	bne 2567b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2568:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2568b
2569:
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
	bne 2570f
	b 2571f
2570:
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
2571:
	cmp lr, #0
	bne 2572f
	b 2573f
2572:
2574:
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
	bne 2574b
2573:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2569b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2575:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2575b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2576:
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
	bne 2576b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2577:
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
	bne 2578f
	b 2579f
2578:
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
2579:
	cmp lr, #0
	bne 2580f
	b 2581f
2580:
2582:
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
	bne 2582b
2581:
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
	bne 2577b
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
2583:
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
	bne 2583b
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
2584:
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
	bne 2584b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2585:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2585b
2586:
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
	bne 2587f
	b 2588f
2587:
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
2588:
	cmp lr, #0
	bne 2589f
	b 2590f
2589:
2591:
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
	bne 2591b
2590:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2586b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2592:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2592b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2593:
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
	bne 2593b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2594:
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
	bne 2595f
	b 2596f
2595:
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
2596:
	cmp lr, #0
	bne 2597f
	b 2598f
2597:
2599:
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
	bne 2599b
2598:
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
	bne 2594b
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
2600:
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
	bne 2600b
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
2601:
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
	bne 2601b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2602:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2602b
2603:
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
	bne 2604f
	b 2605f
2604:
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
2605:
	cmp lr, #0
	bne 2606f
	b 2607f
2606:
2608:
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
	bne 2608b
2607:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2603b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2609:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2609b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2610:
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
	bne 2610b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2611:
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
	bne 2612f
	b 2613f
2612:
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
2613:
	cmp lr, #0
	bne 2614f
	b 2615f
2614:
2616:
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
	bne 2616b
2615:
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
	bne 2611b
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
2617:
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
	bne 2617b
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
2618:
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
	bne 2618b
	ldr r0, [sp, #0]
	mov r2, #4
	mov r3, #4
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
2619:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2619b
2620:
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
	bne 2621f
	b 2622f
2621:
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
2622:
	cmp lr, #0
	bne 2623f
	b 2624f
2623:
2625:
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
	bne 2625b
2624:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2620b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2626:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2626b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2627:
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
	bne 2627b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2628:
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
	bne 2629f
	b 2630f
2629:
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
2630:
	cmp lr, #0
	bne 2631f
	b 2632f
2631:
2633:
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
	bne 2633b
2632:
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
	bne 2628b
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
2634:
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
	bne 2634b
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
2635:
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
	bne 2635b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #228]
	ldr r1, [r1, #72]
	ldr r4, [r0, #72]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2636:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2636b
	mov r0, r5
	ldr r1, [sp, #88]
	ldr r2, [sp, #92]
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
2637:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2637b
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
2638:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2638b
	mov r0, r5
2639:
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
	bne 2640f
	b 2641f
2640:
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
2641:
	cmp lr, #0
	bne 2642f
	b 2643f
2642:
2644:
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
	bne 2644b
2643:
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
2645:
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
	bne 2645b
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
	bne 2639b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2646:
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
	bne 2646b
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
2647:
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
	bne 2647b
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
2648:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2648b
	mov r0, r5
2649:
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
	bne 2650f
	b 2651f
2650:
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
2651:
	cmp lr, #0
	bne 2652f
	b 2653f
2652:
2654:
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
	bne 2654b
2653:
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
2655:
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
	bne 2655b
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
	bne 2649b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2656:
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
	bne 2656b
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
2657:
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
	bne 2657b
	ldr r0, [sp, #0]
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
	mov r11, #1
	ldr r12, [r0, #112]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #220]
	mov r10, r0
	mov r4, #0
	sub r4, r4, r11
2658:
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
	bne 2658b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	mov r11, #1
	ldr r12, [r0, #104]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #220]
	mov r10, r0
	mov r4, #0
	sub r4, r4, r11
2659:
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
	bne 2659b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	mov r11, #1
	ldr r10, [r0, #72]
	ldr r12, [r0, #104]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r4, #0
	sub r4, r4, r11
2660:
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
	bne 2660b
	ldr r0, [sp, #0]
2661:
	mov r2, #1
	mov r3, #1
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
2662:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2662b
	mov r0, r5
2663:
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
	bne 2664f
	b 2665f
2664:
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
2665:
	cmp lr, #0
	bne 2666f
	b 2667f
2666:
2668:
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
	bne 2668b
2667:
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
2669:
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
	bne 2669b
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
	bne 2663b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2670:
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
	bne 2670b
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
2671:
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
	bne 2671b
	ldr r0, [sp, #0]
	mov r11, #1
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #220]
	mov r10, r0
	mov r4, #0
	sub r4, r4, r11
2672:
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
	bne 2672b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	bne 2661b
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
2673:
	ldr r2, [r0, #128]
	ldrb r1, [r2, #0]
	str r1, [r0, #200]
	mov r1, #8
	str r1, [r0, #192]
2674:
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
2675:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2675b
2676:
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
	bne 2677f
	b 2678f
2677:
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
2678:
	cmp lr, #0
	bne 2679f
	b 2680f
2679:
2681:
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
	bne 2681b
2680:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2676b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2682:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2682b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2683:
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
	bne 2683b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2684:
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
	bne 2685f
	b 2686f
2685:
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
2686:
	cmp lr, #0
	bne 2687f
	b 2688f
2687:
2689:
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
	bne 2689b
2688:
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
	bne 2684b
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
2690:
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
	bne 2690b
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
2691:
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
	bne 2691b
	ldr r0, [sp, #0]
	ldr r1, [r0, #200]
	lsr r1, r1, #7
	and r1, r1, #1
	ldr r2, [r0, #196]
	add r2, r1, r2, lsl #1
	str r2, [r0, #196]
	ldr r1, [r0, #204]
	add r1, r1, #1
	str r1, [r0, #204]
	cmp r1, #3
	beq 2692f
	b 2693f
2692:
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
2694:
	ldr r1, [r0, #196]
	ldr r2, [r0, #228]
	eor r11, r1, r2
	sub r11, r11, #1
	lsr r11, r11, #31
	ldr r10, [r0, #72]
	ldr r12, [r0, #220]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r4, #0
	sub r4, r4, r11
2695:
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
	bne 2695b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	bne 2694b
	mov r2, #6
	mov r3, #6
	mov r12, #1
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
2696:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2696b
	mov r0, r5
2697:
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
	bne 2698f
	b 2699f
2698:
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
2699:
	cmp lr, #0
	bne 2700f
	b 2701f
2700:
2702:
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
	bne 2702b
2701:
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
2703:
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
	bne 2703b
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
	bne 2697b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2704:
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
	bne 2704b
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
2705:
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
	bne 2705b
	ldr r0, [sp, #0]
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
2693:
	ldr r1, [r0, #200]
	add r1, r1, r1
	str r1, [r0, #200]
	ldr r1, [r0, #192]
	subs r1, r1, #1
	str r1, [r0, #192]
	bne 2674b
	ldr r1, [r0, #128]
	add r1, r1, #1
	str r1, [r0, #128]
	ldr r1, [r0, #132]
	subs r1, r1, #1
	str r1, [r0, #132]
	bne 2673b
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
2706:
	ldr r1, [r0, #196]
	ldr r2, [r0, #228]
	eor r11, r1, r2
	sub r11, r11, #1
	lsr r11, r11, #31
	ldr r10, [r0, #72]
	ldr r12, [r0, #220]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r4, #0
	sub r4, r4, r11
2707:
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
	bne 2707b
	ldr r0, [sp, #0]
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	bne 2706b
	mov r2, #6
	mov r3, #6
	mov r12, #1
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
2708:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2708b
	mov r0, r5
2709:
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
	bne 2710f
	b 2711f
2710:
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
2711:
	cmp lr, #0
	bne 2712f
	b 2713f
2712:
2714:
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
	bne 2714b
2713:
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
2715:
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
	bne 2715b
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
	bne 2709b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2716:
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
	bne 2716b
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
2717:
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
	bne 2717b
	ldr r0, [sp, #0]
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
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
2718:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2718b
	mov r0, r5
2719:
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
	bne 2720f
	b 2721f
2720:
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
2721:
	cmp lr, #0
	bne 2722f
	b 2723f
2722:
2724:
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
	bne 2724b
2723:
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
2725:
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
	bne 2725b
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
	bne 2719b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2726:
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
	bne 2726b
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
2727:
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
	bne 2727b
	ldr r0, [sp, #0]
	mov r1, r0
	ldr r0, [sp, #8]
	ldr r0, [r0, #228]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r4, [r0, #112]
	mov r0, r1
	mov r2, #6
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2728:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2728b
	mov r0, r5
	ldr r0, [sp, #0]
	ldr r0, [sp, #8]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [r0, #224]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #228]
	ldr r4, [r0, #72]
	mov r0, r1
	mov r2, #6
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2729:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2729b
	mov r0, r5
	ldr r0, [sp, #0]
	mov r2, #1
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
2730:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2730b
	mov r0, r5
2731:
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
	bne 2732f
	b 2733f
2732:
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
2733:
	cmp lr, #0
	bne 2734f
	b 2735f
2734:
2736:
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
	bne 2736b
2735:
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
2737:
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
	bne 2737b
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
	bne 2731b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2738:
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
	bne 2738b
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
2739:
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
	bne 2739b
	ldr r0, [sp, #0]
	mov r2, #1
	mov r3, #1
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
2740:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2740b
	mov r0, r5
2741:
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
	bne 2742f
	b 2743f
2742:
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
2743:
	cmp lr, #0
	bne 2744f
	b 2745f
2744:
2746:
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
	bne 2746b
2745:
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
2747:
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
	bne 2747b
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
	bne 2741b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2748:
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
	bne 2748b
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
2749:
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
	bne 2749b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #104]
2750:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2750b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #112]
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #104]
	mov r7, r0
	mov r8, lr
	mov r11, #0
2751:
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
	bne 2751b
	mov r1, r11
	mov r0, r7
	mov r12, r9
	mov lr, r8
	mov r11, #0
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
	and r2, lr, #1
	cmp r2, #0
	bne 2752f
	b 2753f
2752:
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
2753:
	cmp lr, #0
	bne 2754f
	b 2755f
2754:
2756:
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
	bne 2756b
2755:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r4, [sp, #96]
	ldr r6, [sp, #100]
	mov r2, #1
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
2757:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2757b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2758:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2758b
	ldr r0, [sp, #0]
	mov r2, #1
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
2759:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2759b
	mov r0, r5
2760:
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
	bne 2761f
	b 2762f
2761:
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
2762:
	cmp lr, #0
	bne 2763f
	b 2764f
2763:
2765:
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
	bne 2765b
2764:
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
2766:
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
	bne 2766b
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
	bne 2760b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2767:
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
	bne 2767b
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
2768:
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
	bne 2768b
	ldr r0, [sp, #0]
	mov r2, #5
	mov r3, #5
	mov r12, #1
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
2769:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2769b
	mov r0, r5
2770:
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
	bne 2771f
	b 2772f
2771:
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
2772:
	cmp lr, #0
	bne 2773f
	b 2774f
2773:
2775:
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
	bne 2775b
2774:
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
2776:
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
	bne 2776b
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
	bne 2770b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2777:
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
	bne 2777b
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
2778:
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
	bne 2778b
	ldr r0, [sp, #0]
	ldr r0, [sp, #8]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #228]
	ldr r4, [r0, #72]
	mov r0, r1
	mov r2, #6
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2779:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2779b
	mov r0, r5
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #2
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #232]
2780:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2780b
	ldr r0, [sp, #0]
	ldr r1, [r0, #224]
	ldr r1, [r1, #104]
	str r1, [r0, #128]
	ldr r1, [r0, #228]
	ldr r1, [r1, #64]
	str r1, [r0, #132]
	ldr r1, [r0, #232]
	str r1, [r0, #136]
	ldr r1, [r0, #48]
	add r1, r1, r1
	str r1, [r0, #140]
	str r1, [r0, #144]
2781:
	ldr r12, [r0, #132]
	ldr lr, [r0, #144]
	ldr r1, [r0, #128]
	ldr r1, [r1, #0]
	mov r11, #0
	ldr r0, [r0, #136]
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
	and r2, lr, #1
	cmp r2, #0
	bne 2782f
	b 2783f
2782:
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
2783:
	cmp lr, #0
	bne 2784f
	b 2785f
2784:
2786:
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
	bne 2786b
2785:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [r0, #128]
	add r1, r1, #4
	str r1, [r0, #128]
	ldr r1, [r0, #136]
	add r1, r1, #4
	str r1, [r0, #136]
	ldr r1, [r0, #140]
	subs r1, r1, #1
	str r1, [r0, #140]
	bne 2781b
	ldr lr, [r0, #48]
	lsl lr, lr, #2
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #240]
2787:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2787b
	ldr r0, [sp, #0]
	ldr r4, [r0, #240]
	mov r2, #1
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2788:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2788b
	mov r0, r5
	ldr r12, [r0, #240]
	ldr lr, [r0, #48]
	lsl lr, lr, #2
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #232]
	sub lr, lr, #2
	mov r1, #1
	mov r11, #0
	movw r9, #65535
	lsr r10, r1, #16
	and r1, r1, r9
	and r2, lr, #1
	cmp r2, #0
	bne 2789f
	b 2790f
2789:
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
2790:
	cmp lr, #0
	bne 2791f
	b 2792f
2791:
2793:
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
	bne 2793b
2792:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [r0, #232]
	ldr r4, [sp, #4]
	ldr r6, [sp, #12]
	mov r5, r0
	mov lr, r6
	add r1, r1, r6
	sub r1, r1, #1
	mov r0, r4
2794:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2794b
	mov r0, r4
	mov lr, r6
	ldr r4, [sp, #48]
	mov r2, #0
	sub r2, r2, r4
2795:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2795b
	mov r0, r4
21:
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
