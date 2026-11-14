// The functions of `src/internal/vg_ffdh_generate_key_cached_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_generate_key_cached_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #72
	add r12, sp, #0
	str r0, [r12, #40]
	str r2, [r12, #36]
	str r2, [r12, #4]
	ldr r3, [sp, #128]
	str r3, [r12, #24]
	ldr r3, [sp, #132]
	str r3, [r12, #28]
	ldr r3, [sp, #136]
	str r3, [r12, #32]
	str r3, [r12, #44]
	ldr r3, [sp, #140]
	str r3, [r12, #48]
	ldr r0, [sp, #148]
	str r0, [r12, #0]
	add r12, sp, #0
	ldr r3, [sp, #156]
	str r3, [r12, #52]
	ldr r4, [sp, #24]
	ldr r6, [sp, #32]
	add r12, sp, #0
	str r4, [r12, #8]
	str r6, [r12, #12]
	add r3, r4, r6
	str r3, [r12, #56]
	add r3, r3, r6
	str r3, [r12, #60]
	ldr r4, [sp, #24]
	ldr r6, [sp, #32]
	add r12, sp, #0
	str r4, [r12, #8]
	str r6, [r12, #12]
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
20:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 20b
	mov r0, r8
	ldr r4, [sp, #8]
	ldr r6, [sp, #12]
	ldr r4, [sp, #52]
	add r4, r4, #24
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
21:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 21b
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
22:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 22b
	mov r0, r5
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
	ldr r9, [sp, #52]
	ldr r6, [r9, #8]
	ldr r10, [r9, #0]
	sub r10, r10, #1
	and r10, r10, #7
	mov r9, #7
	sub r9, r9, r10
	mov r3, #255
	and r12, r9, #4
	cmp r12, #0
	bne 23f
	b 24f
23:
	lsr r3, r3, #4
24:
	and r12, r9, #2
	cmp r12, #0
	bne 25f
	b 26f
25:
	lsr r3, r3, #2
26:
	and r12, r9, #1
	cmp r12, #0
	bne 27f
	b 28f
27:
	lsr r3, r3, #1
28:
	add r12, sp, #0
	str r6, [r12, #20]
	str r3, [r12, #68]
	ldr r0, [sp, #40]
	ldr r1, [sp, #48]
	ldr lr, [sp, #32]
	ldr r3, [sp, #20]
	sub lr, lr, r3
	add r3, r0, lr
	add r12, sp, #0
	str r3, [r12, #16]
	mov r2, #0
	cmp lr, #0
	beq 29f
211:
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 211b
	b 210f
29:
210:
	ldrb r2, [r1, #0]
	ldr r3, [sp, #68]
	and r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	ldr lr, [sp, #20]
	sub lr, lr, #1
	cmp lr, #0
	beq 212f
214:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 214b
	b 213f
212:
213:
	ldr r0, [sp, #0]
	ldr r4, [sp, #40]
	ldr r6, [sp, #44]
	mov r2, #1
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
215:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 215b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
216:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 216b
	ldr r0, [sp, #0]
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
217:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 217b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r10, [r0, #72]
	ldr r12, [r0, #120]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
218:
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
	bne 218b
	ldr r0, [sp, #0]
	eor r11, r11, #1
	str r11, [r0, #136]
	ldr r3, [sp, #28]
	ldr r4, [sp, #32]
	sub r3, r3, r4
	sub r3, r3, r4
	cmp r3, #0
	bne 219f
	mov r11, #0
	ldr r10, [r0, #72]
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #120]
	mov r4, #0
	sub r4, r4, r11
221:
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
	bne 221b
	ldr r0, [sp, #0]
	ldr r4, [r0, #120]
	ldr r3, [r4, #0]
	orr r3, r3, #1
	str r3, [r4, #0]
	ldr r10, [r0, #120]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
222:
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
	bne 222b
	ldr r0, [sp, #0]
	b 220f
219:
	ldr r4, [sp, #60]
	ldr r6, [sp, #32]
	mov r2, #6
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
223:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 223b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
224:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 224b
	ldr r0, [sp, #0]
	ldr r10, [r0, #72]
	ldr r12, [r0, #112]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
225:
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
	bne 225b
	ldr r0, [sp, #0]
220:
	ldr r3, [r0, #136]
	and r11, r11, r3
	cmp r11, #0
	bne 226f
	ldr r0, [sp, #40]
	ldr lr, [sp, #32]
	mov r2, #0
228:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 228b
	ldr r0, [sp, #36]
	ldr lr, [sp, #32]
	mov r2, #0
229:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 229b
	mov r0, #2
	b 227f
226:
	ldr r1, [sp, #16]
	ldr r2, [sp, #20]
	ldr r4, [sp, #52]
	str r1, [r0, #128]
	str r2, [r0, #132]
	ldr r1, [r4, #0]
	ldr r2, [r4, #16]
	ldr r3, [r0, #48]
	lsl r3, r3, #4
	add r4, r4, r3
	add r4, r4, #24
	str r1, [r0, #136]
	str r2, [r0, #204]
	str r4, [r0, #232]
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
230:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 230b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	sub sp, sp, #8
	mov r2, #6
	mov r3, #4
	mov lr, #7
	add r12, sp, #0
	str lr, [r12, #0]
	ldr r1, [r0, #48]
	add r1, r1, #6
	lsl r1, r1, #3
	bl {vg_rsa_mont_mul_umaal}
	add sp, sp, #8
	ldr r0, [sp, #0]
	ldr r1, [r0, #204]
	str r1, [r0, #192]
231:
	sub sp, sp, #8
	mov r2, #6
	mov r3, #6
	mov lr, #6
	add r12, sp, #0
	str lr, [r12, #0]
	ldr r1, [r0, #48]
	add r1, r1, #6
	lsl r1, r1, #3
	bl {vg_rsa_mont_mul_umaal}
	add sp, sp, #8
	ldr r0, [sp, #0]
	ldr r4, [r0, #128]
	ldr r5, [r0, #132]
	ldr r6, [r0, #192]
	sub r6, r6, #1
	ldr r7, [r0, #204]
	ldr r8, [r0, #136]
	mov r9, r6
	mov r10, #0
	sub r12, r9, r8
	lsr r12, r12, #31
	cmp r12, #0
	bne 232f
	mov r11, #0
	b 233f
232:
	lsr r12, r9, #3
	sub r12, r5, r12
	sub r12, r12, #1
	add r12, r4, r12
	ldrb r11, [r12, #0]
	and r2, r9, #7
	cmp r2, #0
	bne 234f
	b 235f
234:
236:
	lsr r11, r11, #1
	subs r2, r2, #1
	bne 236b
235:
	and r11, r11, #1
233:
	orr r10, r10, r11
	add r9, r9, r7
	sub r12, r9, r8
	lsr r12, r12, #31
	cmp r12, #0
	bne 237f
	mov r11, #0
	b 238f
237:
	lsr r12, r9, #3
	sub r12, r5, r12
	sub r12, r12, #1
	add r12, r4, r12
	ldrb r11, [r12, #0]
	and r2, r9, #7
	cmp r2, #0
	bne 239f
	b 240f
239:
241:
	lsr r11, r11, #1
	subs r2, r2, #1
	bne 241b
240:
	and r11, r11, #1
238:
	orr r10, r10, r11, lsl #1
	add r9, r9, r7
	sub r12, r9, r8
	lsr r12, r12, #31
	cmp r12, #0
	bne 242f
	mov r11, #0
	b 243f
242:
	lsr r12, r9, #3
	sub r12, r5, r12
	sub r12, r12, #1
	add r12, r4, r12
	ldrb r11, [r12, #0]
	and r2, r9, #7
	cmp r2, #0
	bne 244f
	b 245f
244:
246:
	lsr r11, r11, #1
	subs r2, r2, #1
	bne 246b
245:
	and r11, r11, #1
243:
	orr r10, r10, r11, lsl #2
	add r9, r9, r7
	sub r12, r9, r8
	lsr r12, r12, #31
	cmp r12, #0
	bne 247f
	mov r11, #0
	b 248f
247:
	lsr r12, r9, #3
	sub r12, r5, r12
	sub r12, r12, #1
	add r12, r4, r12
	ldrb r11, [r12, #0]
	and r2, r9, #7
	cmp r2, #0
	bne 249f
	b 250f
249:
251:
	lsr r11, r11, #1
	subs r2, r2, #1
	bne 251b
250:
	and r11, r11, #1
248:
	orr r10, r10, r11, lsl #3
	add r9, r9, r7
	sub r12, r9, r8
	lsr r12, r12, #31
	cmp r12, #0
	bne 252f
	mov r11, #0
	b 253f
252:
	lsr r12, r9, #3
	sub r12, r5, r12
	sub r12, r12, #1
	add r12, r4, r12
	ldrb r11, [r12, #0]
	and r2, r9, #7
	cmp r2, #0
	bne 254f
	b 255f
254:
256:
	lsr r11, r11, #1
	subs r2, r2, #1
	bne 256b
255:
	and r11, r11, #1
253:
	orr r10, r10, r11, lsl #4
	add r9, r9, r7
	mov r11, r10
	str r11, [r0, #196]
	ldr r12, [r0, #232]
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
257:
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
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #32
	bne 257b
	sub sp, sp, #8
	mov r2, #6
	mov r3, #6
	mov lr, #1
	add r12, sp, #0
	str lr, [r12, #0]
	ldr r1, [r0, #48]
	add r1, r1, #6
	lsl r1, r1, #3
	bl {vg_rsa_mont_mul_umaal}
	add sp, sp, #8
	ldr r0, [sp, #0]
	ldr r1, [r0, #192]
	subs r1, r1, #1
	str r1, [r0, #192]
	bne 231b
	sub sp, sp, #8
	mov r2, #6
	mov r3, #6
	mov lr, #7
	add r12, sp, #0
	str lr, [r12, #0]
	ldr r1, [r0, #48]
	add r1, r1, #6
	lsl r1, r1, #3
	bl {vg_rsa_mont_mul_umaal}
	add sp, sp, #8
	ldr r0, [sp, #0]
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
259:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 259b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r10, [r0, #120]
	ldr r12, [r0, #112]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
260:
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
	bne 260b
	ldr r0, [sp, #0]
	str r11, [r0, #136]
	mov r11, #0
	ldr r10, [r0, #112]
	ldr r12, [r0, #112]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #120]
	mov r4, #0
	sub r4, r4, r11
261:
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
	bne 261b
	ldr r0, [sp, #0]
	ldr r4, [r0, #120]
	ldr r3, [r4, #0]
	orr r3, r3, #1
	str r3, [r4, #0]
	ldr r10, [r0, #120]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
262:
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
	bne 262b
	ldr r0, [sp, #0]
	ldr r3, [r0, #136]
	and r11, r11, r3
	add r12, sp, #0
	str r11, [r12, #64]
	mov r2, #6
	ldr r4, [sp, #4]
	ldr r6, [sp, #32]
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	mov lr, r6
	add r1, r1, r6
	sub r1, r1, #1
	mov r0, r4
263:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 263b
	mov r0, r5
	ldr r0, [sp, #40]
	ldr lr, [sp, #32]
	ldr r3, [sp, #64]
	mov r2, #0
	sub r2, r2, r3
264:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 264b
	ldr r0, [sp, #36]
	ldr lr, [sp, #32]
	ldr r3, [sp, #64]
	mov r2, #0
	sub r2, r2, r3
265:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 265b
	ldr r3, [sp, #64]
	mov r0, #3
	sub r0, r0, r3, lsl #1
227:
	add sp, sp, #72
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
