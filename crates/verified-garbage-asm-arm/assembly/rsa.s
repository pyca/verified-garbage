// The functions of `src/rsa.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_crt_values:
	ldr r12, [sp, #40]
	str r4, [r12, #20]
	str r5, [r12, #24]
	str r6, [r12, #28]
	str r7, [r12, #32]
	str r8, [r12, #36]
	str r9, [r12, #40]
	str r10, [r12, #44]
	str r11, [r12, #48]
	str lr, [r12, #52]
	str r0, [r12, #56]
	str r2, [r12, #60]
	mov r8, r12
	mov r3, r2
	ldr r4, [sp, #8]
	ldr r6, [sp, #12]
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
	mov r2, #0
	ldr lr, [sp, #20]
22:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 22b
	mov r0, r3
	mov r2, #0
	ldr lr, [sp, #28]
23:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 23b
	ldr r0, [sp, #0]
	mov r2, #0
	ldr lr, [sp, #20]
24:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 24b
	mov r0, #0
	b 21f
20:
	ldr r8, [sp, #40]
	ldr r9, [sp, #12]
	add r9, r9, #3
	lsr r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	str r9, [r8, #16]
	add r0, r8, #160
	mov lr, #25
	mul lr, lr, r7
	lsr lr, lr, #2
	mov r3, #0
25:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 25b
	ldr r4, [sp, #8]
	ldr r6, [sp, #12]
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
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
	ldr r4, [sp, #16]
	ldr r6, [sp, #20]
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
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
	ldr r4, [sp, #24]
	ldr r6, [sp, #28]
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
210:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 210b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
211:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 211b
	ldr r4, [sp, #32]
	ldr r6, [sp, #36]
	mov r0, #24
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
212:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 212b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
213:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 213b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #17
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
214:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 214b
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #116]
	mov r1, #18
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #19
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #20
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #21
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
215:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 215b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
216:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
217:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 217b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
218:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 218b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
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
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
220:
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
	bne 220b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 216b
	ldr r8, [sp, #40]
	ldr r9, [sp, #12]
	add r9, r9, #3
	lsr r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #16
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
221:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 221b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #120]
	mov r0, #19
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #10
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
222:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 222b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #124]
	add r0, r8, #160
	mov r10, #16
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #16
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
223:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 223b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #17
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
224:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 224b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	orr r1, r1, #1
	str r1, [r0, #0]
	add r0, r8, r7
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #8
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
225:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 225b
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #1
	str r1, [r0, #0]
	mov r0, #15
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #1
	str r1, [r0, #0]
	mov r0, #9
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #8
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
226:
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
	bne 226b
	ldr r0, [sp, #20]
	ldr r1, [sp, #28]
	sub r2, r0, r1
	lsr r3, r2, #31
	sub r3, r3, #1
	and r2, r2, r3
	add r9, r1, r2
	add r9, r9, #3
	lsr r9, r9, #2
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #8
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
227:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 227b
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	add r0, r8, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
228:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 228b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	add r0, r8, #160
	ldr r1, [r0, #0]
	mvn r1, r1
	and r11, r1, #1
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
231:
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
	bne 231b
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
232:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 232b
	add r0, r8, #160
	add lr, r9, #1
	mov r3, #0
233:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 233b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
234:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 234b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
235:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 235b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #1
	str r1, [r0, #0]
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r5, [r0, #0]
	mov r2, r5
	mul r4, r5, r2
	movw r3, #2
	sub r3, r3, r4
	mul r2, r2, r3
	mul r4, r5, r2
	movw r3, #2
	sub r3, r3, r4
	mul r2, r2, r3
	mul r4, r5, r2
	movw r3, #2
	sub r3, r3, r4
	mul r2, r2, r3
	mul r4, r5, r2
	movw r3, #2
	sub r3, r3, r4
	mul r2, r2, r3
	sub r2, r2, r2, lsl #1
	str r2, [r8, #104]
	mov r1, #1
	str r1, [r8, #100]
	add r6, r9, #1
	lsl r6, r6, #5
	add r6, r6, r6, lsl #1
236:
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r2, [r12, #0]
	ldr r0, [r8, #100]
	mov r3, #1
	mov r4, #0
	mov r5, #0
	mov r10, #1
	add r6, r6, #30
237:
	and r11, r2, #1
	sub r11, r11, r11, lsl #1
	lsr r12, r0, #31
	sub r12, r12, #1
	and r12, r12, r11
	eor lr, r1, r12
	sub lr, lr, r12
	and lr, lr, r11
	add r2, r2, lr
	eor lr, r3, r12
	sub lr, lr, r12
	and lr, lr, r11
	add r5, r5, lr
	eor lr, r4, r12
	sub lr, lr, r12
	and lr, lr, r11
	add r10, r10, lr
	eor r0, r0, r12
	sub r0, r0, r12
	add r0, r0, #2
	and lr, r2, r12
	add r1, r1, lr
	lsr r2, r2, #1
	and lr, r5, r12
	add r3, r3, lr
	lsl r3, r3, #1
	and lr, r10, r12
	add r4, r4, lr
	lsl r4, r4, #1
	sub r6, r6, #1
	and r11, r6, #31
	cmp r11, #0
	bne 237b
	str r0, [r8, #100]
	add r12, r8, r7
	add r12, r12, #160
	str r3, [r12, #0]
	str r4, [r12, #4]
	str r5, [r12, #8]
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	str r10, [r12, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
238:
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
	bne 238b
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
239:
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
	bne 239b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #4]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
242:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 242b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
243:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 243b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #4]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
244:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 244b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
245:
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
	bne 245b
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #8]
	lsr r11, r1, #31
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
246:
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
	bne 246b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
247:
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
	bne 247b
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
248:
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
	bne 248b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
249:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 249b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #8]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
250:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 250b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
251:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 251b
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
252:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 252b
	ldr r1, [r12, #0]
	lsr r2, r1, #30
	lsr r1, r1, #31
	sub r2, r2, r1, lsl #2
	str r2, [r0, #0]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
253:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 253b
	ldr r1, [r12, #0]
	lsr r2, r1, #30
	lsr r1, r1, #31
	sub r2, r2, r1, lsl #2
	str r2, [r0, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
254:
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
	bne 254b
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
255:
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
	bne 255b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
256:
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
	bne 256b
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #4]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #7
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
257:
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
	bne 257b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
258:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 258b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
259:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 259b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #4]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
260:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 260b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
261:
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
	bne 261b
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #8]
	lsr r11, r1, #31
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
262:
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
	bne 262b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
263:
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
	bne 263b
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #7
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
264:
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
	bne 264b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
265:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 265b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #8]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
266:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 266b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
267:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 267b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	ldr r2, [r8, #104]
	mul r1, r1, r2
	bic r1, r1, #3221225472
	mov r11, #0
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
268:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 268b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	ldr r2, [r8, #104]
	mul r1, r1, r2
	bic r1, r1, #3221225472
	mov r11, #0
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
269:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 269b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
270:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 270b
	ldr r1, [r12, #0]
	lsr r2, r1, #30
	lsr r1, r1, #31
	sub r2, r2, r1, lsl #2
	str r2, [r0, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #12
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
271:
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
	bne 271b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
272:
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
	bne 272b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
273:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 273b
	ldr r1, [r12, #0]
	lsr r2, r1, #30
	lsr r1, r1, #31
	sub r2, r2, r1, lsl #2
	str r2, [r0, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #12
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	subs r6, r6, #32
	bne 236b
	add r0, r8, r7
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
276:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 276b
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
277:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 277b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
278:
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
	bne 278b
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add r12, r12, r9, lsl #2
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	add r0, r8, r7
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r4, #0
	sub r4, r4, r11
279:
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
	bne 279b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add r12, r12, r9, lsl #2
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #12
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
282:
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
	bne 282b
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r4, #0
	sub r4, r4, r11
283:
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
	bne 283b
	ldr r8, [sp, #40]
	ldr r9, [sp, #12]
	add r9, r9, #3
	lsr r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	add r0, r8, r7
	add r0, r0, #160
	mov r1, #15
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
284:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 284b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #128]
	ldr r1, [r8, #116]
	ldr r2, [r8, #120]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #132]
	ldr r2, [r8, #124]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #132]
	ldr r2, [r8, #128]
	and r1, r1, r2
	str r1, [r8, #132]
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #24
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #24
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
285:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 285b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #17
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
286:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 286b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	orr r1, r1, #1
	eor r1, r1, #1
	str r1, [r0, #0]
	mov r1, #18
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #22
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #20
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #21
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
287:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 287b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
288:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
289:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 289b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
290:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 290b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
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
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 288b
	ldr r8, [sp, #40]
	ldr r9, [sp, #12]
	add r9, r9, #3
	lsr r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #24
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #24
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
293:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 293b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #16
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #16
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
294:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 294b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	orr r1, r1, #1
	eor r1, r1, #1
	str r1, [r0, #0]
	mov r1, #18
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #23
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #20
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #21
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
295:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 295b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
296:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
297:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 297b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
298:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 298b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
	mov r11, #0
299:
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
	bne 299b
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
2100:
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
	bne 2100b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 296b
	ldr r8, [sp, #40]
	ldr r9, [sp, #12]
	add r9, r9, #3
	lsr r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	ldr r10, [r8, #56]
	ldr r12, [r8, #60]
	ldr r11, [sp, #20]
	mov r1, #22
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2101:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2101b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2102:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2102b
	mov r10, r12
	ldr r11, [sp, #28]
	mov r1, #23
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2103:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2103b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2104:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2104b
	ldr r10, [sp, #0]
	ldr r11, [sp, #20]
	mov r1, #3
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2105:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2105b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2106:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2106b
	ldr r0, [r8, #132]
21:
	ldr r12, [sp, #40]
	ldr r4, [r12, #20]
	ldr r5, [r12, #24]
	ldr r6, [r12, #28]
	ldr r7, [r12, #32]
	ldr r8, [r12, #36]
	ldr r9, [r12, #40]
	ldr r10, [r12, #44]
	ldr r11, [r12, #48]
	ldr lr, [r12, #52]
	bx lr

vg_rsa_check_key:
	ldr r12, [sp, #48]
	str r4, [r12, #20]
	str r5, [r12, #24]
	str r6, [r12, #28]
	str r7, [r12, #32]
	str r8, [r12, #36]
	str r9, [r12, #40]
	str r10, [r12, #44]
	str r11, [r12, #48]
	str lr, [r12, #52]
	str r2, [r12, #56]
	str r3, [r12, #60]
	mov r8, r12
	mov r10, r0
	mov r11, r1
	mov r4, r2
	mov r6, r3
	add r9, r11, #3
	lsr r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	str r9, [r8, #16]
	add r0, r8, #160
	mov lr, #24
	mul lr, lr, r7
	lsr lr, lr, #2
	mov r3, #0
20:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 20b
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
21:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 21b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
22:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 22b
	ldr r4, [sp, #0]
	ldr r6, [sp, #4]
	mov r0, #9
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
23:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 23b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
24:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 24b
	ldr r4, [sp, #8]
	ldr r6, [sp, #12]
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
25:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 25b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
26:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 26b
	ldr r4, [sp, #16]
	ldr r6, [sp, #20]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
27:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 27b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
28:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 28b
	ldr r4, [sp, #24]
	ldr r6, [sp, #28]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
29:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 29b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
210:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 210b
	ldr r4, [sp, #32]
	ldr r6, [sp, #36]
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
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
	ldr r4, [sp, #40]
	ldr r6, [sp, #44]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
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
	mov r4, r10
	mov r6, r11
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
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
	beq 217f
	mov r0, #0
	b 218f
217:
	ldr r1, [r8, #56]
	ldr lr, [r8, #60]
	mov r3, #0
	mov r4, #0
219:
	ldrb r7, [r1, #0]
	lsr r5, r3, #24
	lsl r4, r4, #8
	add r4, r4, r5
	lsl r3, r3, #8
	add r3, r3, r7
	lsr r5, r4, #1
	subs r5, r5, #0
	beq 220f
	mov r4, #2
	b 221f
220:
221:
	add r1, r1, #1
	subs lr, lr, #1
	bne 219b
	lsr r5, r4, #1
	and r7, r3, #1
	eor r7, r7, #1
	orr r5, r5, r7
	subs r5, r5, #0
	beq 222f
	mov r7, #0
	b 223f
222:
	eor r5, r3, #1
	orr r5, r5, r4
	subs r5, r5, #0
	beq 224f
	mov r7, #1
	b 225f
224:
	mov r7, #0
225:
223:
	cmp r7, #1
	beq 226f
	mov r0, #0
	b 227f
226:
	add r9, r11, #3
	lsr r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	add r0, r8, r7
	add r0, r0, #160
	mov r1, #1
	str r1, [r0, #0]
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #120]
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
228:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 228b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
229:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 229b
	mov r1, #12
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #13
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #14
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #15
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
230:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 230b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
231:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
232:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 232b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
233:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 233b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
	mov r11, #0
234:
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
	bne 234b
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
235:
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
	bne 235b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 231b
	ldr r9, [r8, #16]
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #5
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
236:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 236b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r8, #160
	mov lr, r9
	mov r2, #0
237:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 237b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #10
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
238:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 238b
	mov r0, #10
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	orr r1, r1, #1
	eor r1, r1, #1
	str r1, [r0, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
239:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 239b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	orr r1, r1, #1
	eor r1, r1, #1
	str r1, [r0, #0]
	mov r0, #23
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	str r11, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #3
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
241:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 241b
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
242:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 242b
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	add r12, r8, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
243:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 243b
	mov r6, #33
244:
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #104]
	mov r0, #19
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #104]
	mov r4, #0
	sub r4, r4, r11
245:
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
	bne 245b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #19
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
246:
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
	bne 246b
	mov r0, #21
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #18
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
247:
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
	bne 247b
	mov r0, #22
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #21
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
248:
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
	bne 248b
	str r11, [r8, #108]
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
249:
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
	bne 249b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
250:
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
	bne 250b
	mov r0, #21
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #17
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
251:
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
	bne 251b
	mov r0, #22
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #21
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
252:
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
	bne 252b
	str r11, [r8, #108]
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
253:
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
	bne 253b
	mov r11, #0
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
254:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 254b
	subs r6, r6, #1
	bne 244b
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r8, r7
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
255:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 255b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #23
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #7
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
256:
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
	bne 256b
	str r11, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #3
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
257:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 257b
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #7
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
258:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 258b
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	add r12, r8, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
259:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 259b
	mov r6, #33
260:
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #104]
	mov r0, #19
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #104]
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
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #19
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	mov r0, #21
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #18
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
263:
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
	bne 263b
	mov r0, #22
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #21
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
264:
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
	bne 264b
	str r11, [r8, #108]
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
265:
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
	bne 265b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
266:
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
	bne 266b
	mov r0, #21
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #17
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
267:
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
	bne 267b
	mov r0, #22
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #21
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
268:
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
	bne 268b
	str r11, [r8, #108]
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
269:
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
	bne 269b
	mov r11, #0
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
270:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 270b
	subs r6, r6, #1
	bne 260b
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r8, r7
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
271:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 271b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #23
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
272:
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
	bne 272b
	str r11, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
273:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 273b
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #8
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
274:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 274b
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	add r12, r8, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
275:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 275b
	lsl r6, r9, #5
276:
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #104]
	mov r0, #19
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #104]
	mov r4, #0
	sub r4, r4, r11
277:
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
	bne 277b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #19
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
278:
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
	bne 278b
	mov r0, #21
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #18
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
279:
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
	bne 279b
	mov r0, #22
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #21
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	str r11, [r8, #108]
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
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
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
282:
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
	bne 282b
	mov r0, #21
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #17
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
283:
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
	bne 283b
	mov r0, #22
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #21
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
284:
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
	bne 284b
	str r11, [r8, #108]
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
285:
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
	bne 285b
	mov r11, #0
	mov r0, #16
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
286:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 286b
	subs r6, r6, #1
	bne 276b
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r8, r7
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
287:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 287b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #23
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #9
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
288:
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
	bne 288b
	str r11, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #9
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #9
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
289:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 289b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
290:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 290b
	mov r1, #12
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #13
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #14
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #15
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
291:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 291b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
292:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
293:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 293b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
294:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 294b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
	mov r11, #0
295:
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
	bne 295b
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
296:
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
	bne 296b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 292b
	ldr r9, [r8, #16]
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #6
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
297:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 297b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #9
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #9
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
298:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 298b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
299:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 299b
	mov r1, #12
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #13
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #14
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #15
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
2100:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2100b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
2101:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
2102:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2102b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
2103:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2103b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
	mov r11, #0
2104:
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
	bne 2104b
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
2105:
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
	bne 2105b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 2101b
	ldr r9, [r8, #16]
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #7
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2106:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2106b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #116]
	ldr r1, [r8, #120]
	ldr r2, [r8, #116]
	and r1, r1, r2
	str r1, [r8, #120]
	ldr r0, [r8, #120]
227:
218:
	ldr r12, [sp, #48]
	ldr r4, [r12, #20]
	ldr r5, [r12, #24]
	ldr r6, [r12, #28]
	ldr r7, [r12, #32]
	ldr r8, [r12, #36]
	ldr r9, [r12, #40]
	ldr r10, [r12, #44]
	ldr r11, [r12, #48]
	ldr lr, [r12, #52]
	bx lr

vg_rsa_recover_primes_det:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	add r12, sp, #0
	str r0, [r12, #4]
	ldr r4, [sp, #56]
	ldr r6, [sp, #60]
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
	ldr lr, [sp, #60]
	mov r2, #0
22:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 22b
	ldr r0, [sp, #8]
	ldr lr, [sp, #60]
	mov r2, #0
23:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 23b
	mov r0, #0
	b 21f
20:
	ldr r8, [sp, #80]
	ldr r9, [sp, #60]
	add r9, r9, #7
	lsr r9, r9, #3
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	str r9, [r8, #16]
	add r0, r8, #160
	mov lr, #44
	mul lr, lr, r7
	lsr lr, lr, #2
	mov r3, #0
24:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 24b
	ldr r4, [sp, #56]
	ldr r6, [sp, #60]
	mov r0, #32
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
25:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 25b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
26:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 26b
	ldr r4, [sp, #64]
	ldr r6, [sp, #68]
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
27:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 27b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
28:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 28b
	ldr r4, [sp, #72]
	ldr r6, [sp, #76]
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r5, r0
	add lr, r9, #2
	mov r3, #0
29:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 29b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
210:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 210b
	ldr r9, [r8, #16]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #4
	mov r1, #2147483648
	str r1, [r0, #0]
	ldr r6, [sp, #68]
	lsl r6, r6, #3
211:
	add r0, r8, r7
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #104]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #104]
	mov r4, #0
	sub r4, r4, r11
212:
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
	bne 212b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #3
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #7
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	str r11, [r8, #108]
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
216:
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
	bne 216b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
217:
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
	bne 217b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #7
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	str r11, [r8, #108]
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
220:
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
	bne 220b
	mov r11, #0
	add r0, r8, r7
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
221:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 221b
	subs r6, r6, #1
	bne 211b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #3
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #14
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
223:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 223b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #1
	str r1, [r0, #0]
	mov r0, #10
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #3
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
224:
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
	bne 224b
	str r11, [r8, #20]
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	str r11, [r8, #24]
	ldr r1, [r8, #20]
	ldr r2, [r8, #24]
	orr r1, r1, r2
	eor r1, r1, #1
	str r1, [r8, #28]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
226:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 226b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #40
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #32
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #32
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	mov r0, #41
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #40
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #40
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
228:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 228b
	mov r0, #41
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #1
	str r1, [r0, #0]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #32
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #41
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	lsl r1, r9, #5
	str r1, [r8, #80]
230:
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #32]
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #36]
	ldr r1, [r8, #32]
	eor r1, r1, #1
	str r1, [r8, #40]
	ldr r1, [r8, #32]
	ldr r2, [r8, #36]
	orr r1, r1, r2
	eor r1, r1, #1
	str r1, [r8, #44]
	mov r0, #36
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #8
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
231:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 231b
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #8
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
232:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 232b
	mov r11, #0
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
233:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 233b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #36
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #37
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #40]
	mov r4, #0
	sub r4, r4, r11
234:
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
	bne 234b
	mov r0, #36
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #20
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
235:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 235b
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #20
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
236:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 236b
	mov r11, #0
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
237:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 237b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #36
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #37
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #44]
	mov r4, #0
	sub r4, r4, r11
238:
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
	bne 238b
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
239:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 239b
	mov r0, #15
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
240:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 240b
	mov r11, #0
	mov r0, #15
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
241:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 241b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #12
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #15
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #44]
	mov r4, #0
	sub r4, r4, r11
242:
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
	bne 242b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	ldr r1, [r8, #80]
	subs r1, r1, #1
	str r1, [r8, #80]
	bne 230b
	add r0, r8, #160
	mov r10, #20
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
243:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 243b
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #8
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
244:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 244b
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	add r0, r8, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
245:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 245b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
246:
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
	bne 246b
	add r0, r8, #160
	ldr r1, [r0, #0]
	mvn r1, r1
	and r11, r1, #1
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
247:
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
	bne 247b
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
248:
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
	bne 248b
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
249:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 249b
	add r0, r8, #160
	add lr, r9, #1
	mov r3, #0
250:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 250b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
251:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 251b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
252:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 252b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #1
	str r1, [r0, #0]
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r5, [r0, #0]
	mov r2, r5
	mul r4, r5, r2
	movw r3, #2
	sub r3, r3, r4
	mul r2, r2, r3
	mul r4, r5, r2
	movw r3, #2
	sub r3, r3, r4
	mul r2, r2, r3
	mul r4, r5, r2
	movw r3, #2
	sub r3, r3, r4
	mul r2, r2, r3
	mul r4, r5, r2
	movw r3, #2
	sub r3, r3, r4
	mul r2, r2, r3
	sub r2, r2, r2, lsl #1
	str r2, [r8, #104]
	mov r1, #1
	str r1, [r8, #100]
	add r6, r9, #1
	lsl r6, r6, #5
	add r6, r6, r6, lsl #1
253:
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r2, [r12, #0]
	ldr r0, [r8, #100]
	mov r3, #1
	mov r4, #0
	mov r5, #0
	mov r10, #1
	add r6, r6, #30
254:
	and r11, r2, #1
	sub r11, r11, r11, lsl #1
	lsr r12, r0, #31
	sub r12, r12, #1
	and r12, r12, r11
	eor lr, r1, r12
	sub lr, lr, r12
	and lr, lr, r11
	add r2, r2, lr
	eor lr, r3, r12
	sub lr, lr, r12
	and lr, lr, r11
	add r5, r5, lr
	eor lr, r4, r12
	sub lr, lr, r12
	and lr, lr, r11
	add r10, r10, lr
	eor r0, r0, r12
	sub r0, r0, r12
	add r0, r0, #2
	and lr, r2, r12
	add r1, r1, lr
	lsr r2, r2, #1
	and lr, r5, r12
	add r3, r3, lr
	lsl r3, r3, #1
	and lr, r10, r12
	add r4, r4, lr
	lsl r4, r4, #1
	sub r6, r6, #1
	and r11, r6, #31
	cmp r11, #0
	bne 254b
	str r0, [r8, #100]
	add r12, r8, r7
	add r12, r12, #160
	str r3, [r12, #0]
	str r4, [r12, #4]
	str r5, [r12, #8]
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	str r10, [r12, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
255:
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
	bne 255b
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
256:
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
	bne 256b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #4]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
259:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 259b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
260:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 260b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #4]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
261:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 261b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #8]
	lsr r11, r1, #31
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
263:
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
	bne 263b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
264:
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
	bne 264b
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
265:
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
	bne 265b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
266:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 266b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #8]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
267:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 267b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
268:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 268b
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
269:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 269b
	ldr r1, [r12, #0]
	lsr r2, r1, #30
	lsr r1, r1, #31
	sub r2, r2, r1, lsl #2
	str r2, [r0, #0]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
270:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 270b
	ldr r1, [r12, #0]
	lsr r2, r1, #30
	lsr r1, r1, #31
	sub r2, r2, r1, lsl #2
	str r2, [r0, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
271:
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
	bne 271b
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
272:
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
	bne 272b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
273:
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
	bne 273b
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #4]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #7
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
274:
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
	bne 274b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
275:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 275b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
276:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 276b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #4]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
277:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 277b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
278:
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
	bne 278b
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #8]
	lsr r11, r1, #31
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
279:
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
	bne 279b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #7
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
282:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 282b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r12, r8, r7
	add r12, r12, #160
	ldr r1, [r12, #8]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
283:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 283b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	sub r2, r11, r11, lsl #1
	eor r1, r1, r2
	sub r1, r1, r2
	mov r11, #0
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
284:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 284b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	ldr r2, [r8, #104]
	mul r1, r1, r2
	bic r1, r1, #3221225472
	mov r11, #0
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
285:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 285b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	ldr r2, [r8, #104]
	mul r1, r1, r2
	bic r1, r1, #3221225472
	mov r11, #0
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	lsr r10, r1, #16
	bic r1, r1, r10, lsl #16
286:
	ldr r2, [r12, #0]
	lsr r3, r2, #16
	bic r2, r2, r3, lsl #16
	mul r4, r1, r2
	mul r2, r10, r2
	mul r5, r10, r3
	mul r3, r1, r3
	adds r4, r4, r2, lsl #16
	adc r5, r5, r2, lsr #16
	adds r4, r4, r3, lsl #16
	adc r5, r5, r3, lsr #16
	adds r4, r4, r11
	adc r5, r5, #0
	ldr r2, [r0, #0]
	adds r4, r4, r2
	adc r11, r5, #0
	str r4, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 286b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
287:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 287b
	ldr r1, [r12, #0]
	lsr r2, r1, #30
	lsr r1, r1, #31
	sub r2, r2, r1, lsl #2
	str r2, [r0, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #12
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
288:
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
	bne 288b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
289:
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
	bne 289b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
290:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 290b
	ldr r1, [r12, #0]
	lsr r2, r1, #30
	lsr r1, r1, #31
	sub r2, r2, r1, lsl #2
	str r2, [r0, #0]
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #12
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
	subs r6, r6, #32
	bne 253b
	add r0, r8, r7
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
293:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 293b
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
294:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 294b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
295:
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
	bne 295b
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add r12, r12, r9, lsl #2
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	add r0, r8, r7
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r4, #0
	sub r4, r4, r11
296:
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
	bne 296b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
297:
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
	bne 297b
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add r12, r12, r9, lsl #2
	ldr r1, [r12, #0]
	lsr r11, r1, #31
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r4, #0
	sub r4, r4, r11
298:
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
	bne 298b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #12
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #2
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
299:
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
	bne 299b
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r4, #0
	sub r4, r4, r11
2100:
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
	bne 2100b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #41
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2101:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2101b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #84]
	mov r0, #34
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, r7
	add r10, r10, #160
	mov r12, #41
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #84]
	mov r4, #0
	sub r4, r4, r11
2102:
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
	bne 2102b
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #9
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #14
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2103:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2103b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	lsl r1, r9, #5
	str r1, [r8, #80]
2104:
	mov r0, #34
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #14
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #48]
	mov r4, #0
	sub r4, r4, r11
2105:
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
	bne 2105b
	mov r0, #15
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #14
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2106:
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
	bne 2106b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #9
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #15
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2107:
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
	bne 2107b
	mov r0, #9
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #12
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2108:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2108b
	mov r11, #0
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
2109:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2109b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	mov r11, #0
	mov r0, #34
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
2110:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2110b
	ldr r1, [r8, #80]
	subs r1, r1, #1
	str r1, [r8, #80]
	bne 2104b
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #14
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2111:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2111b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #34
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #32
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #32
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2112:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2112b
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	str r9, [r8, #16]
	mov r1, #9
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #19
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #17
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #18
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
2113:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2113b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
2114:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
2115:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2115b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
2116:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2116b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
	mov r11, #0
2117:
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
	bne 2117b
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
2118:
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
	bne 2118b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 2114b
	ldr r9, [r8, #16]
	sub r9, r9, #2
	lsr r9, r9, #1
	str r9, [r8, #16]
	add r7, r9, #2
	lsl r7, r7, #2
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #9
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2119:
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
	bne 2119b
	str r11, [r8, #52]
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #40
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #41
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2120:
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
	bne 2120b
	mov r0, #36
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #18
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #37
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2121:
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
	bne 2121b
	mov r0, #36
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #40
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2122:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2122b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #88]
	mov r0, #22
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #36
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #41
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
2123:
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
	bne 2123b
	mov r0, #24
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #32
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #38
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2124:
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
	bne 2124b
	mov r0, #22
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	mov r1, #24
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #2
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #22
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #3
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
2125:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2125b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
2126:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
2127:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2127b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
2128:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2128b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
	mov r11, #0
2129:
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
	bne 2129b
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
2130:
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
	bne 2130b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 2126b
	ldr r9, [r8, #16]
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #40
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2131:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2131b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #56]
	mov r0, #36
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #40
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #41
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2132:
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
	bne 2132b
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #24
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #36
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2133:
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
	bne 2133b
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2134:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2134b
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #10
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #14
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2135:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2135b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2136:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2136b
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #9
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #14
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2137:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2137b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	lsl r1, r9, #5
	str r1, [r8, #80]
2138:
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #14
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #48]
	mov r4, #0
	sub r4, r4, r11
2139:
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
	bne 2139b
	mov r0, #15
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #14
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2140:
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
	bne 2140b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #9
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #15
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2141:
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
	bne 2141b
	mov r0, #9
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #12
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2142:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2142b
	mov r11, #0
	mov r0, #10
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
2143:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2143b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	mov r11, #0
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
2144:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2144b
	ldr r1, [r8, #80]
	subs r1, r1, #1
	str r1, [r8, #80]
	bne 2138b
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r11, #0
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
2145:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2145b
	mov r11, #0
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
2146:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2146b
	mov r0, #19
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #9
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2147:
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
	bne 2147b
	str r11, [r8, #60]
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #19
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2148:
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
	bne 2148b
	str r11, [r8, #64]
	ldr r1, [r8, #60]
	ldr r2, [r8, #64]
	orr r1, r1, r2
	eor r1, r1, #1
	str r1, [r8, #68]
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #40
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #40
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2149:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2149b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #40
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #40
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2150:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2150b
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	lsl r1, r9, #4
	str r1, [r8, #80]
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
2151:
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r11, #0
	mov r0, #19
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
2152:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2152b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
2153:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2153b
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r11, #0
	mov r0, #19
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
2154:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2154b
	sub r9, r9, #2
	lsr r9, r9, #1
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
2155:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2155b
	add r0, r8, #160
	mov r10, #7
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2156:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2156b
	mov r11, #0
	add r0, r8, #160
	mov lr, r9
2157:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2157b
	mov r11, #1
	add r0, r8, #160
	mov lr, r9
2158:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2158b
	add r0, r8, r7
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	add r12, r8, #160
	mov lr, r9
	mov r11, #0
2159:
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
	bne 2159b
	str r11, [r8, #72]
	mov r0, #36
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2160:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2160b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, r7
	add r10, r10, #160
	mov r12, #36
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #72]
	mov r4, #0
	sub r4, r4, r11
2161:
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
	bne 2161b
	ldr r11, [r8, #72]
	eor r11, r11, #1
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov lr, r9
2162:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2162b
	ldr r1, [r8, #80]
	subs r1, r1, #1
	str r1, [r8, #80]
	bne 2151b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #40
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2163:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2163b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #76]
	mov r0, #36
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #40
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2164:
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
	bne 2164b
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #36
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	mov r11, #0
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
2166:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2166b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #4
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2167:
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
	bne 2167b
	mov r11, #0
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
2168:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2168b
	ldr r1, [r8, #28]
	ldr r2, [r8, #52]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #132]
	ldr r2, [r8, #56]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #132]
	ldr r2, [r8, #68]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #132]
	ldr r2, [r8, #76]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r10, [sp, #4]
	ldr r11, [sp, #60]
	mov r1, #5
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2169:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2169b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2170:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2170b
	ldr r10, [sp, #8]
	ldr r11, [sp, #60]
	mov r1, #6
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2171:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2171b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2172:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2172b
	ldr r0, [r8, #132]
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

vg_rsa_private_precompute:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	lsl lr, r1, #1
	mov r3, #0
20:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 20b
	ldr r0, [sp, #0]
	ldr r1, [sp, #12]
	ldr r2, [sp, #56]
	ldr r3, [sp, #60]
	ldr r4, [sp, #64]
	ldr r5, [sp, #68]
	mov r6, r2
	mov r7, r3
	mov r8, r4
	mov r9, r5
	mov r10, r0
	mov r11, r3
	ldr r12, [sp, #72]
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	ldr r0, [sp, #56]
	ldr r2, [sp, #64]
	ldr r3, [sp, #68]
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
	beq 21f
	mov r0, #0
	b 22f
21:
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
229:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 229b
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
230:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 230b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
231:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 231b
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
232:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 232b
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
233:
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
	bne 233b
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
234:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 234b
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
235:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 235b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
236:
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
237:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 237b
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
	bne 238f
	b 239f
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
	ldr r5, [r0, #0]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
239:
	cmp lr, #0
	bne 240f
	b 241f
240:
242:
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
	bne 242b
241:
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
243:
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
	bne 243b
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
244:
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
	bne 244b
	ldr r0, [sp, #0]
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 236b
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
245:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 245b
246:
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
	bne 247f
	b 248f
247:
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
248:
	cmp lr, #0
	bne 249f
	b 250f
249:
251:
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
	bne 251b
250:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 246b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
252:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 252b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
253:
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
	bne 253b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
254:
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
	bne 255f
	b 256f
255:
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
256:
	cmp lr, #0
	bne 257f
	b 258f
257:
259:
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
	bne 259b
258:
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
	bne 254b
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
262:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 262b
263:
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
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 263b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
269:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 269b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
270:
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
	bne 270b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
271:
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
	bne 272f
	b 273f
272:
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
273:
	cmp lr, #0
	bne 274f
	b 275f
274:
276:
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
	bne 276b
275:
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
	bne 271b
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
277:
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
	bne 277b
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
278:
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
	bne 278b
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
279:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 279b
280:
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
	bne 281f
	b 282f
281:
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
282:
	cmp lr, #0
	bne 283f
	b 284f
283:
285:
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
	bne 285b
284:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 280b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
286:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 286b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
287:
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
	bne 287b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
288:
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
	bne 289f
	b 290f
289:
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
290:
	cmp lr, #0
	bne 291f
	b 292f
291:
293:
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
	bne 293b
292:
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
	bne 288b
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
294:
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
	bne 294b
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
295:
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
	bne 295b
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
296:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 296b
297:
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
	bne 298f
	b 299f
298:
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
299:
	cmp lr, #0
	bne 2100f
	b 2101f
2100:
2102:
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
	bne 2102b
2101:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 297b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2103:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2103b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2104:
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
	bne 2104b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2105:
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
	bne 2106f
	b 2107f
2106:
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
2107:
	cmp lr, #0
	bne 2108f
	b 2109f
2108:
2110:
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
	bne 2110b
2109:
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
	bne 2105b
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
2111:
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
	bne 2111b
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
2112:
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
	bne 2112b
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
2113:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2113b
2114:
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
	bne 2115f
	b 2116f
2115:
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
2116:
	cmp lr, #0
	bne 2117f
	b 2118f
2117:
2119:
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
	bne 2119b
2118:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2114b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2120:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2120b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2121:
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
	bne 2121b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2122:
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
	bne 2123f
	b 2124f
2123:
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
2124:
	cmp lr, #0
	bne 2125f
	b 2126f
2125:
2127:
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
	bne 2127b
2126:
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
	bne 2122b
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
2128:
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
	bne 2128b
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
2129:
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
	bne 2129b
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
2130:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2130b
2131:
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
	bne 2132f
	b 2133f
2132:
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
2133:
	cmp lr, #0
	bne 2134f
	b 2135f
2134:
2136:
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
	bne 2136b
2135:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2131b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2137:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2137b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2138:
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
	bne 2138b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2139:
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
	bne 2140f
	b 2141f
2140:
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
2141:
	cmp lr, #0
	bne 2142f
	b 2143f
2142:
2144:
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
	bne 2144b
2143:
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
	bne 2139b
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
2145:
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
	bne 2145b
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
2146:
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
	bne 2146b
	ldr r0, [sp, #0]
	ldr r4, [sp, #4]
	ldr r1, [sp, #8]
	ldr r1, [r1, #48]
	add r4, r4, r1, lsl #4
	mov r2, #4
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2147:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2147b
	mov r0, r5
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
2148:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 2148b
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
2149:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2149b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2150:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2150b
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
2151:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2151b
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
2152:
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
	bne 2152b
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
2153:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2153b
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
2154:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2154b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
2155:
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
2156:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2156b
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
	bne 2157f
	b 2158f
2157:
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
2158:
	cmp lr, #0
	bne 2159f
	b 2160f
2159:
2161:
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
	bne 2161b
2160:
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
2162:
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
	bne 2162b
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
2163:
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
	bne 2163b
	ldr r0, [sp, #0]
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 2155b
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
2164:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2164b
2165:
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
	bne 2166f
	b 2167f
2166:
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
2167:
	cmp lr, #0
	bne 2168f
	b 2169f
2168:
2170:
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
	bne 2170b
2169:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2165b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2171:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2171b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2172:
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
	bne 2172b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2173:
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
	bne 2174f
	b 2175f
2174:
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
2175:
	cmp lr, #0
	bne 2176f
	b 2177f
2176:
2178:
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
	bne 2178b
2177:
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
	bne 2173b
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
2179:
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
	bne 2179b
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
2180:
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
	bne 2180b
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
2181:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2181b
2182:
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
	bne 2183f
	b 2184f
2183:
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
2184:
	cmp lr, #0
	bne 2185f
	b 2186f
2185:
2187:
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
	bne 2187b
2186:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2182b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2188:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2188b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2189:
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
	bne 2189b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2190:
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
	bne 2191f
	b 2192f
2191:
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
2192:
	cmp lr, #0
	bne 2193f
	b 2194f
2193:
2195:
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
	bne 2195b
2194:
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
	bne 2190b
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
2196:
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
	bne 2196b
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
2197:
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
	bne 2197b
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
2198:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2198b
2199:
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
	bne 2200f
	b 2201f
2200:
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
2201:
	cmp lr, #0
	bne 2202f
	b 2203f
2202:
2204:
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
	bne 2204b
2203:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2199b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2205:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2205b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2206:
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
	bne 2206b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2207:
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
	bne 2208f
	b 2209f
2208:
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
2209:
	cmp lr, #0
	bne 2210f
	b 2211f
2210:
2212:
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
	bne 2212b
2211:
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
	bne 2207b
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
2213:
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
	bne 2213b
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
2214:
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
	bne 2214b
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
2215:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2215b
2216:
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
	bne 2217f
	b 2218f
2217:
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
2218:
	cmp lr, #0
	bne 2219f
	b 2220f
2219:
2221:
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
	bne 2221b
2220:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2216b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2222:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2222b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2223:
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
	bne 2223b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2224:
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
	bne 2225f
	b 2226f
2225:
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
2226:
	cmp lr, #0
	bne 2227f
	b 2228f
2227:
2229:
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
	bne 2229b
2228:
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
	bne 2224b
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
2230:
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
	bne 2230b
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
2231:
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
	bne 2231b
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
2232:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2232b
2233:
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
	bne 2234f
	b 2235f
2234:
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
2235:
	cmp lr, #0
	bne 2236f
	b 2237f
2236:
2238:
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
	bne 2238b
2237:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2233b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2239:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2239b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2240:
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
	bne 2240b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2241:
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
	bne 2242f
	b 2243f
2242:
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
2243:
	cmp lr, #0
	bne 2244f
	b 2245f
2244:
2246:
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
	bne 2246b
2245:
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
	bne 2241b
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
2247:
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
	bne 2247b
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
2248:
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
	bne 2248b
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
2249:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2249b
2250:
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
	bne 2251f
	b 2252f
2251:
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
2252:
	cmp lr, #0
	bne 2253f
	b 2254f
2253:
2255:
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
	bne 2255b
2254:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2250b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2256:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2256b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2257:
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
	bne 2257b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2258:
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
	bne 2259f
	b 2260f
2259:
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
2260:
	cmp lr, #0
	bne 2261f
	b 2262f
2261:
2263:
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
	bne 2263b
2262:
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
	bne 2258b
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
2264:
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
	bne 2264b
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
2265:
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
	bne 2265b
	ldr r0, [sp, #0]
	ldr r4, [sp, #4]
	ldr r1, [sp, #8]
	ldr r1, [r1, #48]
	add r4, r4, r1, lsl #4
	ldr r7, [sp, #68]
	add r7, r7, #7
	lsr r7, r7, #3
	sub r1, r7, #2
	lsr r1, r1, #31
	add r7, r7, r1
	mov r3, #0
	add r4, r4, r7, lsl #3
	mov r2, #4
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2266:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2266b
	mov r0, r5
	ldr r0, [sp, #8]
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
2267:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2267b
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
2269:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2269b
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
2270:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2270b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
2271:
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
2272:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2272b
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
	bne 2273f
	b 2274f
2273:
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
2274:
	cmp lr, #0
	bne 2275f
	b 2276f
2275:
2277:
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
	bne 2277b
2276:
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
2278:
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
	bne 2278b
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
2279:
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
	bne 2279b
	ldr r0, [sp, #0]
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 2271b
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
2280:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2280b
2281:
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
	bne 2282f
	b 2283f
2282:
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
2283:
	cmp lr, #0
	bne 2284f
	b 2285f
2284:
2286:
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
	bne 2286b
2285:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2281b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2287:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2287b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2288:
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
	bne 2288b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2289:
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
	bne 2289b
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
2295:
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
	bne 2295b
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
2296:
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
	bne 2296b
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
2297:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2297b
2298:
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
	bne 2299f
	b 2300f
2299:
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
2300:
	cmp lr, #0
	bne 2301f
	b 2302f
2301:
2303:
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
	bne 2303b
2302:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2298b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2304:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2304b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2305:
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
	bne 2305b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2306:
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
	bne 2307f
	b 2308f
2307:
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
2308:
	cmp lr, #0
	bne 2309f
	b 2310f
2309:
2311:
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
	bne 2311b
2310:
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
	bne 2306b
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
2312:
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
	bne 2312b
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
2313:
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
	bne 2313b
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
2314:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2314b
2315:
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
	bne 2316f
	b 2317f
2316:
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
2317:
	cmp lr, #0
	bne 2318f
	b 2319f
2318:
2320:
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
	bne 2320b
2319:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2315b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2321:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2321b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2322:
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
	bne 2322b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2323:
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
	bne 2324f
	b 2325f
2324:
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
2325:
	cmp lr, #0
	bne 2326f
	b 2327f
2326:
2328:
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
	bne 2328b
2327:
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
	bne 2323b
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
2329:
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
	bne 2329b
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
2330:
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
	bne 2330b
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
2331:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2331b
2332:
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
	bne 2333f
	b 2334f
2333:
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
2334:
	cmp lr, #0
	bne 2335f
	b 2336f
2335:
2337:
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
	bne 2337b
2336:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2332b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2338:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2338b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2339:
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
	bne 2339b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2340:
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
	bne 2341f
	b 2342f
2341:
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
2342:
	cmp lr, #0
	bne 2343f
	b 2344f
2343:
2345:
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
	bne 2345b
2344:
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
	bne 2340b
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
2346:
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
	bne 2346b
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
2347:
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
	bne 2347b
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
2348:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2348b
2349:
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
	bne 2350f
	b 2351f
2350:
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
2351:
	cmp lr, #0
	bne 2352f
	b 2353f
2352:
2354:
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
	bne 2354b
2353:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2349b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2355:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2355b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2356:
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
	bne 2356b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2357:
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
	bne 2358f
	b 2359f
2358:
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
2359:
	cmp lr, #0
	bne 2360f
	b 2361f
2360:
2362:
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
	bne 2362b
2361:
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
	bne 2357b
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
2363:
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
	bne 2363b
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
2364:
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
	bne 2364b
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
2365:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2365b
2366:
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
	bne 2367f
	b 2368f
2367:
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
2368:
	cmp lr, #0
	bne 2369f
	b 2370f
2369:
2371:
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
	bne 2371b
2370:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2366b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2372:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2372b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2373:
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
	bne 2373b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2374:
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
	bne 2375f
	b 2376f
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
	ldr r5, [r0, #0]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2376:
	cmp lr, #0
	bne 2377f
	b 2378f
2377:
2379:
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
	bne 2379b
2378:
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
	bne 2374b
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
2380:
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
	bne 2380b
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
2381:
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
	bne 2381b
	ldr r0, [sp, #0]
	ldr r4, [sp, #4]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2382:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2382b
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
2383:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2383b
	mov r0, r5
	mov r0, #1
	ldr r1, [sp, #8]
	ldr r1, [r1, #48]
	lsl r6, r1, #4
	ldr r7, [sp, #68]
	add r7, r7, #7
	lsr r7, r7, #3
	sub r1, r7, #2
	lsr r1, r1, #31
	add r7, r7, r1
	mov r3, #0
	add r6, r6, r7, lsl #3
	ldr r7, [sp, #76]
	add r7, r7, #7
	lsr r7, r7, #3
	sub r1, r7, #2
	lsr r1, r1, #31
	add r7, r7, r1
	mov r3, #0
	add r6, r6, r7, lsl #3
	ldr r4, [sp, #4]
	mov r0, r4
	mov lr, r6
	ldr r4, [sp, #48]
	mov r2, #0
	sub r2, r2, r4
2384:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2384b
	mov r0, r4
22:
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
	ldr r12, [sp], #56
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

vg_rsa_public_precompute_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	add r12, sp, #0
	str r0, [r12, #4]
	ldr r0, [sp, #56]
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
	add lr, r6, #7
	lsr lr, lr, #3
	lsl lr, lr, #2
	ldr r0, [sp, #4]
	mov r3, #0
22:
	str r3, [r0, #0]
	add r0, r0, #4
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
	ldr r4, [sp, #8]
	ldr r6, [sp, #12]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
24:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 24b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
25:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 25b
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
	mov r5, #0
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
26:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 26b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r4, [r0, #96]
	ldr r1, [r0, #48]
	add r4, r4, r1, lsl #3
	sub r4, r4, #4
	mov r5, #2147483648
	str r5, [r4, #0]
	mov r2, #7
	mov r5, #2
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
27:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 27b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r10, [r0, #96]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
28:
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
	bne 28b
	ldr r0, [sp, #0]
	subs r11, r11, #0
	bne 29f
	mov r2, #4
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
211:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 211b
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
212:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 212b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
	b 210f
29:
	ldr r1, [r0, #48]
	add r1, r1, #1
	str r1, [r0, #208]
210:
213:
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
214:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 214b
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
	bne 215f
	b 216f
215:
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
216:
	cmp lr, #0
	bne 217f
	b 218f
217:
	orr r9, r1, r10, lsl #16
219:
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
	bne 219b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
218:
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
220:
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
	bne 220b
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
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 213b
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
222:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 222b
223:
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
	bne 224f
	b 225f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
225:
	cmp lr, #0
	bne 226f
	b 227f
226:
	orr r9, r1, r10, lsl #16
228:
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
	bne 228b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
227:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 223b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
229:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 229b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
230:
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
	bne 230b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
231:
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
	bne 232f
	b 233f
232:
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
233:
	cmp lr, #0
	bne 234f
	b 235f
234:
	orr r9, r1, r10, lsl #16
236:
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
	bne 236b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
235:
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
	bne 231b
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
237:
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
	bne 237b
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
238:
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
	bne 238b
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
239:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 239b
240:
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
	bne 241f
	b 242f
241:
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
242:
	cmp lr, #0
	bne 243f
	b 244f
243:
	orr r9, r1, r10, lsl #16
245:
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
	bne 245b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
244:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 240b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
246:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 246b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
247:
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
	bne 247b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
248:
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
	bne 249f
	b 250f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
250:
	cmp lr, #0
	bne 251f
	b 252f
251:
	orr r9, r1, r10, lsl #16
253:
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
	bne 253b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
252:
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
	bne 248b
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
254:
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
	bne 254b
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
255:
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
	bne 255b
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
256:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 256b
257:
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
	bne 258f
	b 259f
258:
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
259:
	cmp lr, #0
	bne 260f
	b 261f
260:
	orr r9, r1, r10, lsl #16
262:
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
	bne 262b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
261:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 257b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
263:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 263b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
264:
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
	bne 264b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
265:
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
	bne 266f
	b 267f
266:
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
267:
	cmp lr, #0
	bne 268f
	b 269f
268:
	orr r9, r1, r10, lsl #16
270:
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
	bne 270b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
269:
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
	bne 265b
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
271:
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
	bne 271b
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
272:
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
	bne 272b
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
273:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 273b
274:
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
	bne 275f
	b 276f
275:
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
276:
	cmp lr, #0
	bne 277f
	b 278f
277:
	orr r9, r1, r10, lsl #16
279:
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
	bne 279b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
278:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 274b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
280:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 280b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
281:
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
	bne 281b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
282:
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
	bne 283f
	b 284f
283:
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
284:
	cmp lr, #0
	bne 285f
	b 286f
285:
	orr r9, r1, r10, lsl #16
287:
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
	bne 287b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
286:
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
	bne 282b
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
288:
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
	bne 288b
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
289:
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
	bne 289b
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
290:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 290b
291:
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
	bne 292f
	b 293f
292:
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
293:
	cmp lr, #0
	bne 294f
	b 295f
294:
	orr r9, r1, r10, lsl #16
296:
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
	bne 296b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
295:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 291b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
297:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 297b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
298:
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
	bne 298b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
299:
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
	bne 2100f
	b 2101f
2100:
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
2101:
	cmp lr, #0
	bne 2102f
	b 2103f
2102:
	orr r9, r1, r10, lsl #16
2104:
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
	bne 2104b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2103:
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
	bne 299b
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
2105:
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
	bne 2105b
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
2106:
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
	bne 2106b
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
2107:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2107b
2108:
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
	bne 2109f
	b 2110f
2109:
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
2110:
	cmp lr, #0
	bne 2111f
	b 2112f
2111:
	orr r9, r1, r10, lsl #16
2113:
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
	bne 2113b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2112:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2108b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2114:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2114b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2115:
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
	bne 2115b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2116:
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
	bne 2117f
	b 2118f
2117:
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
2118:
	cmp lr, #0
	bne 2119f
	b 2120f
2119:
	orr r9, r1, r10, lsl #16
2121:
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
	bne 2121b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2120:
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
	bne 2116b
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
2122:
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
	bne 2122b
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
2123:
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
	bne 2123b
	ldr r0, [sp, #0]
	ldr r4, [sp, #4]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2124:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2124b
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
2125:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2125b
	mov r0, r5
	mov r0, #1
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

vg_rsa_public_precompute:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	add r12, sp, #0
	str r0, [r12, #4]
	ldr r0, [sp, #56]
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
	add lr, r6, #7
	lsr lr, lr, #3
	lsl lr, lr, #2
	ldr r0, [sp, #4]
	mov r3, #0
22:
	str r3, [r0, #0]
	add r0, r0, #4
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
	ldr r4, [sp, #8]
	ldr r6, [sp, #12]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
24:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 24b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
25:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 25b
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
	mov r5, #0
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
26:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 26b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r4, [r0, #96]
	ldr r1, [r0, #48]
	add r4, r4, r1, lsl #3
	sub r4, r4, #4
	mov r5, #2147483648
	str r5, [r4, #0]
	mov r2, #7
	mov r5, #2
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
27:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 27b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r10, [r0, #96]
	ldr r12, [r0, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #88]
	mov r11, #0
28:
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
	bne 28b
	ldr r0, [sp, #0]
	subs r11, r11, #0
	bne 29f
	mov r2, #4
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
211:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 211b
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
212:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 212b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
	b 210f
29:
	ldr r1, [r0, #48]
	add r1, r1, #1
	str r1, [r0, #208]
210:
213:
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
214:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 214b
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
	bne 215f
	b 216f
215:
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
216:
	cmp lr, #0
	bne 217f
	b 218f
217:
219:
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
	bne 219b
218:
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
220:
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
	bne 220b
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
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 213b
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
222:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 222b
223:
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
	bne 224f
	b 225f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
225:
	cmp lr, #0
	bne 226f
	b 227f
226:
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
	bne 228b
227:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 223b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
229:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 229b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
230:
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
	bne 230b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
231:
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
	bne 232f
	b 233f
232:
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
233:
	cmp lr, #0
	bne 234f
	b 235f
234:
236:
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
	bne 236b
235:
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
	bne 231b
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
237:
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
	bne 237b
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
238:
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
	bne 238b
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
239:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 239b
240:
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
	bne 241f
	b 242f
241:
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
242:
	cmp lr, #0
	bne 243f
	b 244f
243:
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
	bne 245b
244:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 240b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
246:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 246b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
247:
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
	bne 247b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
248:
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
	bne 249f
	b 250f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
250:
	cmp lr, #0
	bne 251f
	b 252f
251:
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
	bne 253b
252:
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
	bne 248b
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
254:
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
	bne 254b
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
255:
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
	bne 255b
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
256:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 256b
257:
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
	bne 258f
	b 259f
258:
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
259:
	cmp lr, #0
	bne 260f
	b 261f
260:
262:
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
	bne 262b
261:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 257b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
263:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 263b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
264:
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
	bne 264b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
265:
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
	bne 266f
	b 267f
266:
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
267:
	cmp lr, #0
	bne 268f
	b 269f
268:
270:
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
	bne 270b
269:
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
	bne 265b
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
271:
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
	bne 271b
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
272:
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
	bne 272b
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
273:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 273b
274:
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
	bne 275f
	b 276f
275:
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
276:
	cmp lr, #0
	bne 277f
	b 278f
277:
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
	bne 279b
278:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 274b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
280:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 280b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
281:
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
	bne 281b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
282:
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
	bne 283f
	b 284f
283:
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
284:
	cmp lr, #0
	bne 285f
	b 286f
285:
287:
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
	bne 287b
286:
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
	bne 282b
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
288:
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
	bne 288b
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
289:
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
	bne 289b
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
290:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 290b
291:
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
	bne 292f
	b 293f
292:
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
293:
	cmp lr, #0
	bne 294f
	b 295f
294:
296:
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
	bne 296b
295:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 291b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
297:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 297b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
298:
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
	bne 298b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
299:
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
	bne 2100f
	b 2101f
2100:
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
2101:
	cmp lr, #0
	bne 2102f
	b 2103f
2102:
2104:
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
	bne 2104b
2103:
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
	bne 299b
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
2105:
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
	bne 2105b
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
2106:
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
	bne 2106b
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
2107:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2107b
2108:
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
	bne 2109f
	b 2110f
2109:
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
2110:
	cmp lr, #0
	bne 2111f
	b 2112f
2111:
2113:
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
	bne 2113b
2112:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2108b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2114:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2114b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2115:
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
	bne 2115b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2116:
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
	bne 2117f
	b 2118f
2117:
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
2118:
	cmp lr, #0
	bne 2119f
	b 2120f
2119:
2121:
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
	bne 2121b
2120:
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
	bne 2116b
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
2122:
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
	bne 2122b
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
2123:
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
	bne 2123b
	ldr r0, [sp, #0]
	ldr r4, [sp, #4]
	mov r2, #0
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2124:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2124b
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
2125:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2125b
	mov r0, r5
	mov r0, #1
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
