// The functions of `src/internal/vg_miller_rabin_round.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_miller_rabin_round:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #11
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
20:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 20b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #12
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
21:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 21b
	mov r0, #6
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
22:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 22b
	mov r1, #14
	str r1, [r8, #140]
23:
	ldr r0, [sp, #0]
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
24:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 24b
	mov r0, r5
25:
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
	bne 26f
	b 27f
26:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
27:
	cmp lr, #0
	bne 28f
	b 29f
28:
210:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
	bne 210b
29:
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
211:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
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
	bne 211b
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
	bne 25b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
212:
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
	bne 212b
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
213:
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
	bne 213b
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	ldr lr, [r8, #140]
	mov r0, #27
	sub r0, r0, lr
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
214:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 214b
	ldr r1, [r8, #140]
	subs r1, r1, #1
	str r1, [r8, #140]
	bne 23b
	mov r0, #8
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
215:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 215b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
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
216:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 216b
	mov r1, #0
	str r1, [r8, #136]
	lsl r1, r9, #3
	sub r1, r1, #16
	str r1, [r8, #140]
217:
	ldr r1, [r8, #140]
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	lsr r1, r1, #3
	sub r1, r1, #1
	add r0, r0, r1, lsl #2
	ldr r2, [r0, #0]
	str r2, [r8, #116]
218:
	mov r1, #0
	str r1, [r8, #148]
	mov r1, #4
	str r1, [r8, #144]
219:
	ldr r0, [sp, #0]
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
220:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 220b
221:
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
	bne 222f
	b 223f
222:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
223:
	cmp lr, #0
	bne 224f
	b 225f
224:
226:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
	bne 226b
225:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 221b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
227:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 227b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
228:
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
	bne 228b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
229:
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
	bne 230f
	b 231f
230:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
231:
	cmp lr, #0
	bne 232f
	b 233f
232:
234:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
	bne 234b
233:
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
	bne 229b
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
235:
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
	bne 235b
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
236:
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
	bne 236b
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #8
	mla r1, r1, r7, r8
	add r1, r1, #160
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
	str r1, [r8, #92]
	ldr r1, [r8, #144]
	ldr r2, [r8, #148]
	sub r2, r2, r1
	lsr r2, r2, #31
	ldr r3, [r8, #92]
	and r3, r3, r2
	ldr r4, [r8, #136]
	orr r4, r4, r3
	str r4, [r8, #136]
	subs r1, r1, #1
	str r1, [r8, #144]
	bne 219b
	mov r0, #8
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
238:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 238b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #1
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #3
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #4
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #15
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #5
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #16
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
243:
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
	bne 243b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #6
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #7
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #18
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #8
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #19
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #9
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #10
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #11
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #12
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #23
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
250:
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
	bne 250b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #13
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #24
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
251:
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
	bne 251b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #14
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #25
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
252:
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
	bne 252b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #15
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #26
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
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
	mov r0, #8
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
254:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 254b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	ldr r0, [sp, #0]
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
255:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 255b
	mov r0, r5
256:
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
	bne 257f
	b 258f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
258:
	cmp lr, #0
	bne 259f
	b 260f
259:
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
	bne 261b
260:
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
	ldr r5, [r0, #4]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 262b
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
	bne 256b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
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
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #11
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
265:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 265b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #88]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #8
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
266:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 266b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #92]
	ldr r1, [r8, #116]
	lsr r2, r1, #28
	sub r2, r2, #1
	lsr r2, r2, #31
	eor r3, r2, #1
	ldr r4, [r8, #88]
	ldr r5, [r8, #92]
	orr r4, r4, r5
	and r4, r4, r3
	ldr r5, [r8, #136]
	and r5, r5, r2
	orr r4, r4, r5
	str r4, [r8, #136]
	lsl r1, r1, #4
	str r1, [r8, #116]
	ldr r1, [r8, #140]
	sub r1, r1, #1
	str r1, [r8, #140]
	and r1, r1, #7
	cmp r1, #0
	bne 218b
	ldr r1, [r8, #140]
	cmp r1, #0
	bne 217b
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	ldr r1, [r0, #0]
	ldr r2, [r0, #4]
	orr r1, r1, r2
	orr r1, r1, r1, lsr #16
	orr r1, r1, r1, lsr #8
	orr r1, r1, r1, lsr #4
	lsr r2, r1, #1
	and r2, r2, #1
	lsr r3, r1, #2
	and r3, r3, #1
	lsr r4, r1, #3
	and r4, r4, #1
	add r4, r4, r2
	add r4, r4, r2, lsl #1
	add r4, r4, r3, lsl #1
	str r4, [r8, #148]
	mov r1, #3
	str r1, [r8, #144]
267:
	ldr r0, [sp, #0]
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
268:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 268b
269:
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
	bne 270f
	b 271f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
271:
	cmp lr, #0
	bne 272f
	b 273f
272:
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
	bne 274b
273:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 269b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
275:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 275b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
276:
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
	bne 276b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
277:
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
	bne 277b
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
284:
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
	bne 284b
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #8
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
285:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 285b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #92]
	ldr r1, [r8, #144]
	ldr r2, [r8, #148]
	sub r2, r2, r1
	lsr r2, r2, #31
	ldr r3, [r8, #92]
	and r3, r3, r2
	ldr r4, [r8, #136]
	orr r4, r4, r3
	str r4, [r8, #136]
	subs r1, r1, #1
	str r1, [r8, #144]
	bne 267b
	ldr r0, [r8, #136]
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
