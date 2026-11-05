// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_key:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	ldr r8, [sp, #104]
	ldr r9, [sp, #60]
	lsr r9, r9, #1
	add r9, r9, #4
	add r7, r9, #2
	lsl r7, r7, #2
	str r9, [r8, #16]
	add r0, r8, #160
	mov lr, #55
	mul lr, lr, r7
	lsr lr, lr, #2
	mov r3, #0
20:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 20b
	ldr r4, [sp, #56]
	ldr r6, [sp, #60]
	mov r0, #15
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
	ldr r4, [sp, #64]
	ldr r6, [sp, #68]
	mov r0, #16
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
	ldr r4, [sp, #96]
	ldr r6, [sp, #100]
	mov r0, #17
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
	mov r0, #22
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #1
	str r1, [r0, #0]
	mov r0, #23
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #2
	str r1, [r0, #0]
	mov r0, #24
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #3
	str r1, [r0, #0]
	mov r0, #25
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #4
	mov r1, #2147483648
	str r1, [r0, #0]
	mov r0, #43
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #20
	mov r1, #2147483648
	str r1, [r0, #0]
	mov r0, #44
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #2
	str r1, [r0, #4]
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #15
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #16
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
27:
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
	bne 27b
	str r11, [r8, #20]
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #15
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #16
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #20]
	mov r4, #0
	sub r4, r4, r11
28:
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
	bne 28b
	mov r0, #19
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #16
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #15
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #20]
	mov r4, #0
	sub r4, r4, r11
29:
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
	bne 29b
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #18
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	str r11, [r8, #24]
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #45
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #24]
	mov r4, #0
	sub r4, r4, r11
211:
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
	bne 211b
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #19
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	str r11, [r8, #28]
	mov r0, #21
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #45
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #28]
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
	mov r0, #48
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #21
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
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
	mov r0, #49
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
215:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 215b
	mov r0, #50
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
216:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 216b
	ldr r6, [sp, #60]
	lsl r6, r6, #3
217:
	mov r0, #48
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #104]
	mov r0, #51
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #49
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #104]
	mov r4, #0
	sub r4, r4, r11
218:
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
	bne 218b
	mov r0, #52
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #51
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
	mov r0, #53
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #50
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #52
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	mov r0, #54
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #53
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #25
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
221:
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
	bne 221b
	str r11, [r8, #108]
	mov r0, #50
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #54
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #53
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
222:
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
	bne 222b
	mov r0, #52
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #49
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
223:
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
	bne 223b
	mov r0, #53
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #49
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #52
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
	mov r0, #54
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #53
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #25
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
	str r11, [r8, #108]
	mov r0, #49
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #54
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #53
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
226:
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
	bne 226b
	mov r11, #0
	mov r0, #48
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
227:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 227b
	subs r6, r6, #1
	bne 217b
	mov r0, #28
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #50
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #50
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
	mov r0, #26
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
229:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 229b
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #21
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
230:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 230b
	ldr r6, [sp, #60]
	lsl r6, r6, #3
	str r6, [r8, #152]
231:
	mov r0, #26
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #32]
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #36]
	ldr r1, [r8, #32]
	ldr r2, [r8, #36]
	orr r1, r1, r2
	eor r1, r1, #1
	str r1, [r8, #40]
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #26
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #26
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
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #26
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #26
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
233:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 233b
	mov r11, #0
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
234:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 234b
	mov r0, #26
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #45
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #46
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #40]
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
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #27
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #27
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
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #27
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #27
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
237:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 237b
	mov r11, #0
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
238:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 238b
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #45
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #46
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #40]
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
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #28
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #28
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
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #28
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #28
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
	mov r11, #0
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
242:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 242b
	mov r0, #28
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #45
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #46
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #40]
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
	ldr r1, [r8, #152]
	subs r1, r1, #1
	str r1, [r8, #152]
	bne 231b
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #44]
	ldr r1, [r8, #44]
	eor r1, r1, #1
	str r1, [r8, #44]
	mov r0, #29
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #26
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #27
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #44]
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
	mov r0, #30
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #27
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #26
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #44]
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
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #30
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #23
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
	str r11, [r8, #48]
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #30
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #24
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #48]
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
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #46
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #46
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
248:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 248b
	add r0, r8, #160
	mov r10, #29
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #29
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
250:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 250b
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
251:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 251b
	mov r0, #3
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
252:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 252b
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
253:
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
	bne 253b
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
254:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 254b
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
255:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 255b
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
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
259:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 259b
	add r0, r8, #160
	add lr, r9, #1
	mov r3, #0
260:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 260b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
261:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 261b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
262:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 262b
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
263:
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
264:
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
	bne 264b
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
265:
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
	bne 265b
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
266:
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
	bne 266b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
268:
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
	bne 268b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
269:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 269b
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
270:
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
	bne 270b
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
271:
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
	bne 271b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
273:
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
	bne 273b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
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
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
276:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 276b
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
278:
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
	bne 278b
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
279:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 279b
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
280:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 280b
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
281:
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
	bne 281b
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
282:
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
	bne 282b
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
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
285:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 285b
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
287:
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
	bne 287b
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
	mov r10, #2
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #7
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
290:
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
	bne 290b
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
291:
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
	bne 291b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
292:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 292b
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
293:
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
	bne 293b
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
294:
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
	bne 294b
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
295:
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
	bne 295b
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
296:
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
	bne 296b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
297:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 297b
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
298:
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
	bne 298b
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
299:
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
	bne 299b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2100:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2100b
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
2101:
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
	bne 2101b
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
	subs r6, r6, #32
	bne 263b
	add r0, r8, r7
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
2103:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2103b
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
2104:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2104b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
2108:
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
	bne 2108b
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
2109:
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
	bne 2109b
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
2110:
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
	bne 2110b
	mov r0, #31
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, r7
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #48]
	mov r4, #0
	sub r4, r4, r11
2111:
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
	bne 2111b
	mov r0, #32
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #28
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #28
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
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #31
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #31
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2113:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2113b
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	mov r1, #32
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #36
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #37
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #38
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
2114:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2114b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
2115:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
2116:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2116b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
2117:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2117b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
	mov r11, #0
2118:
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
	bne 2118b
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
2119:
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
	bne 2119b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 2115b
	ldr r9, [r8, #16]
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #10
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2120:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2120b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #52]
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #22
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2121:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2121b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #56]
	mov r0, #17
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #60]
	ldr r1, [r8, #52]
	cmp r1, #1
	beq 2122f
	ldr r1, [r8, #56]
	cmp r1, #1
	beq 2124f
	ldr r1, [r8, #60]
	cmp r1, #1
	beq 2126f
	mov r0, #32
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #76]
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #32
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #24
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	str r11, [r8, #80]
	ldr r1, [r8, #80]
	eor r1, r1, #1
	ldr r2, [r8, #76]
	and r1, r1, r2
	str r1, [r8, #84]
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #24
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #32
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #84]
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
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #46
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #46
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2130:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2130b
	add r0, r8, #160
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
2131:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2131b
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
2132:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2132b
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2133:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2133b
	mov r0, #3
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
2134:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2134b
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
2135:
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
	bne 2135b
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
2136:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2136b
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
2137:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2137b
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
2138:
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
	bne 2138b
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
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
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
2141:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2141b
	add r0, r8, #160
	add lr, r9, #1
	mov r3, #0
2142:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2142b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2143:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2143b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2144:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2144b
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
2145:
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
2146:
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
	bne 2146b
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
2148:
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
	bne 2148b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2149:
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
	bne 2149b
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
2150:
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
	bne 2150b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2151:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2151b
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
2152:
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
	bne 2152b
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
2153:
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
	bne 2153b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2154:
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
	bne 2154b
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
2155:
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
	bne 2155b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2156:
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
	bne 2156b
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
2157:
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
	bne 2157b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2158:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2158b
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
2159:
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
	bne 2159b
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
2160:
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
	bne 2160b
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2161:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2161b
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
2162:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2162b
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
2163:
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
	bne 2163b
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
2164:
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
	bne 2164b
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
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2167:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2167b
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
2168:
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
	bne 2168b
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
2169:
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
	bne 2169b
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
2170:
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
	bne 2170b
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
2171:
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
	bne 2171b
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
2172:
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
	bne 2172b
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
2173:
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
	bne 2173b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2174:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2174b
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
2175:
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
	bne 2175b
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
2176:
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
	bne 2176b
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
2177:
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
	bne 2177b
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
2178:
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
	bne 2178b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2179:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2179b
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
2180:
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
	bne 2180b
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
2181:
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
	bne 2181b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2182:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2182b
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
2183:
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
	bne 2183b
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
2184:
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
	bne 2184b
	subs r6, r6, #32
	bne 2145b
	add r0, r8, r7
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
2185:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2185b
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
2186:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2186b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2187:
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
	bne 2187b
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
2188:
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
	bne 2188b
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
2189:
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
	bne 2189b
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
2190:
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
	bne 2190b
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
2191:
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
	bne 2191b
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
2192:
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
	bne 2192b
	add r0, r8, r7
	add r0, r0, #160
	mov r1, #22
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2193:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2193b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #68]
	ldr r1, [r8, #84]
	ldr r2, [r8, #68]
	and r1, r1, r2
	str r1, [r8, #64]
	mov r0, #33
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
2194:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2194b
	b 2127f
2126:
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
2195:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2195b
	add r0, r8, #160
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
2196:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2196b
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
2197:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2197b
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2198:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2198b
	mov r0, #3
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
2199:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2199b
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
2200:
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
	bne 2200b
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
2201:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2201b
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
2202:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2202b
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
2203:
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
	bne 2203b
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
2204:
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
	bne 2204b
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2205:
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
	bne 2205b
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
2206:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2206b
	add r0, r8, #160
	add lr, r9, #1
	mov r3, #0
2207:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2207b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2208:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2208b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2209:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2209b
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
2210:
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
2211:
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
	bne 2211b
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
2212:
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
	bne 2212b
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
2213:
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
	bne 2213b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2214:
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
	bne 2214b
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
2215:
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
	bne 2215b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2216:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2216b
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
2217:
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
	bne 2217b
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
2218:
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
	bne 2218b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2219:
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
	bne 2219b
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
2220:
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
	bne 2220b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2221:
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
	bne 2221b
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
2222:
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
	bne 2222b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2223:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2223b
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
2224:
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
	bne 2224b
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
2225:
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
	bne 2225b
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2226:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2226b
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
2227:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2227b
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
2228:
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
	bne 2228b
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
2229:
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
	bne 2229b
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
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2232:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2232b
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
2233:
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
	bne 2233b
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
2234:
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
	bne 2234b
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
2235:
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
	bne 2235b
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
2236:
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
	bne 2236b
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
2237:
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
	bne 2237b
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
2238:
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
	bne 2238b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2239:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2239b
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
2240:
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
	bne 2240b
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
2241:
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
	bne 2241b
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
2242:
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
	bne 2242b
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
2243:
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
	bne 2243b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2244:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2244b
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
2245:
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
	bne 2245b
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
2246:
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
	bne 2246b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2247:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2247b
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
2248:
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
	bne 2248b
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
2249:
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
	bne 2249b
	subs r6, r6, #32
	bne 2210b
	add r0, r8, r7
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
2250:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2250b
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
2251:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2251b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2252:
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
	bne 2252b
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
2253:
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
	bne 2253b
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
2254:
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
	bne 2254b
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
2255:
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
	bne 2255b
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
2256:
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
	bne 2256b
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
2257:
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
	bne 2257b
	add r0, r8, r7
	add r0, r0, #160
	mov r1, #22
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2258:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2258b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #68]
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #32
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #23
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2259:
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
	bne 2259b
	str r11, [r8, #72]
	ldr r1, [r8, #72]
	eor r1, r1, #1
	ldr r2, [r8, #68]
	and r1, r1, r2
	str r1, [r8, #64]
	mov r0, #47
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #17
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #3
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2260:
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
	bne 2260b
	mov r0, #48
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #47
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #47
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2261:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2261b
	mov r0, #49
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
2262:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2262b
	mov r0, #50
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2263:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2263b
	mov r6, #64
2264:
	mov r0, #48
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #104]
	mov r0, #51
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #49
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #104]
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
	mov r0, #52
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #51
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2266:
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
	bne 2266b
	mov r0, #53
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #50
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #52
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	mov r0, #54
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #53
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #25
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2268:
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
	bne 2268b
	str r11, [r8, #108]
	mov r0, #50
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #54
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #53
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
2269:
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
	bne 2269b
	mov r0, #52
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #49
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2270:
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
	bne 2270b
	mov r0, #53
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #49
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #52
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2271:
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
	bne 2271b
	mov r0, #54
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #53
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #25
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2272:
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
	bne 2272b
	str r11, [r8, #108]
	mov r0, #49
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #54
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #53
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
2273:
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
	bne 2273b
	mov r11, #0
	mov r0, #48
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
2274:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2274b
	subs r6, r6, #1
	bne 2264b
	mov r0, #35
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #50
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #50
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2275:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2275b
	mov r0, #37
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
2276:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2276b
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	mov r1, #35
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #36
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #37
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #38
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
2277:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2277b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
2278:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
2279:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2279b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
2280:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2280b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
	mov r11, #0
2281:
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
	bne 2281b
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
2282:
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
	bne 2282b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 2278b
	ldr r9, [r8, #16]
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #33
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #35
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #35
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2283:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2283b
2127:
	b 2125f
2124:
	mov r0, #32
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #22
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2284:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2284b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #68]
	ldr r1, [r8, #68]
	eor r1, r1, #1
	str r1, [r8, #64]
	mov r0, #33
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2285:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2285b
2125:
	b 2123f
2122:
	mov r1, #0
	str r1, [r8, #64]
2123:
	mov r0, #34
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2286:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2286b
	mov r0, #34
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #1
	sub r0, r0, #8
	mov r1, #1
	str r1, [r0, #0]
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #33
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #34
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2287:
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
	bne 2287b
	str r11, [r8, #88]
	ldr r1, [r8, #88]
	ldr r2, [r8, #64]
	and r1, r1, r2
	str r1, [r8, #92]
	ldr r1, [r8, #92]
	cmp r1, #1
	beq 2288f
	mov r0, #18
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #96]
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #18
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #24
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2290:
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
	bne 2290b
	str r11, [r8, #116]
	ldr r1, [r8, #116]
	eor r1, r1, #1
	ldr r2, [r8, #96]
	and r1, r1, r2
	str r1, [r8, #120]
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #24
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #18
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #120]
	mov r4, #0
	sub r4, r4, r11
2291:
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
	bne 2291b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #46
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #46
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2292:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2292b
	add r0, r8, #160
	mov r10, #19
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #19
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2293:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2293b
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
2294:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2294b
	mov r0, #2
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #22
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2295:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2295b
	mov r0, #3
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
2296:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2296b
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
2297:
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
	bne 2297b
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
2298:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2298b
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
2299:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2299b
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
2300:
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
	bne 2300b
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
2301:
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
	bne 2301b
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2302:
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
	bne 2302b
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
2303:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2303b
	add r0, r8, #160
	add lr, r9, #1
	mov r3, #0
2304:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2304b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2305:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2305b
	mov r0, #7
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2306:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2306b
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
2307:
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
2308:
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
	bne 2308b
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
2309:
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
	bne 2309b
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
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2311:
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
	bne 2311b
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
2312:
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
	bne 2312b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2313:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2313b
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
2314:
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
	bne 2314b
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
2315:
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
	bne 2315b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2316:
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
	bne 2316b
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
2317:
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
	bne 2317b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2318:
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
	bne 2318b
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
2319:
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
	bne 2319b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2320:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2320b
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
2321:
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
	bne 2321b
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
2322:
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
	bne 2322b
	mov r0, #4
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2323:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2323b
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
2324:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2324b
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
2325:
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
	bne 2325b
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
2326:
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
	bne 2326b
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
2327:
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
	bne 2327b
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
2328:
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
	bne 2328b
	mov r0, #13
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2329:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2329b
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
2330:
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
	bne 2330b
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
2331:
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
	bne 2331b
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
2332:
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
	bne 2332b
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
2333:
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
	bne 2333b
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
2334:
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
	bne 2334b
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
2335:
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
	bne 2335b
	mov r0, #14
	mla r0, r0, r7, r8
	add r0, r0, #160
	add lr, r9, #1
	mov r3, #0
2336:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2336b
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
2337:
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
	bne 2337b
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
2338:
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
	bne 2338b
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
2339:
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
	bne 2339b
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
2340:
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
	bne 2340b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2341:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2341b
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
2342:
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
	bne 2342b
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
2343:
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
	bne 2343b
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
2344:
	ldr r1, [r12, #0]
	ldr r2, [r12, #4]
	lsr r1, r1, #30
	add r1, r1, r2, lsl #2
	str r1, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2344b
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
2345:
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
	bne 2345b
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
2346:
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
	bne 2346b
	subs r6, r6, #32
	bne 2307b
	add r0, r8, r7
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
2347:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2347b
	mov r0, #3
	mla r0, r0, r7, r8
	add r0, r0, #160
	lsr lr, r7, #2
	sub lr, lr, #2
	mov r3, #0
2348:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2348b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r10, r8, #160
	mov r12, #4
	mla r12, r12, r7, r8
	add r12, r12, #160
	add lr, r9, #1
	mov r11, #0
2349:
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
	bne 2349b
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
2350:
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
	bne 2350b
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
2351:
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
	bne 2351b
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
2352:
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
	bne 2352b
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
2353:
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
	bne 2353b
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
2354:
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
	bne 2354b
	add r0, r8, r7
	add r0, r0, #160
	mov r1, #22
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2355:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2355b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #124]
	mov r0, #39
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
2356:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2356b
	mov r0, #20
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #10
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2357:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2357b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #148]
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #20
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #148]
	mov r4, #0
	sub r4, r4, r11
2358:
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
	bne 2358b
	mov r0, #35
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #33
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #33
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2359:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2359b
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #46
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #46
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2360:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2360b
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	mov r1, #35
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #36
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #37
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #38
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
2361:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2361b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
2362:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
2363:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2363b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
2364:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2364b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
	mov lr, r7
	mov r11, #0
2365:
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
	bne 2365b
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
2366:
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
	bne 2366b
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 2362b
	ldr r9, [r8, #16]
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #40
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #36
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #36
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2367:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2367b
	mov r0, #21
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #10
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
2368:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 2368b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #148]
	mov r0, #46
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #21
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #148]
	mov r4, #0
	sub r4, r4, r11
2369:
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
	bne 2369b
	mov r0, #35
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #33
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #33
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2370:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2370b
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #46
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #46
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2371:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2371b
	mov r0, #37
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	mov r1, #0
	str r1, [r0, #0]
	mov r1, #35
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #0]
	mov r1, #36
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #4]
	mov r1, #37
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #8]
	mov r1, #38
	mla r1, r1, r7, r8
	add r1, r1, #160
	str r1, [r8, #12]
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
	mov r3, #0
2372:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2372b
	ldr r6, [r8, #16]
	lsl r6, r6, #5
2373:
	ldr r0, [r8, #0]
	ldr lr, [r8, #16]
	mov r11, #0
2374:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2374b
	ldr r0, [r8, #4]
	ldr lr, [r8, #16]
	add lr, lr, #1
2375:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2375b
	ldr r0, [r8, #12]
	ldr r10, [r8, #4]
	ldr r12, [r8, #8]
	mov r9, r10
	ldr r7, [r8, #16]
	add r7, r7, #1
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
	ldr r0, [r8, #0]
	ldr r3, [r0, #0]
	eor r11, r11, #1
	add r3, r3, r11
	str r3, [r0, #0]
	subs r6, r6, #1
	bne 2373b
	ldr r9, [r8, #16]
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #41
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #36
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #36
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2378:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2378b
	mov r0, #48
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #19
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #19
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2379:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2379b
	mov r0, #49
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #18
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #18
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2380:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2380b
	mov r0, #50
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
2381:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2381b
	ldr r6, [sp, #60]
	lsl r6, r6, #3
2382:
	mov r0, #48
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #104]
	mov r0, #51
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #49
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #104]
	mov r4, #0
	sub r4, r4, r11
2383:
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
	bne 2383b
	mov r0, #52
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #51
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2384:
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
	bne 2384b
	mov r0, #53
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #50
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #52
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2385:
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
	bne 2385b
	mov r0, #54
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #53
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #25
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2386:
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
	bne 2386b
	str r11, [r8, #108]
	mov r0, #50
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #54
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #53
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
	mov r4, #0
	sub r4, r4, r11
2387:
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
	bne 2387b
	mov r0, #52
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #49
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2388:
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
	bne 2388b
	mov r0, #53
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #49
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #52
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2389:
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
	bne 2389b
	mov r0, #54
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #53
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #25
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
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
	str r11, [r8, #108]
	mov r0, #49
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #54
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #53
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #108]
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
	mov r11, #0
	mov r0, #48
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r1, r0, r9, lsl #2
	str r11, [r1, #0]
	mov lr, r9
2392:
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	lsr r3, r3, #1
	add r3, r3, r4, lsl #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2392b
	subs r6, r6, #1
	bne 2382b
	mov r0, #42
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #50
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #50
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
2393:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2393b
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #42
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #43
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2394:
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
	bne 2394b
	str r11, [r8, #128]
	mov r0, #19
	mla r0, r0, r7, r8
	add r0, r0, #160
	ldr r1, [r0, #0]
	and r1, r1, #1
	str r1, [r8, #136]
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #17
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #24
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2395:
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
	bne 2395b
	str r11, [r8, #140]
	mov r0, #45
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #17
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #44
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
2396:
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
	bne 2396b
	str r11, [r8, #144]
	ldr r1, [r8, #128]
	eor r1, r1, #1
	ldr r2, [r8, #64]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #132]
	ldr r2, [r8, #124]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #132]
	ldr r2, [r8, #96]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #132]
	ldr r2, [r8, #136]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #132]
	ldr r2, [r8, #60]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r1, [r8, #140]
	eor r1, r1, #1
	ldr r2, [r8, #144]
	and r1, r1, r2
	str r1, [r8, #140]
	ldr r1, [r8, #132]
	ldr r2, [r8, #140]
	and r1, r1, r2
	str r1, [r8, #132]
	ldr r10, [sp, #0]
	ldr r11, [sp, #4]
	mov r1, #42
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2397:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2397b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2398:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2398b
	ldr r10, [sp, #8]
	ldr r11, [sp, #4]
	mov r1, #33
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2399:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2399b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2400:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2400b
	ldr r10, [sp, #56]
	ldr r11, [sp, #60]
	mov r1, #18
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2401:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2401b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2402:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2402b
	ldr r10, [sp, #64]
	ldr r11, [sp, #60]
	mov r1, #19
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2403:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2403b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2404:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2404b
	ldr r10, [sp, #72]
	ldr r11, [sp, #60]
	mov r1, #40
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2405:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2405b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2406:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2406b
	ldr r10, [sp, #80]
	ldr r11, [sp, #60]
	mov r1, #41
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2407:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2407b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2408:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2408b
	ldr r10, [sp, #88]
	ldr r11, [sp, #60]
	mov r1, #39
	mla r1, r1, r7, r8
	add r1, r1, #160
	add r1, r1, r11
	sub r1, r1, #1
	mov r0, r10
	mov lr, r11
2409:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2409b
	mov r0, r10
	mov lr, r11
	ldr r1, [r8, #132]
	mov r2, #0
	sub r2, r2, r1
2410:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2410b
	ldr r0, [r8, #132]
	b 2289f
2288:
	ldr r0, [sp, #0]
	ldr lr, [sp, #4]
	mov r2, #0
2411:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2411b
	ldr r0, [sp, #8]
	ldr lr, [sp, #4]
	mov r2, #0
2412:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2412b
	ldr r0, [sp, #56]
	ldr lr, [sp, #60]
	mov r2, #0
2413:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2413b
	ldr r0, [sp, #64]
	ldr lr, [sp, #60]
	mov r2, #0
2414:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2414b
	ldr r0, [sp, #72]
	ldr lr, [sp, #60]
	mov r2, #0
2415:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2415b
	ldr r0, [sp, #80]
	ldr lr, [sp, #60]
	mov r2, #0
2416:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2416b
	ldr r0, [sp, #88]
	ldr lr, [sp, #60]
	mov r2, #0
2417:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2417b
	mov r0, #2
2289:
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

vg_rsa_prime_search_init:
	cmp r1, #32
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 20f
	mov r12, #512
	cmp r12, r1
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 22f
	and r12, r1, #7
	cmp r12, #0
	bne 24f
	cmp r3, #0
	beq 26f
	mov r12, #8
	cmp r12, r3
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 28f
	mov r12, #0
	str r12, [r0, #4]
	str r12, [r0, #12]
	str r12, [r0, #20]
	str r12, [r0, #28]
	str r1, [r0, #8]
	lsl r12, r1, #15
	add r12, r12, r1
	str r12, [r0, #16]
	lsl r12, r1, #5
	str r12, [r0, #24]
	mov r1, #0
	subs r3, r3, #1
	beq 210f
212:
	ldrb r12, [r2, #0]
	orr r1, r1, r12
	add r2, r2, #1
	subs r3, r3, #1
	bne 212b
	b 211f
210:
211:
	ldrb r12, [r2, #0]
	eor r12, r12, #3
	orr r1, r1, r12
	subs r1, r1, #1
	mov r1, #0
	adc r1, r1, #0
	ldr r12, [r0, #8]
	lsl r3, r12, #3
	add r3, r3, r12, lsl #4
	mul r1, r1, r3
	lsl r12, r12, #6
	sub r12, r12, r1
	str r12, [r0, #0]
	mov r0, #1
	b 29f
28:
	mov r12, #0
	str r12, [r0, #0]
	str r12, [r0, #4]
	str r12, [r0, #8]
	str r12, [r0, #12]
	str r12, [r0, #16]
	str r12, [r0, #20]
	str r12, [r0, #24]
	str r12, [r0, #28]
	mov r0, #0
29:
	b 27f
26:
	mov r12, #0
	str r12, [r0, #0]
	str r12, [r0, #4]
	str r12, [r0, #8]
	str r12, [r0, #12]
	str r12, [r0, #16]
	str r12, [r0, #20]
	str r12, [r0, #24]
	str r12, [r0, #28]
	mov r0, #0
27:
	b 25f
24:
	mov r12, #0
	str r12, [r0, #0]
	str r12, [r0, #4]
	str r12, [r0, #8]
	str r12, [r0, #12]
	str r12, [r0, #16]
	str r12, [r0, #20]
	str r12, [r0, #24]
	str r12, [r0, #28]
	mov r0, #0
25:
	b 23f
22:
	mov r12, #0
	str r12, [r0, #0]
	str r12, [r0, #4]
	str r12, [r0, #8]
	str r12, [r0, #12]
	str r12, [r0, #16]
	str r12, [r0, #20]
	str r12, [r0, #24]
	str r12, [r0, #28]
	mov r0, #0
23:
	b 21f
20:
	mov r12, #0
	str r12, [r0, #0]
	str r12, [r0, #4]
	str r12, [r0, #8]
	str r12, [r0, #12]
	str r12, [r0, #16]
	str r12, [r0, #20]
	str r12, [r0, #24]
	str r12, [r0, #28]
	mov r0, #0
21:
	bx lr

vg_rsa_prime_search:
	push {r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	ldr r12, [sp, #68]
	ldr r9, [r12, #0]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r8, #0
	mov r10, #0
	mov r11, #4
20:
	cmp r9, #0
	beq 21f
	ldr r0, [sp, #56]
	sub r0, r0, r8
	cmp r0, r5
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 23f
	sub sp, sp, #32
	mov r0, r4
	mov r1, r5
	mov r2, r6
	mov r3, r7
	add lr, sp, #0
	ldr r12, [sp, #72]
	str r12, [lr, #0]
	ldr r12, [sp, #76]
	str r12, [lr, #4]
	ldr r12, [sp, #80]
	str r12, [lr, #8]
	ldr r12, [sp, #84]
	add r12, r12, r8
	str r12, [lr, #12]
	ldr r12, [sp, #88]
	sub r12, r12, r8
	str r12, [lr, #16]
	ldr r12, [sp, #92]
	str r12, [lr, #20]
	ldr r12, [sp, #96]
	str r12, [lr, #24]
	bl {vg_rsa_keygen_candidate}
	add sp, sp, #32
	ldr r12, [r6, #0]
	cmp r0, #1
	beq 25f
	cmp r0, #0
	beq 27f
	cmp r12, #0
	beq 29f
	add r8, r8, r12
	cmp r0, #3
	beq 211f
	b 212f
211:
	sub r9, r9, #1
212:
	b 210f
29:
	mov r9, #0
	mov r10, #0
	mov r11, #3
	mov r0, r4
	mov lr, r5
	mov r2, #0
213:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 213b
210:
	b 28f
27:
	ldr r0, [sp, #56]
	sub r0, r0, r8
	lsl r1, r5, #15
	add r1, r1, r5
	cmp r0, r1
	beq 214f
	lsl r2, r5, #4
	cmp r0, r2
	mov r3, #0
	adc r3, r3, #0
	cmp r3, #0
	beq 216f
	b 217f
216:
	mov r0, r2
217:
	add r0, r0, r0
	cmp r0, r1
	mov r3, #0
	adc r3, r3, #0
	cmp r3, #0
	beq 218f
	mov r0, r1
	b 219f
218:
219:
	mov r10, r0
	mov r11, #0
	b 215f
214:
	mov r9, #0
	mov r10, #0
	mov r11, #3
	mov r0, r4
	mov lr, r5
	mov r2, #0
220:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 220b
215:
28:
	b 26f
25:
	add r8, r8, r12
	mov r9, #0
	mov r10, #0
	mov r11, #1
26:
	b 24f
23:
	mov r0, r4
	mov lr, r5
	mov r2, #0
221:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 221b
	ldr r0, [sp, #56]
	sub r0, r0, r8
	lsl r1, r5, #15
	add r1, r1, r5
	cmp r0, r1
	beq 222f
	lsl r2, r5, #4
	cmp r0, r2
	mov r3, #0
	adc r3, r3, #0
	cmp r3, #0
	beq 224f
	b 225f
224:
	mov r0, r2
225:
	add r0, r0, r0
	cmp r0, r1
	mov r3, #0
	adc r3, r3, #0
	cmp r3, #0
	beq 226f
	mov r0, r1
	b 227f
226:
227:
	mov r10, r0
	mov r11, #0
	b 223f
222:
	mov r9, #0
	mov r10, #0
	mov r11, #3
	mov r0, r4
	mov lr, r5
	mov r2, #0
228:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 228b
223:
24:
	b 22f
21:
	mov r9, #0
	mov r10, #0
	mov r11, #3
	mov r0, r4
	mov lr, r5
	mov r2, #0
229:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 229b
22:
	cmp r11, #4
	beq 20b
	ldr r12, [sp, #68]
	mov r0, #0
	lsl r1, r5, #15
	add r1, r1, r5
	str r9, [r12, #0]
	str r0, [r12, #4]
	str r5, [r12, #8]
	str r0, [r12, #12]
	str r1, [r12, #16]
	str r0, [r12, #20]
	str r10, [r12, #24]
	str r0, [r12, #28]
	str r8, [r6, #0]
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

vg_rsa_prime_search_umaal:
	push {r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	ldr r12, [sp, #68]
	ldr r9, [r12, #0]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r8, #0
	mov r10, #0
	mov r11, #4
20:
	cmp r9, #0
	beq 21f
	ldr r0, [sp, #56]
	sub r0, r0, r8
	cmp r0, r5
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 23f
	sub sp, sp, #32
	mov r0, r4
	mov r1, r5
	mov r2, r6
	mov r3, r7
	add lr, sp, #0
	ldr r12, [sp, #72]
	str r12, [lr, #0]
	ldr r12, [sp, #76]
	str r12, [lr, #4]
	ldr r12, [sp, #80]
	str r12, [lr, #8]
	ldr r12, [sp, #84]
	add r12, r12, r8
	str r12, [lr, #12]
	ldr r12, [sp, #88]
	sub r12, r12, r8
	str r12, [lr, #16]
	ldr r12, [sp, #92]
	str r12, [lr, #20]
	ldr r12, [sp, #96]
	str r12, [lr, #24]
	bl {vg_rsa_keygen_candidate_umaal}
	add sp, sp, #32
	ldr r12, [r6, #0]
	cmp r0, #1
	beq 25f
	cmp r0, #0
	beq 27f
	cmp r12, #0
	beq 29f
	add r8, r8, r12
	cmp r0, #3
	beq 211f
	b 212f
211:
	sub r9, r9, #1
212:
	b 210f
29:
	mov r9, #0
	mov r10, #0
	mov r11, #3
	mov r0, r4
	mov lr, r5
	mov r2, #0
213:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 213b
210:
	b 28f
27:
	ldr r0, [sp, #56]
	sub r0, r0, r8
	lsl r1, r5, #15
	add r1, r1, r5
	cmp r0, r1
	beq 214f
	lsl r2, r5, #4
	cmp r0, r2
	mov r3, #0
	adc r3, r3, #0
	cmp r3, #0
	beq 216f
	b 217f
216:
	mov r0, r2
217:
	add r0, r0, r0
	cmp r0, r1
	mov r3, #0
	adc r3, r3, #0
	cmp r3, #0
	beq 218f
	mov r0, r1
	b 219f
218:
219:
	mov r10, r0
	mov r11, #0
	b 215f
214:
	mov r9, #0
	mov r10, #0
	mov r11, #3
	mov r0, r4
	mov lr, r5
	mov r2, #0
220:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 220b
215:
28:
	b 26f
25:
	add r8, r8, r12
	mov r9, #0
	mov r10, #0
	mov r11, #1
26:
	b 24f
23:
	mov r0, r4
	mov lr, r5
	mov r2, #0
221:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 221b
	ldr r0, [sp, #56]
	sub r0, r0, r8
	lsl r1, r5, #15
	add r1, r1, r5
	cmp r0, r1
	beq 222f
	lsl r2, r5, #4
	cmp r0, r2
	mov r3, #0
	adc r3, r3, #0
	cmp r3, #0
	beq 224f
	b 225f
224:
	mov r0, r2
225:
	add r0, r0, r0
	cmp r0, r1
	mov r3, #0
	adc r3, r3, #0
	cmp r3, #0
	beq 226f
	mov r0, r1
	b 227f
226:
227:
	mov r10, r0
	mov r11, #0
	b 223f
222:
	mov r9, #0
	mov r10, #0
	mov r11, #3
	mov r0, r4
	mov lr, r5
	mov r2, #0
228:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 228b
223:
24:
	b 22f
21:
	mov r9, #0
	mov r10, #0
	mov r11, #3
	mov r0, r4
	mov lr, r5
	mov r2, #0
229:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 229b
22:
	cmp r11, #4
	beq 20b
	ldr r12, [sp, #68]
	mov r0, #0
	lsl r1, r5, #15
	add r1, r1, r5
	str r9, [r12, #0]
	str r0, [r12, #4]
	str r5, [r12, #8]
	str r0, [r12, #12]
	str r1, [r12, #16]
	str r0, [r12, #20]
	str r10, [r12, #24]
	str r0, [r12, #28]
	str r8, [r6, #0]
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
