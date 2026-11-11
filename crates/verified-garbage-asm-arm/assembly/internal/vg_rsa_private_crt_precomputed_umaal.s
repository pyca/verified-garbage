// The functions of `src/internal/vg_rsa_private_crt_precomputed_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_private_crt_precomputed_umaal:
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
	ldr r0, [r0, #224]
	add r12, sp, #0
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
218:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 218b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
219:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 219b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #64]
220:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 220b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #112]
221:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 221b
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
	add r2, r2, #8
	lsr r2, r2, #5
	sub r1, r7, r2
	lsr r1, r1, #31
	mov r3, #0
	sub r1, r3, r1
	sub r2, r2, r7
	and r2, r2, r1
	add r7, r7, r2
	str r7, [r0, #48]
	str r3, [r0, #52]
	mov r8, r0
	add r5, r7, #2
	lsl r5, r5, #3
	add r4, r0, #256
	add r0, r0, #64
	mov lr, #8
222:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 222b
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
225:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 225b
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
	ldr r1, [r0, #48]
	ldr r2, [sp, #68]
	add r2, r2, #7
	lsr r2, r2, #3
	cmp r1, r2
	beq 227f
	mov r2, #4
	mov r5, #1
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
	mov r2, #7
	mov r5, #2
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
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
231:
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
232:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 232b
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
	orr r9, r1, r10, lsl #16
237:
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
	bne 237b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
236:
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
	ldr r0, [sp, #0]
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 231b
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
240:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 240b
241:
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
	bne 242f
	b 243f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
243:
	cmp lr, #0
	bne 244f
	b 245f
244:
	orr r9, r1, r10, lsl #16
246:
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
	bne 246b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
245:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 241b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
247:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 247b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
248:
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
	bne 248b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
249:
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
	bne 250f
	b 251f
250:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
251:
	cmp lr, #0
	bne 252f
	b 253f
252:
	orr r9, r1, r10, lsl #16
254:
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
	bne 254b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
253:
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
	bne 249b
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
257:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 257b
258:
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
	bne 259f
	b 260f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
260:
	cmp lr, #0
	bne 261f
	b 262f
261:
	orr r9, r1, r10, lsl #16
263:
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
	bne 263b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
262:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 258b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
264:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 264b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
265:
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
	bne 265b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
266:
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
	bne 267f
	b 268f
267:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
268:
	cmp lr, #0
	bne 269f
	b 270f
269:
	orr r9, r1, r10, lsl #16
271:
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
	bne 271b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
270:
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
	bne 266b
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
274:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 274b
275:
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
	bne 276f
	b 277f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
277:
	cmp lr, #0
	bne 278f
	b 279f
278:
	orr r9, r1, r10, lsl #16
280:
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
	bne 280b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
279:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 275b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
281:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 281b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
282:
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
	bne 282b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
283:
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
	bne 284f
	b 285f
284:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
285:
	cmp lr, #0
	bne 286f
	b 287f
286:
	orr r9, r1, r10, lsl #16
288:
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
	bne 288b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
287:
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
	bne 283b
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
289:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 289b
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
290:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 290b
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
291:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 291b
292:
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
	bne 293f
	b 294f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
294:
	cmp lr, #0
	bne 295f
	b 296f
295:
	orr r9, r1, r10, lsl #16
297:
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
	bne 297b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
296:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 292b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
298:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 298b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
299:
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
	bne 299b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2100:
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
	bne 2101f
	b 2102f
2101:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2102:
	cmp lr, #0
	bne 2103f
	b 2104f
2103:
	orr r9, r1, r10, lsl #16
2105:
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
	bne 2105b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2104:
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
	bne 2100b
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
2107:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2107b
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
2108:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2108b
2109:
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
	bne 2110f
	b 2111f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2111:
	cmp lr, #0
	bne 2112f
	b 2113f
2112:
	orr r9, r1, r10, lsl #16
2114:
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
	bne 2114b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2113:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2109b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2115:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2115b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2116:
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
	bne 2116b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2117:
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
	bne 2118f
	b 2119f
2118:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2119:
	cmp lr, #0
	bne 2120f
	b 2121f
2120:
	orr r9, r1, r10, lsl #16
2122:
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
	bne 2122b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2121:
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
	bne 2117b
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
2123:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2123b
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
2124:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2124b
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
2125:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2125b
2126:
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
	bne 2127f
	b 2128f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2128:
	cmp lr, #0
	bne 2129f
	b 2130f
2129:
	orr r9, r1, r10, lsl #16
2131:
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
	bne 2131b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2130:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2126b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2132:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2132b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2133:
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
	bne 2133b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2134:
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
	bne 2135f
	b 2136f
2135:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2136:
	cmp lr, #0
	bne 2137f
	b 2138f
2137:
	orr r9, r1, r10, lsl #16
2139:
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
	bne 2139b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2138:
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
	bne 2134b
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
2141:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2141b
	ldr r0, [sp, #0]
	b 228f
227:
	ldr r1, [sp, #112]
	ldr r4, [r0, #96]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2142:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2142b
	mov r0, r5
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2143:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2143b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r11, [sp, #48]
	ldr r10, [r0, #120]
	ldr r12, [r0, #96]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #96]
	mov r4, #0
	sub r4, r4, r11
2144:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2144b
	ldr r0, [sp, #0]
228:
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #64]
	mov r4, r1
	ldr r1, [r0, #64]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2145:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2145b
	mov r0, r5
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #72]
2146:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2146b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #72]
	ldr r2, [sp, #8]
	ldr r2, [r2, #48]
	ldr r3, [r0, #48]
	add r1, r1, r3, lsl #3
	sub r2, r2, r3
	ldr r4, [r0, #72]
	mov r5, r0
	mov r0, r4
	lsl lr, r2, #3
	cmp lr, #0
	beq 2147f
2149:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2149b
	b 2148f
2147:
2148:
	mov r0, r5
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2150:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2150b
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
2151:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2151b
	mov r0, r5
2152:
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
	bne 2153f
	b 2154f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2154:
	cmp lr, #0
	bne 2155f
	b 2156f
2155:
	orr r9, r1, r10, lsl #16
2157:
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
	bne 2157b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2156:
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
	orr r9, r1, r10, lsl #16
2158:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2158b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2152b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
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
2160:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2160b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #104]
2161:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2161b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #112]
2162:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2162b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #104]
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #112]
	mov r7, r0
	mov r8, lr
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
	bne 2164f
	b 2165f
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
	ldr r5, [r0, #0]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2165:
	cmp lr, #0
	bne 2166f
	b 2167f
2166:
	orr r9, r1, r10, lsl #16
2168:
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
	bne 2168b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2167:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #72]
	ldr r4, [r0, #104]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2169:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2169b
	mov r0, r5
	mov r2, #5
	mov r3, #5
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
2170:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2170b
	mov r0, r5
2171:
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
	bne 2172f
	b 2173f
2172:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2173:
	cmp lr, #0
	bne 2174f
	b 2175f
2174:
	orr r9, r1, r10, lsl #16
2176:
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
	bne 2176b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2175:
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
	orr r9, r1, r10, lsl #16
2177:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2177b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2171b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2178:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2178b
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
2179:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2179b
	ldr r0, [sp, #0]
	mov r2, #5
	mov r3, #5
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
2180:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2180b
	mov r0, r5
2181:
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
	bne 2182f
	b 2183f
2182:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2183:
	cmp lr, #0
	bne 2184f
	b 2185f
2184:
	orr r9, r1, r10, lsl #16
2186:
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
	bne 2186b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2185:
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
	orr r9, r1, r10, lsl #16
2187:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2187b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2181b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2188:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2188b
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
2189:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2189b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #72]
2190:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2190b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #104]
	ldr r12, [r0, #112]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r7, r0
	mov r8, lr
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
	bne 2192f
	b 2193f
2192:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2193:
	cmp lr, #0
	bne 2194f
	b 2195f
2194:
	orr r9, r1, r10, lsl #16
2196:
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
	bne 2196b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2195:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
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
2197:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2197b
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
2198:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2198b
	mov r0, r5
2199:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2200:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2200b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2199b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2201:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2201b
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
2202:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2202b
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
2203:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2203b
	mov r0, r5
2204:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2205:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2205b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2204b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2206:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2206b
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
2207:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2207b
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
2208:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2208b
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
2209:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2209b
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
2210:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2210b
	ldr r0, [sp, #0]
2211:
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
2212:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2212b
	mov r0, r5
2213:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2214:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2214b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2213b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2215:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2215b
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
2216:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2216b
	ldr r0, [sp, #0]
	mov r11, #1
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #220]
	mov r10, r0
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
	ldr r1, [r0, #220]
	ldr r2, [r0, #48]
	add r2, r2, #2
	add r1, r1, r2, lsl #3
	str r1, [r0, #220]
	ldr r1, [r0, #228]
	add r1, r1, #1
	str r1, [r0, #228]
	cmp r1, #8
	bne 2211b
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
2218:
	ldr r2, [r0, #128]
	ldrb r1, [r2, #0]
	str r1, [r0, #200]
	mov r1, #8
	str r1, [r0, #192]
2219:
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
2220:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2220b
	mov r0, r5
2221:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2222:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2222b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2221b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2223:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2223b
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
2224:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2224b
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
	beq 2225f
	b 2226f
2225:
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
2227:
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
2228:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2228b
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
	bne 2227b
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
2229:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2229b
	mov r0, r5
2230:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2231:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2231b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2230b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2232:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2232b
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
2233:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2233b
	ldr r0, [sp, #0]
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
2226:
	ldr r1, [r0, #200]
	add r1, r1, r1
	str r1, [r0, #200]
	ldr r1, [r0, #192]
	subs r1, r1, #1
	str r1, [r0, #192]
	bne 2219b
	ldr r1, [r0, #128]
	add r1, r1, #1
	str r1, [r0, #128]
	ldr r1, [r0, #132]
	subs r1, r1, #1
	str r1, [r0, #132]
	bne 2218b
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
2234:
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
2235:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2235b
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
	bne 2234b
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
2236:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2236b
	mov r0, r5
2237:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2238:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2238b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2237b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2239:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2239b
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
2240:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2240b
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
2241:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2241b
	mov r0, r5
2242:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2243:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2243b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2242b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2244:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2244b
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
2245:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2245b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #112]
	mov r4, r1
	ldr r1, [r0, #112]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2246:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2246b
	mov r0, r5
	ldr r0, [sp, #8]
	add r12, sp, #0
	str r0, [r12, #0]
	ldr r0, [r0, #228]
	add r12, sp, #0
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
2247:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2247b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2248:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2248b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #64]
2249:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2249b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #112]
2250:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2250b
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
	add r2, r2, #8
	lsr r2, r2, #5
	sub r1, r7, r2
	lsr r1, r1, #31
	mov r3, #0
	sub r1, r3, r1
	sub r2, r2, r7
	and r2, r2, r1
	add r7, r7, r2
	str r7, [r0, #48]
	str r3, [r0, #52]
	mov r8, r0
	add r5, r7, #2
	lsl r5, r5, #3
	add r4, r0, #256
	add r0, r0, #64
	mov lr, #8
2251:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 2251b
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
2252:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2252b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2253:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2253b
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
2254:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2254b
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
	ldr r1, [r0, #48]
	ldr r2, [sp, #76]
	add r2, r2, #7
	lsr r2, r2, #3
	cmp r1, r2
	beq 2256f
	mov r2, #4
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2258:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2258b
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
2259:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2259b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
2260:
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
2261:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2261b
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
	orr r9, r1, r10, lsl #16
2266:
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
	bne 2266b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2265:
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
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 2260b
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
	orr r9, r1, r10, lsl #16
2275:
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
	bne 2275b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	orr r9, r1, r10, lsl #16
2283:
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
	bne 2283b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
2286:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2286b
2287:
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
	bne 2288f
	b 2289f
2288:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2289:
	cmp lr, #0
	bne 2290f
	b 2291f
2290:
	orr r9, r1, r10, lsl #16
2292:
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
	bne 2292b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2291:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2287b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2293:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2293b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2294:
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
	bne 2294b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2295:
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
	bne 2296f
	b 2297f
2296:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2297:
	cmp lr, #0
	bne 2298f
	b 2299f
2298:
	orr r9, r1, r10, lsl #16
2300:
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
	bne 2300b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2299:
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
	bne 2295b
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
2301:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2301b
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
2302:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2302b
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
2303:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2303b
2304:
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
	bne 2305f
	b 2306f
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
	ldr r5, [r0, #0]
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r11, r4, #0
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2306:
	cmp lr, #0
	bne 2307f
	b 2308f
2307:
	orr r9, r1, r10, lsl #16
2309:
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
	bne 2309b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2308:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2304b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2310:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2310b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2311:
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
	bne 2311b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2312:
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
	bne 2313f
	b 2314f
2313:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2314:
	cmp lr, #0
	bne 2315f
	b 2316f
2315:
	orr r9, r1, r10, lsl #16
2317:
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
	bne 2317b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2316:
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
	bne 2312b
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
2320:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2320b
2321:
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
	bne 2322f
	b 2323f
2322:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2323:
	cmp lr, #0
	bne 2324f
	b 2325f
2324:
	orr r9, r1, r10, lsl #16
2326:
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
	bne 2326b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2325:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2321b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2327:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2327b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2328:
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
	bne 2328b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2329:
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
	bne 2330f
	b 2331f
2330:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2331:
	cmp lr, #0
	bne 2332f
	b 2333f
2332:
	orr r9, r1, r10, lsl #16
2334:
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
	bne 2334b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2333:
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
	bne 2329b
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
2335:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2335b
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
2336:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2336b
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
2337:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2337b
2338:
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
	bne 2339f
	b 2340f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2340:
	cmp lr, #0
	bne 2341f
	b 2342f
2341:
	orr r9, r1, r10, lsl #16
2343:
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
	bne 2343b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2342:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2338b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2344:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2344b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2345:
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
	bne 2345b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2346:
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
	bne 2347f
	b 2348f
2347:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2348:
	cmp lr, #0
	bne 2349f
	b 2350f
2349:
	orr r9, r1, r10, lsl #16
2351:
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
	bne 2351b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2350:
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
	bne 2346b
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
2352:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2352b
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
2353:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2353b
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
2354:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2354b
2355:
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
	bne 2356f
	b 2357f
2356:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2357:
	cmp lr, #0
	bne 2358f
	b 2359f
2358:
	orr r9, r1, r10, lsl #16
2360:
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
	bne 2360b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2359:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2355b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2361:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2361b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2362:
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
	bne 2362b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2363:
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
	bne 2364f
	b 2365f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2365:
	cmp lr, #0
	bne 2366f
	b 2367f
2366:
	orr r9, r1, r10, lsl #16
2368:
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
	bne 2368b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2367:
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
	bne 2363b
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
2369:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2369b
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
2370:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2370b
	ldr r0, [sp, #0]
	b 2257f
2256:
	ldr r1, [sp, #112]
	ldr r2, [sp, #68]
	add r2, r2, #7
	lsr r2, r2, #3
	sub r3, r2, #2
	lsr r3, r3, #31
	add r2, r2, r3
	add r1, r1, r2, lsl #3
	ldr r4, [r0, #96]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2371:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2371b
	mov r0, r5
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2372:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2372b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r11, [sp, #48]
	ldr r10, [r0, #120]
	ldr r12, [r0, #96]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #96]
	mov r4, #0
	sub r4, r4, r11
2373:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2373b
	ldr r0, [sp, #0]
2257:
	ldr r1, [sp, #8]
	ldr r1, [r1, #228]
	ldr r1, [r1, #64]
	mov r4, r1
	ldr r1, [r0, #64]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2374:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2374b
	mov r0, r5
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #72]
2375:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2375b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #228]
	ldr r1, [r1, #72]
	ldr r2, [sp, #8]
	ldr r2, [r2, #48]
	ldr r3, [r0, #48]
	add r1, r1, r3, lsl #3
	sub r2, r2, r3
	ldr r4, [r0, #72]
	mov r5, r0
	mov r0, r4
	lsl lr, r2, #3
	cmp lr, #0
	beq 2376f
2378:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2378b
	b 2377f
2376:
2377:
	mov r0, r5
	mov r2, #7
	mov r5, #1
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
2380:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2380b
	mov r0, r5
2381:
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
	bne 2382f
	b 2383f
2382:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2383:
	cmp lr, #0
	bne 2384f
	b 2385f
2384:
	orr r9, r1, r10, lsl #16
2386:
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
	bne 2386b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2385:
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
	orr r9, r1, r10, lsl #16
2387:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2387b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2381b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
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
2389:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2389b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #104]
2390:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2390b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #112]
2391:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2391b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #104]
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #112]
	mov r7, r0
	mov r8, lr
	mov r11, #0
2392:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2392b
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
	bne 2393f
	b 2394f
2393:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2394:
	cmp lr, #0
	bne 2395f
	b 2396f
2395:
	orr r9, r1, r10, lsl #16
2397:
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
	bne 2397b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2396:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #228]
	ldr r1, [r1, #72]
	ldr r4, [r0, #104]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2398:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2398b
	mov r0, r5
	mov r2, #5
	mov r3, #5
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
2399:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2399b
	mov r0, r5
2400:
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
	bne 2401f
	b 2402f
2401:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2402:
	cmp lr, #0
	bne 2403f
	b 2404f
2403:
	orr r9, r1, r10, lsl #16
2405:
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
	bne 2405b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2404:
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
	orr r9, r1, r10, lsl #16
2406:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2406b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2400b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
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
	mov r2, #5
	mov r3, #5
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
2409:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2409b
	mov r0, r5
2410:
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
	orr r9, r1, r10, lsl #16
2415:
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
	bne 2415b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2414:
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
	orr r9, r1, r10, lsl #16
2416:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2416b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2410b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2417:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2417b
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
2418:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2418b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #72]
2419:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2419b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #104]
	ldr r12, [r0, #112]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r7, r0
	mov r8, lr
	mov r11, #0
2420:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2420b
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
	bne 2421f
	b 2422f
2421:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2422:
	cmp lr, #0
	bne 2423f
	b 2424f
2423:
	orr r9, r1, r10, lsl #16
2425:
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
	bne 2425b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2424:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
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
2426:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2426b
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
2427:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2427b
	mov r0, r5
2428:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2429:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2429b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2428b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2430:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2430b
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
2431:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2431b
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
2432:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2432b
	mov r0, r5
2433:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2434:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2434b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2433b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2435:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2435b
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
2436:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2436b
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
2437:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2437b
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
2438:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2438b
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
2439:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2439b
	ldr r0, [sp, #0]
2440:
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
2441:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2441b
	mov r0, r5
2442:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2443:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2443b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2442b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2444:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2444b
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
2445:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2445b
	ldr r0, [sp, #0]
	mov r11, #1
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #220]
	mov r10, r0
	mov r4, #0
	sub r4, r4, r11
2446:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2446b
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
	bne 2440b
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
2447:
	ldr r2, [r0, #128]
	ldrb r1, [r2, #0]
	str r1, [r0, #200]
	mov r1, #8
	str r1, [r0, #192]
2448:
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
2449:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2449b
	mov r0, r5
2450:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2451:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2451b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2450b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2452:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2452b
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
2453:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2453b
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
	beq 2454f
	b 2455f
2454:
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
2456:
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
2457:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2457b
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
	bne 2456b
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
2458:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2458b
	mov r0, r5
2459:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2460:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2460b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2459b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2461:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2461b
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
2462:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2462b
	ldr r0, [sp, #0]
	mov r1, #0
	str r1, [r0, #196]
	str r1, [r0, #204]
2455:
	ldr r1, [r0, #200]
	add r1, r1, r1
	str r1, [r0, #200]
	ldr r1, [r0, #192]
	subs r1, r1, #1
	str r1, [r0, #192]
	bne 2448b
	ldr r1, [r0, #128]
	add r1, r1, #1
	str r1, [r0, #128]
	ldr r1, [r0, #132]
	subs r1, r1, #1
	str r1, [r0, #132]
	bne 2447b
	ldr r12, [r0, #120]
	ldr r1, [r0, #48]
	add r1, r1, #2
	lsl r1, r1, #3
	add r12, r12, r1
	str r12, [r0, #220]
	mov r1, #0
	str r1, [r0, #228]
2463:
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
2464:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2464b
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
	bne 2463b
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
2465:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2465b
	mov r0, r5
2466:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2467:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2467b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2466b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2468:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2468b
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
2469:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2469b
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
2470:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2470b
	mov r0, r5
2471:
	ldr r1, [r0, #16]
	ldr r1, [r1, #0]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	umaal r6, r8, r5, r2
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
	ldr r3, [r12, #0]
	ldr r5, [r4, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	add r4, r4, #4
	subs lr, lr, #1
2472:
	ldr r3, [r12, #0]
	ldr r6, [r0, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r12, #4]
	ldr r10, [r0, #8]
	umaal r10, r7, r3, r1
	ldr r5, [r4, #0]
	umaal r6, r8, r5, r2
	str r6, [r0, #0]
	ldr r5, [r4, #4]
	umaal r10, r8, r5, r2
	str r10, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 2472b
	ldr r3, [r0, #4]
	ldr r4, [r0, #8]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
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
	bne 2471b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2473:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2473b
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
2474:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2474b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #228]
	ldr r1, [r1, #112]
	mov r4, r1
	ldr r1, [r0, #112]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2475:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2475b
	mov r0, r5
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
2476:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2476b
	mov r0, r5
	ldr r0, [sp, #0]
	ldr r4, [sp, #96]
	ldr r6, [sp, #100]
	mov r2, #4
	add r2, r0, r2, lsl #3
	ldr r5, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r5
2477:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2477b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2478:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2478b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #104]
2479:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2479b
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
	add r2, r2, #8
	lsr r2, r2, #5
	sub r1, r7, r2
	lsr r1, r1, #31
	mov r3, #0
	sub r1, r3, r1
	sub r2, r2, r7
	and r2, r2, r1
	add r7, r7, r2
	str r7, [r0, #48]
	str r3, [r0, #52]
	mov r8, r0
	add r5, r7, #2
	lsl r5, r5, #3
	add r4, r0, #256
	add r0, r0, #64
	mov lr, #8
2480:
	str r4, [r0, #0]
	str r3, [r0, #4]
	add r0, r0, #8
	add r4, r4, r5
	subs lr, lr, #1
	bne 2480b
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
2481:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2481b
	mov r0, r5
	add r1, r4, r6
	sub r1, r1, #1
	mov lr, r6
2482:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2482b
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
2483:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2483b
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
2484:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2484b
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
	ldr r1, [r0, #48]
	ldr r2, [sp, #68]
	add r2, r2, #7
	lsr r2, r2, #3
	cmp r1, r2
	beq 2485f
	mov r2, #4
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2487:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2487b
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
2488:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2488b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r1, [r0, #48]
	add r1, r1, r1, lsl #6
	str r1, [r0, #208]
2489:
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
2490:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2490b
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
	bne 2491f
	b 2492f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2492:
	cmp lr, #0
	bne 2493f
	b 2494f
2493:
	orr r9, r1, r10, lsl #16
2495:
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
	bne 2495b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2494:
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
2496:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2496b
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
2497:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2497b
	ldr r0, [sp, #0]
	ldr r1, [r0, #208]
	subs r1, r1, #1
	str r1, [r0, #208]
	bne 2489b
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
2498:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2498b
2499:
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
	bne 2500f
	b 2501f
2500:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2501:
	cmp lr, #0
	bne 2502f
	b 2503f
2502:
	orr r9, r1, r10, lsl #16
2504:
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
	bne 2504b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2503:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2499b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2505:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2505b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2506:
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
	bne 2506b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2507:
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
	bne 2508f
	b 2509f
2508:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2509:
	cmp lr, #0
	bne 2510f
	b 2511f
2510:
	orr r9, r1, r10, lsl #16
2512:
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
	bne 2512b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2511:
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
	bne 2507b
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
2513:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2513b
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
2514:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2514b
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
2515:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2515b
2516:
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
	bne 2517f
	b 2518f
2517:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2518:
	cmp lr, #0
	bne 2519f
	b 2520f
2519:
	orr r9, r1, r10, lsl #16
2521:
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
	bne 2521b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2520:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2516b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2522:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2522b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2523:
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
	bne 2523b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2524:
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
	bne 2525f
	b 2526f
2525:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2526:
	cmp lr, #0
	bne 2527f
	b 2528f
2527:
	orr r9, r1, r10, lsl #16
2529:
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
	bne 2529b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2528:
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
	bne 2524b
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
2530:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2530b
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
2531:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2531b
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
2532:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2532b
2533:
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
	bne 2534f
	b 2535f
2534:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2535:
	cmp lr, #0
	bne 2536f
	b 2537f
2536:
	orr r9, r1, r10, lsl #16
2538:
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
	bne 2538b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2537:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2533b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2539:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2539b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2540:
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
	bne 2540b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2541:
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
	bne 2542f
	b 2543f
2542:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2543:
	cmp lr, #0
	bne 2544f
	b 2545f
2544:
	orr r9, r1, r10, lsl #16
2546:
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
	bne 2546b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2545:
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
	bne 2541b
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
2547:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2547b
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
2548:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2548b
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
2549:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2549b
2550:
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
	bne 2551f
	b 2552f
2551:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2552:
	cmp lr, #0
	bne 2553f
	b 2554f
2553:
	orr r9, r1, r10, lsl #16
2555:
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
	bne 2555b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2554:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2550b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2556:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2556b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2557:
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
	bne 2557b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2558:
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
	bne 2559f
	b 2560f
2559:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2560:
	cmp lr, #0
	bne 2561f
	b 2562f
2561:
	orr r9, r1, r10, lsl #16
2563:
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
	bne 2563b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2562:
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
	bne 2558b
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
2564:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2564b
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
2565:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2565b
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
2566:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2566b
2567:
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
	bne 2568f
	b 2569f
2568:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2569:
	cmp lr, #0
	bne 2570f
	b 2571f
2570:
	orr r9, r1, r10, lsl #16
2572:
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
	bne 2572b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2571:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2567b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2573:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2573b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2574:
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
	bne 2574b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2575:
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
	bne 2576f
	b 2577f
2576:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2577:
	cmp lr, #0
	bne 2578f
	b 2579f
2578:
	orr r9, r1, r10, lsl #16
2580:
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
	bne 2580b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2579:
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
	bne 2575b
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
2581:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2581b
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
2582:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2582b
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
2583:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2583b
2584:
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
	bne 2585f
	b 2586f
2585:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2586:
	cmp lr, #0
	bne 2587f
	b 2588f
2587:
	orr r9, r1, r10, lsl #16
2589:
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
	bne 2589b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2588:
	orr r1, r1, r10, lsl #16
	str r11, [r0, #0]
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #16]
	subs lr, lr, #1
	str lr, [r0, #16]
	bne 2584b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr lr, [r0, #0]
	lsl lr, lr, #1
	add r0, r0, #24
	mov r11, #0
2590:
	ldr r4, [r0, #0]
	orr r3, r11, r4, lsl #1
	lsr r11, r4, #31
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2590b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r12, [r0, #8]
	ldr lr, [r0, #0]
	add r0, r0, #24
	mov r11, #0
2591:
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
	bne 2591b
	ldr r0, [sp, #0]
	ldr r0, [r0, #80]
	ldr r1, [r0, #0]
	str r1, [r0, #16]
	add r1, r0, #24
	str r1, [r0, #20]
	mov r1, #0
	str r1, [r0, #12]
2592:
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
	bne 2593f
	b 2594f
2593:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2594:
	cmp lr, #0
	bne 2595f
	b 2596f
2595:
	orr r9, r1, r10, lsl #16
2597:
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
	bne 2597b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2596:
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
	bne 2592b
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
2598:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2598b
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
2599:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2599b
	ldr r0, [sp, #0]
	b 2486f
2485:
	ldr r1, [sp, #112]
	ldr r4, [r0, #96]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2600:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2600b
	mov r0, r5
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2601:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2601b
	str r5, [r4, #0]
	ldr r0, [sp, #0]
	ldr r11, [sp, #48]
	ldr r10, [r0, #120]
	ldr r12, [r0, #96]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #96]
	mov r4, #0
	sub r4, r4, r11
2602:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2602b
	ldr r0, [sp, #0]
2486:
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #72]
2603:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2603b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #96]
	ldr r2, [sp, #8]
	ldr r2, [r2, #48]
	ldr r3, [r0, #48]
	add r1, r1, r3, lsl #3
	sub r2, r2, r3
	ldr r4, [r0, #72]
	mov r5, r0
	mov r0, r4
	lsl lr, r2, #3
	cmp lr, #0
	beq 2604f
2606:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2606b
	b 2605f
2604:
2605:
	mov r0, r5
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2607:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2607b
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
2608:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2608b
	mov r0, r5
2609:
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
	bne 2610f
	b 2611f
2610:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2611:
	cmp lr, #0
	bne 2612f
	b 2613f
2612:
	orr r9, r1, r10, lsl #16
2614:
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
	bne 2614b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2613:
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
	orr r9, r1, r10, lsl #16
2615:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2615b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2609b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2616:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2616b
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
2617:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2617b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #104]
2618:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2618b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #112]
2619:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2619b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #104]
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #112]
	mov r7, r0
	mov r8, lr
	mov r11, #0
2620:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2620b
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
	orr r9, r1, r10, lsl #16
2625:
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
	bne 2625b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2624:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #96]
	ldr r4, [r0, #104]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2626:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2626b
	mov r0, r5
	mov r2, #5
	mov r3, #5
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
2627:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2627b
	mov r0, r5
2628:
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
	orr r9, r1, r10, lsl #16
2633:
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
	bne 2633b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2632:
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
	orr r9, r1, r10, lsl #16
2634:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2634b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2628b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2635:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2635b
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
2636:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2636b
	ldr r0, [sp, #0]
	mov r2, #5
	mov r3, #5
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
2637:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2637b
	mov r0, r5
2638:
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
	bne 2639f
	b 2640f
2639:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2640:
	cmp lr, #0
	bne 2641f
	b 2642f
2641:
	orr r9, r1, r10, lsl #16
2643:
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
	bne 2643b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2642:
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
	orr r9, r1, r10, lsl #16
2644:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2644b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2638b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2645:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2645b
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
2646:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2646b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #72]
2647:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2647b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #104]
	ldr r12, [r0, #112]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r7, r0
	mov r8, lr
	mov r11, #0
2648:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2648b
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
	bne 2649f
	b 2650f
2649:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2650:
	cmp lr, #0
	bne 2651f
	b 2652f
2651:
	orr r9, r1, r10, lsl #16
2653:
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
	bne 2653b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2652:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #96]
	mov r4, r1
	ldr r1, [r0, #72]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2654:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2654b
	mov r0, r5
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #72]
2655:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2655b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #72]
	ldr r2, [sp, #8]
	ldr r2, [r2, #48]
	ldr r3, [r0, #48]
	add r1, r1, r3, lsl #3
	sub r2, r2, r3
	ldr r4, [r0, #72]
	mov r5, r0
	mov r0, r4
	lsl lr, r2, #3
	cmp lr, #0
	beq 2656f
2658:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2658b
	b 2657f
2656:
2657:
	mov r0, r5
	mov r2, #7
	mov r5, #1
	add r2, r0, r2, lsl #3
	ldr r4, [r2, #64]
	ldr lr, [r0, #48]
	add lr, lr, lr
	mov r3, #0
	mov r0, r4
2659:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2659b
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
2660:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2660b
	mov r0, r5
2661:
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
	bne 2662f
	b 2663f
2662:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2663:
	cmp lr, #0
	bne 2664f
	b 2665f
2664:
	orr r9, r1, r10, lsl #16
2666:
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
	bne 2666b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2665:
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
	orr r9, r1, r10, lsl #16
2667:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2667b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2661b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2668:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2668b
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
2669:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2669b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #104]
2670:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2670b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #112]
2671:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2671b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #104]
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #112]
	mov r7, r0
	mov r8, lr
	mov r11, #0
2672:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2672b
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
	bne 2673f
	b 2674f
2673:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2674:
	cmp lr, #0
	bne 2675f
	b 2676f
2675:
	orr r9, r1, r10, lsl #16
2677:
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
	bne 2677b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2676:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #72]
	ldr r4, [r0, #104]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2678:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2678b
	mov r0, r5
	mov r2, #5
	mov r3, #5
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
2679:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2679b
	mov r0, r5
2680:
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
	bne 2681f
	b 2682f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2682:
	cmp lr, #0
	bne 2683f
	b 2684f
2683:
	orr r9, r1, r10, lsl #16
2685:
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
	bne 2685b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2684:
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
	orr r9, r1, r10, lsl #16
2686:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2686b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2680b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2687:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2687b
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
2688:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2688b
	ldr r0, [sp, #0]
	mov r2, #5
	mov r3, #5
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
2689:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2689b
	mov r0, r5
2690:
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
	bne 2691f
	b 2692f
2691:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2692:
	cmp lr, #0
	bne 2693f
	b 2694f
2693:
	orr r9, r1, r10, lsl #16
2695:
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
	bne 2695b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2694:
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
	orr r9, r1, r10, lsl #16
2696:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2696b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2690b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2697:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2697b
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
2698:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2698b
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #72]
2699:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2699b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #104]
	ldr r12, [r0, #112]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #72]
	mov r7, r0
	mov r8, lr
	mov r11, #0
2700:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2700b
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
	bne 2701f
	b 2702f
2701:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2702:
	cmp lr, #0
	bne 2703f
	b 2704f
2703:
	orr r9, r1, r10, lsl #16
2705:
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
	bne 2705b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2704:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #112]
	ldr r4, [r0, #104]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2706:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2706b
	mov r0, r5
	ldr lr, [r0, #48]
	lsl lr, lr, #1
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #112]
2707:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2707b
	ldr r0, [sp, #0]
	ldr r9, [r0, #64]
	ldr r10, [r0, #104]
	ldr r12, [r0, #72]
	ldr lr, [r0, #48]
	add lr, lr, lr
	ldr r0, [r0, #112]
	mov r7, r0
	mov r8, lr
	mov r11, #0
2708:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2708b
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
	bne 2709f
	b 2710f
2709:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2710:
	cmp lr, #0
	bne 2711f
	b 2712f
2711:
	orr r9, r1, r10, lsl #16
2713:
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
	bne 2713b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2712:
	orr r1, r1, r10, lsl #16
	ldr r3, [r0, #0]
	ldr r4, [r0, #4]
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #0]
	str r4, [r0, #4]
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #96]
	ldr r4, [r0, #72]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2714:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2714b
	mov r0, r5
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
2715:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2715b
	mov r0, r5
2716:
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
	bne 2717f
	b 2718f
2717:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2718:
	cmp lr, #0
	bne 2719f
	b 2720f
2719:
	orr r9, r1, r10, lsl #16
2721:
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
	bne 2721b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2720:
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
	orr r9, r1, r10, lsl #16
2722:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2722b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2716b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2723:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2723b
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
2724:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2724b
	ldr r0, [sp, #0]
	mov r2, #5
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
2725:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2725b
	mov r0, r5
2726:
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
	bne 2727f
	b 2728f
2727:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2728:
	cmp lr, #0
	bne 2729f
	b 2730f
2729:
	orr r9, r1, r10, lsl #16
2731:
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
	bne 2731b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2730:
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
	orr r9, r1, r10, lsl #16
2732:
	ldr r2, [r12, #0]
	ldr r3, [r0, #4]
	mov r5, r3
	umaal r3, r11, r2, r9
	str r3, [r0, #0]
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2732b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
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
	bne 2726b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
2733:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2733b
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
2734:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 2734b
	ldr r0, [sp, #0]
	ldr r1, [sp, #8]
	ldr r1, [r1, #224]
	ldr r1, [r1, #104]
	mov r4, r1
	ldr r1, [r0, #104]
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r5, r0
	mov r0, r4
2735:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2735b
	mov r0, r5
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
2736:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2736b
	mov r0, r5
	ldr r0, [sp, #0]
	ldr lr, [r0, #48]
	lsl lr, lr, #2
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #232]
2737:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2737b
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
2738:
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
	bne 2739f
	b 2740f
2739:
	ldr r2, [r12, #0]
	lsr r6, r2, #16
	and r2, r2, r9
	mul r3, r1, r2
	mul r5, r10, r2
	mul r7, r1, r6
	mul r4, r10, r6
	adds r3, r3, r5, lsl #16
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
2740:
	cmp lr, #0
	bne 2741f
	b 2742f
2741:
	orr r9, r1, r10, lsl #16
2743:
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
	bne 2743b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2742:
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
	bne 2738b
	ldr lr, [r0, #48]
	lsl lr, lr, #2
	add lr, lr, #2
	mov r3, #0
	ldr r0, [r0, #240]
2744:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 2744b
	ldr r0, [sp, #0]
	ldr r4, [r0, #240]
	mov r2, #1
	add r2, r0, r2, lsl #3
	ldr r1, [r2, #64]
	mov r5, r0
	ldr lr, [r0, #48]
	lsl lr, lr, #3
	mov r0, r4
2745:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 2745b
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
	bne 2746f
	b 2747f
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
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
2747:
	cmp lr, #0
	bne 2748f
	b 2749f
2748:
	orr r9, r1, r10, lsl #16
2750:
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
	bne 2750b
	mov r6, r5
	mov r4, #0
	umaal r6, r4, r2, r9
	lsr r6, r2, #16
	movw r9, #65535
	and r2, r2, r9
	mul r7, r1, r6
2749:
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
2751:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	sub r1, r1, #1
	subs lr, lr, #1
	bne 2751b
	mov r0, r4
	mov lr, r6
	ldr r4, [sp, #48]
	mov r2, #0
	sub r2, r2, r4
2752:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 2752b
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
