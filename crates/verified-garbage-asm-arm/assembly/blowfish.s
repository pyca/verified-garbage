// The functions of `src/blowfish.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_expand_key:
	sub sp, sp, #64
	add r3, sp, #0
	str r4, [r3, #0]
	str r5, [r3, #4]
	str r6, [r3, #8]
	str r7, [r3, #12]
	str r8, [r3, #16]
	str r9, [r3, #20]
	str r10, [r3, #24]
	str r11, [r3, #28]
	str lr, [r3, #32]
	movw r9, #:lower16:({VG_BLOWFISH_INIT}
	movt r9, #:upper16:({VG_BLOWFISH_INIT}
2:
	add r9, pc
3:
	add r11, r2, #0
	mov r12, #148
20:
	ldr r4, [r9, #0]
	ldr r5, [r9, #4]
	ldr r6, [r9, #8]
	ldr r7, [r9, #12]
	ldr r8, [r9, #16]
	ldr r10, [r9, #20]
	ldr lr, [r9, #24]
	str r4, [r11, #0]
	str r5, [r11, #4]
	str r6, [r11, #8]
	str r7, [r11, #12]
	str r8, [r11, #16]
	str r10, [r11, #20]
	str lr, [r11, #24]
	add r9, r9, #28
	add r11, r11, #28
	subs r12, r12, #1
	bne 20b
	ldr r4, [r9, #0]
	ldr r5, [r9, #4]
	ldr r6, [r9, #8]
	ldr r7, [r9, #12]
	ldr r8, [r9, #16]
	ldr r10, [r9, #20]
	str r4, [r11, #0]
	str r5, [r11, #4]
	str r6, [r11, #8]
	str r7, [r11, #12]
	str r8, [r11, #16]
	str r10, [r11, #20]
	mov r4, #0
	add r12, r2, #4096
	mov r8, #18
21:
	mov r5, #0
	add r7, r0, r4
	ldrb r6, [r7, #0]
	lsl r5, r5, #8
	orr r5, r5, r6
	add r4, r4, #1
	cmp r4, r1
	beq 22f
	b 23f
22:
	mov r4, #0
23:
	add r7, r0, r4
	ldrb r6, [r7, #0]
	lsl r5, r5, #8
	orr r5, r5, r6
	add r4, r4, #1
	cmp r4, r1
	beq 24f
	b 25f
24:
	mov r4, #0
25:
	add r7, r0, r4
	ldrb r6, [r7, #0]
	lsl r5, r5, #8
	orr r5, r5, r6
	add r4, r4, #1
	cmp r4, r1
	beq 26f
	b 27f
26:
	mov r4, #0
27:
	add r7, r0, r4
	ldrb r6, [r7, #0]
	lsl r5, r5, #8
	orr r5, r5, r6
	add r4, r4, #1
	cmp r4, r1
	beq 28f
	b 29f
28:
	mov r4, #0
29:
	ldr r6, [r12, #0]
	eor r6, r6, r5
	str r6, [r12, #0]
	add r12, r12, #4
	subs r8, r8, #1
	bne 21b
	mov r0, r2
	mov r1, #0
	mov r2, #0
	add r12, r0, #4096
	str r12, [r3, #36]
	mov r11, #9
	str r11, [r3, #40]
210:
	movw r8, #65535
	movt r8, #65535
	add r12, r0, #4096
211:
	ldr r9, [r12, #0]
	eor r1, r1, r9
	lsr r4, r1, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
212:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #0]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #256]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #512]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #768]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 212b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	mov lr, r5
	lsl r4, r1, #8
	lsr r4, r4, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
213:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #1024]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #1280]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #1536]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #1792]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 213b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	add lr, lr, r5
	lsl r4, r1, #16
	lsr r4, r4, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
214:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #2048]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #2304]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #2560]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #2816]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 214b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	eor lr, lr, r5
	and r4, r1, #255
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
215:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #3072]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #3328]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #3584]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #3840]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 215b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	add lr, lr, r5
	eor r2, r2, lr
	mov r9, r1
	mov r1, r2
	mov r2, r9
	add r12, r12, #4
	sub r9, r12, r0
	cmp r9, #4160
	bne 211b
	ldr r9, [r12, #0]
	eor r9, r1, r9
	ldr r1, [r12, #4]
	eor r1, r1, r2
	mov r2, r9
	ldr r12, [r3, #36]
	ldr r11, [r3, #40]
	str r1, [r12, #0]
	str r2, [r12, #4]
	add r12, r12, #8
	str r12, [r3, #36]
	subs r11, r11, #1
	str r11, [r3, #40]
	bne 210b
	str r0, [r3, #36]
	movw r11, #512
	str r11, [r3, #40]
216:
	movw r8, #65535
	movt r8, #65535
	add r12, r0, #4096
217:
	ldr r9, [r12, #0]
	eor r1, r1, r9
	lsr r4, r1, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
218:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #0]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #256]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #512]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #768]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 218b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	mov lr, r5
	lsl r4, r1, #8
	lsr r4, r4, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
219:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #1024]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #1280]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #1536]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #1792]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 219b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	add lr, lr, r5
	lsl r4, r1, #16
	lsr r4, r4, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
220:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #2048]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #2304]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #2560]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #2816]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 220b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	eor lr, lr, r5
	and r4, r1, #255
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
221:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #3072]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #3328]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #3584]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #3840]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 221b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	add lr, lr, r5
	eor r2, r2, lr
	mov r9, r1
	mov r1, r2
	mov r2, r9
	add r12, r12, #4
	sub r9, r12, r0
	cmp r9, #4160
	bne 217b
	ldr r9, [r12, #0]
	eor r9, r1, r9
	ldr r1, [r12, #4]
	eor r1, r1, r2
	mov r2, r9
	ldr r12, [r3, #36]
	ldr r11, [r3, #40]
	strb r1, [r12, #0]
	lsr r9, r1, #8
	strb r9, [r12, #256]
	lsr r9, r1, #16
	strb r9, [r12, #512]
	lsr r9, r1, #24
	strb r9, [r12, #768]
	strb r2, [r12, #1]
	lsr r9, r2, #8
	strb r9, [r12, #257]
	lsr r9, r2, #16
	strb r9, [r12, #513]
	lsr r9, r2, #24
	strb r9, [r12, #769]
	add r12, r12, #2
	sub r9, r12, r0
	and r9, r9, #255
	cmp r9, #0
	beq 222f
	b 223f
222:
	add r12, r12, #768
223:
	str r12, [r3, #36]
	subs r11, r11, #1
	str r11, [r3, #40]
	bne 216b
	ldr r4, [r3, #0]
	ldr r5, [r3, #4]
	ldr r6, [r3, #8]
	ldr r7, [r3, #12]
	ldr r8, [r3, #16]
	ldr r9, [r3, #20]
	ldr r10, [r3, #24]
	ldr r11, [r3, #28]
	ldr lr, [r3, #32]
	add r12, sp, #0
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
	add sp, sp, #64
	bx lr

vg_blowfish_ecb_encrypt:
	sub sp, sp, #256
	add r3, sp, #0
	str r4, [r3, #0]
	str r5, [r3, #4]
	str r6, [r3, #8]
	str r7, [r3, #12]
	str r8, [r3, #16]
	str r9, [r3, #20]
	str r10, [r3, #24]
	str r11, [r3, #28]
	str lr, [r3, #32]
	str r1, [r3, #36]
	str r2, [r3, #40]
	cmp r2, #0
	beq 20f
22:
	ldr r12, [r3, #36]
	ldr r1, [r12, #0]
	rev r1, r1
	ldr r2, [r12, #4]
	rev r2, r2
	movw r8, #65535
	movt r8, #65535
	add r12, r0, #4096
23:
	ldr r9, [r12, #0]
	eor r1, r1, r9
	lsr r4, r1, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
24:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #0]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #256]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #512]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #768]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 24b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	mov lr, r5
	lsl r4, r1, #8
	lsr r4, r4, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
25:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #1024]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #1280]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #1536]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #1792]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 25b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	add lr, lr, r5
	lsl r4, r1, #16
	lsr r4, r4, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
26:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #2048]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #2304]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #2560]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #2816]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 26b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	eor lr, lr, r5
	and r4, r1, #255
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
27:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #3072]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #3328]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #3584]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #3840]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 27b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	add lr, lr, r5
	eor r2, r2, lr
	mov r9, r1
	mov r1, r2
	mov r2, r9
	add r12, r12, #4
	sub r9, r12, r0
	cmp r9, #4160
	bne 23b
	ldr r9, [r12, #0]
	eor r9, r1, r9
	ldr r1, [r12, #4]
	eor r1, r1, r2
	mov r2, r9
	ldr r12, [r3, #36]
	ldr r11, [r3, #40]
	rev r1, r1
	str r1, [r12, #0]
	rev r2, r2
	str r2, [r12, #4]
	add r12, r12, #8
	str r12, [r3, #36]
	subs r11, r11, #1
	str r11, [r3, #40]
	bne 22b
	b 21f
20:
21:
	ldr r4, [r3, #0]
	ldr r5, [r3, #4]
	ldr r6, [r3, #8]
	ldr r7, [r3, #12]
	ldr r8, [r3, #16]
	ldr r9, [r3, #20]
	ldr r10, [r3, #24]
	ldr r11, [r3, #28]
	ldr lr, [r3, #32]
	add r12, sp, #0
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
	add sp, sp, #256
	bx lr

vg_blowfish_ecb_decrypt:
	sub sp, sp, #256
	add r3, sp, #0
	str r4, [r3, #0]
	str r5, [r3, #4]
	str r6, [r3, #8]
	str r7, [r3, #12]
	str r8, [r3, #16]
	str r9, [r3, #20]
	str r10, [r3, #24]
	str r11, [r3, #28]
	str lr, [r3, #32]
	str r1, [r3, #36]
	str r2, [r3, #40]
	cmp r2, #0
	beq 20f
22:
	ldr r12, [r3, #36]
	ldr r1, [r12, #0]
	rev r1, r1
	ldr r2, [r12, #4]
	rev r2, r2
	movw r8, #65535
	movt r8, #65535
	add r12, r0, #4160
23:
	ldr r9, [r12, #4]
	eor r1, r1, r9
	lsr r4, r1, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
24:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #0]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #256]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #512]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #768]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 24b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	mov lr, r5
	lsl r4, r1, #8
	lsr r4, r4, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
25:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #1024]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #1280]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #1536]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #1792]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 25b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	add lr, lr, r5
	lsl r4, r1, #16
	lsr r4, r4, #24
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
26:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #2048]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #2304]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #2560]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #2816]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 26b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	eor lr, lr, r5
	and r4, r1, #255
	mov r7, #255
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #24
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r7, #16
	eor r7, r7, r9
	and r7, r7, r6
	eor r7, r7, r9
	mov r5, #0
	mov r10, r0
	mov r11, #64
27:
	cmp r4, #4
	adc r6, r8, #0
	and r6, r6, r7
	sub r4, r4, #4
	ldr r9, [r10, #3072]
	and r9, r9, r6
	orr r5, r5, r9
	ldr r9, [r10, #3328]
	and r9, r9, r6
	orr r5, r5, r9, ror #24
	ldr r9, [r10, #3584]
	and r9, r9, r6
	orr r5, r5, r9, ror #16
	ldr r9, [r10, #3840]
	and r9, r9, r6
	orr r5, r5, r9, ror #8
	add r10, r10, #4
	subs r11, r11, #1
	bne 27b
	and r6, r4, #1
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #8
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	and r6, r4, #2
	cmp r6, #1
	adc r6, r8, #0
	ror r9, r5, #16
	eor r5, r5, r9
	and r5, r5, r6
	eor r5, r5, r9
	add lr, lr, r5
	eor r2, r2, lr
	mov r9, r1
	mov r1, r2
	mov r2, r9
	sub r12, r12, #4
	sub r9, r12, r0
	cmp r9, #4096
	bne 23b
	ldr r9, [r12, #4]
	eor r9, r1, r9
	ldr r1, [r12, #0]
	eor r1, r1, r2
	mov r2, r9
	ldr r12, [r3, #36]
	ldr r11, [r3, #40]
	rev r1, r1
	str r1, [r12, #0]
	rev r2, r2
	str r2, [r12, #4]
	add r12, r12, #8
	str r12, [r3, #36]
	subs r11, r11, #1
	str r11, [r3, #40]
	bne 22b
	b 21f
20:
21:
	ldr r4, [r3, #0]
	ldr r5, [r3, #4]
	ldr r6, [r3, #8]
	ldr r7, [r3, #12]
	ldr r8, [r3, #16]
	ldr r9, [r3, #20]
	ldr r10, [r3, #24]
	ldr r11, [r3, #28]
	ldr lr, [r3, #32]
	add r12, sp, #0
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
	add sp, sp, #256
	bx lr
