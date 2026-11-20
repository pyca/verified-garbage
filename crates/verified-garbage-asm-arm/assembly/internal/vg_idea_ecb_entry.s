// The functions of `src/internal/vg_idea_ecb_entry.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_idea_ecb_entry:
	sub sp, sp, #32
	add r3, sp, #0
	str r4, [r3, #0]
	str r5, [r3, #4]
	str r6, [r3, #8]
	str r7, [r3, #12]
	str r8, [r3, #16]
	str r9, [r3, #20]
	str r10, [r3, #24]
	str r11, [r3, #28]
	cmp r2, #0
	beq 20f
22:
	movw r12, #65535
	ldrb r4, [r1, #0]
	ldrb r8, [r1, #1]
	orr r4, r8, r4, lsl #8
	ldrb r5, [r1, #2]
	ldrb r8, [r1, #3]
	orr r5, r8, r5, lsl #8
	ldrb r6, [r1, #4]
	ldrb r8, [r1, #5]
	orr r6, r8, r6, lsl #8
	ldrb r7, [r1, #6]
	ldrb r8, [r1, #7]
	orr r7, r8, r7, lsl #8
	ldr r9, [r0, #0]
	sub r8, r4, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r4, r9, r12
	ldr r9, [r0, #6]
	sub r8, r7, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r7, r9, r12
	ldr r9, [r0, #2]
	add r5, r5, r9
	and r5, r5, r12
	ldr r9, [r0, #4]
	add r6, r6, r9
	and r6, r6, r12
	eor r10, r4, r6
	ldr r9, [r0, #8]
	sub r8, r10, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r10, r9, r12
	eor r11, r5, r7
	add r11, r11, r10
	ldr r9, [r0, #10]
	sub r8, r11, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r11, r9, r12
	add r10, r10, r11
	and r10, r10, r12
	eor r4, r4, r11
	eor r6, r6, r11
	eor r5, r5, r10
	eor r7, r7, r10
	ldr r9, [r0, #12]
	sub r8, r4, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r4, r9, r12
	ldr r9, [r0, #18]
	sub r8, r7, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r7, r9, r12
	ldr r9, [r0, #14]
	add r6, r6, r9
	and r6, r6, r12
	ldr r9, [r0, #16]
	add r5, r5, r9
	and r5, r5, r12
	eor r10, r4, r5
	ldr r9, [r0, #20]
	sub r8, r10, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r10, r9, r12
	eor r11, r6, r7
	add r11, r11, r10
	ldr r9, [r0, #22]
	sub r8, r11, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r11, r9, r12
	add r10, r10, r11
	and r10, r10, r12
	eor r4, r4, r11
	eor r5, r5, r11
	eor r6, r6, r10
	eor r7, r7, r10
	ldr r9, [r0, #24]
	sub r8, r4, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r4, r9, r12
	ldr r9, [r0, #30]
	sub r8, r7, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r7, r9, r12
	ldr r9, [r0, #26]
	add r5, r5, r9
	and r5, r5, r12
	ldr r9, [r0, #28]
	add r6, r6, r9
	and r6, r6, r12
	eor r10, r4, r6
	ldr r9, [r0, #32]
	sub r8, r10, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r10, r9, r12
	eor r11, r5, r7
	add r11, r11, r10
	ldr r9, [r0, #34]
	sub r8, r11, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r11, r9, r12
	add r10, r10, r11
	and r10, r10, r12
	eor r4, r4, r11
	eor r6, r6, r11
	eor r5, r5, r10
	eor r7, r7, r10
	ldr r9, [r0, #36]
	sub r8, r4, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r4, r9, r12
	ldr r9, [r0, #42]
	sub r8, r7, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r7, r9, r12
	ldr r9, [r0, #38]
	add r6, r6, r9
	and r6, r6, r12
	ldr r9, [r0, #40]
	add r5, r5, r9
	and r5, r5, r12
	eor r10, r4, r5
	ldr r9, [r0, #44]
	sub r8, r10, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r10, r9, r12
	eor r11, r6, r7
	add r11, r11, r10
	ldr r9, [r0, #46]
	sub r8, r11, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r11, r9, r12
	add r10, r10, r11
	and r10, r10, r12
	eor r4, r4, r11
	eor r5, r5, r11
	eor r6, r6, r10
	eor r7, r7, r10
	ldr r9, [r0, #48]
	sub r8, r4, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r4, r9, r12
	ldr r9, [r0, #54]
	sub r8, r7, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r7, r9, r12
	ldr r9, [r0, #50]
	add r5, r5, r9
	and r5, r5, r12
	ldr r9, [r0, #52]
	add r6, r6, r9
	and r6, r6, r12
	eor r10, r4, r6
	ldr r9, [r0, #56]
	sub r8, r10, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r10, r9, r12
	eor r11, r5, r7
	add r11, r11, r10
	ldr r9, [r0, #58]
	sub r8, r11, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r11, r9, r12
	add r10, r10, r11
	and r10, r10, r12
	eor r4, r4, r11
	eor r6, r6, r11
	eor r5, r5, r10
	eor r7, r7, r10
	ldr r9, [r0, #60]
	sub r8, r4, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r4, r9, r12
	ldr r9, [r0, #66]
	sub r8, r7, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r7, r9, r12
	ldr r9, [r0, #62]
	add r6, r6, r9
	and r6, r6, r12
	ldr r9, [r0, #64]
	add r5, r5, r9
	and r5, r5, r12
	eor r10, r4, r5
	ldr r9, [r0, #68]
	sub r8, r10, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r10, r9, r12
	eor r11, r6, r7
	add r11, r11, r10
	ldr r9, [r0, #70]
	sub r8, r11, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r11, r9, r12
	add r10, r10, r11
	and r10, r10, r12
	eor r4, r4, r11
	eor r5, r5, r11
	eor r6, r6, r10
	eor r7, r7, r10
	ldr r9, [r0, #72]
	sub r8, r4, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r4, r9, r12
	ldr r9, [r0, #78]
	sub r8, r7, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r7, r9, r12
	ldr r9, [r0, #74]
	add r5, r5, r9
	and r5, r5, r12
	ldr r9, [r0, #76]
	add r6, r6, r9
	and r6, r6, r12
	eor r10, r4, r6
	ldr r9, [r0, #80]
	sub r8, r10, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r10, r9, r12
	eor r11, r5, r7
	add r11, r11, r10
	ldr r9, [r0, #82]
	sub r8, r11, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r11, r9, r12
	add r10, r10, r11
	and r10, r10, r12
	eor r4, r4, r11
	eor r6, r6, r11
	eor r5, r5, r10
	eor r7, r7, r10
	ldr r9, [r0, #84]
	sub r8, r4, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r4, r9, r12
	ldr r9, [r0, #90]
	sub r8, r7, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r7, r9, r12
	ldr r9, [r0, #86]
	add r6, r6, r9
	and r6, r6, r12
	ldr r9, [r0, #88]
	add r5, r5, r9
	and r5, r5, r12
	eor r10, r4, r5
	ldr r9, [r0, #92]
	sub r8, r10, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r10, r9, r12
	eor r11, r6, r7
	add r11, r11, r10
	ldr r9, [r0, #94]
	sub r8, r11, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r11, r9, r12
	add r10, r10, r11
	and r10, r10, r12
	eor r4, r4, r11
	eor r5, r5, r11
	eor r6, r6, r10
	eor r7, r7, r10
	ldr r9, [r0, #96]
	sub r8, r4, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r4, r9, r12
	ldr r9, [r0, #100]
	lsr r9, r9, #16
	sub r8, r7, #1
	and r8, r8, r12
	add r8, r8, #1
	sub r9, r9, #1
	and r9, r9, r12
	add r9, r9, #1
	mul r8, r8, r9
	sub r8, r8, #1
	and r9, r8, r12
	add r9, r9, #1
	sub r9, r9, r8, lsr #16
	add r9, r9, r9, lsr #31
	and r7, r9, r12
	ldr r9, [r0, #98]
	add r6, r6, r9
	and r6, r6, r12
	ldr r9, [r0, #100]
	add r5, r5, r9
	and r5, r5, r12
	strb r4, [r1, #1]
	lsr r8, r4, #8
	strb r8, [r1, #0]
	strb r6, [r1, #3]
	lsr r8, r6, #8
	strb r8, [r1, #2]
	strb r5, [r1, #5]
	lsr r8, r5, #8
	strb r8, [r1, #4]
	strb r7, [r1, #7]
	lsr r8, r7, #8
	strb r8, [r1, #6]
	add r1, r1, #8
	subs r2, r2, #1
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
	add sp, sp, #32
	bx lr
