// The functions of `src/internal/vg_rc2_encrypt_block.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_encrypt_block:
	str r4, [r2, #0]
	str r5, [r2, #4]
	str r6, [r2, #8]
	str r7, [r2, #12]
	str r8, [r2, #16]
	str r9, [r2, #20]
	str r10, [r2, #24]
	str r11, [r2, #28]
	str lr, [r2, #32]
	ldrb r4, [r1, #0]
	ldrb r12, [r1, #1]
	orr r4, r4, r12, lsl #8
	ldrb r5, [r1, #2]
	ldrb r12, [r1, #3]
	orr r5, r5, r12, lsl #8
	ldrb r6, [r1, #4]
	ldrb r12, [r1, #5]
	orr r6, r6, r12, lsl #8
	ldrb r7, [r1, #6]
	ldrb r12, [r1, #7]
	orr r7, r7, r12, lsl #8
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #0]
	ldrb r9, [r0, #1]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #2]
	ldrb r9, [r0, #3]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #4]
	ldrb r9, [r0, #5]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #6]
	ldrb r9, [r0, #7]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #8]
	ldrb r9, [r0, #9]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #10]
	ldrb r9, [r0, #11]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #12]
	ldrb r9, [r0, #13]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #14]
	ldrb r9, [r0, #15]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #16]
	ldrb r9, [r0, #17]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #18]
	ldrb r9, [r0, #19]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #20]
	ldrb r9, [r0, #21]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #22]
	ldrb r9, [r0, #23]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #24]
	ldrb r9, [r0, #25]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #26]
	ldrb r9, [r0, #27]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #28]
	ldrb r9, [r0, #29]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #30]
	ldrb r9, [r0, #31]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #32]
	ldrb r9, [r0, #33]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #34]
	ldrb r9, [r0, #35]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #36]
	ldrb r9, [r0, #37]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #38]
	ldrb r9, [r0, #39]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
20:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 20b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
21:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 21b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
22:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 22b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
23:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 23b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #40]
	ldrb r9, [r0, #41]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #42]
	ldrb r9, [r0, #43]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #44]
	ldrb r9, [r0, #45]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #46]
	ldrb r9, [r0, #47]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #48]
	ldrb r9, [r0, #49]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #50]
	ldrb r9, [r0, #51]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #52]
	ldrb r9, [r0, #53]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #54]
	ldrb r9, [r0, #55]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #56]
	ldrb r9, [r0, #57]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #58]
	ldrb r9, [r0, #59]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #60]
	ldrb r9, [r0, #61]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #62]
	ldrb r9, [r0, #63]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #64]
	ldrb r9, [r0, #65]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #66]
	ldrb r9, [r0, #67]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #68]
	ldrb r9, [r0, #69]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #70]
	ldrb r9, [r0, #71]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #72]
	ldrb r9, [r0, #73]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #74]
	ldrb r9, [r0, #75]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #76]
	ldrb r9, [r0, #77]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #78]
	ldrb r9, [r0, #79]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #80]
	ldrb r9, [r0, #81]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #82]
	ldrb r9, [r0, #83]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #84]
	ldrb r9, [r0, #85]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #86]
	ldrb r9, [r0, #87]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
24:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 24b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
25:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 25b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
26:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 26b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
27:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 27b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #88]
	ldrb r9, [r0, #89]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #90]
	ldrb r9, [r0, #91]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #92]
	ldrb r9, [r0, #93]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #94]
	ldrb r9, [r0, #95]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #96]
	ldrb r9, [r0, #97]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #98]
	ldrb r9, [r0, #99]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #100]
	ldrb r9, [r0, #101]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #102]
	ldrb r9, [r0, #103]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #104]
	ldrb r9, [r0, #105]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #106]
	ldrb r9, [r0, #107]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #108]
	ldrb r9, [r0, #109]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #110]
	ldrb r9, [r0, #111]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #112]
	ldrb r9, [r0, #113]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #114]
	ldrb r9, [r0, #115]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #116]
	ldrb r9, [r0, #117]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #118]
	ldrb r9, [r0, #119]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #120]
	ldrb r9, [r0, #121]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #122]
	ldrb r9, [r0, #123]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #124]
	ldrb r9, [r0, #125]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #126]
	ldrb r9, [r0, #127]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	strb r4, [r1, #0]
	lsr r12, r4, #8
	strb r12, [r1, #1]
	strb r5, [r1, #2]
	lsr r12, r5, #8
	strb r12, [r1, #3]
	strb r6, [r1, #4]
	lsr r12, r6, #8
	strb r12, [r1, #5]
	strb r7, [r1, #6]
	lsr r12, r7, #8
	strb r12, [r1, #7]
	ldr r4, [r2, #0]
	ldr r5, [r2, #4]
	ldr r6, [r2, #8]
	ldr r7, [r2, #12]
	ldr r8, [r2, #16]
	ldr r9, [r2, #20]
	ldr r10, [r2, #24]
	ldr r11, [r2, #28]
	ldr lr, [r2, #32]
	bx lr
