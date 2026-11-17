// The functions of `src/internal/vg_ghash.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	ldr r12, [sp, #0]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r8, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	str r1, [r12, #36]
	str r2, [r12, #76]
	str r3, [r12, #80]
	cmp r3, #0
	beq 20f
	ldr r4, [r0, #0]
	rev r4, r4
	ldr r5, [r0, #4]
	rev r5, r5
	ldr r6, [r0, #8]
	rev r6, r6
	ldr r7, [r0, #12]
	rev r7, r7
	lsl r8, r4, #1
	eor r8, r8, r5, lsr #31
	lsl r9, r5, #1
	eor r9, r9, r6, lsr #31
	lsl r2, r6, #1
	eor r2, r2, r7, lsr #31
	lsl r3, r7, #1
	eor r3, r3, r4, lsr #31
	mov r5, #0
	sub r5, r5, r4, lsr #31
	and r5, r5, #3254779904
	eor r8, r8, r5
	str r3, [r12, #40]
	str r2, [r12, #44]
	eor r4, r3, r2
	str r4, [r12, #48]
	str r9, [r12, #52]
	str r8, [r12, #56]
	eor r4, r9, r8
	str r4, [r12, #60]
	eor r4, r3, r9
	str r4, [r12, #64]
	eor r5, r2, r8
	str r5, [r12, #68]
	eor r4, r4, r5
	str r4, [r12, #72]
	movw r11, #37449
	movt r11, #18724
	ldr r10, [r1, #12]
	rev r10, r10
	ldr lr, [r1, #8]
	rev lr, lr
	ldr r0, [r1, #4]
	rev r0, r0
	ldr r1, [r1, #0]
	rev r1, r1
22:
	ldr r2, [r12, #76]
	ldr r3, [r2, #0]
	rev r3, r3
	eor r1, r1, r3
	ldr r3, [r2, #4]
	rev r3, r3
	eor r0, r0, r3
	ldr r3, [r2, #8]
	rev r3, r3
	eor lr, lr, r3
	ldr r3, [r2, #12]
	rev r3, r3
	eor r10, r10, r3
	add r2, r2, #16
	str r2, [r12, #76]
	str r10, [r12, #84]
	str lr, [r12, #88]
	eor r2, r10, lr
	str r2, [r12, #92]
	str r0, [r12, #96]
	str r1, [r12, #100]
	eor r2, r0, r1
	str r2, [r12, #104]
	eor r2, r10, r0
	str r2, [r12, #108]
	eor r3, lr, r1
	str r3, [r12, #112]
	eor r2, r2, r3
	str r2, [r12, #116]
	movw r10, #37449
	ldr r0, [r12, #84]
	ldr r1, [r12, #40]
	and r2, r0, r10
	and r3, r0, r10, lsr #2
	and r4, r0, r10, lsr #1
	and r5, r1, r10
	and r6, r1, r10, lsr #2
	and r7, r1, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	str r8, [r12, #120]
	eor lr, r0, r0, lsr #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	eor lr, r1, r1, lsr #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	lsr lr, r0, #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	lsr lr, r1, #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r0, r2, r5
	mul lr, r3, r7
	eor r0, r0, lr
	mul lr, r4, r6
	eor r0, r0, lr
	and r0, r0, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r0, r0, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r0, r0, r9
	ldr r1, [r12, #120]
	eor r8, r8, r1
	eor r8, r8, r0
	eor r1, r1, r8, lsl #16
	eor r0, r0, r8, lsr #16
	str r1, [r12, #124]
	str r0, [r12, #128]
	ldr r0, [r12, #88]
	ldr r1, [r12, #44]
	and r2, r0, r10
	and r3, r0, r10, lsr #2
	and r4, r0, r10, lsr #1
	and r5, r1, r10
	and r6, r1, r10, lsr #2
	and r7, r1, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	str r8, [r12, #120]
	eor lr, r0, r0, lsr #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	eor lr, r1, r1, lsr #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	lsr lr, r0, #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	lsr lr, r1, #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r0, r2, r5
	mul lr, r3, r7
	eor r0, r0, lr
	mul lr, r4, r6
	eor r0, r0, lr
	and r0, r0, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r0, r0, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r0, r0, r9
	ldr r1, [r12, #120]
	eor r8, r8, r1
	eor r8, r8, r0
	eor r1, r1, r8, lsl #16
	eor r0, r0, r8, lsr #16
	str r1, [r12, #132]
	str r0, [r12, #136]
	ldr r0, [r12, #92]
	ldr r1, [r12, #48]
	and r2, r0, r10
	and r3, r0, r10, lsr #2
	and r4, r0, r10, lsr #1
	and r5, r1, r10
	and r6, r1, r10, lsr #2
	and r7, r1, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	str r8, [r12, #120]
	eor lr, r0, r0, lsr #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	eor lr, r1, r1, lsr #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	lsr lr, r0, #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	lsr lr, r1, #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r0, r2, r5
	mul lr, r3, r7
	eor r0, r0, lr
	mul lr, r4, r6
	eor r0, r0, lr
	and r0, r0, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r0, r0, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r0, r0, r9
	ldr r1, [r12, #120]
	eor r8, r8, r1
	eor r8, r8, r0
	eor r1, r1, r8, lsl #16
	eor r0, r0, r8, lsr #16
	ldr r2, [r12, #124]
	ldr r3, [r12, #128]
	ldr r4, [r12, #132]
	ldr r5, [r12, #136]
	eor r1, r1, r2
	eor r1, r1, r4
	eor r0, r0, r3
	eor r0, r0, r5
	eor r3, r3, r1
	eor r4, r4, r0
	str r3, [r12, #128]
	str r4, [r12, #132]
	ldr r0, [r12, #96]
	ldr r1, [r12, #52]
	and r2, r0, r10
	and r3, r0, r10, lsr #2
	and r4, r0, r10, lsr #1
	and r5, r1, r10
	and r6, r1, r10, lsr #2
	and r7, r1, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	str r8, [r12, #120]
	eor lr, r0, r0, lsr #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	eor lr, r1, r1, lsr #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	lsr lr, r0, #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	lsr lr, r1, #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r0, r2, r5
	mul lr, r3, r7
	eor r0, r0, lr
	mul lr, r4, r6
	eor r0, r0, lr
	and r0, r0, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r0, r0, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r0, r0, r9
	ldr r1, [r12, #120]
	eor r8, r8, r1
	eor r8, r8, r0
	eor r1, r1, r8, lsl #16
	eor r0, r0, r8, lsr #16
	str r1, [r12, #140]
	str r0, [r12, #144]
	ldr r0, [r12, #100]
	ldr r1, [r12, #56]
	and r2, r0, r10
	and r3, r0, r10, lsr #2
	and r4, r0, r10, lsr #1
	and r5, r1, r10
	and r6, r1, r10, lsr #2
	and r7, r1, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	str r8, [r12, #120]
	eor lr, r0, r0, lsr #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	eor lr, r1, r1, lsr #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	lsr lr, r0, #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	lsr lr, r1, #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r0, r2, r5
	mul lr, r3, r7
	eor r0, r0, lr
	mul lr, r4, r6
	eor r0, r0, lr
	and r0, r0, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r0, r0, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r0, r0, r9
	ldr r1, [r12, #120]
	eor r8, r8, r1
	eor r8, r8, r0
	eor r1, r1, r8, lsl #16
	eor r0, r0, r8, lsr #16
	str r1, [r12, #148]
	str r0, [r12, #152]
	ldr r0, [r12, #104]
	ldr r1, [r12, #60]
	and r2, r0, r10
	and r3, r0, r10, lsr #2
	and r4, r0, r10, lsr #1
	and r5, r1, r10
	and r6, r1, r10, lsr #2
	and r7, r1, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	str r8, [r12, #120]
	eor lr, r0, r0, lsr #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	eor lr, r1, r1, lsr #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	lsr lr, r0, #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	lsr lr, r1, #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r0, r2, r5
	mul lr, r3, r7
	eor r0, r0, lr
	mul lr, r4, r6
	eor r0, r0, lr
	and r0, r0, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r0, r0, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r0, r0, r9
	ldr r1, [r12, #120]
	eor r8, r8, r1
	eor r8, r8, r0
	eor r1, r1, r8, lsl #16
	eor r0, r0, r8, lsr #16
	ldr r2, [r12, #140]
	ldr r3, [r12, #144]
	ldr r4, [r12, #148]
	ldr r5, [r12, #152]
	eor r1, r1, r2
	eor r1, r1, r4
	eor r0, r0, r3
	eor r0, r0, r5
	eor r3, r3, r1
	eor r4, r4, r0
	str r3, [r12, #144]
	str r4, [r12, #148]
	ldr r0, [r12, #108]
	ldr r1, [r12, #64]
	and r2, r0, r10
	and r3, r0, r10, lsr #2
	and r4, r0, r10, lsr #1
	and r5, r1, r10
	and r6, r1, r10, lsr #2
	and r7, r1, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	str r8, [r12, #120]
	eor lr, r0, r0, lsr #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	eor lr, r1, r1, lsr #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	lsr lr, r0, #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	lsr lr, r1, #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r0, r2, r5
	mul lr, r3, r7
	eor r0, r0, lr
	mul lr, r4, r6
	eor r0, r0, lr
	and r0, r0, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r0, r0, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r0, r0, r9
	ldr r1, [r12, #120]
	eor r8, r8, r1
	eor r8, r8, r0
	eor r1, r1, r8, lsl #16
	eor r0, r0, r8, lsr #16
	str r1, [r12, #156]
	str r0, [r12, #160]
	ldr r0, [r12, #112]
	ldr r1, [r12, #68]
	and r2, r0, r10
	and r3, r0, r10, lsr #2
	and r4, r0, r10, lsr #1
	and r5, r1, r10
	and r6, r1, r10, lsr #2
	and r7, r1, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	str r8, [r12, #120]
	eor lr, r0, r0, lsr #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	eor lr, r1, r1, lsr #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	lsr lr, r0, #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	lsr lr, r1, #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r0, r2, r5
	mul lr, r3, r7
	eor r0, r0, lr
	mul lr, r4, r6
	eor r0, r0, lr
	and r0, r0, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r0, r0, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r0, r0, r9
	ldr r1, [r12, #120]
	eor r8, r8, r1
	eor r8, r8, r0
	eor r1, r1, r8, lsl #16
	eor r0, r0, r8, lsr #16
	str r1, [r12, #164]
	str r0, [r12, #168]
	ldr r0, [r12, #116]
	ldr r1, [r12, #72]
	and r2, r0, r10
	and r3, r0, r10, lsr #2
	and r4, r0, r10, lsr #1
	and r5, r1, r10
	and r6, r1, r10, lsr #2
	and r7, r1, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	str r8, [r12, #120]
	eor lr, r0, r0, lsr #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	eor lr, r1, r1, lsr #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r8, r2, r5
	mul lr, r3, r7
	eor r8, r8, lr
	mul lr, r4, r6
	eor r8, r8, lr
	and r8, r8, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r8, r8, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r8, r8, r9
	lsr lr, r0, #16
	and r2, lr, r10
	and r3, lr, r10, lsr #2
	and r4, lr, r10, lsr #1
	lsr lr, r1, #16
	and r5, lr, r10
	and r6, lr, r10, lsr #2
	and r7, lr, r10, lsr #1
	mul r0, r2, r5
	mul lr, r3, r7
	eor r0, r0, lr
	mul lr, r4, r6
	eor r0, r0, lr
	and r0, r0, r11
	mul r9, r2, r6
	mul lr, r3, r5
	eor r9, r9, lr
	mul lr, r4, r7
	eor r9, r9, lr
	and r9, r9, r11, lsl #1
	orr r0, r0, r9
	mul r9, r2, r7
	mul lr, r3, r6
	eor r9, r9, lr
	mul lr, r4, r5
	eor r9, r9, lr
	and r9, r9, r11, lsl #2
	orr r0, r0, r9
	ldr r1, [r12, #120]
	eor r8, r8, r1
	eor r8, r8, r0
	eor r1, r1, r8, lsl #16
	eor r0, r0, r8, lsr #16
	ldr r2, [r12, #156]
	ldr r3, [r12, #160]
	ldr r4, [r12, #164]
	ldr r5, [r12, #168]
	eor r1, r1, r2
	eor r1, r1, r4
	eor r0, r0, r3
	eor r0, r0, r5
	eor r3, r3, r1
	eor r4, r4, r0
	ldr r6, [r12, #124]
	ldr r7, [r12, #128]
	ldr r8, [r12, #132]
	ldr r9, [r12, #136]
	ldr r10, [r12, #140]
	ldr lr, [r12, #144]
	ldr r0, [r12, #148]
	ldr r1, [r12, #152]
	eor r2, r2, r6
	eor r2, r2, r10
	eor r3, r3, r7
	eor r3, r3, lr
	eor r4, r4, r8
	eor r4, r4, r0
	eor r5, r5, r9
	eor r5, r5, r1
	eor r8, r8, r2
	eor r9, r9, r3
	eor r10, r10, r4
	eor lr, lr, r5
	eor r10, r10, r6
	eor r10, r10, r6, lsr #1
	eor r10, r10, r6, lsr #2
	eor r10, r10, r6, lsr #7
	eor r9, r9, r6, lsl #31
	eor r9, r9, r6, lsl #30
	eor r9, r9, r6, lsl #25
	eor lr, lr, r7
	eor lr, lr, r7, lsr #1
	eor lr, lr, r7, lsr #2
	eor lr, lr, r7, lsr #7
	eor r10, r10, r7, lsl #31
	eor r10, r10, r7, lsl #30
	eor r10, r10, r7, lsl #25
	eor r0, r0, r8
	eor r0, r0, r8, lsr #1
	eor r0, r0, r8, lsr #2
	eor r0, r0, r8, lsr #7
	eor lr, lr, r8, lsl #31
	eor lr, lr, r8, lsl #30
	eor lr, lr, r8, lsl #25
	eor r1, r1, r9
	eor r1, r1, r9, lsr #1
	eor r1, r1, r9, lsr #2
	eor r1, r1, r9, lsr #7
	eor r0, r0, r9, lsl #31
	eor r0, r0, r9, lsl #30
	eor r0, r0, r9, lsl #25
	ldr r2, [r12, #80]
	subs r2, r2, #1
	str r2, [r12, #80]
	bne 22b
	ldr r2, [r12, #36]
	rev r1, r1
	str r1, [r2, #0]
	rev r0, r0
	str r0, [r2, #4]
	rev lr, lr
	str lr, [r2, #8]
	rev r10, r10
	str r10, [r2, #12]
	b 21f
20:
21:
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r8, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	bx lr
