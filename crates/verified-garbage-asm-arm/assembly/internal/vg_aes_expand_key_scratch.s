// The functions of `src/internal/vg_aes_expand_key_scratch.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_expand_key_scratch:
	str r4, [r3, #128]
	str r5, [r3, #132]
	str r6, [r3, #136]
	str r7, [r3, #140]
	str r8, [r3, #144]
	str r9, [r3, #148]
	str r10, [r3, #152]
	str r11, [r3, #156]
	str lr, [r3, #160]
	mov r8, r3
	mov r9, r0
	mov r10, r2
	mov lr, r1
20:
	ldr r0, [r9, #0]
	str r0, [r10, #0]
	add r9, r9, #4
	add r10, r10, #4
	subs lr, lr, #4
	bne 20b
	sub r9, r10, r1
	lsr r12, r1, #2
	mov r11, #0
	add lr, r12, r12, lsl #1
	add lr, lr, #28
	mov r1, #1
	str r1, [r8, #164]
21:
	cmp r11, #0
	beq 22f
	sub r1, r11, #4
	sub r2, r12, #8
	orr r1, r1, r2
	cmp r1, #0
	beq 24f
	b 25f
24:
	str r10, [r8, #168]
	str r11, [r8, #172]
	str r12, [r8, #176]
	str lr, [r8, #180]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r4, r2
	eor r11, r7, r1
	eor r12, r7, r4
	eor lr, r7, r2
	eor r5, r6, r5
	str r12, [r8, #4]
	eor r12, r5, r0
	eor r4, r12, r4
	str r4, [r8, #8]
	eor r4, r11, r10
	str r10, [r8, #12]
	eor r10, r12, r7
	eor r1, r12, r1
	str r10, [r8, #16]
	eor r10, r1, lr
	eor r3, r3, r4
	eor r2, r3, r2
	eor r3, r3, r6
	eor r6, r2, r0
	str r1, [r8, #20]
	eor r1, r2, r5
	str r12, [r8, #24]
	ldr r12, [r8, #4]
	str r6, [r8, #28]
	eor r6, r3, r12
	str r3, [r8, #32]
	eor r3, r0, r6
	eor r12, r1, r6
	str r12, [r8, #36]
	eor r12, r1, lr
	eor r5, r5, r6
	str r12, [r8, #40]
	eor r12, r11, r5
	eor r7, r7, r5
	str r7, [r8, #44]
	and r7, r4, r2
	str r4, [r8, #48]
	ldr r4, [r8, #28]
	str r2, [r8, #52]
	and r2, r10, r4
	eor r2, r2, r7
	str r10, [r8, #56]
	ldr r10, [r8, #8]
	and r4, r10, r0
	eor r4, r4, r7
	and r7, r11, r5
	str r11, [r8, #60]
	ldr r11, [r8, #20]
	ldr r10, [r8, #24]
	str r5, [r8, #64]
	and r5, r11, r10
	eor r5, r5, r7
	ldr r11, [r8, #16]
	and r10, r11, r3
	eor r10, r10, r7
	ldr r7, [r8, #4]
	and r11, r7, r6
	ldr r7, [r8, #12]
	str r6, [r8, #68]
	ldr r6, [r8, #36]
	str r3, [r8, #72]
	and r3, r7, r6
	eor r3, r3, r11
	and r7, lr, r1
	eor r7, r7, r11
	eor r2, r2, r3
	eor r4, r4, r7
	eor r5, r5, r3
	eor r10, r10, r7
	ldr r7, [r8, #32]
	eor r2, r2, r7
	ldr r7, [r8, #40]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #44]
	eor r10, r10, r12
	eor r12, r2, r4
	and r2, r2, r5
	eor r7, r10, r2
	and r3, r12, r7
	eor r3, r3, r4
	eor r11, r5, r10
	eor r4, r4, r2
	and r4, r4, r11
	eor r4, r4, r10
	eor r5, r5, r4
	eor r11, r7, r4
	and r10, r10, r11
	eor r5, r10, r5
	eor r7, r7, r10
	and r7, r3, r7
	eor r12, r12, r7
	eor r7, r12, r5
	eor r10, r3, r4
	eor r11, r3, r12
	eor r2, r4, r5
	str lr, [r8, #44]
	eor lr, r10, r7
	str r7, [r8, #40]
	ldr r7, [r8, #52]
	and r7, r2, r7
	str r7, [r8, #52]
	ldr r7, [r8, #28]
	and r7, r5, r7
	and r0, r4, r0
	str r7, [r8, #28]
	ldr r7, [r8, #64]
	and r7, r11, r7
	str r7, [r8, #64]
	ldr r7, [r8, #24]
	and r7, r12, r7
	str r7, [r8, #24]
	ldr r7, [r8, #72]
	and r7, r3, r7
	str r0, [r8, #72]
	ldr r0, [r8, #68]
	and r0, r10, r0
	and r6, lr, r6
	str r0, [r8, #36]
	ldr r0, [r8, #40]
	and r1, r0, r1
	str r1, [r8, #68]
	ldr r1, [r8, #48]
	and r2, r2, r1
	ldr r1, [r8, #56]
	and r5, r5, r1
	ldr r1, [r8, #8]
	and r4, r4, r1
	ldr r1, [r8, #60]
	and r11, r11, r1
	ldr r1, [r8, #20]
	and r12, r12, r1
	ldr r1, [r8, #16]
	and r3, r3, r1
	ldr r1, [r8, #4]
	and r10, r10, r1
	ldr r1, [r8, #12]
	and lr, lr, r1
	ldr r1, [r8, #44]
	and r0, r0, r1
	eor r10, r10, lr
	eor r4, r5, r4
	eor r12, r7, r12
	eor r2, r2, r5
	ldr r5, [r8, #72]
	eor r1, r5, r11
	eor r5, r5, r7
	ldr r7, [r8, #68]
	eor r7, r6, r7
	str r4, [r8, #68]
	ldr r4, [r8, #52]
	str r5, [r8, #72]
	ldr r5, [r8, #64]
	eor r4, r4, r5
	str r2, [r8, #52]
	ldr r2, [r8, #36]
	eor r2, r2, r6
	eor lr, lr, r0
	eor r11, r11, r12
	eor r1, r1, r4
	ldr r0, [r8, #24]
	eor r6, r0, r10
	eor r5, r5, r2
	eor r10, r10, r1
	eor r3, r3, r1
	eor r7, r7, r6
	ldr r1, [r8, #52]
	eor r1, r1, r6
	eor r0, r0, r5
	eor r3, r3, r7
	ldr r6, [r8, #28]
	eor r6, r6, r1
	eor r5, r5, r1
	eor r11, r11, r7
	ldr r7, [r8, #0]
	eor r1, r11, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r10, r0, r3
	eor r4, r4, r6
	ldr r11, [r8, #72]
	eor r11, r11, r6
	ldr r6, [r8, #68]
	eor r2, r6, r3
	eor r0, r0, r4
	eor r6, r0, r7
	eor lr, lr, r10
	eor lr, lr, r7
	mov r7, r5
	mov r5, lr
	mov r3, r11
	mov r0, r12
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	ldr r10, [r8, #168]
	ldr r11, [r8, #172]
	ldr r12, [r8, #176]
	ldr lr, [r8, #180]
25:
	b 23f
22:
	str r10, [r8, #168]
	str r11, [r8, #172]
	str r12, [r8, #176]
	str lr, [r8, #180]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r4, r2
	eor r11, r7, r1
	eor r12, r7, r4
	eor lr, r7, r2
	eor r5, r6, r5
	str r12, [r8, #4]
	eor r12, r5, r0
	eor r4, r12, r4
	str r4, [r8, #8]
	eor r4, r11, r10
	str r10, [r8, #12]
	eor r10, r12, r7
	eor r1, r12, r1
	str r10, [r8, #16]
	eor r10, r1, lr
	eor r3, r3, r4
	eor r2, r3, r2
	eor r3, r3, r6
	eor r6, r2, r0
	str r1, [r8, #20]
	eor r1, r2, r5
	str r12, [r8, #24]
	ldr r12, [r8, #4]
	str r6, [r8, #28]
	eor r6, r3, r12
	str r3, [r8, #32]
	eor r3, r0, r6
	eor r12, r1, r6
	str r12, [r8, #36]
	eor r12, r1, lr
	eor r5, r5, r6
	str r12, [r8, #40]
	eor r12, r11, r5
	eor r7, r7, r5
	str r7, [r8, #44]
	and r7, r4, r2
	str r4, [r8, #48]
	ldr r4, [r8, #28]
	str r2, [r8, #52]
	and r2, r10, r4
	eor r2, r2, r7
	str r10, [r8, #56]
	ldr r10, [r8, #8]
	and r4, r10, r0
	eor r4, r4, r7
	and r7, r11, r5
	str r11, [r8, #60]
	ldr r11, [r8, #20]
	ldr r10, [r8, #24]
	str r5, [r8, #64]
	and r5, r11, r10
	eor r5, r5, r7
	ldr r11, [r8, #16]
	and r10, r11, r3
	eor r10, r10, r7
	ldr r7, [r8, #4]
	and r11, r7, r6
	ldr r7, [r8, #12]
	str r6, [r8, #68]
	ldr r6, [r8, #36]
	str r3, [r8, #72]
	and r3, r7, r6
	eor r3, r3, r11
	and r7, lr, r1
	eor r7, r7, r11
	eor r2, r2, r3
	eor r4, r4, r7
	eor r5, r5, r3
	eor r10, r10, r7
	ldr r7, [r8, #32]
	eor r2, r2, r7
	ldr r7, [r8, #40]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #44]
	eor r10, r10, r12
	eor r12, r2, r4
	and r2, r2, r5
	eor r7, r10, r2
	and r3, r12, r7
	eor r3, r3, r4
	eor r11, r5, r10
	eor r4, r4, r2
	and r4, r4, r11
	eor r4, r4, r10
	eor r5, r5, r4
	eor r11, r7, r4
	and r10, r10, r11
	eor r5, r10, r5
	eor r7, r7, r10
	and r7, r3, r7
	eor r12, r12, r7
	eor r7, r12, r5
	eor r10, r3, r4
	eor r11, r3, r12
	eor r2, r4, r5
	str lr, [r8, #44]
	eor lr, r10, r7
	str r7, [r8, #40]
	ldr r7, [r8, #52]
	and r7, r2, r7
	str r7, [r8, #52]
	ldr r7, [r8, #28]
	and r7, r5, r7
	and r0, r4, r0
	str r7, [r8, #28]
	ldr r7, [r8, #64]
	and r7, r11, r7
	str r7, [r8, #64]
	ldr r7, [r8, #24]
	and r7, r12, r7
	str r7, [r8, #24]
	ldr r7, [r8, #72]
	and r7, r3, r7
	str r0, [r8, #72]
	ldr r0, [r8, #68]
	and r0, r10, r0
	and r6, lr, r6
	str r0, [r8, #36]
	ldr r0, [r8, #40]
	and r1, r0, r1
	str r1, [r8, #68]
	ldr r1, [r8, #48]
	and r2, r2, r1
	ldr r1, [r8, #56]
	and r5, r5, r1
	ldr r1, [r8, #8]
	and r4, r4, r1
	ldr r1, [r8, #60]
	and r11, r11, r1
	ldr r1, [r8, #20]
	and r12, r12, r1
	ldr r1, [r8, #16]
	and r3, r3, r1
	ldr r1, [r8, #4]
	and r10, r10, r1
	ldr r1, [r8, #12]
	and lr, lr, r1
	ldr r1, [r8, #44]
	and r0, r0, r1
	eor r10, r10, lr
	eor r4, r5, r4
	eor r12, r7, r12
	eor r2, r2, r5
	ldr r5, [r8, #72]
	eor r1, r5, r11
	eor r5, r5, r7
	ldr r7, [r8, #68]
	eor r7, r6, r7
	str r4, [r8, #68]
	ldr r4, [r8, #52]
	str r5, [r8, #72]
	ldr r5, [r8, #64]
	eor r4, r4, r5
	str r2, [r8, #52]
	ldr r2, [r8, #36]
	eor r2, r2, r6
	eor lr, lr, r0
	eor r11, r11, r12
	eor r1, r1, r4
	ldr r0, [r8, #24]
	eor r6, r0, r10
	eor r5, r5, r2
	eor r10, r10, r1
	eor r3, r3, r1
	eor r7, r7, r6
	ldr r1, [r8, #52]
	eor r1, r1, r6
	eor r0, r0, r5
	eor r3, r3, r7
	ldr r6, [r8, #28]
	eor r6, r6, r1
	eor r5, r5, r1
	eor r11, r11, r7
	ldr r7, [r8, #0]
	eor r1, r11, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r10, r0, r3
	eor r4, r4, r6
	ldr r11, [r8, #72]
	eor r11, r11, r6
	ldr r6, [r8, #68]
	eor r2, r6, r3
	eor r0, r0, r4
	eor r6, r0, r7
	eor lr, lr, r10
	eor lr, lr, r7
	mov r7, r5
	mov r5, lr
	mov r3, r11
	mov r0, r12
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	ldr r10, [r8, #168]
	ldr r11, [r8, #172]
	ldr r12, [r8, #176]
	ldr lr, [r8, #180]
	ror r0, r0, #8
	ldr r1, [r8, #164]
	eor r0, r0, r1
	lsr r2, r1, #7
	mov r3, #27
	mul r2, r2, r3
	lsl r1, r1, #1
	eor r1, r1, r2
	and r1, r1, #255
	str r1, [r8, #164]
23:
	ldr r1, [r9, #0]
	eor r0, r0, r1
	str r0, [r10, #0]
	add r9, r9, #4
	add r10, r10, #4
	add r11, r11, #1
	cmp r11, r12
	beq 26f
	b 27f
26:
	mov r11, #0
27:
	subs lr, lr, #1
	bne 21b
	mov r12, r8
	ldr r4, [r12, #128]
	ldr r5, [r12, #132]
	ldr r6, [r12, #136]
	ldr r7, [r12, #140]
	ldr r8, [r12, #144]
	ldr r9, [r12, #148]
	ldr r10, [r12, #152]
	ldr r11, [r12, #156]
	ldr lr, [r12, #160]
	bx lr
