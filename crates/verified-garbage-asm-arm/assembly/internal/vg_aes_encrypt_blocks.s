// The functions of `src/internal/vg_aes_encrypt_blocks.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_encrypt_blocks:
	ldr r12, [sp, #0]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	add r9, r12, #672
	add r12, r0, r1, lsl #4
	lsl lr, r3, #4
	add lr, lr, r1
	add lr, lr, #1
	mov r8, r2
20:
	ldr r1, [r12, #0]
	ldr r3, [r12, #4]
	ldr r5, [r12, #8]
	ldr r7, [r12, #12]
	and r10, lr, #15
	cmp r10, #1
	bne 21f
	b 22f
21:
	movw r10, #25443
	movt r10, #25443
	eor r1, r1, r10
	eor r3, r3, r10
	eor r5, r5, r10
	eor r7, r7, r10
22:
	and r10, lr, #1
	cmp r10, #0
	beq 23f
	b 24f
23:
	eor r10, r1, r5
	lsr r10, r10, #16
	eor r1, r1, r10, ror #16
	eor r5, r5, r10, ror #16
	eor r10, r3, r7
	lsr r10, r10, #16
	eor r3, r3, r10, ror #16
	eor r7, r7, r10, ror #16
	movw r11, #65280
	movt r11, #65280
	eor r0, r1, r7
	and r0, r0, r11
	eor r10, r7, r5
	and r10, r10, r11
	eor r7, r7, r10
	eor r10, r5, r3
	and r10, r10, r11
	eor r5, r5, r10
	eor r10, r3, r1
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r0
24:
	sub r10, lr, #1
	and r10, r10, #2
	cmp r10, #0
	bne 25f
	b 26f
25:
	movw r11, #65280
	movt r11, #65280
	eor r10, r1, r5
	and r10, r10, r11
	eor r1, r1, r10
	eor r5, r5, r10
	eor r10, r3, r7
	and r10, r10, r11
	eor r3, r3, r10
	eor r7, r7, r10
26:
	movw r11, #3855
	movt r11, #3855
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	movw r11, #13107
	movt r11, #13107
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #21845
	movt r11, #21845
	and r0, r1, r11
	eor r1, r1, r0
	eor r0, r0, r0, ror #31
	eor r1, r1, r1, lsr #1
	and r2, r3, r11
	eor r3, r3, r2
	eor r2, r2, r2, ror #31
	eor r3, r3, r3, lsr #1
	and r4, r5, r11
	eor r5, r5, r4
	eor r4, r4, r4, ror #31
	eor r5, r5, r5, lsr #1
	and r6, r7, r11
	eor r7, r7, r6
	eor r6, r6, r6, ror #31
	eor r7, r7, r7, lsr #1
	str r0, [r9, #0]
	str r1, [r9, #4]
	str r2, [r9, #8]
	str r3, [r9, #12]
	str r4, [r9, #16]
	str r5, [r9, #20]
	str r6, [r9, #24]
	str r7, [r9, #28]
	sub r12, r12, #16
	sub r9, r9, #32
	sub lr, lr, #1
	and r10, lr, #15
	cmp r10, #0
	bne 20b
	add r12, r9, #32
	mov r10, r8
	ldr r8, [sp, #0]
	lsr r11, lr, #4
	cmp r11, #0
	beq 27f
29:
	str r10, [r8, #180]
	str r11, [r8, #184]
	str r12, [r8, #188]
	mov r9, r12
	lsr lr, r11, #1
	cmp lr, #0
	bne 210f
	ldr r0, [r10, #0]
	ldr r2, [r10, #4]
	ldr r4, [r10, #8]
	ldr r6, [r10, #12]
	b 211f
210:
	ldr r0, [r10, #0]
	ldr r2, [r10, #4]
	ldr r4, [r10, #8]
	ldr r6, [r10, #12]
	ldr r1, [r10, #16]
	ldr r3, [r10, #20]
	ldr r5, [r10, #24]
	ldr r7, [r10, #28]
211:
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
	str r9, [r8, #124]
	ldr r10, [r9, #0]
	eor r0, r0, r10
	ldr r10, [r9, #4]
	eor r1, r1, r10
	ldr r10, [r9, #8]
	eor r2, r2, r10
	ldr r10, [r9, #12]
	eor r3, r3, r10
	ldr r10, [r9, #16]
	eor r4, r4, r10
	ldr r10, [r9, #20]
	eor r5, r5, r10
	ldr r10, [r9, #24]
	eor r6, r6, r10
	ldr r10, [r9, #28]
	eor r7, r7, r10
212:
	eor r2, r5, r2
	eor lr, r2, r1
	eor r10, lr, r6
	eor r3, r10, r3
	eor r3, r3, r7
	eor r12, r3, r2
	eor r9, lr, r0
	eor r0, r12, r4
	eor r1, r0, r1
	eor r11, r9, r7
	str r0, [r8, #0]
	and r0, r11, r1
	eor r2, r2, r0
	eor r0, r3, r4
	str r11, [r8, #4]
	and r11, r9, r0
	str r0, [r8, #8]
	eor r0, r11, r12
	eor r12, r12, r9
	eor r11, lr, r11
	eor r4, r12, r4
	eor r5, r12, r5
	str r9, [r8, #12]
	and r9, r7, lr
	str lr, [r8, #16]
	eor lr, r5, r7
	str r7, [r8, #20]
	and r7, r4, r12
	eor r2, r2, r7
	eor r11, r11, r5
	eor r3, r4, r3
	eor r7, r7, r9
	eor r9, r4, lr
	str r4, [r8, #24]
	and r4, r5, r6
	eor r7, r7, r6
	eor r4, r11, r4
	eor r11, r12, r10
	str r12, [r8, #28]
	ldr r12, [r8, #0]
	str r6, [r8, #32]
	and r6, r12, r3
	str r3, [r8, #36]
	and r3, lr, r10
	str r10, [r8, #40]
	eor r10, r12, r5
	eor r12, r11, r1
	str r1, [r8, #44]
	and r1, r9, r11
	eor r1, r6, r1
	eor r6, r6, r3
	and r3, r10, r12
	eor r4, r4, r6
	eor r2, r2, r1
	eor r6, r6, lr
	eor r6, r6, r7
	and r7, r6, r2
	eor r1, r1, r0
	eor r3, r1, r3
	eor r1, r3, r7
	eor r7, r4, r7
	eor r0, r2, r3
	and r7, r7, r0
	eor r7, r3, r7
	eor r6, r6, r4
	eor r0, r1, r7
	and r3, r3, r0
	eor r0, r1, r3
	and r1, r6, r1
	eor r1, r4, r1
	and r4, r1, r0
	eor r4, r4, r6
	eor r6, r1, r4
	eor r3, r3, r2
	eor r3, r3, r7
	and r2, r6, r12
	ldr r0, [r8, #40]
	and r12, r3, r0
	eor r0, r4, r3
	and r11, r4, r11
	and r6, r6, r10
	eor r2, r2, r11
	and r4, r4, r9
	eor r9, r7, r3
	ldr r10, [r8, #32]
	and r10, r9, r10
	and lr, r3, lr
	and r3, r9, r5
	ldr r5, [r8, #16]
	and r5, r7, r5
	ldr r9, [r8, #20]
	and r9, r7, r9
	eor r12, r12, r5
	eor r10, r10, r2
	eor r5, r10, r5
	eor lr, lr, r9
	ldr r10, [r8, #44]
	and r10, r1, r10
	eor r7, r1, r7
	eor r9, r6, r9
	eor lr, lr, r4
	eor r3, r9, r3
	eor r10, r10, r11
	eor r9, r7, r0
	eor r11, r10, r12
	ldr r10, [r8, #8]
	and r10, r7, r10
	eor r10, r10, r2
	ldr r2, [r8, #0]
	and r2, r9, r2
	eor r4, r2, r4
	ldr r2, [r8, #12]
	and r7, r7, r2
	ldr r2, [r8, #4]
	and r2, r1, r2
	ldr r1, [r8, #36]
	and r9, r9, r1
	eor r1, r11, r4
	eor r1, r7, r1
	eor r1, r1, r6
	ldr r6, [r8, #24]
	and r7, r0, r6
	eor r4, r4, r7
	eor r7, r1, r2
	ldr r6, [r8, #28]
	and r0, r0, r6
	eor r6, r0, r9
	eor r3, r3, r4
	eor r2, r4, r2
	eor r9, r2, r9
	eor r4, r6, r5
	eor r12, r12, r9
	eor r10, r10, r9
	eor r5, r7, lr
	eor r6, r11, r2
	eor lr, r12, r0
	eor r7, r10, r3
	movw r10, #3855
	movt r10, #3855
	and r9, r10, r10, ror #2
	and r11, lr, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, lr
	ror r12, r11, #10
	eor lr, lr, r12
	and r11, lr, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, lr
	eor r12, r12, r11, ror #20
	and r11, r1, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r1
	eor r0, lr, r11, ror #10
	eor r1, r1, r11, ror #10
	and r11, r1, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r1
	eor r0, r0, r11, ror #20
	and r11, r2, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r2
	eor r1, r1, r11, ror #10
	eor r2, r2, r11, ror #10
	and r11, r2, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r2
	eor r1, r1, r11, ror #20
	eor r1, r1, lr
	and r11, r3, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r3
	eor r2, r2, r11, ror #10
	eor r3, r3, r11, ror #10
	and r11, r3, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r3
	eor r2, r2, r11, ror #20
	and r11, r4, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r4
	eor r3, r3, r11, ror #10
	eor r4, r4, r11, ror #10
	and r11, r4, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r4
	eor r3, r3, r11, ror #20
	eor r3, r3, lr
	and r11, r5, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r5
	eor r4, r4, r11, ror #10
	eor r5, r5, r11, ror #10
	and r11, r5, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r5
	eor r4, r4, r11, ror #20
	eor r4, r4, lr
	and r11, r6, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r6
	eor r5, r5, r11, ror #10
	eor r6, r6, r11, ror #10
	and r11, r6, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r6
	eor r5, r5, r11, ror #20
	and r11, r7, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r7
	eor r6, r6, r11, ror #10
	eor r7, r7, r11, ror #10
	and r11, r7, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r7
	eor r6, r6, r11, ror #20
	eor r7, r7, r12
	ldr r9, [r8, #124]
	ldr r10, [r9, #32]
	eor r0, r0, r10
	ldr r10, [r9, #36]
	eor r1, r1, r10
	ldr r10, [r9, #40]
	eor r2, r2, r10
	ldr r10, [r9, #44]
	eor r3, r3, r10
	ldr r10, [r9, #48]
	eor r4, r4, r10
	ldr r10, [r9, #52]
	eor r5, r5, r10
	ldr r10, [r9, #56]
	eor r6, r6, r10
	ldr r10, [r9, #60]
	eor r7, r7, r10
	eor r2, r5, r2
	eor lr, r2, r1
	eor r10, lr, r6
	eor r3, r10, r3
	eor r3, r3, r7
	eor r12, r3, r2
	eor r9, lr, r0
	eor r0, r12, r4
	eor r1, r0, r1
	eor r11, r9, r7
	str r0, [r8, #0]
	and r0, r11, r1
	eor r2, r2, r0
	eor r0, r3, r4
	str r11, [r8, #4]
	and r11, r9, r0
	str r0, [r8, #8]
	eor r0, r11, r12
	eor r12, r12, r9
	eor r11, lr, r11
	eor r4, r12, r4
	eor r5, r12, r5
	str r9, [r8, #12]
	and r9, r7, lr
	str lr, [r8, #16]
	eor lr, r5, r7
	str r7, [r8, #20]
	and r7, r4, r12
	eor r2, r2, r7
	eor r11, r11, r5
	eor r3, r4, r3
	eor r7, r7, r9
	eor r9, r4, lr
	str r4, [r8, #24]
	and r4, r5, r6
	eor r7, r7, r6
	eor r4, r11, r4
	eor r11, r12, r10
	str r12, [r8, #28]
	ldr r12, [r8, #0]
	str r6, [r8, #32]
	and r6, r12, r3
	str r3, [r8, #36]
	and r3, lr, r10
	str r10, [r8, #40]
	eor r10, r12, r5
	eor r12, r11, r1
	str r1, [r8, #44]
	and r1, r9, r11
	eor r1, r6, r1
	eor r6, r6, r3
	and r3, r10, r12
	eor r4, r4, r6
	eor r2, r2, r1
	eor r6, r6, lr
	eor r6, r6, r7
	and r7, r6, r2
	eor r1, r1, r0
	eor r3, r1, r3
	eor r1, r3, r7
	eor r7, r4, r7
	eor r0, r2, r3
	and r7, r7, r0
	eor r7, r3, r7
	eor r6, r6, r4
	eor r0, r1, r7
	and r3, r3, r0
	eor r0, r1, r3
	and r1, r6, r1
	eor r1, r4, r1
	and r4, r1, r0
	eor r4, r4, r6
	eor r6, r1, r4
	eor r3, r3, r2
	eor r3, r3, r7
	and r2, r6, r12
	ldr r0, [r8, #40]
	and r12, r3, r0
	eor r0, r4, r3
	and r11, r4, r11
	and r6, r6, r10
	eor r2, r2, r11
	and r4, r4, r9
	eor r9, r7, r3
	ldr r10, [r8, #32]
	and r10, r9, r10
	and lr, r3, lr
	and r3, r9, r5
	ldr r5, [r8, #16]
	and r5, r7, r5
	ldr r9, [r8, #20]
	and r9, r7, r9
	eor r12, r12, r5
	eor r10, r10, r2
	eor r5, r10, r5
	eor lr, lr, r9
	ldr r10, [r8, #44]
	and r10, r1, r10
	eor r7, r1, r7
	eor r9, r6, r9
	eor lr, lr, r4
	eor r3, r9, r3
	eor r10, r10, r11
	eor r9, r7, r0
	eor r11, r10, r12
	ldr r10, [r8, #8]
	and r10, r7, r10
	eor r10, r10, r2
	ldr r2, [r8, #0]
	and r2, r9, r2
	eor r4, r2, r4
	ldr r2, [r8, #12]
	and r7, r7, r2
	ldr r2, [r8, #4]
	and r2, r1, r2
	ldr r1, [r8, #36]
	and r9, r9, r1
	eor r1, r11, r4
	eor r1, r7, r1
	eor r1, r1, r6
	ldr r6, [r8, #24]
	and r7, r0, r6
	eor r4, r4, r7
	eor r7, r1, r2
	ldr r6, [r8, #28]
	and r0, r0, r6
	eor r6, r0, r9
	eor r3, r3, r4
	eor r2, r4, r2
	eor r9, r2, r9
	eor r4, r6, r5
	eor r12, r12, r9
	eor r10, r10, r9
	eor r5, r7, lr
	eor r6, r11, r2
	eor lr, r12, r0
	eor r7, r10, r3
	ldr r9, [r8, #124]
	sub r10, r9, r8
	cmp r10, #608
	beq 213f
	movw r10, #3855
	movt r10, #3855
	and r11, lr, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, lr
	ror r12, r11, #12
	eor lr, lr, r12
	eor r12, r12, lr, ror #16
	and r11, r1, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r1
	eor r0, lr, r11, ror #12
	eor r1, r1, r11, ror #12
	eor r0, r0, r1, ror #16
	and r11, r2, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r2
	eor r1, r1, r11, ror #12
	eor r2, r2, r11, ror #12
	eor r1, r1, r2, ror #16
	eor r1, r1, lr
	and r11, r3, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r3
	eor r2, r2, r11, ror #12
	eor r3, r3, r11, ror #12
	eor r2, r2, r3, ror #16
	and r11, r4, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r4
	eor r3, r3, r11, ror #12
	eor r4, r4, r11, ror #12
	eor r3, r3, r4, ror #16
	eor r3, r3, lr
	and r11, r5, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r5
	eor r4, r4, r11, ror #12
	eor r5, r5, r11, ror #12
	eor r4, r4, r5, ror #16
	eor r4, r4, lr
	and r11, r6, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r6
	eor r5, r5, r11, ror #12
	eor r6, r6, r11, ror #12
	eor r5, r5, r6, ror #16
	and r11, r7, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r7
	eor r6, r6, r11, ror #12
	eor r7, r7, r11, ror #12
	eor r6, r6, r7, ror #16
	eor r7, r7, r12
	ldr r10, [r9, #64]
	eor r0, r0, r10
	ldr r10, [r9, #68]
	eor r1, r1, r10
	ldr r10, [r9, #72]
	eor r2, r2, r10
	ldr r10, [r9, #76]
	eor r3, r3, r10
	ldr r10, [r9, #80]
	eor r4, r4, r10
	ldr r10, [r9, #84]
	eor r5, r5, r10
	ldr r10, [r9, #88]
	eor r6, r6, r10
	ldr r10, [r9, #92]
	eor r7, r7, r10
	eor r2, r5, r2
	eor lr, r2, r1
	eor r10, lr, r6
	eor r3, r10, r3
	eor r3, r3, r7
	eor r12, r3, r2
	eor r9, lr, r0
	eor r0, r12, r4
	eor r1, r0, r1
	eor r11, r9, r7
	str r0, [r8, #0]
	and r0, r11, r1
	eor r2, r2, r0
	eor r0, r3, r4
	str r11, [r8, #4]
	and r11, r9, r0
	str r0, [r8, #8]
	eor r0, r11, r12
	eor r12, r12, r9
	eor r11, lr, r11
	eor r4, r12, r4
	eor r5, r12, r5
	str r9, [r8, #12]
	and r9, r7, lr
	str lr, [r8, #16]
	eor lr, r5, r7
	str r7, [r8, #20]
	and r7, r4, r12
	eor r2, r2, r7
	eor r11, r11, r5
	eor r3, r4, r3
	eor r7, r7, r9
	eor r9, r4, lr
	str r4, [r8, #24]
	and r4, r5, r6
	eor r7, r7, r6
	eor r4, r11, r4
	eor r11, r12, r10
	str r12, [r8, #28]
	ldr r12, [r8, #0]
	str r6, [r8, #32]
	and r6, r12, r3
	str r3, [r8, #36]
	and r3, lr, r10
	str r10, [r8, #40]
	eor r10, r12, r5
	eor r12, r11, r1
	str r1, [r8, #44]
	and r1, r9, r11
	eor r1, r6, r1
	eor r6, r6, r3
	and r3, r10, r12
	eor r4, r4, r6
	eor r2, r2, r1
	eor r6, r6, lr
	eor r6, r6, r7
	and r7, r6, r2
	eor r1, r1, r0
	eor r3, r1, r3
	eor r1, r3, r7
	eor r7, r4, r7
	eor r0, r2, r3
	and r7, r7, r0
	eor r7, r3, r7
	eor r6, r6, r4
	eor r0, r1, r7
	and r3, r3, r0
	eor r0, r1, r3
	and r1, r6, r1
	eor r1, r4, r1
	and r4, r1, r0
	eor r4, r4, r6
	eor r6, r1, r4
	eor r3, r3, r2
	eor r3, r3, r7
	and r2, r6, r12
	ldr r0, [r8, #40]
	and r12, r3, r0
	eor r0, r4, r3
	and r11, r4, r11
	and r6, r6, r10
	eor r2, r2, r11
	and r4, r4, r9
	eor r9, r7, r3
	ldr r10, [r8, #32]
	and r10, r9, r10
	and lr, r3, lr
	and r3, r9, r5
	ldr r5, [r8, #16]
	and r5, r7, r5
	ldr r9, [r8, #20]
	and r9, r7, r9
	eor r12, r12, r5
	eor r10, r10, r2
	eor r5, r10, r5
	eor lr, lr, r9
	ldr r10, [r8, #44]
	and r10, r1, r10
	eor r7, r1, r7
	eor r9, r6, r9
	eor lr, lr, r4
	eor r3, r9, r3
	eor r10, r10, r11
	eor r9, r7, r0
	eor r11, r10, r12
	ldr r10, [r8, #8]
	and r10, r7, r10
	eor r10, r10, r2
	ldr r2, [r8, #0]
	and r2, r9, r2
	eor r4, r2, r4
	ldr r2, [r8, #12]
	and r7, r7, r2
	ldr r2, [r8, #4]
	and r2, r1, r2
	ldr r1, [r8, #36]
	and r9, r9, r1
	eor r1, r11, r4
	eor r1, r7, r1
	eor r1, r1, r6
	ldr r6, [r8, #24]
	and r7, r0, r6
	eor r4, r4, r7
	eor r7, r1, r2
	ldr r6, [r8, #28]
	and r0, r0, r6
	eor r6, r0, r9
	eor r3, r3, r4
	eor r2, r4, r2
	eor r9, r2, r9
	eor r4, r6, r5
	eor r12, r12, r9
	eor r10, r10, r9
	eor r5, r7, lr
	eor r6, r11, r2
	eor lr, r12, r0
	eor r7, r10, r3
	movw r10, #3855
	movt r10, #3855
	orr r9, r10, r10, ror #30
	and r11, lr, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, lr
	ror r12, r11, #14
	eor lr, lr, r12
	and r11, lr, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, lr
	eor r12, r12, r11, ror #20
	and r11, r1, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r1
	eor r0, lr, r11, ror #14
	eor r1, r1, r11, ror #14
	and r11, r1, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r1
	eor r0, r0, r11, ror #20
	and r11, r2, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r2
	eor r1, r1, r11, ror #14
	eor r2, r2, r11, ror #14
	and r11, r2, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r2
	eor r1, r1, r11, ror #20
	eor r1, r1, lr
	and r11, r3, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r3
	eor r2, r2, r11, ror #14
	eor r3, r3, r11, ror #14
	and r11, r3, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r3
	eor r2, r2, r11, ror #20
	and r11, r4, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r4
	eor r3, r3, r11, ror #14
	eor r4, r4, r11, ror #14
	and r11, r4, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r4
	eor r3, r3, r11, ror #20
	eor r3, r3, lr
	and r11, r5, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r5
	eor r4, r4, r11, ror #14
	eor r5, r5, r11, ror #14
	and r11, r5, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r5
	eor r4, r4, r11, ror #20
	eor r4, r4, lr
	and r11, r6, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r6
	eor r5, r5, r11, ror #14
	eor r6, r6, r11, ror #14
	and r11, r6, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r6
	eor r5, r5, r11, ror #20
	and r11, r7, r9
	eor r11, r11, r11, ror #24
	eor r11, r11, r7
	eor r6, r6, r11, ror #14
	eor r7, r7, r11, ror #14
	and r11, r7, r10
	eor r11, r11, r11, ror #24
	eor r11, r11, r7
	eor r6, r6, r11, ror #20
	eor r7, r7, r12
	ldr r9, [r8, #124]
	ldr r10, [r9, #96]
	eor r0, r0, r10
	ldr r10, [r9, #100]
	eor r1, r1, r10
	ldr r10, [r9, #104]
	eor r2, r2, r10
	ldr r10, [r9, #108]
	eor r3, r3, r10
	ldr r10, [r9, #112]
	eor r4, r4, r10
	ldr r10, [r9, #116]
	eor r5, r5, r10
	ldr r10, [r9, #120]
	eor r6, r6, r10
	ldr r10, [r9, #124]
	eor r7, r7, r10
	eor r2, r5, r2
	eor lr, r2, r1
	eor r10, lr, r6
	eor r3, r10, r3
	eor r3, r3, r7
	eor r12, r3, r2
	eor r9, lr, r0
	eor r0, r12, r4
	eor r1, r0, r1
	eor r11, r9, r7
	str r0, [r8, #0]
	and r0, r11, r1
	eor r2, r2, r0
	eor r0, r3, r4
	str r11, [r8, #4]
	and r11, r9, r0
	str r0, [r8, #8]
	eor r0, r11, r12
	eor r12, r12, r9
	eor r11, lr, r11
	eor r4, r12, r4
	eor r5, r12, r5
	str r9, [r8, #12]
	and r9, r7, lr
	str lr, [r8, #16]
	eor lr, r5, r7
	str r7, [r8, #20]
	and r7, r4, r12
	eor r2, r2, r7
	eor r11, r11, r5
	eor r3, r4, r3
	eor r7, r7, r9
	eor r9, r4, lr
	str r4, [r8, #24]
	and r4, r5, r6
	eor r7, r7, r6
	eor r4, r11, r4
	eor r11, r12, r10
	str r12, [r8, #28]
	ldr r12, [r8, #0]
	str r6, [r8, #32]
	and r6, r12, r3
	str r3, [r8, #36]
	and r3, lr, r10
	str r10, [r8, #40]
	eor r10, r12, r5
	eor r12, r11, r1
	str r1, [r8, #44]
	and r1, r9, r11
	eor r1, r6, r1
	eor r6, r6, r3
	and r3, r10, r12
	eor r4, r4, r6
	eor r2, r2, r1
	eor r6, r6, lr
	eor r6, r6, r7
	and r7, r6, r2
	eor r1, r1, r0
	eor r3, r1, r3
	eor r1, r3, r7
	eor r7, r4, r7
	eor r0, r2, r3
	and r7, r7, r0
	eor r7, r3, r7
	eor r6, r6, r4
	eor r0, r1, r7
	and r3, r3, r0
	eor r0, r1, r3
	and r1, r6, r1
	eor r1, r4, r1
	and r4, r1, r0
	eor r4, r4, r6
	eor r6, r1, r4
	eor r3, r3, r2
	eor r3, r3, r7
	and r2, r6, r12
	ldr r0, [r8, #40]
	and r12, r3, r0
	eor r0, r4, r3
	and r11, r4, r11
	and r6, r6, r10
	eor r2, r2, r11
	and r4, r4, r9
	eor r9, r7, r3
	ldr r10, [r8, #32]
	and r10, r9, r10
	and lr, r3, lr
	and r3, r9, r5
	ldr r5, [r8, #16]
	and r5, r7, r5
	ldr r9, [r8, #20]
	and r9, r7, r9
	eor r12, r12, r5
	eor r10, r10, r2
	eor r5, r10, r5
	eor lr, lr, r9
	ldr r10, [r8, #44]
	and r10, r1, r10
	eor r7, r1, r7
	eor r9, r6, r9
	eor lr, lr, r4
	eor r3, r9, r3
	eor r10, r10, r11
	eor r9, r7, r0
	eor r11, r10, r12
	ldr r10, [r8, #8]
	and r10, r7, r10
	eor r10, r10, r2
	ldr r2, [r8, #0]
	and r2, r9, r2
	eor r4, r2, r4
	ldr r2, [r8, #12]
	and r7, r7, r2
	ldr r2, [r8, #4]
	and r2, r1, r2
	ldr r1, [r8, #36]
	and r9, r9, r1
	eor r1, r11, r4
	eor r1, r7, r1
	eor r1, r1, r6
	ldr r6, [r8, #24]
	and r7, r0, r6
	eor r4, r4, r7
	eor r7, r1, r2
	ldr r6, [r8, #28]
	and r0, r0, r6
	eor r6, r0, r9
	eor r3, r3, r4
	eor r2, r4, r2
	eor r9, r2, r9
	eor r4, r6, r5
	eor r12, r12, r9
	eor r10, r10, r9
	eor r5, r7, lr
	eor r6, r11, r2
	eor lr, r12, r0
	eor r7, r10, r3
	ldr r9, [r8, #124]
	sub r10, r9, r8
	cmp r10, #544
	beq 215f
	ror r12, lr, #8
	eor lr, lr, r12
	eor r12, r12, lr, ror #16
	eor r0, lr, r1, ror #8
	eor r1, r1, r1, ror #8
	eor r0, r0, r1, ror #16
	eor r1, r1, r2, ror #8
	eor r2, r2, r2, ror #8
	eor r1, r1, r2, ror #16
	eor r1, r1, lr
	eor r2, r2, r3, ror #8
	eor r3, r3, r3, ror #8
	eor r2, r2, r3, ror #16
	eor r3, r3, r4, ror #8
	eor r4, r4, r4, ror #8
	eor r3, r3, r4, ror #16
	eor r3, r3, lr
	eor r4, r4, r5, ror #8
	eor r5, r5, r5, ror #8
	eor r4, r4, r5, ror #16
	eor r4, r4, lr
	eor r5, r5, r6, ror #8
	eor r6, r6, r6, ror #8
	eor r5, r5, r6, ror #16
	eor r6, r6, r7, ror #8
	eor r7, r7, r7, ror #8
	eor r6, r6, r7, ror #16
	eor r7, r7, r12
	ldr r10, [r9, #128]
	eor r0, r0, r10
	ldr r10, [r9, #132]
	eor r1, r1, r10
	ldr r10, [r9, #136]
	eor r2, r2, r10
	ldr r10, [r9, #140]
	eor r3, r3, r10
	ldr r10, [r9, #144]
	eor r4, r4, r10
	ldr r10, [r9, #148]
	eor r5, r5, r10
	ldr r10, [r9, #152]
	eor r6, r6, r10
	ldr r10, [r9, #156]
	eor r7, r7, r10
	add r9, r9, #128
	str r9, [r8, #124]
	b 216f
215:
	ldr r10, [r9, #128]
	eor r0, r1, r10
	ldr r10, [r9, #132]
	eor r1, r2, r10
	ldr r10, [r9, #136]
	eor r2, r3, r10
	ldr r10, [r9, #140]
	eor r3, r4, r10
	ldr r10, [r9, #144]
	eor r4, r5, r10
	ldr r10, [r9, #148]
	eor r5, r6, r10
	ldr r10, [r9, #152]
	eor r6, r7, r10
	ldr r10, [r9, #156]
	eor r7, lr, r10
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
216:
	b 214f
213:
	ldr r10, [r9, #64]
	eor r0, r1, r10
	ldr r10, [r9, #68]
	eor r1, r2, r10
	ldr r10, [r9, #72]
	eor r2, r3, r10
	ldr r10, [r9, #76]
	eor r3, r4, r10
	ldr r10, [r9, #80]
	eor r4, r5, r10
	ldr r10, [r9, #84]
	eor r5, r6, r10
	ldr r10, [r9, #88]
	eor r6, r7, r10
	ldr r10, [r9, #92]
	eor r7, lr, r10
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
	movw r11, #65280
	movt r11, #65280
	eor r10, r0, r4
	and r10, r10, r11
	eor r0, r0, r10
	eor r4, r4, r10
	eor r10, r1, r5
	and r10, r10, r11
	eor r1, r1, r10
	eor r5, r5, r10
	eor r10, r2, r6
	and r10, r10, r11
	eor r2, r2, r10
	eor r6, r6, r10
	eor r10, r3, r7
	and r10, r10, r11
	eor r3, r3, r10
	eor r7, r7, r10
214:
	bne 212b
	ldr r10, [r8, #180]
	ldr r11, [r8, #184]
	ldr r12, [r8, #188]
	lsr r9, r11, #1
	cmp r9, #0
	bne 217f
	str r0, [r10, #0]
	str r2, [r10, #4]
	str r4, [r10, #8]
	str r6, [r10, #12]
	mov r11, #0
	b 218f
217:
	str r0, [r10, #0]
	str r2, [r10, #4]
	str r4, [r10, #8]
	str r6, [r10, #12]
	str r1, [r10, #16]
	str r3, [r10, #20]
	str r5, [r10, #24]
	str r7, [r10, #28]
	add r10, r10, #32
	sub r11, r11, #2
218:
	cmp r11, #0
	bne 29b
	b 28f
27:
28:
	ldr r12, [sp, #0]
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
