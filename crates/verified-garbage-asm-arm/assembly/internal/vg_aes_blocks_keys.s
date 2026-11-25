// The functions of `src/internal/vg_aes_blocks_keys.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_blocks_keys:
	mov r12, r2
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r8, r12
	add r9, r12, #672
	add r12, r0, r1, lsl #4
	add lr, r1, #1
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
	subs lr, lr, #1
	bne 20b
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
