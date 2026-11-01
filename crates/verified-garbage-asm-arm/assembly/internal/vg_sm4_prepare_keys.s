// The functions of `src/internal/vg_sm4_prepare_keys.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_prepare_keys:
	str r4, [r2, #1408]
	str r5, [r2, #1412]
	str r6, [r2, #1416]
	str r7, [r2, #1420]
	str r8, [r2, #1424]
	str r9, [r2, #1428]
	str r10, [r2, #1432]
	str r11, [r2, #1436]
	str lr, [r2, #1440]
	mov r8, r2
	mov r12, r0
	mov r3, r1
	cmp r3, #0
	beq 20f
	add r9, r8, #1376
	mov lr, #32
22:
	ldr r0, [r12, #0]
	rev r0, r0
	movw r11, #257
	movt r11, #257
	and r3, r11, r0
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #0]
	and r3, r11, r0, lsr #1
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #4]
	and r3, r11, r0, lsr #2
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #8]
	and r3, r11, r0, lsr #3
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #12]
	and r3, r11, r0, lsr #4
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #16]
	and r3, r11, r0, lsr #5
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #20]
	and r3, r11, r0, lsr #6
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #24]
	and r3, r11, r0, lsr #7
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #28]
	add r12, r12, #4
	sub r9, r9, #32
	subs lr, lr, #1
	bne 22b
	b 21f
20:
	add r9, r8, #384
	mov lr, #32
23:
	ldr r0, [r12, #0]
	rev r0, r0
	movw r11, #257
	movt r11, #257
	and r3, r11, r0
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #0]
	and r3, r11, r0, lsr #1
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #4]
	and r3, r11, r0, lsr #2
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #8]
	and r3, r11, r0, lsr #3
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #12]
	and r3, r11, r0, lsr #4
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #16]
	and r3, r11, r0, lsr #5
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #20]
	and r3, r11, r0, lsr #6
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #24]
	and r3, r11, r0, lsr #7
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #28]
	add r12, r12, #4
	add r9, r9, #32
	subs lr, lr, #1
	bne 23b
21:
	mov r12, r8
	ldr r4, [r12, #1408]
	ldr r5, [r12, #1412]
	ldr r6, [r12, #1416]
	ldr r7, [r12, #1420]
	ldr r8, [r12, #1424]
	ldr r9, [r12, #1428]
	ldr r10, [r12, #1432]
	ldr r11, [r12, #1436]
	ldr lr, [r12, #1440]
	bx lr
