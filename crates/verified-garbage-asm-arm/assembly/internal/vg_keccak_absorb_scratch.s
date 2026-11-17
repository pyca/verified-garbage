// The functions of `src/internal/vg_keccak_absorb_scratch.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_absorb_scratch:
	ldr r12, [sp, #4]
	str r4, [r12, #512]
	str r5, [r12, #516]
	str r6, [r12, #520]
	str r7, [r12, #524]
	str lr, [r12, #528]
	mov r4, r1
	mov r1, r12
	mov r5, r2
	mov r6, r3
	ldr r7, [sp, #0]
	cmp r7, #0
	beq 20f
22:
	sub r12, r4, r5
	mvn r3, #0
	subs r2, r7, r12
	adc r3, r3, #0
	and r2, r2, r3
	add r2, r12, r2
	lsr lr, r2, #2
	cmp lr, #0
	beq 23f
	sub r7, r7, lr, lsl #2
	add r3, r0, r5
	add r5, r5, lr, lsl #2
25:
	ldr r2, [r6, #0]
	ldr r12, [r3, #0]
	eor r2, r2, r12
	str r2, [r3, #0]
	add r6, r6, #4
	add r3, r3, #4
	subs lr, lr, #1
	bne 25b
	cmp r5, r4
	b 24f
23:
	ldrb r2, [r6, #0]
	add r3, r0, r5
	ldrb r12, [r3, #0]
	eor r2, r2, r12
	strb r2, [r3, #0]
	add r6, r6, #1
	add r5, r5, #1
	sub r7, r7, #1
	cmp r5, r4
24:
	beq 26f
	b 27f
26:
	mov r5, #0
	bl {vg_keccak_f1600}
27:
	cmp r7, #0
	bne 22b
	b 21f
20:
21:
	mov r0, r5
	ldr r4, [r1, #512]
	ldr r5, [r1, #516]
	ldr r6, [r1, #520]
	ldr r7, [r1, #524]
	ldr lr, [r1, #528]
	bx lr
