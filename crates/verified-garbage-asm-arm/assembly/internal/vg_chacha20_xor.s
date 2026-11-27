// The functions of `src/internal/vg_chacha20_xor.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_xor:
	str r4, [r3, #256]
	str r5, [r3, #260]
	str r6, [r3, #264]
	str lr, [r3, #268]
	str r7, [r3, #272]
	mov r7, r5
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r1, r3
	cmp r6, #0
	beq 20f
22:
	mov r0, r4
	bl {vg_chacha20_block}
	lsr r2, r6, #6
	cmp r2, #0
	bne 23f
	mov r2, r6
	sub r6, r6, r2
	mov r3, r1
25:
	ldrb r0, [r5, #0]
	ldrb r12, [r3, #0]
	eor r0, r0, r12
	strb r0, [r7, #0]
	add r5, r5, #1
	add r7, r7, #1
	add r3, r3, #1
	subs r2, r2, #1
	bne 25b
	b 24f
23:
	sub r6, r6, #64
	ldr r0, [r5, #0]
	ldr r12, [r1, #0]
	eor r0, r0, r12
	str r0, [r7, #0]
	ldr r0, [r5, #4]
	ldr r12, [r1, #4]
	eor r0, r0, r12
	str r0, [r7, #4]
	ldr r0, [r5, #8]
	ldr r12, [r1, #8]
	eor r0, r0, r12
	str r0, [r7, #8]
	ldr r0, [r5, #12]
	ldr r12, [r1, #12]
	eor r0, r0, r12
	str r0, [r7, #12]
	ldr r0, [r5, #16]
	ldr r12, [r1, #16]
	eor r0, r0, r12
	str r0, [r7, #16]
	ldr r0, [r5, #20]
	ldr r12, [r1, #20]
	eor r0, r0, r12
	str r0, [r7, #20]
	ldr r0, [r5, #24]
	ldr r12, [r1, #24]
	eor r0, r0, r12
	str r0, [r7, #24]
	ldr r0, [r5, #28]
	ldr r12, [r1, #28]
	eor r0, r0, r12
	str r0, [r7, #28]
	ldr r0, [r5, #32]
	ldr r12, [r1, #32]
	eor r0, r0, r12
	str r0, [r7, #32]
	ldr r0, [r5, #36]
	ldr r12, [r1, #36]
	eor r0, r0, r12
	str r0, [r7, #36]
	ldr r0, [r5, #40]
	ldr r12, [r1, #40]
	eor r0, r0, r12
	str r0, [r7, #40]
	ldr r0, [r5, #44]
	ldr r12, [r1, #44]
	eor r0, r0, r12
	str r0, [r7, #44]
	ldr r0, [r5, #48]
	ldr r12, [r1, #48]
	eor r0, r0, r12
	str r0, [r7, #48]
	ldr r0, [r5, #52]
	ldr r12, [r1, #52]
	eor r0, r0, r12
	str r0, [r7, #52]
	ldr r0, [r5, #56]
	ldr r12, [r1, #56]
	eor r0, r0, r12
	str r0, [r7, #56]
	ldr r0, [r5, #60]
	ldr r12, [r1, #60]
	eor r0, r0, r12
	str r0, [r7, #60]
	add r5, r5, #64
	add r7, r7, #64
24:
	ldr r0, [r4, #48]
	add r0, r0, #1
	str r0, [r4, #48]
	cmp r6, #0
	bne 22b
	b 21f
20:
21:
	mov r0, r4
	ldr r4, [r1, #256]
	ldr r5, [r1, #260]
	ldr r6, [r1, #264]
	ldr lr, [r1, #268]
	ldr r7, [r1, #272]
	bx lr
