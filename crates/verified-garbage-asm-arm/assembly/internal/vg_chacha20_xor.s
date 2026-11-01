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
	beq 23f
	mov r2, #64
	b 24f
23:
	mov r2, r6
24:
	sub r6, r6, r2
	mov r3, r1
25:
	ldrb r0, [r5, #0]
	ldrb r12, [r3, #0]
	eor r0, r0, r12
	strb r0, [r5, #0]
	add r5, r5, #1
	add r3, r3, #1
	subs r2, r2, #1
	bne 25b
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
	bx lr
