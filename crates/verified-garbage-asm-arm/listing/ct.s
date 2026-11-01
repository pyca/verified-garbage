// The functions of `src/ct.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ct_eq:
	push {r4}
	cmp r1, r3
	beq 20f
	mov r0, #0
	b 21f
20:
	mov r3, #0
	cmp r1, #0
	beq 22f
24:
	ldrb r12, [r0, #0]
	ldrb r4, [r2, #0]
	eor r12, r12, r4
	orr r3, r3, r12
	add r0, r0, #1
	add r2, r2, #1
	subs r1, r1, #1
	bne 24b
	b 23f
22:
23:
	sub r3, r3, #1
	lsr r0, r3, #31
21:
	ldr r4, [sp], #4
	bx lr
