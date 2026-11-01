// The functions of `src/zeroize.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_zeroize:
	mov r2, #0
	lsr r3, r1, #5
	cmp r3, #0
	beq 20f
22:
	str r2, [r0, #0]
	str r2, [r0, #4]
	str r2, [r0, #8]
	str r2, [r0, #12]
	str r2, [r0, #16]
	str r2, [r0, #20]
	str r2, [r0, #24]
	str r2, [r0, #28]
	add r0, r0, #32
	subs r3, r3, #1
	bne 22b
	b 21f
20:
21:
	lsr r3, r1, #2
	and r3, r3, #7
	cmp r3, #0
	beq 23f
25:
	str r2, [r0, #0]
	add r0, r0, #4
	subs r3, r3, #1
	bne 25b
	b 24f
23:
24:
	and r1, r1, #3
	mov r3, r1
	cmp r3, #0
	beq 26f
28:
	strb r2, [r0, #0]
	add r0, r0, #1
	subs r3, r3, #1
	bne 28b
	b 27f
26:
27:
	bx lr
