// The functions of `src/internal/vg_mlkem_decode12.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode12:
	mov r2, #128
20:
	ldrb r3, [r0, #0]
	ldrb r12, [r0, #1]
	lsl r12, r12, #28
	add r3, r3, r12, lsr #20
	sub r3, r3, #3328
	sub r3, r3, #1
	lsr r12, r3, #31
	add r3, r3, r12
	add r3, r3, r12, lsl #8
	add r3, r3, r12, lsl #10
	add r3, r3, r12, lsl #11
	str r3, [r1, #0]
	ldrb r3, [r0, #1]
	lsr r3, r3, #4
	ldrb r12, [r0, #2]
	add r3, r3, r12, lsl #4
	sub r3, r3, #3328
	sub r3, r3, #1
	lsr r12, r3, #31
	add r3, r3, r12
	add r3, r3, r12, lsl #8
	add r3, r3, r12, lsl #10
	add r3, r3, r12, lsl #11
	str r3, [r1, #4]
	add r0, r0, #3
	add r1, r1, #8
	subs r2, r2, #1
	bne 20b
	bx lr
