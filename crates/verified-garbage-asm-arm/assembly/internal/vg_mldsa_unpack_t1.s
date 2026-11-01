// The functions of `src/internal/vg_mldsa_unpack_t1.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_unpack_t1:
	mov r2, #64
20:
	mov r3, #0
	ldrb r12, [r0, #0]
	add r3, r3, r12
	ldrb r12, [r0, #1]
	add r3, r3, r12, lsl #8
	lsl r12, r3, #22
	lsr r12, r12, #22
	lsr r3, r3, #10
	lsl r12, r12, #13
	str r12, [r1, #0]
	ldrb r12, [r0, #2]
	add r3, r3, r12, lsl #6
	lsl r12, r3, #22
	lsr r12, r12, #22
	lsr r3, r3, #10
	lsl r12, r12, #13
	str r12, [r1, #4]
	ldrb r12, [r0, #3]
	add r3, r3, r12, lsl #4
	lsl r12, r3, #22
	lsr r12, r12, #22
	lsr r3, r3, #10
	lsl r12, r12, #13
	str r12, [r1, #8]
	ldrb r12, [r0, #4]
	add r3, r3, r12, lsl #2
	lsl r12, r3, #22
	lsr r12, r12, #22
	lsr r3, r3, #10
	lsl r12, r12, #13
	str r12, [r1, #12]
	add r0, r0, #5
	add r1, r1, #16
	subs r2, r2, #1
	bne 20b
	bx lr
