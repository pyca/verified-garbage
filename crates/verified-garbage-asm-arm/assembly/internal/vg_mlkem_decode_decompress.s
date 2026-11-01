// The functions of `src/internal/vg_mlkem_decode_decompress.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode_decompress:
	cmp r2, #1
	beq 20f
	cmp r2, #4
	beq 22f
24:
	ldrb r2, [r0, #1]
	lsl r2, r2, #30
	lsr r2, r2, #22
	ldrb r12, [r0, #0]
	add r2, r2, r12
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #512
	lsr r12, r12, #10
	str r12, [r3, #0]
	ldrb r2, [r0, #2]
	lsl r2, r2, #28
	lsr r2, r2, #22
	ldrb r12, [r0, #1]
	add r2, r2, r12, lsr #2
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #512
	lsr r12, r12, #10
	str r12, [r3, #4]
	ldrb r2, [r0, #3]
	lsl r2, r2, #26
	lsr r2, r2, #22
	ldrb r12, [r0, #2]
	add r2, r2, r12, lsr #4
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #512
	lsr r12, r12, #10
	str r12, [r3, #8]
	ldrb r2, [r0, #4]
	lsl r2, r2, #2
	ldrb r12, [r0, #3]
	add r2, r2, r12, lsr #6
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #512
	lsr r12, r12, #10
	str r12, [r3, #12]
	add r0, r0, #5
	add r3, r3, #16
	subs r1, r1, #5
	bne 24b
	b 23f
22:
25:
	ldrb r2, [r0, #0]
	lsl r2, r2, #28
	lsr r2, r2, #28
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #8
	lsr r12, r12, #4
	str r12, [r3, #0]
	ldrb r2, [r0, #0]
	lsr r2, r2, #4
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #8
	lsr r12, r12, #4
	str r12, [r3, #4]
	add r0, r0, #1
	add r3, r3, #8
	subs r1, r1, #1
	bne 25b
23:
	b 21f
20:
26:
	ldrb r2, [r0, #0]
	lsl r2, r2, #31
	lsr r2, r2, #31
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1
	lsr r12, r12, #1
	str r12, [r3, #0]
	ldrb r2, [r0, #0]
	lsl r2, r2, #30
	lsr r2, r2, #31
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1
	lsr r12, r12, #1
	str r12, [r3, #4]
	ldrb r2, [r0, #0]
	lsl r2, r2, #29
	lsr r2, r2, #31
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1
	lsr r12, r12, #1
	str r12, [r3, #8]
	ldrb r2, [r0, #0]
	lsl r2, r2, #28
	lsr r2, r2, #31
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1
	lsr r12, r12, #1
	str r12, [r3, #12]
	ldrb r2, [r0, #0]
	lsl r2, r2, #27
	lsr r2, r2, #31
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1
	lsr r12, r12, #1
	str r12, [r3, #16]
	ldrb r2, [r0, #0]
	lsl r2, r2, #26
	lsr r2, r2, #31
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1
	lsr r12, r12, #1
	str r12, [r3, #20]
	ldrb r2, [r0, #0]
	lsl r2, r2, #25
	lsr r2, r2, #31
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1
	lsr r12, r12, #1
	str r12, [r3, #24]
	ldrb r2, [r0, #0]
	lsl r2, r2, #24
	lsr r2, r2, #31
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1
	lsr r12, r12, #1
	str r12, [r3, #28]
	add r0, r0, #1
	add r3, r3, #32
	subs r1, r1, #1
	bne 26b
21:
	bx lr
