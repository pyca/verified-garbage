// The functions of `src/internal/vg_mlkem1024_decode_decompress.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_decode_decompress:
	cmp r2, #5
	beq 20f
22:
	ldrb r2, [r0, #0]
	ldrb r12, [r0, #1]
	add r2, r2, r12, lsl #8
	lsl r2, r2, #21
	lsr r2, r2, #21
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1024
	lsr r12, r12, #11
	str r12, [r3, #0]
	ldrb r2, [r0, #1]
	lsr r2, r2, #3
	ldrb r12, [r0, #2]
	add r2, r2, r12, lsl #5
	lsl r2, r2, #21
	lsr r2, r2, #21
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1024
	lsr r12, r12, #11
	str r12, [r3, #4]
	ldrb r2, [r0, #2]
	lsr r2, r2, #6
	ldrb r12, [r0, #3]
	add r2, r2, r12, lsl #2
	ldrb r12, [r0, #4]
	add r2, r2, r12, lsl #10
	lsl r2, r2, #21
	lsr r2, r2, #21
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1024
	lsr r12, r12, #11
	str r12, [r3, #8]
	ldrb r2, [r0, #4]
	lsr r2, r2, #1
	ldrb r12, [r0, #5]
	add r2, r2, r12, lsl #7
	lsl r2, r2, #21
	lsr r2, r2, #21
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1024
	lsr r12, r12, #11
	str r12, [r3, #12]
	ldrb r2, [r0, #5]
	lsr r2, r2, #4
	ldrb r12, [r0, #6]
	add r2, r2, r12, lsl #4
	lsl r2, r2, #21
	lsr r2, r2, #21
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1024
	lsr r12, r12, #11
	str r12, [r3, #16]
	ldrb r2, [r0, #6]
	lsr r2, r2, #7
	ldrb r12, [r0, #7]
	add r2, r2, r12, lsl #1
	ldrb r12, [r0, #8]
	add r2, r2, r12, lsl #9
	lsl r2, r2, #21
	lsr r2, r2, #21
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1024
	lsr r12, r12, #11
	str r12, [r3, #20]
	ldrb r2, [r0, #8]
	lsr r2, r2, #2
	ldrb r12, [r0, #9]
	add r2, r2, r12, lsl #6
	lsl r2, r2, #21
	lsr r2, r2, #21
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1024
	lsr r12, r12, #11
	str r12, [r3, #24]
	ldrb r2, [r0, #9]
	lsr r2, r2, #5
	ldrb r12, [r0, #10]
	add r2, r2, r12, lsl #3
	lsl r2, r2, #21
	lsr r2, r2, #21
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #1024
	lsr r12, r12, #11
	str r12, [r3, #28]
	add r0, r0, #11
	add r3, r3, #32
	subs r1, r1, #11
	bne 22b
	b 21f
20:
23:
	ldrb r2, [r0, #0]
	lsl r2, r2, #27
	lsr r2, r2, #27
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #16
	lsr r12, r12, #5
	str r12, [r3, #0]
	ldrb r2, [r0, #0]
	lsr r2, r2, #5
	ldrb r12, [r0, #1]
	add r2, r2, r12, lsl #3
	lsl r2, r2, #27
	lsr r2, r2, #27
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #16
	lsr r12, r12, #5
	str r12, [r3, #4]
	ldrb r2, [r0, #1]
	lsr r2, r2, #2
	lsl r2, r2, #27
	lsr r2, r2, #27
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #16
	lsr r12, r12, #5
	str r12, [r3, #8]
	ldrb r2, [r0, #1]
	lsr r2, r2, #7
	ldrb r12, [r0, #2]
	add r2, r2, r12, lsl #1
	lsl r2, r2, #27
	lsr r2, r2, #27
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #16
	lsr r12, r12, #5
	str r12, [r3, #12]
	ldrb r2, [r0, #2]
	lsr r2, r2, #4
	ldrb r12, [r0, #3]
	add r2, r2, r12, lsl #4
	lsl r2, r2, #27
	lsr r2, r2, #27
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #16
	lsr r12, r12, #5
	str r12, [r3, #16]
	ldrb r2, [r0, #3]
	lsr r2, r2, #1
	lsl r2, r2, #27
	lsr r2, r2, #27
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #16
	lsr r12, r12, #5
	str r12, [r3, #20]
	ldrb r2, [r0, #3]
	lsr r2, r2, #6
	ldrb r12, [r0, #4]
	add r2, r2, r12, lsl #2
	lsl r2, r2, #27
	lsr r2, r2, #27
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #16
	lsr r12, r12, #5
	str r12, [r3, #24]
	ldrb r2, [r0, #4]
	lsr r2, r2, #3
	lsl r2, r2, #27
	lsr r2, r2, #27
	add r12, r2, r2, lsl #8
	add r12, r12, r2, lsl #10
	add r12, r12, r2, lsl #11
	add r12, r12, #16
	lsr r12, r12, #5
	str r12, [r3, #28]
	add r0, r0, #5
	add r3, r3, #32
	subs r1, r1, #5
	bne 23b
21:
	bx lr
