// The functions of `src/internal/vg_mlkem1024_compress_encode.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_compress_encode:
	cmp r1, #5
	mov r3, #32
	beq 20f
22:
	ldr r1, [r0, #0]
	movw r12, #60398
	movt r12, #4
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	strb r1, [r2, #0]
	lsr r1, r1, #8
	strb r1, [r2, #1]
	ldr r1, [r0, #4]
	movw r12, #60398
	movt r12, #4
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	ldrb r12, [r2, #1]
	add r12, r12, r1, lsl #3
	strb r12, [r2, #1]
	lsr r1, r1, #5
	strb r1, [r2, #2]
	ldr r1, [r0, #8]
	movw r12, #60398
	movt r12, #4
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	ldrb r12, [r2, #2]
	add r12, r12, r1, lsl #6
	strb r12, [r2, #2]
	lsr r1, r1, #2
	strb r1, [r2, #3]
	lsr r1, r1, #8
	strb r1, [r2, #4]
	ldr r1, [r0, #12]
	movw r12, #60398
	movt r12, #4
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	ldrb r12, [r2, #4]
	add r12, r12, r1, lsl #1
	strb r12, [r2, #4]
	lsr r1, r1, #7
	strb r1, [r2, #5]
	ldr r1, [r0, #16]
	movw r12, #60398
	movt r12, #4
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	ldrb r12, [r2, #5]
	add r12, r12, r1, lsl #4
	strb r12, [r2, #5]
	lsr r1, r1, #4
	strb r1, [r2, #6]
	ldr r1, [r0, #20]
	movw r12, #60398
	movt r12, #4
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	ldrb r12, [r2, #6]
	add r12, r12, r1, lsl #7
	strb r12, [r2, #6]
	lsr r1, r1, #1
	strb r1, [r2, #7]
	lsr r1, r1, #8
	strb r1, [r2, #8]
	ldr r1, [r0, #24]
	movw r12, #60398
	movt r12, #4
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	ldrb r12, [r2, #8]
	add r12, r12, r1, lsl #2
	strb r12, [r2, #8]
	lsr r1, r1, #6
	strb r1, [r2, #9]
	ldr r1, [r0, #28]
	movw r12, #60398
	movt r12, #4
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	ldrb r12, [r2, #9]
	add r12, r12, r1, lsl #5
	strb r12, [r2, #9]
	lsr r1, r1, #3
	strb r1, [r2, #10]
	add r0, r0, #32
	add r2, r2, #11
	subs r3, r3, #1
	bne 22b
	b 21f
20:
23:
	ldr r1, [r0, #0]
	movw r12, #5040
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	and r1, r1, #31
	strb r1, [r2, #0]
	ldr r1, [r0, #4]
	movw r12, #5040
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	and r1, r1, #31
	ldrb r12, [r2, #0]
	add r12, r12, r1, lsl #5
	strb r12, [r2, #0]
	lsr r1, r1, #3
	strb r1, [r2, #1]
	ldr r1, [r0, #8]
	movw r12, #5040
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	and r1, r1, #31
	ldrb r12, [r2, #1]
	add r12, r12, r1, lsl #2
	strb r12, [r2, #1]
	ldr r1, [r0, #12]
	movw r12, #5040
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	and r1, r1, #31
	ldrb r12, [r2, #1]
	add r12, r12, r1, lsl #7
	strb r12, [r2, #1]
	lsr r1, r1, #1
	strb r1, [r2, #2]
	ldr r1, [r0, #16]
	movw r12, #5040
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	and r1, r1, #31
	ldrb r12, [r2, #2]
	add r12, r12, r1, lsl #4
	strb r12, [r2, #2]
	lsr r1, r1, #4
	strb r1, [r2, #3]
	ldr r1, [r0, #20]
	movw r12, #5040
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	and r1, r1, #31
	ldrb r12, [r2, #3]
	add r12, r12, r1, lsl #1
	strb r12, [r2, #3]
	ldr r1, [r0, #24]
	movw r12, #5040
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	and r1, r1, #31
	ldrb r12, [r2, #3]
	add r12, r12, r1, lsl #6
	strb r12, [r2, #3]
	lsr r1, r1, #2
	strb r1, [r2, #4]
	ldr r1, [r0, #28]
	movw r12, #5040
	mul r1, r1, r12
	add r1, r1, #262144
	sub r1, r1, #256
	lsr r1, r1, #19
	and r1, r1, #31
	ldrb r12, [r2, #4]
	add r12, r12, r1, lsl #3
	strb r12, [r2, #4]
	add r0, r0, #32
	add r2, r2, #5
	subs r3, r3, #1
	bne 23b
21:
	bx lr
