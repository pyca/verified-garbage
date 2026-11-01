// The functions of `src/internal/vg_cmac_aes_subkeys.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_subkeys:
	str r4, [r3, #2064]
	str r5, [r3, #2068]
	str r6, [r3, #2072]
	str lr, [r3, #2076]
	mov r6, r2
	mov r5, r3
	mov r12, #0
	str r12, [r3, #2048]
	str r12, [r3, #2052]
	str r12, [r3, #2056]
	str r12, [r3, #2060]
	str r12, [r2, #0]
	str r12, [r2, #4]
	str r12, [r2, #8]
	str r12, [r2, #12]
	add r2, r5, #2048
	mov r3, r6
	mov r4, #1
	push {r4, r5}
	bl {vg_aes_ctr32}
	ldr r4, [sp], #8
	ldr r0, [r6, #0]
	ldr r1, [r6, #4]
	ldr r2, [r6, #8]
	ldr r3, [r6, #12]
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	lsr r12, r0, #31
	mov r4, #0
	sub r12, r4, r12
	and r12, r12, #135
	lsl r0, r0, #1
	orr r0, r0, r1, lsr #31
	lsl r1, r1, #1
	orr r1, r1, r2, lsr #31
	lsl r2, r2, #1
	orr r2, r2, r3, lsr #31
	lsl r3, r3, #1
	eor r3, r3, r12
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	str r0, [r6, #0]
	str r1, [r6, #4]
	str r2, [r6, #8]
	str r3, [r6, #12]
	ldr r0, [r6, #0]
	ldr r1, [r6, #4]
	ldr r2, [r6, #8]
	ldr r3, [r6, #12]
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	lsr r12, r0, #31
	mov r4, #0
	sub r12, r4, r12
	and r12, r12, #135
	lsl r0, r0, #1
	orr r0, r0, r1, lsr #31
	lsl r1, r1, #1
	orr r1, r1, r2, lsr #31
	lsl r2, r2, #1
	orr r2, r2, r3, lsr #31
	lsl r3, r3, #1
	eor r3, r3, r12
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	str r0, [r6, #16]
	str r1, [r6, #20]
	str r2, [r6, #24]
	str r3, [r6, #28]
	ldr r4, [r5, #2064]
	ldr r6, [r5, #2072]
	ldr lr, [r5, #2076]
	ldr r5, [r5, #2068]
	bx lr
