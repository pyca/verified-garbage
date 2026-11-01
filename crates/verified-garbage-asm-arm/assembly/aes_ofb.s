// The functions of `src/aes_ofb.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ofb:
	ldr r12, [sp, #4]
	str r4, [r12, #2064]
	str r5, [r12, #2068]
	str r6, [r12, #2072]
	str r7, [r12, #2076]
	str r8, [r12, #2080]
	str r9, [r12, #2084]
	str lr, [r12, #2092]
	str r10, [r12, #2088]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	ldr r8, [sp, #0]
	mov r10, r12
	cmp r8, #0
	beq 20f
22:
	mov r0, r4
	mov r1, r5
	mov r2, r6
	mov r3, #1
	mov r12, r10
	push {r12, lr}
	bl {vg_aes_encrypt_blocks}
	ldr r12, [sp], #8
	ldr r12, [r7, #0]
	ldr lr, [r6, #0]
	eor r12, r12, lr
	str r12, [r7, #0]
	ldr r12, [r7, #4]
	ldr lr, [r6, #4]
	eor r12, r12, lr
	str r12, [r7, #4]
	ldr r12, [r7, #8]
	ldr lr, [r6, #8]
	eor r12, r12, lr
	str r12, [r7, #8]
	ldr r12, [r7, #12]
	ldr lr, [r6, #12]
	eor r12, r12, lr
	str r12, [r7, #12]
	add r7, r7, #16
	subs r8, r8, #1
	bne 22b
	b 21f
20:
21:
	ldr r4, [r10, #2064]
	ldr r5, [r10, #2068]
	ldr r6, [r10, #2072]
	ldr r7, [r10, #2076]
	ldr r8, [r10, #2080]
	ldr r9, [r10, #2084]
	ldr lr, [r10, #2092]
	ldr r10, [r10, #2088]
	bx lr
