// The functions of `src/internal/vg_p192_add_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_add_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #4056]
	str r5, [r12, #4060]
	str r6, [r12, #4064]
	str r7, [r12, #4068]
	str r8, [r12, #4072]
	add r2, r12, r2
	add r3, r12, r3
	mov r8, #1
	mov r5, #0
	mov r6, #0
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	umaal r4, r5, r0, r8
	str r4, [r12, #4008]
	movw r7, #1
	umaal r4, r6, r7, r8
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	umaal r4, r5, r0, r8
	str r4, [r12, #4012]
	movw r7, #0
	umaal r4, r6, r7, r8
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	umaal r4, r5, r0, r8
	str r4, [r12, #4016]
	movw r7, #1
	umaal r4, r6, r7, r8
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	umaal r4, r5, r0, r8
	str r4, [r12, #4020]
	movw r7, #0
	umaal r4, r6, r7, r8
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	umaal r4, r5, r0, r8
	str r4, [r12, #4024]
	umaal r4, r6, r7, r8
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	umaal r4, r5, r0, r8
	str r4, [r12, #4028]
	umaal r4, r6, r7, r8
	add r6, r5, r6
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #4008]
	movw r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #4012]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #4016]
	movw r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #4020]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #4024]
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #4028]
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #4056]
	ldr r5, [r12, #4060]
	ldr r6, [r12, #4064]
	ldr r7, [r12, #4068]
	ldr r8, [r12, #4072]
	bx lr
