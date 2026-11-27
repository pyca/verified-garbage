// The functions of `src/internal/vg_p384_mul_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #4008]
	str r5, [r12, #4012]
	str r6, [r12, #4016]
	str r7, [r12, #4020]
	str r8, [r12, #4024]
	str r9, [r12, #4028]
	str lr, [r12, #4032]
	add lr, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3712]
	str r7, [r12, #3716]
	str r7, [r12, #3720]
	str r7, [r12, #3724]
	str r7, [r12, #3728]
	str r7, [r12, #3732]
	str r7, [r12, #3736]
	str r7, [r12, #3740]
	str r7, [r12, #3744]
	str r7, [r12, #3748]
	str r7, [r12, #3752]
	str r7, [r12, #3756]
	str r7, [r12, #3760]
	mov r9, #12
20:
	ldr r2, [lr, #0]
	ldr r7, [r4, #0]
	ldr r5, [r12, #3712]
	mov r3, #0
	umaal r5, r3, r2, r7
	mov r0, r5
	mov r6, #0
	mvn r8, #0
	umaal r5, r6, r0, r8
	ldr r7, [r4, #4]
	ldr r5, [r12, #3716]
	umaal r5, r3, r2, r7
	movw r8, #0
	umaal r5, r6, r0, r8
	str r5, [r12, #3712]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3720]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3716]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3724]
	umaal r5, r3, r2, r7
	mvn r8, #0
	umaal r5, r6, r0, r8
	str r5, [r12, #3720]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3728]
	umaal r5, r3, r2, r7
	mvn r8, #1
	umaal r5, r6, r0, r8
	str r5, [r12, #3724]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3732]
	umaal r5, r3, r2, r7
	mvn r8, #0
	umaal r5, r6, r0, r8
	str r5, [r12, #3728]
	ldr r7, [r4, #24]
	ldr r5, [r12, #3736]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3732]
	ldr r7, [r4, #28]
	ldr r5, [r12, #3740]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3736]
	ldr r7, [r4, #32]
	ldr r5, [r12, #3744]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3740]
	ldr r7, [r4, #36]
	ldr r5, [r12, #3748]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3744]
	ldr r7, [r4, #40]
	ldr r5, [r12, #3752]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3748]
	ldr r7, [r4, #44]
	ldr r5, [r12, #3756]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3752]
	ldr r5, [r12, #3760]
	mov r7, #1
	umaal r3, r5, r6, r7
	str r3, [r12, #3756]
	str r5, [r12, #3760]
	add lr, lr, #4
	subs r9, r9, #1
	bne 20b
	mov r6, #1
	mov r5, #0
	ldr r4, [r12, #3712]
	movw r0, #1
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3716]
	mvn r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3720]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3724]
	movw r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3728]
	movw r0, #1
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3732]
	movw r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3736]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3740]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3744]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3748]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3752]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3756]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3760]
	add r6, r5, r4
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3712]
	movw r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3716]
	mvn r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3720]
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3724]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3728]
	movw r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3732]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3736]
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3740]
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #3744]
	umaal r4, r5, r0, r6
	str r4, [r1, #32]
	ldr r4, [r12, #3748]
	umaal r4, r5, r0, r6
	str r4, [r1, #36]
	ldr r4, [r12, #3752]
	umaal r4, r5, r0, r6
	str r4, [r1, #40]
	ldr r4, [r12, #3756]
	umaal r4, r5, r0, r6
	str r4, [r1, #44]
	ldr r4, [r12, #4008]
	ldr r5, [r12, #4012]
	ldr r6, [r12, #4016]
	ldr r7, [r12, #4020]
	ldr r8, [r12, #4024]
	ldr r9, [r12, #4028]
	ldr lr, [r12, #4032]
	bx lr
