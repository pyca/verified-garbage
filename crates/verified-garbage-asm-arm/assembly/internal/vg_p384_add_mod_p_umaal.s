// The functions of `src/internal/vg_p384_add_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_add_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #4008]
	str r5, [r12, #4012]
	str r6, [r12, #4016]
	str r7, [r12, #4020]
	str r8, [r12, #4024]
	add r2, r12, r2
	add r3, r12, r3
	mov r8, #1
	mov r5, #0
	mov r6, #0
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	umaal r4, r5, r0, r8
	str r4, [r12, #3912]
	movw r7, #1
	umaal r4, r6, r7, r8
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	umaal r4, r5, r0, r8
	str r4, [r12, #3916]
	mvn r7, #0
	umaal r4, r6, r7, r8
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	umaal r4, r5, r0, r8
	str r4, [r12, #3920]
	umaal r4, r6, r7, r8
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	umaal r4, r5, r0, r8
	str r4, [r12, #3924]
	movw r7, #0
	umaal r4, r6, r7, r8
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	umaal r4, r5, r0, r8
	str r4, [r12, #3928]
	movw r7, #1
	umaal r4, r6, r7, r8
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	umaal r4, r5, r0, r8
	str r4, [r12, #3932]
	movw r7, #0
	umaal r4, r6, r7, r8
	ldr r0, [r2, #24]
	ldr r4, [r3, #24]
	umaal r4, r5, r0, r8
	str r4, [r12, #3936]
	umaal r4, r6, r7, r8
	ldr r0, [r2, #28]
	ldr r4, [r3, #28]
	umaal r4, r5, r0, r8
	str r4, [r12, #3940]
	umaal r4, r6, r7, r8
	ldr r0, [r2, #32]
	ldr r4, [r3, #32]
	umaal r4, r5, r0, r8
	str r4, [r12, #3944]
	umaal r4, r6, r7, r8
	ldr r0, [r2, #36]
	ldr r4, [r3, #36]
	umaal r4, r5, r0, r8
	str r4, [r12, #3948]
	umaal r4, r6, r7, r8
	ldr r0, [r2, #40]
	ldr r4, [r3, #40]
	umaal r4, r5, r0, r8
	str r4, [r12, #3952]
	umaal r4, r6, r7, r8
	ldr r0, [r2, #44]
	ldr r4, [r3, #44]
	umaal r4, r5, r0, r8
	str r4, [r12, #3956]
	umaal r4, r6, r7, r8
	add r6, r5, r6
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3912]
	movw r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3916]
	mvn r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3920]
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3924]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3928]
	movw r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3932]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3936]
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3940]
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #3944]
	umaal r4, r5, r0, r6
	str r4, [r1, #32]
	ldr r4, [r12, #3948]
	umaal r4, r5, r0, r6
	str r4, [r1, #36]
	ldr r4, [r12, #3952]
	umaal r4, r5, r0, r6
	str r4, [r1, #40]
	ldr r4, [r12, #3956]
	umaal r4, r5, r0, r6
	str r4, [r1, #44]
	ldr r4, [r12, #4008]
	ldr r5, [r12, #4012]
	ldr r6, [r12, #4016]
	ldr r7, [r12, #4020]
	ldr r8, [r12, #4024]
	bx lr
