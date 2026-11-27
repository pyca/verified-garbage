// The functions of `src/internal/vg_p192_mul_mod_n_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_mul_mod_n_umaal:
	mov r12, r0
	str r4, [r12, #4056]
	str r5, [r12, #4060]
	str r6, [r12, #4064]
	str r7, [r12, #4068]
	str r8, [r12, #4072]
	str r9, [r12, #4076]
	str lr, [r12, #4080]
	add lr, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3904]
	str r7, [r12, #3908]
	str r7, [r12, #3912]
	str r7, [r12, #3916]
	str r7, [r12, #3920]
	str r7, [r12, #3924]
	str r7, [r12, #3928]
	mov r9, #6
20:
	ldr r2, [lr, #0]
	ldr r7, [r4, #0]
	ldr r5, [r12, #3904]
	mov r3, #0
	umaal r5, r3, r2, r7
	movw r0, #53039
	movt r0, #3547
	mul r0, r0, r5
	mov r6, #0
	movw r8, #10289
	movt r8, #46290
	umaal r5, r6, r0, r8
	ldr r7, [r4, #4]
	ldr r5, [r12, #3908]
	umaal r5, r3, r2, r7
	movw r8, #51633
	movt r8, #5227
	umaal r5, r6, r0, r8
	str r5, [r12, #3904]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3912]
	umaal r5, r3, r2, r7
	movw r8, #63542
	movt r8, #39390
	umaal r5, r6, r0, r8
	str r5, [r12, #3908]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3916]
	umaal r5, r3, r2, r7
	mvn r8, #0
	umaal r5, r6, r0, r8
	str r5, [r12, #3912]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3920]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3916]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3924]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3920]
	ldr r5, [r12, #3928]
	mov r7, #1
	umaal r3, r5, r6, r7
	str r3, [r12, #3924]
	str r5, [r12, #3928]
	add lr, lr, #4
	subs r9, r9, #1
	bne 20b
	mov r6, #1
	mov r5, #0
	ldr r4, [r12, #3904]
	movw r0, #55247
	movt r0, #19245
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3908]
	movw r0, #13902
	movt r0, #60308
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3912]
	movw r0, #1993
	movt r0, #26145
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3916]
	movw r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3920]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3924]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3928]
	add r6, r5, r4
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3904]
	movw r0, #55247
	movt r0, #19245
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3908]
	movw r0, #13902
	movt r0, #60308
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3912]
	movw r0, #1993
	movt r0, #26145
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3916]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3920]
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3924]
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #4056]
	ldr r5, [r12, #4060]
	ldr r6, [r12, #4064]
	ldr r7, [r12, #4068]
	ldr r8, [r12, #4072]
	ldr r9, [r12, #4076]
	ldr lr, [r12, #4080]
	bx lr
