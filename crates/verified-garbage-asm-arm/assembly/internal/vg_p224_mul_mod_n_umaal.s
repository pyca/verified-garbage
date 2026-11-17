// The functions of `src/internal/vg_p224_mul_mod_n_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_mul_mod_n_umaal:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	add lr, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3840]
	str r7, [r12, #3844]
	str r7, [r12, #3848]
	str r7, [r12, #3852]
	str r7, [r12, #3856]
	str r7, [r12, #3860]
	str r7, [r12, #3864]
	str r7, [r12, #3868]
	str r7, [r12, #3872]
	mov r9, #8
20:
	ldr r2, [lr, #0]
	ldr r7, [r4, #0]
	ldr r5, [r12, #3840]
	mov r3, #0
	umaal r5, r3, r2, r7
	movw r0, #49899
	movt r0, #27167
	mul r0, r0, r5
	mov r6, #0
	movw r8, #10813
	movt r8, #23644
	umaal r5, r6, r0, r8
	ldr r7, [r4, #4]
	ldr r5, [r12, #3844]
	umaal r5, r3, r2, r7
	movw r8, #10565
	movt r8, #5085
	umaal r5, r6, r0, r8
	str r5, [r12, #3840]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3848]
	umaal r5, r3, r2, r7
	movw r8, #61502
	movt r8, #57528
	umaal r5, r6, r0, r8
	str r5, [r12, #3844]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3852]
	umaal r5, r3, r2, r7
	movw r8, #5794
	movt r8, #65535
	umaal r5, r6, r0, r8
	str r5, [r12, #3848]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3856]
	umaal r5, r3, r2, r7
	mvn r8, #0
	umaal r5, r6, r0, r8
	str r5, [r12, #3852]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3860]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3856]
	ldr r7, [r4, #24]
	ldr r5, [r12, #3864]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3860]
	ldr r7, [r4, #28]
	ldr r5, [r12, #3868]
	umaal r5, r3, r2, r7
	movw r8, #0
	umaal r5, r6, r0, r8
	str r5, [r12, #3864]
	ldr r5, [r12, #3872]
	mov r7, #1
	umaal r3, r5, r6, r7
	str r3, [r12, #3868]
	str r5, [r12, #3872]
	add lr, lr, #4
	subs r9, r9, #1
	bne 20b
	mov r6, #1
	mov r5, #0
	ldr r4, [r12, #3840]
	movw r0, #54723
	movt r0, #41891
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3844]
	movw r0, #54970
	movt r0, #60450
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3848]
	movw r0, #4033
	movt r0, #8007
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3852]
	movw r0, #59741
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3856]
	movw r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3860]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3864]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3868]
	mvn r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3872]
	add r6, r5, r4
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3840]
	movw r0, #54723
	movt r0, #41891
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3844]
	movw r0, #54970
	movt r0, #60450
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3848]
	movw r0, #4033
	movt r0, #8007
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3852]
	movw r0, #59741
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3856]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3860]
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3864]
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3868]
	mvn r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr
