// The functions of `src/internal/vg_p192_mul_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_mul_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #4056]
	str r5, [r12, #4060]
	str r6, [r12, #4064]
	str r7, [r12, #4068]
	str r8, [r12, #4072]
	str r9, [r12, #4076]
	str lr, [r12, #4080]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4036]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #4040]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4044]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4048]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4052]
	add lr, r12, r1
	add r1, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3904]
	str r7, [r12, #3908]
	str r7, [r12, #3912]
	str r7, [r12, #3916]
	str r7, [r12, #3920]
	str r7, [r12, #3924]
	str r7, [r12, #3928]
	str r7, [r12, #3932]
	mov r9, #6
20:
	ldr r2, [r1, #0]
	mov r3, #0
	ldr r7, [r4, #0]
	ldr r5, [r12, #3904]
	umaal r5, r3, r2, r7
	str r5, [r12, #3904]
	ldr r7, [r4, #4]
	ldr r5, [r12, #3908]
	umaal r5, r3, r2, r7
	str r5, [r12, #3908]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3912]
	umaal r5, r3, r2, r7
	str r5, [r12, #3912]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3916]
	umaal r5, r3, r2, r7
	str r5, [r12, #3916]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3920]
	umaal r5, r3, r2, r7
	str r5, [r12, #3920]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3924]
	umaal r5, r3, r2, r7
	str r5, [r12, #3924]
	ldr r5, [r12, #3928]
	ldr r6, [r12, #3932]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3928]
	str r6, [r12, #3932]
	ldr r2, [r12, #3904]
	movw r7, #1
	movt r7, #0
	mul r2, r2, r7
	mov r3, #0
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3904]
	umaal r5, r3, r2, r7
	str r5, [r12, #3904]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3908]
	umaal r5, r3, r2, r7
	str r5, [r12, #3908]
	ldr r7, [r12, #4040]
	ldr r5, [r12, #3912]
	umaal r5, r3, r2, r7
	str r5, [r12, #3912]
	ldr r7, [r12, #4044]
	ldr r5, [r12, #3916]
	umaal r5, r3, r2, r7
	str r5, [r12, #3916]
	ldr r7, [r12, #4048]
	ldr r5, [r12, #3920]
	umaal r5, r3, r2, r7
	str r5, [r12, #3920]
	ldr r7, [r12, #4052]
	ldr r5, [r12, #3924]
	umaal r5, r3, r2, r7
	str r5, [r12, #3924]
	ldr r5, [r12, #3928]
	ldr r6, [r12, #3932]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3928]
	str r6, [r12, #3932]
	ldr r5, [r12, #3908]
	str r5, [r12, #3904]
	ldr r5, [r12, #3912]
	str r5, [r12, #3908]
	ldr r5, [r12, #3916]
	str r5, [r12, #3912]
	ldr r5, [r12, #3920]
	str r5, [r12, #3916]
	ldr r5, [r12, #3924]
	str r5, [r12, #3920]
	ldr r5, [r12, #3928]
	str r5, [r12, #3924]
	ldr r5, [r12, #3932]
	str r5, [r12, #3928]
	mov r5, #0
	str r5, [r12, #3932]
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	sub r1, lr, r12
	mov r6, #1
	mov r5, #0
	ldr r4, [r12, #3904]
	movw r0, #1
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3908]
	movw r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3912]
	movw r0, #1
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
	movw r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3908]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3912]
	movw r0, #1
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
