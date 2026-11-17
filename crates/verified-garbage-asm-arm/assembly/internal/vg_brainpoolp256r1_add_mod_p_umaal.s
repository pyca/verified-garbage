// The functions of `src/internal/vg_brainpoolp256r1_add_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp256r1_add_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	add r2, r12, r2
	add r3, r12, r3
	mov r8, #1
	mov r5, #0
	mov r6, #0
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	umaal r4, r5, r0, r8
	str r4, [r12, #3976]
	movw r7, #44169
	movt r7, #57489
	umaal r4, r6, r7, r8
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	umaal r4, r5, r0, r8
	str r4, [r12, #3980]
	movw r7, #47074
	movt r7, #57324
	umaal r4, r6, r7, r8
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	umaal r4, r5, r0, r8
	str r4, [r12, #3984]
	movw r7, #57303
	movt r7, #10969
	umaal r4, r6, r7, r8
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	umaal r4, r5, r0, r8
	str r4, [r12, #3988]
	movw r7, #2524
	movt r7, #37316
	umaal r4, r6, r7, r8
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	umaal r4, r5, r0, r8
	str r4, [r12, #3992]
	movw r7, #29325
	movt r7, #25212
	umaal r4, r6, r7, r8
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	umaal r4, r5, r0, r8
	str r4, [r12, #3996]
	movw r7, #62831
	movt r7, #49561
	umaal r4, r6, r7, r8
	ldr r0, [r2, #24]
	ldr r4, [r3, #24]
	umaal r4, r5, r0, r8
	str r4, [r12, #4000]
	movw r7, #22083
	movt r7, #24081
	umaal r4, r6, r7, r8
	ldr r0, [r2, #28]
	ldr r4, [r3, #28]
	umaal r4, r5, r0, r8
	str r4, [r12, #4004]
	movw r7, #43044
	movt r7, #22020
	umaal r4, r6, r7, r8
	add r6, r5, r6
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3976]
	movw r0, #44169
	movt r0, #57489
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3980]
	movw r0, #47074
	movt r0, #57324
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3984]
	movw r0, #57303
	movt r0, #10969
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3988]
	movw r0, #2524
	movt r0, #37316
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3992]
	movw r0, #29325
	movt r0, #25212
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3996]
	movw r0, #62831
	movt r0, #49561
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #4000]
	movw r0, #22083
	movt r0, #24081
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #4004]
	movw r0, #43044
	movt r0, #22020
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	bx lr
