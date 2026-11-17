// The functions of `src/internal/vg_p224_add_mod_n_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_add_mod_n_umaal:
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
	movw r7, #54723
	movt r7, #41891
	umaal r4, r6, r7, r8
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	umaal r4, r5, r0, r8
	str r4, [r12, #3980]
	movw r7, #54970
	movt r7, #60450
	umaal r4, r6, r7, r8
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	umaal r4, r5, r0, r8
	str r4, [r12, #3984]
	movw r7, #4033
	movt r7, #8007
	umaal r4, r6, r7, r8
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	umaal r4, r5, r0, r8
	str r4, [r12, #3988]
	movw r7, #59741
	umaal r4, r6, r7, r8
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	umaal r4, r5, r0, r8
	str r4, [r12, #3992]
	movw r7, #0
	umaal r4, r6, r7, r8
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	umaal r4, r5, r0, r8
	str r4, [r12, #3996]
	umaal r4, r6, r7, r8
	ldr r0, [r2, #24]
	ldr r4, [r3, #24]
	umaal r4, r5, r0, r8
	str r4, [r12, #4000]
	umaal r4, r6, r7, r8
	ldr r0, [r2, #28]
	ldr r4, [r3, #28]
	umaal r4, r5, r0, r8
	str r4, [r12, #4004]
	mvn r7, #0
	umaal r4, r6, r7, r8
	add r6, r5, r6
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3976]
	movw r0, #54723
	movt r0, #41891
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3980]
	movw r0, #54970
	movt r0, #60450
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3984]
	movw r0, #4033
	movt r0, #8007
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3988]
	movw r0, #59741
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3992]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3996]
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #4000]
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #4004]
	mvn r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	bx lr
