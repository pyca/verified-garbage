// The functions of `src/internal/vg_p192_sub_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_sub_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #4056]
	str r5, [r12, #4060]
	str r6, [r12, #4064]
	add r2, r12, r2
	add r3, r12, r3
	mov r6, #1
	mov r5, #1
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #4008]
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #4012]
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #4016]
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #4020]
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #4024]
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #4028]
	eor r6, r5, #1
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #4008]
	mvn r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #4012]
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #4016]
	mvn r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #4020]
	mvn r0, #0
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
	bx lr
