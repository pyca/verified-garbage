// The functions of `src/internal/vg_secp256k1_sub_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_sub_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	add r2, r12, r2
	add r3, r12, r3
	mov r6, #1
	mov r5, #1
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3976]
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3980]
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3984]
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3988]
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3992]
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3996]
	ldr r0, [r2, #24]
	ldr r4, [r3, #24]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #4000]
	ldr r0, [r2, #28]
	ldr r4, [r3, #28]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #4004]
	eor r6, r5, #1
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3976]
	mvn r0, #976
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3980]
	mvn r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3984]
	mvn r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3988]
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3992]
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3996]
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #4000]
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #4004]
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	bx lr
