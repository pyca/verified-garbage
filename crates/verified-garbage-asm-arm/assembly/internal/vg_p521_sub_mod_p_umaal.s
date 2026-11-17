// The functions of `src/internal/vg_p521_sub_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_sub_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #3960]
	str r5, [r12, #3964]
	str r6, [r12, #3968]
	add r2, r12, r2
	add r3, r12, r3
	mov r6, #1
	mov r5, #1
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3816]
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3820]
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3824]
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3828]
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3832]
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3836]
	ldr r0, [r2, #24]
	ldr r4, [r3, #24]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3840]
	ldr r0, [r2, #28]
	ldr r4, [r3, #28]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3844]
	ldr r0, [r2, #32]
	ldr r4, [r3, #32]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3848]
	ldr r0, [r2, #36]
	ldr r4, [r3, #36]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3852]
	ldr r0, [r2, #40]
	ldr r4, [r3, #40]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3856]
	ldr r0, [r2, #44]
	ldr r4, [r3, #44]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3860]
	ldr r0, [r2, #48]
	ldr r4, [r3, #48]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3864]
	ldr r0, [r2, #52]
	ldr r4, [r3, #52]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3868]
	ldr r0, [r2, #56]
	ldr r4, [r3, #56]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3872]
	ldr r0, [r2, #60]
	ldr r4, [r3, #60]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3876]
	ldr r0, [r2, #64]
	ldr r4, [r3, #64]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3880]
	ldr r0, [r2, #68]
	ldr r4, [r3, #68]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3884]
	eor r6, r5, #1
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3816]
	mvn r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3820]
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3824]
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3828]
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3832]
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3836]
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3840]
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3844]
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #3848]
	umaal r4, r5, r0, r6
	str r4, [r1, #32]
	ldr r4, [r12, #3852]
	umaal r4, r5, r0, r6
	str r4, [r1, #36]
	ldr r4, [r12, #3856]
	umaal r4, r5, r0, r6
	str r4, [r1, #40]
	ldr r4, [r12, #3860]
	umaal r4, r5, r0, r6
	str r4, [r1, #44]
	ldr r4, [r12, #3864]
	umaal r4, r5, r0, r6
	str r4, [r1, #48]
	ldr r4, [r12, #3868]
	umaal r4, r5, r0, r6
	str r4, [r1, #52]
	ldr r4, [r12, #3872]
	umaal r4, r5, r0, r6
	str r4, [r1, #56]
	ldr r4, [r12, #3876]
	umaal r4, r5, r0, r6
	str r4, [r1, #60]
	ldr r4, [r12, #3880]
	movw r0, #511
	umaal r4, r5, r0, r6
	str r4, [r1, #64]
	ldr r4, [r12, #3884]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #68]
	ldr r4, [r12, #3960]
	ldr r5, [r12, #3964]
	ldr r6, [r12, #3968]
	bx lr
