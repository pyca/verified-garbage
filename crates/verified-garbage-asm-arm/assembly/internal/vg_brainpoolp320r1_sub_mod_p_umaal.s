// The functions of `src/internal/vg_brainpoolp320r1_sub_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_sub_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #4024]
	str r5, [r12, #4028]
	str r6, [r12, #4032]
	add r2, r12, r2
	add r3, r12, r3
	mov r6, #1
	mov r5, #1
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3944]
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3948]
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3952]
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3956]
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3960]
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3964]
	ldr r0, [r2, #24]
	ldr r4, [r3, #24]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3968]
	ldr r0, [r2, #28]
	ldr r4, [r3, #28]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3972]
	ldr r0, [r2, #32]
	ldr r4, [r3, #32]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3976]
	ldr r0, [r2, #36]
	ldr r4, [r3, #36]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3980]
	eor r6, r5, #1
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3944]
	movw r0, #11815
	movt r0, #61875
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3948]
	movw r0, #4785
	movt r0, #64724
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3952]
	movw r0, #60456
	movt r0, #30867
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3956]
	movw r0, #47596
	movt r0, #20370
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3960]
	movw r0, #3567
	movt r0, #63220
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3964]
	movw r0, #53158
	movt r0, #63887
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3968]
	movw r0, #57445
	movt r0, #53761
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3972]
	movw r0, #30814
	movt r0, #57660
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #3976]
	movw r0, #20407
	movt r0, #14012
	umaal r4, r5, r0, r6
	str r4, [r1, #32]
	ldr r4, [r12, #3980]
	movw r0, #18208
	movt r0, #54110
	umaal r4, r5, r0, r6
	str r4, [r1, #36]
	ldr r4, [r12, #4024]
	ldr r5, [r12, #4028]
	ldr r6, [r12, #4032]
	bx lr
