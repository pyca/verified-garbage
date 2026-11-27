// The functions of `src/internal/vg_brainpoolp512r1_sub_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_sub_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #3976]
	str r5, [r12, #3980]
	str r6, [r12, #3984]
	add r2, r12, r2
	add r3, r12, r3
	mov r6, #1
	mov r5, #1
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3848]
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3852]
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3856]
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3860]
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3864]
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3868]
	ldr r0, [r2, #24]
	ldr r4, [r3, #24]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3872]
	ldr r0, [r2, #28]
	ldr r4, [r3, #28]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3876]
	ldr r0, [r2, #32]
	ldr r4, [r3, #32]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3880]
	ldr r0, [r2, #36]
	ldr r4, [r3, #36]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3884]
	ldr r0, [r2, #40]
	ldr r4, [r3, #40]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3888]
	ldr r0, [r2, #44]
	ldr r4, [r3, #44]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3892]
	ldr r0, [r2, #48]
	ldr r4, [r3, #48]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3896]
	ldr r0, [r2, #52]
	ldr r4, [r3, #52]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3900]
	ldr r0, [r2, #56]
	ldr r4, [r3, #56]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3904]
	ldr r0, [r2, #60]
	ldr r4, [r3, #60]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3908]
	eor r6, r5, #1
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3848]
	movw r0, #18675
	movt r0, #22586
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3852]
	movw r0, #24662
	movt r0, #10410
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3856]
	movw r0, #50821
	movt r0, #11650
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3860]
	movw r0, #65327
	movt r0, #10369
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3864]
	movw r0, #32998
	movt r0, #59043
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3868]
	movw r0, #41258
	movt r0, #44749
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3872]
	movw r0, #26690
	movt r0, #39878
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3876]
	movw r0, #39680
	movt r0, #32077
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #3880]
	movw r0, #2161
	movt r0, #28723
	umaal r4, r5, r0, r6
	str r4, [r1, #32]
	ldr r4, [r12, #3884]
	movw r0, #40138
	movt r0, #54883
	umaal r4, r5, r0, r6
	str r4, [r1, #36]
	ldr r4, [r12, #3888]
	movw r0, #53774
	movt r0, #46025
	umaal r4, r5, r0, r6
	str r4, [r1, #40]
	ldr r4, [r12, #3892]
	movw r0, #36275
	movt r0, #52016
	umaal r4, r5, r0, r6
	str r4, [r1, #44]
	ldr r4, [r12, #3896]
	movw r0, #64519
	movt r0, #13257
	umaal r4, r5, r0, r6
	str r4, [r1, #48]
	ldr r4, [r12, #3900]
	movw r0, #59054
	movt r0, #16340
	umaal r4, r5, r0, r6
	str r4, [r1, #52]
	ldr r4, [r12, #3904]
	movw r0, #50315
	movt r0, #56297
	umaal r4, r5, r0, r6
	str r4, [r1, #56]
	ldr r4, [r12, #3908]
	movw r0, #40376
	movt r0, #43741
	umaal r4, r5, r0, r6
	str r4, [r1, #60]
	ldr r4, [r12, #3976]
	ldr r5, [r12, #3980]
	ldr r6, [r12, #3984]
	bx lr
