// The functions of `src/internal/vg_brainpoolp512r1_add_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_add_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #3976]
	str r5, [r12, #3980]
	str r6, [r12, #3984]
	str r7, [r12, #3988]
	str r8, [r12, #3992]
	add r2, r12, r2
	add r3, r12, r3
	mov r8, #1
	mov r5, #0
	mov r6, #0
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	umaal r4, r5, r0, r8
	str r4, [r12, #3848]
	movw r7, #46861
	movt r7, #42949
	umaal r4, r6, r7, r8
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	umaal r4, r5, r0, r8
	str r4, [r12, #3852]
	movw r7, #40873
	movt r7, #55125
	umaal r4, r6, r7, r8
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	umaal r4, r5, r0, r8
	str r4, [r12, #3856]
	movw r7, #14714
	movt r7, #53885
	umaal r4, r6, r7, r8
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	umaal r4, r5, r0, r8
	str r4, [r12, #3860]
	movw r7, #208
	movt r7, #55166
	umaal r4, r6, r7, r8
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	umaal r4, r5, r0, r8
	str r4, [r12, #3864]
	movw r7, #32537
	movt r7, #6492
	umaal r4, r6, r7, r8
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	umaal r4, r5, r0, r8
	str r4, [r12, #3868]
	movw r7, #24277
	movt r7, #20786
	umaal r4, r6, r7, r8
	ldr r0, [r2, #24]
	ldr r4, [r3, #24]
	umaal r4, r5, r0, r8
	str r4, [r12, #3872]
	movw r7, #38845
	movt r7, #25657
	umaal r4, r6, r7, r8
	ldr r0, [r2, #28]
	ldr r4, [r3, #28]
	umaal r4, r5, r0, r8
	str r4, [r12, #3876]
	movw r7, #25855
	movt r7, #33458
	umaal r4, r6, r7, r8
	ldr r0, [r2, #32]
	ldr r4, [r3, #32]
	umaal r4, r5, r0, r8
	str r4, [r12, #3880]
	movw r7, #63374
	movt r7, #36812
	umaal r4, r6, r7, r8
	ldr r0, [r2, #36]
	ldr r4, [r3, #36]
	umaal r4, r5, r0, r8
	str r4, [r12, #3884]
	movw r7, #25397
	movt r7, #10652
	umaal r4, r6, r7, r8
	ldr r0, [r2, #40]
	ldr r4, [r3, #40]
	umaal r4, r5, r0, r8
	str r4, [r12, #3888]
	movw r7, #11761
	movt r7, #19510
	umaal r4, r6, r7, r8
	ldr r0, [r2, #44]
	ldr r4, [r3, #44]
	umaal r4, r5, r0, r8
	str r4, [r12, #3892]
	movw r7, #29260
	movt r7, #13519
	umaal r4, r6, r7, r8
	ldr r0, [r2, #48]
	ldr r4, [r3, #48]
	umaal r4, r5, r0, r8
	str r4, [r12, #3896]
	movw r7, #1016
	movt r7, #52278
	umaal r4, r6, r7, r8
	ldr r0, [r2, #52]
	ldr r4, [r3, #52]
	umaal r4, r5, r0, r8
	str r4, [r12, #3900]
	movw r7, #6481
	movt r7, #49195
	umaal r4, r6, r7, r8
	ldr r0, [r2, #56]
	ldr r4, [r3, #56]
	umaal r4, r5, r0, r8
	str r4, [r12, #3904]
	movw r7, #15220
	movt r7, #9238
	umaal r4, r6, r7, r8
	ldr r0, [r2, #60]
	ldr r4, [r3, #60]
	umaal r4, r5, r0, r8
	str r4, [r12, #3908]
	movw r7, #25159
	movt r7, #21794
	umaal r4, r6, r7, r8
	add r6, r5, r6
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3848]
	movw r0, #46861
	movt r0, #42949
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3852]
	movw r0, #40873
	movt r0, #55125
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3856]
	movw r0, #14714
	movt r0, #53885
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3860]
	movw r0, #208
	movt r0, #55166
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3864]
	movw r0, #32537
	movt r0, #6492
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3868]
	movw r0, #24277
	movt r0, #20786
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3872]
	movw r0, #38845
	movt r0, #25657
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3876]
	movw r0, #25855
	movt r0, #33458
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #3880]
	movw r0, #63374
	movt r0, #36812
	umaal r4, r5, r0, r6
	str r4, [r1, #32]
	ldr r4, [r12, #3884]
	movw r0, #25397
	movt r0, #10652
	umaal r4, r5, r0, r6
	str r4, [r1, #36]
	ldr r4, [r12, #3888]
	movw r0, #11761
	movt r0, #19510
	umaal r4, r5, r0, r6
	str r4, [r1, #40]
	ldr r4, [r12, #3892]
	movw r0, #29260
	movt r0, #13519
	umaal r4, r5, r0, r6
	str r4, [r1, #44]
	ldr r4, [r12, #3896]
	movw r0, #1016
	movt r0, #52278
	umaal r4, r5, r0, r6
	str r4, [r1, #48]
	ldr r4, [r12, #3900]
	movw r0, #6481
	movt r0, #49195
	umaal r4, r5, r0, r6
	str r4, [r1, #52]
	ldr r4, [r12, #3904]
	movw r0, #15220
	movt r0, #9238
	umaal r4, r5, r0, r6
	str r4, [r1, #56]
	ldr r4, [r12, #3908]
	movw r0, #25159
	movt r0, #21794
	umaal r4, r5, r0, r6
	str r4, [r1, #60]
	ldr r4, [r12, #3976]
	ldr r5, [r12, #3980]
	ldr r6, [r12, #3984]
	ldr r7, [r12, #3988]
	ldr r8, [r12, #3992]
	bx lr
