// The functions of `src/internal/vg_secp256k1_mul_mod_n_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_secp256k1_mul_mod_n_umaal:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #16705
	movt r4, #53302
	str r4, [r12, #4008]
	movw r4, #24204
	movt r4, #49106
	str r4, [r12, #4012]
	movw r4, #41019
	movt r4, #44872
	str r4, [r12, #4016]
	movw r4, #56550
	movt r4, #47790
	str r4, [r12, #4020]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
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
	str r7, [r12, #3876]
	mov r9, #8
20:
	ldr r2, [r1, #0]
	mov r3, #0
	ldr r7, [r4, #0]
	ldr r5, [r12, #3840]
	umaal r5, r3, r2, r7
	str r5, [r12, #3840]
	ldr r7, [r4, #4]
	ldr r5, [r12, #3844]
	umaal r5, r3, r2, r7
	str r5, [r12, #3844]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3848]
	umaal r5, r3, r2, r7
	str r5, [r12, #3848]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3852]
	umaal r5, r3, r2, r7
	str r5, [r12, #3852]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3856]
	umaal r5, r3, r2, r7
	str r5, [r12, #3856]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3860]
	umaal r5, r3, r2, r7
	str r5, [r12, #3860]
	ldr r7, [r4, #24]
	ldr r5, [r12, #3864]
	umaal r5, r3, r2, r7
	str r5, [r12, #3864]
	ldr r7, [r4, #28]
	ldr r5, [r12, #3868]
	umaal r5, r3, r2, r7
	str r5, [r12, #3868]
	ldr r5, [r12, #3872]
	ldr r6, [r12, #3876]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3872]
	str r6, [r12, #3876]
	ldr r2, [r12, #3840]
	movw r7, #45375
	movt r7, #21896
	mul r2, r2, r7
	mov r3, #0
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3840]
	umaal r5, r3, r2, r7
	str r5, [r12, #3840]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3844]
	umaal r5, r3, r2, r7
	str r5, [r12, #3844]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3848]
	umaal r5, r3, r2, r7
	str r5, [r12, #3848]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3852]
	umaal r5, r3, r2, r7
	str r5, [r12, #3852]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3856]
	umaal r5, r3, r2, r7
	str r5, [r12, #3856]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3860]
	umaal r5, r3, r2, r7
	str r5, [r12, #3860]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3864]
	umaal r5, r3, r2, r7
	str r5, [r12, #3864]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3868]
	umaal r5, r3, r2, r7
	str r5, [r12, #3868]
	ldr r5, [r12, #3872]
	ldr r6, [r12, #3876]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3872]
	str r6, [r12, #3876]
	ldr r5, [r12, #3844]
	str r5, [r12, #3840]
	ldr r5, [r12, #3848]
	str r5, [r12, #3844]
	ldr r5, [r12, #3852]
	str r5, [r12, #3848]
	ldr r5, [r12, #3856]
	str r5, [r12, #3852]
	ldr r5, [r12, #3860]
	str r5, [r12, #3856]
	ldr r5, [r12, #3864]
	str r5, [r12, #3860]
	ldr r5, [r12, #3868]
	str r5, [r12, #3864]
	ldr r5, [r12, #3872]
	str r5, [r12, #3868]
	ldr r5, [r12, #3876]
	str r5, [r12, #3872]
	mov r5, #0
	str r5, [r12, #3876]
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	sub r1, lr, r12
	mov r6, #1
	mov r5, #0
	ldr r4, [r12, #3840]
	movw r0, #48831
	movt r0, #12233
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3844]
	movw r0, #41331
	movt r0, #16429
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3848]
	movw r0, #24516
	movt r0, #20663
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3852]
	movw r0, #8985
	movt r0, #17745
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3856]
	movw r0, #1
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3860]
	movw r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3864]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3868]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3872]
	add r6, r5, r4
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3840]
	movw r0, #48831
	movt r0, #12233
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3844]
	movw r0, #41331
	movt r0, #16429
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3848]
	movw r0, #24516
	movt r0, #20663
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3852]
	movw r0, #8985
	movt r0, #17745
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3856]
	movw r0, #1
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3860]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3864]
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3868]
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
