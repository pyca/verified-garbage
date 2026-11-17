// The functions of `src/internal/vg_brainpoolp384r1_sub_mod_n_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp384r1_sub_mod_n_umaal:
	mov r12, r0
	str r4, [r12, #4008]
	str r5, [r12, #4012]
	str r6, [r12, #4016]
	add r2, r12, r2
	add r3, r12, r3
	mov r6, #1
	mov r5, #1
	ldr r0, [r2, #0]
	ldr r4, [r3, #0]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3912]
	ldr r0, [r2, #4]
	ldr r4, [r3, #4]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3916]
	ldr r0, [r2, #8]
	ldr r4, [r3, #8]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3920]
	ldr r0, [r2, #12]
	ldr r4, [r3, #12]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3924]
	ldr r0, [r2, #16]
	ldr r4, [r3, #16]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3928]
	ldr r0, [r2, #20]
	ldr r4, [r3, #20]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3932]
	ldr r0, [r2, #24]
	ldr r4, [r3, #24]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3936]
	ldr r0, [r2, #28]
	ldr r4, [r3, #28]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3940]
	ldr r0, [r2, #32]
	ldr r4, [r3, #32]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3944]
	ldr r0, [r2, #36]
	ldr r4, [r3, #36]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3948]
	ldr r0, [r2, #40]
	ldr r4, [r3, #40]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3952]
	ldr r0, [r2, #44]
	ldr r4, [r3, #44]
	mvn r4, r4
	umaal r4, r5, r0, r6
	str r4, [r12, #3956]
	eor r6, r5, #1
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3912]
	movw r0, #25957
	movt r0, #59652
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3916]
	movw r0, #12802
	movt r0, #15240
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3920]
	movw r0, #49936
	movt r0, #27519
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3924]
	movw r0, #46767
	movt r0, #53050
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3928]
	movw r0, #9639
	movt r0, #44036
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3932]
	movw r0, #28268
	movt r0, #7958
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3936]
	movw r0, #22195
	movt r0, #60756
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3940]
	movw r0, #28937
	movt r0, #5423
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #3944]
	movw r0, #16863
	movt r0, #20710
	umaal r4, r5, r0, r6
	str r4, [r1, #32]
	ldr r4, [r12, #3948]
	movw r0, #28542
	movt r0, #3933
	umaal r4, r5, r0, r6
	str r4, [r1, #36]
	ldr r4, [r12, #3952]
	movw r0, #27944
	movt r0, #41784
	umaal r4, r5, r0, r6
	str r4, [r1, #40]
	ldr r4, [r12, #3956]
	movw r0, #7810
	movt r0, #36025
	umaal r4, r5, r0, r6
	str r4, [r1, #44]
	ldr r4, [r12, #4008]
	ldr r5, [r12, #4012]
	ldr r6, [r12, #4016]
	bx lr
