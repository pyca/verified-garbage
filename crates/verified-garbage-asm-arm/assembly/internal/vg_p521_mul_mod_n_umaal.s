// The functions of `src/internal/vg_p521_mul_mod_n_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul_mod_n_umaal:
	mov r12, r0
	str r4, [r12, #3960]
	str r5, [r12, #3964]
	str r6, [r12, #3968]
	str r7, [r12, #3972]
	str r8, [r12, #3976]
	str r9, [r12, #3980]
	str lr, [r12, #3984]
	add lr, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3520]
	str r7, [r12, #3524]
	str r7, [r12, #3528]
	str r7, [r12, #3532]
	str r7, [r12, #3536]
	str r7, [r12, #3540]
	str r7, [r12, #3544]
	str r7, [r12, #3548]
	str r7, [r12, #3552]
	str r7, [r12, #3556]
	str r7, [r12, #3560]
	str r7, [r12, #3564]
	str r7, [r12, #3568]
	str r7, [r12, #3572]
	str r7, [r12, #3576]
	str r7, [r12, #3580]
	str r7, [r12, #3584]
	str r7, [r12, #3588]
	str r7, [r12, #3592]
	mov r9, #18
20:
	ldr r2, [lr, #0]
	ldr r7, [r4, #0]
	ldr r5, [r12, #3520]
	mov r3, #0
	umaal r5, r3, r2, r7
	movw r0, #38343
	movt r0, #31145
	mul r0, r0, r5
	mov r6, #0
	movw r8, #25609
	movt r8, #37176
	umaal r5, r6, r0, r8
	ldr r7, [r4, #4]
	ldr r5, [r12, #3524]
	umaal r5, r3, r2, r7
	movw r8, #46878
	movt r8, #47983
	umaal r5, r6, r0, r8
	str r5, [r12, #3520]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3528]
	umaal r5, r3, r2, r7
	movw r8, #18350
	movt r8, #35228
	umaal r5, r6, r0, r8
	str r5, [r12, #3524]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3532]
	umaal r5, r3, r2, r7
	movw r8, #51640
	movt r8, #15285
	umaal r5, r6, r0, r8
	str r5, [r12, #3528]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3536]
	umaal r5, r3, r2, r7
	movw r8, #42448
	movt r8, #63241
	umaal r5, r6, r0, r8
	str r5, [r12, #3532]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3540]
	umaal r5, r3, r2, r7
	movw r8, #328
	movt r8, #32716
	umaal r5, r6, r0, r8
	str r5, [r12, #3536]
	ldr r7, [r4, #24]
	ldr r5, [r12, #3544]
	umaal r5, r3, r2, r7
	movw r8, #38507
	movt r8, #48943
	umaal r5, r6, r0, r8
	str r5, [r12, #3540]
	ldr r7, [r4, #28]
	ldr r5, [r12, #3548]
	umaal r5, r3, r2, r7
	movw r8, #34691
	movt r8, #20870
	umaal r5, r6, r0, r8
	str r5, [r12, #3544]
	ldr r7, [r4, #32]
	ldr r5, [r12, #3552]
	umaal r5, r3, r2, r7
	mvn r8, #5
	umaal r5, r6, r0, r8
	str r5, [r12, #3548]
	ldr r7, [r4, #36]
	ldr r5, [r12, #3556]
	umaal r5, r3, r2, r7
	mvn r8, #0
	umaal r5, r6, r0, r8
	str r5, [r12, #3552]
	ldr r7, [r4, #40]
	ldr r5, [r12, #3560]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3556]
	ldr r7, [r4, #44]
	ldr r5, [r12, #3564]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3560]
	ldr r7, [r4, #48]
	ldr r5, [r12, #3568]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3564]
	ldr r7, [r4, #52]
	ldr r5, [r12, #3572]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3568]
	ldr r7, [r4, #56]
	ldr r5, [r12, #3576]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3572]
	ldr r7, [r4, #60]
	ldr r5, [r12, #3580]
	umaal r5, r3, r2, r7
	umaal r5, r6, r0, r8
	str r5, [r12, #3576]
	ldr r7, [r4, #64]
	ldr r5, [r12, #3584]
	umaal r5, r3, r2, r7
	movw r8, #511
	umaal r5, r6, r0, r8
	str r5, [r12, #3580]
	ldr r7, [r4, #68]
	ldr r5, [r12, #3588]
	umaal r5, r3, r2, r7
	movw r8, #0
	umaal r5, r6, r0, r8
	str r5, [r12, #3584]
	ldr r5, [r12, #3592]
	mov r7, #1
	umaal r3, r5, r6, r7
	str r3, [r12, #3588]
	str r5, [r12, #3592]
	add lr, lr, #4
	subs r9, r9, #1
	bne 20b
	mov r6, #1
	mov r5, #0
	ldr r4, [r12, #3520]
	movw r0, #39927
	movt r0, #28359
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3524]
	movw r0, #18657
	movt r0, #17552
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3528]
	movw r0, #47185
	movt r0, #30307
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3532]
	movw r0, #13895
	movt r0, #50250
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3536]
	movw r0, #23087
	movt r0, #2294
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3540]
	movw r0, #65207
	movt r0, #32819
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3544]
	movw r0, #27028
	movt r0, #16592
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3548]
	movw r0, #30844
	movt r0, #44665
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3552]
	movw r0, #5
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3556]
	movw r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3560]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3564]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3568]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3572]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3576]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3580]
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3584]
	movw r0, #65024
	movt r0, #65535
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3588]
	mvn r0, #0
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3592]
	add r6, r5, r4
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3520]
	movw r0, #39927
	movt r0, #28359
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3524]
	movw r0, #18657
	movt r0, #17552
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3528]
	movw r0, #47185
	movt r0, #30307
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3532]
	movw r0, #13895
	movt r0, #50250
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3536]
	movw r0, #23087
	movt r0, #2294
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3540]
	movw r0, #65207
	movt r0, #32819
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3544]
	movw r0, #27028
	movt r0, #16592
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3548]
	movw r0, #30844
	movt r0, #44665
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #3552]
	movw r0, #5
	umaal r4, r5, r0, r6
	str r4, [r1, #32]
	ldr r4, [r12, #3556]
	movw r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #36]
	ldr r4, [r12, #3560]
	umaal r4, r5, r0, r6
	str r4, [r1, #40]
	ldr r4, [r12, #3564]
	umaal r4, r5, r0, r6
	str r4, [r1, #44]
	ldr r4, [r12, #3568]
	umaal r4, r5, r0, r6
	str r4, [r1, #48]
	ldr r4, [r12, #3572]
	umaal r4, r5, r0, r6
	str r4, [r1, #52]
	ldr r4, [r12, #3576]
	umaal r4, r5, r0, r6
	str r4, [r1, #56]
	ldr r4, [r12, #3580]
	umaal r4, r5, r0, r6
	str r4, [r1, #60]
	ldr r4, [r12, #3584]
	movw r0, #65024
	movt r0, #65535
	umaal r4, r5, r0, r6
	str r4, [r1, #64]
	ldr r4, [r12, #3588]
	mvn r0, #0
	umaal r4, r5, r0, r6
	str r4, [r1, #68]
	ldr r4, [r12, #3960]
	ldr r5, [r12, #3964]
	ldr r6, [r12, #3968]
	ldr r7, [r12, #3972]
	ldr r8, [r12, #3976]
	ldr r9, [r12, #3980]
	ldr lr, [r12, #3984]
	bx lr
