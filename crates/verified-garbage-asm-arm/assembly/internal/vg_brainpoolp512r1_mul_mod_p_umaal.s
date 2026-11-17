// The functions of `src/internal/vg_brainpoolp512r1_mul_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_mul_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #3976]
	str r5, [r12, #3980]
	str r6, [r12, #3984]
	str r7, [r12, #3988]
	str r8, [r12, #3992]
	str r9, [r12, #3996]
	str lr, [r12, #4000]
	movw r4, #18675
	movt r4, #22586
	str r4, [r12, #3912]
	movw r4, #24662
	movt r4, #10410
	str r4, [r12, #3916]
	movw r4, #50821
	movt r4, #11650
	str r4, [r12, #3920]
	movw r4, #65327
	movt r4, #10369
	str r4, [r12, #3924]
	movw r4, #32998
	movt r4, #59043
	str r4, [r12, #3928]
	movw r4, #41258
	movt r4, #44749
	str r4, [r12, #3932]
	movw r4, #26690
	movt r4, #39878
	str r4, [r12, #3936]
	movw r4, #39680
	movt r4, #32077
	str r4, [r12, #3940]
	movw r4, #2161
	movt r4, #28723
	str r4, [r12, #3944]
	movw r4, #40138
	movt r4, #54883
	str r4, [r12, #3948]
	movw r4, #53774
	movt r4, #46025
	str r4, [r12, #3952]
	movw r4, #36275
	movt r4, #52016
	str r4, [r12, #3956]
	movw r4, #64519
	movt r4, #13257
	str r4, [r12, #3960]
	movw r4, #59054
	movt r4, #16340
	str r4, [r12, #3964]
	movw r4, #50315
	movt r4, #56297
	str r4, [r12, #3968]
	movw r4, #40376
	movt r4, #43741
	str r4, [r12, #3972]
	add lr, r12, r1
	add r1, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3584]
	str r7, [r12, #3588]
	str r7, [r12, #3592]
	str r7, [r12, #3596]
	str r7, [r12, #3600]
	str r7, [r12, #3604]
	str r7, [r12, #3608]
	str r7, [r12, #3612]
	str r7, [r12, #3616]
	str r7, [r12, #3620]
	str r7, [r12, #3624]
	str r7, [r12, #3628]
	str r7, [r12, #3632]
	str r7, [r12, #3636]
	str r7, [r12, #3640]
	str r7, [r12, #3644]
	str r7, [r12, #3648]
	str r7, [r12, #3652]
	mov r9, #16
20:
	ldr r2, [r1, #0]
	mov r3, #0
	ldr r7, [r4, #0]
	ldr r5, [r12, #3584]
	umaal r5, r3, r2, r7
	str r5, [r12, #3584]
	ldr r7, [r4, #4]
	ldr r5, [r12, #3588]
	umaal r5, r3, r2, r7
	str r5, [r12, #3588]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3592]
	umaal r5, r3, r2, r7
	str r5, [r12, #3592]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3596]
	umaal r5, r3, r2, r7
	str r5, [r12, #3596]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3600]
	umaal r5, r3, r2, r7
	str r5, [r12, #3600]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3604]
	umaal r5, r3, r2, r7
	str r5, [r12, #3604]
	ldr r7, [r4, #24]
	ldr r5, [r12, #3608]
	umaal r5, r3, r2, r7
	str r5, [r12, #3608]
	ldr r7, [r4, #28]
	ldr r5, [r12, #3612]
	umaal r5, r3, r2, r7
	str r5, [r12, #3612]
	ldr r7, [r4, #32]
	ldr r5, [r12, #3616]
	umaal r5, r3, r2, r7
	str r5, [r12, #3616]
	ldr r7, [r4, #36]
	ldr r5, [r12, #3620]
	umaal r5, r3, r2, r7
	str r5, [r12, #3620]
	ldr r7, [r4, #40]
	ldr r5, [r12, #3624]
	umaal r5, r3, r2, r7
	str r5, [r12, #3624]
	ldr r7, [r4, #44]
	ldr r5, [r12, #3628]
	umaal r5, r3, r2, r7
	str r5, [r12, #3628]
	ldr r7, [r4, #48]
	ldr r5, [r12, #3632]
	umaal r5, r3, r2, r7
	str r5, [r12, #3632]
	ldr r7, [r4, #52]
	ldr r5, [r12, #3636]
	umaal r5, r3, r2, r7
	str r5, [r12, #3636]
	ldr r7, [r4, #56]
	ldr r5, [r12, #3640]
	umaal r5, r3, r2, r7
	str r5, [r12, #3640]
	ldr r7, [r4, #60]
	ldr r5, [r12, #3644]
	umaal r5, r3, r2, r7
	str r5, [r12, #3644]
	ldr r5, [r12, #3648]
	ldr r6, [r12, #3652]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3648]
	str r6, [r12, #3652]
	ldr r2, [r12, #3584]
	movw r7, #61381
	movt r7, #32137
	mul r2, r2, r7
	mov r3, #0
	ldr r7, [r12, #3912]
	ldr r5, [r12, #3584]
	umaal r5, r3, r2, r7
	str r5, [r12, #3584]
	ldr r7, [r12, #3916]
	ldr r5, [r12, #3588]
	umaal r5, r3, r2, r7
	str r5, [r12, #3588]
	ldr r7, [r12, #3920]
	ldr r5, [r12, #3592]
	umaal r5, r3, r2, r7
	str r5, [r12, #3592]
	ldr r7, [r12, #3924]
	ldr r5, [r12, #3596]
	umaal r5, r3, r2, r7
	str r5, [r12, #3596]
	ldr r7, [r12, #3928]
	ldr r5, [r12, #3600]
	umaal r5, r3, r2, r7
	str r5, [r12, #3600]
	ldr r7, [r12, #3932]
	ldr r5, [r12, #3604]
	umaal r5, r3, r2, r7
	str r5, [r12, #3604]
	ldr r7, [r12, #3936]
	ldr r5, [r12, #3608]
	umaal r5, r3, r2, r7
	str r5, [r12, #3608]
	ldr r7, [r12, #3940]
	ldr r5, [r12, #3612]
	umaal r5, r3, r2, r7
	str r5, [r12, #3612]
	ldr r7, [r12, #3944]
	ldr r5, [r12, #3616]
	umaal r5, r3, r2, r7
	str r5, [r12, #3616]
	ldr r7, [r12, #3948]
	ldr r5, [r12, #3620]
	umaal r5, r3, r2, r7
	str r5, [r12, #3620]
	ldr r7, [r12, #3952]
	ldr r5, [r12, #3624]
	umaal r5, r3, r2, r7
	str r5, [r12, #3624]
	ldr r7, [r12, #3956]
	ldr r5, [r12, #3628]
	umaal r5, r3, r2, r7
	str r5, [r12, #3628]
	ldr r7, [r12, #3960]
	ldr r5, [r12, #3632]
	umaal r5, r3, r2, r7
	str r5, [r12, #3632]
	ldr r7, [r12, #3964]
	ldr r5, [r12, #3636]
	umaal r5, r3, r2, r7
	str r5, [r12, #3636]
	ldr r7, [r12, #3968]
	ldr r5, [r12, #3640]
	umaal r5, r3, r2, r7
	str r5, [r12, #3640]
	ldr r7, [r12, #3972]
	ldr r5, [r12, #3644]
	umaal r5, r3, r2, r7
	str r5, [r12, #3644]
	ldr r5, [r12, #3648]
	ldr r6, [r12, #3652]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3648]
	str r6, [r12, #3652]
	ldr r5, [r12, #3588]
	str r5, [r12, #3584]
	ldr r5, [r12, #3592]
	str r5, [r12, #3588]
	ldr r5, [r12, #3596]
	str r5, [r12, #3592]
	ldr r5, [r12, #3600]
	str r5, [r12, #3596]
	ldr r5, [r12, #3604]
	str r5, [r12, #3600]
	ldr r5, [r12, #3608]
	str r5, [r12, #3604]
	ldr r5, [r12, #3612]
	str r5, [r12, #3608]
	ldr r5, [r12, #3616]
	str r5, [r12, #3612]
	ldr r5, [r12, #3620]
	str r5, [r12, #3616]
	ldr r5, [r12, #3624]
	str r5, [r12, #3620]
	ldr r5, [r12, #3628]
	str r5, [r12, #3624]
	ldr r5, [r12, #3632]
	str r5, [r12, #3628]
	ldr r5, [r12, #3636]
	str r5, [r12, #3632]
	ldr r5, [r12, #3640]
	str r5, [r12, #3636]
	ldr r5, [r12, #3644]
	str r5, [r12, #3640]
	ldr r5, [r12, #3648]
	str r5, [r12, #3644]
	ldr r5, [r12, #3652]
	str r5, [r12, #3648]
	mov r5, #0
	str r5, [r12, #3652]
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	sub r1, lr, r12
	mov r6, #1
	mov r5, #0
	ldr r4, [r12, #3584]
	movw r0, #46861
	movt r0, #42949
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3588]
	movw r0, #40873
	movt r0, #55125
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3592]
	movw r0, #14714
	movt r0, #53885
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3596]
	movw r0, #208
	movt r0, #55166
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3600]
	movw r0, #32537
	movt r0, #6492
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3604]
	movw r0, #24277
	movt r0, #20786
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3608]
	movw r0, #38845
	movt r0, #25657
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3612]
	movw r0, #25855
	movt r0, #33458
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3616]
	movw r0, #63374
	movt r0, #36812
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3620]
	movw r0, #25397
	movt r0, #10652
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3624]
	movw r0, #11761
	movt r0, #19510
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3628]
	movw r0, #29260
	movt r0, #13519
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3632]
	movw r0, #1016
	movt r0, #52278
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3636]
	movw r0, #6481
	movt r0, #49195
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3640]
	movw r0, #15220
	movt r0, #9238
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3644]
	movw r0, #25159
	movt r0, #21794
	umaal r4, r5, r0, r6
	ldr r4, [r12, #3648]
	add r6, r5, r4
	mov r5, #0
	add r1, r12, r1
	ldr r4, [r12, #3584]
	movw r0, #46861
	movt r0, #42949
	umaal r4, r5, r0, r6
	str r4, [r1, #0]
	ldr r4, [r12, #3588]
	movw r0, #40873
	movt r0, #55125
	umaal r4, r5, r0, r6
	str r4, [r1, #4]
	ldr r4, [r12, #3592]
	movw r0, #14714
	movt r0, #53885
	umaal r4, r5, r0, r6
	str r4, [r1, #8]
	ldr r4, [r12, #3596]
	movw r0, #208
	movt r0, #55166
	umaal r4, r5, r0, r6
	str r4, [r1, #12]
	ldr r4, [r12, #3600]
	movw r0, #32537
	movt r0, #6492
	umaal r4, r5, r0, r6
	str r4, [r1, #16]
	ldr r4, [r12, #3604]
	movw r0, #24277
	movt r0, #20786
	umaal r4, r5, r0, r6
	str r4, [r1, #20]
	ldr r4, [r12, #3608]
	movw r0, #38845
	movt r0, #25657
	umaal r4, r5, r0, r6
	str r4, [r1, #24]
	ldr r4, [r12, #3612]
	movw r0, #25855
	movt r0, #33458
	umaal r4, r5, r0, r6
	str r4, [r1, #28]
	ldr r4, [r12, #3616]
	movw r0, #63374
	movt r0, #36812
	umaal r4, r5, r0, r6
	str r4, [r1, #32]
	ldr r4, [r12, #3620]
	movw r0, #25397
	movt r0, #10652
	umaal r4, r5, r0, r6
	str r4, [r1, #36]
	ldr r4, [r12, #3624]
	movw r0, #11761
	movt r0, #19510
	umaal r4, r5, r0, r6
	str r4, [r1, #40]
	ldr r4, [r12, #3628]
	movw r0, #29260
	movt r0, #13519
	umaal r4, r5, r0, r6
	str r4, [r1, #44]
	ldr r4, [r12, #3632]
	movw r0, #1016
	movt r0, #52278
	umaal r4, r5, r0, r6
	str r4, [r1, #48]
	ldr r4, [r12, #3636]
	movw r0, #6481
	movt r0, #49195
	umaal r4, r5, r0, r6
	str r4, [r1, #52]
	ldr r4, [r12, #3640]
	movw r0, #15220
	movt r0, #9238
	umaal r4, r5, r0, r6
	str r4, [r1, #56]
	ldr r4, [r12, #3644]
	movw r0, #25159
	movt r0, #21794
	umaal r4, r5, r0, r6
	str r4, [r1, #60]
	ldr r4, [r12, #3976]
	ldr r5, [r12, #3980]
	ldr r6, [r12, #3984]
	ldr r7, [r12, #3988]
	ldr r8, [r12, #3992]
	ldr r9, [r12, #3996]
	ldr lr, [r12, #4000]
	bx lr
