// The functions of `src/internal/vg_brainpoolp512r1_mul_mod_n_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_mul_mod_n_umaal:
	mov r12, r0
	str r4, [r12, #3976]
	str r5, [r12, #3980]
	str r6, [r12, #3984]
	str r7, [r12, #3988]
	str r8, [r12, #3992]
	str r9, [r12, #3996]
	str lr, [r12, #4000]
	movw r4, #105
	movt r4, #40105
	str r4, [r12, #3912]
	movw r4, #38530
	movt r4, #46471
	str r4, [r12, #3916]
	movw r4, #56029
	movt r4, #2141
	str r4, [r12, #3920]
	movw r4, #54145
	movt r4, #7601
	str r4, [r12, #3924]
	movw r4, #4167
	movt r4, #32684
	str r4, [r12, #3928]
	movw r4, #24857
	movt r4, #16774
	str r4, [r12, #3932]
	movw r4, #9753
	movt r4, #19625
	str r4, [r12, #3936]
	movw r4, #23617
	movt r4, #21822
	str r4, [r12, #3940]
	movw r4, #2160
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
	movw r7, #28711
	movt r7, #3867
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
	movw r6, #65535
	ldr r7, [r12, #3584]
	and r7, r7, r6
	str r7, [r12, #3656]
	ldr r7, [r12, #3584]
	lsr r7, r7, #16
	str r7, [r12, #3660]
	ldr r7, [r12, #3588]
	and r7, r7, r6
	str r7, [r12, #3664]
	ldr r7, [r12, #3588]
	lsr r7, r7, #16
	str r7, [r12, #3668]
	ldr r7, [r12, #3592]
	and r7, r7, r6
	str r7, [r12, #3672]
	ldr r7, [r12, #3592]
	lsr r7, r7, #16
	str r7, [r12, #3676]
	ldr r7, [r12, #3596]
	and r7, r7, r6
	str r7, [r12, #3680]
	ldr r7, [r12, #3596]
	lsr r7, r7, #16
	str r7, [r12, #3684]
	ldr r7, [r12, #3600]
	and r7, r7, r6
	str r7, [r12, #3688]
	ldr r7, [r12, #3600]
	lsr r7, r7, #16
	str r7, [r12, #3692]
	ldr r7, [r12, #3604]
	and r7, r7, r6
	str r7, [r12, #3696]
	ldr r7, [r12, #3604]
	lsr r7, r7, #16
	str r7, [r12, #3700]
	ldr r7, [r12, #3608]
	and r7, r7, r6
	str r7, [r12, #3704]
	ldr r7, [r12, #3608]
	lsr r7, r7, #16
	str r7, [r12, #3708]
	ldr r7, [r12, #3612]
	and r7, r7, r6
	str r7, [r12, #3712]
	ldr r7, [r12, #3612]
	lsr r7, r7, #16
	str r7, [r12, #3716]
	ldr r7, [r12, #3616]
	and r7, r7, r6
	str r7, [r12, #3720]
	ldr r7, [r12, #3616]
	lsr r7, r7, #16
	str r7, [r12, #3724]
	ldr r7, [r12, #3620]
	and r7, r7, r6
	str r7, [r12, #3728]
	ldr r7, [r12, #3620]
	lsr r7, r7, #16
	str r7, [r12, #3732]
	ldr r7, [r12, #3624]
	and r7, r7, r6
	str r7, [r12, #3736]
	ldr r7, [r12, #3624]
	lsr r7, r7, #16
	str r7, [r12, #3740]
	ldr r7, [r12, #3628]
	and r7, r7, r6
	str r7, [r12, #3744]
	ldr r7, [r12, #3628]
	lsr r7, r7, #16
	str r7, [r12, #3748]
	ldr r7, [r12, #3632]
	and r7, r7, r6
	str r7, [r12, #3752]
	ldr r7, [r12, #3632]
	lsr r7, r7, #16
	str r7, [r12, #3756]
	ldr r7, [r12, #3636]
	and r7, r7, r6
	str r7, [r12, #3760]
	ldr r7, [r12, #3636]
	lsr r7, r7, #16
	str r7, [r12, #3764]
	ldr r7, [r12, #3640]
	and r7, r7, r6
	str r7, [r12, #3768]
	ldr r7, [r12, #3640]
	lsr r7, r7, #16
	str r7, [r12, #3772]
	ldr r7, [r12, #3644]
	and r7, r7, r6
	str r7, [r12, #3776]
	ldr r7, [r12, #3644]
	lsr r7, r7, #16
	str r7, [r12, #3780]
	ldr r7, [r12, #3648]
	and r7, r7, r6
	str r7, [r12, #3784]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #3912]
	ldr r5, [r12, #3656]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3660]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3848]
	ldr r7, [r12, #3916]
	ldr r5, [r12, #3664]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3668]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3852]
	ldr r7, [r12, #3920]
	ldr r5, [r12, #3672]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3676]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3856]
	ldr r7, [r12, #3924]
	ldr r5, [r12, #3680]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3684]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3860]
	ldr r7, [r12, #3928]
	ldr r5, [r12, #3688]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3692]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3864]
	ldr r7, [r12, #3932]
	ldr r5, [r12, #3696]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3700]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3868]
	ldr r7, [r12, #3936]
	ldr r5, [r12, #3704]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3708]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3872]
	ldr r7, [r12, #3940]
	ldr r5, [r12, #3712]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3716]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3876]
	ldr r7, [r12, #3944]
	ldr r5, [r12, #3720]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3724]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3880]
	ldr r7, [r12, #3948]
	ldr r5, [r12, #3728]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3732]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3884]
	ldr r7, [r12, #3952]
	ldr r5, [r12, #3736]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3740]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3888]
	ldr r7, [r12, #3956]
	ldr r5, [r12, #3744]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3748]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3892]
	ldr r7, [r12, #3960]
	ldr r5, [r12, #3752]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3756]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3896]
	ldr r7, [r12, #3964]
	ldr r5, [r12, #3760]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3764]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3900]
	ldr r7, [r12, #3968]
	ldr r5, [r12, #3768]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3772]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3904]
	ldr r7, [r12, #3972]
	ldr r5, [r12, #3776]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3780]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3908]
	ldr r5, [r12, #3784]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3656]
	ldr r7, [r12, #3660]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3848]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3664]
	ldr r7, [r12, #3668]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3852]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3672]
	ldr r7, [r12, #3676]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3856]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3680]
	ldr r7, [r12, #3684]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3860]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3688]
	ldr r7, [r12, #3692]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3864]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3696]
	ldr r7, [r12, #3700]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3868]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3704]
	ldr r7, [r12, #3708]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3872]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3712]
	ldr r7, [r12, #3716]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3876]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r5, [r12, #3720]
	ldr r7, [r12, #3724]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3880]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #32]
	ldr r5, [r12, #3728]
	ldr r7, [r12, #3732]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3884]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #36]
	ldr r5, [r12, #3736]
	ldr r7, [r12, #3740]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3888]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #40]
	ldr r5, [r12, #3744]
	ldr r7, [r12, #3748]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3892]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #44]
	ldr r5, [r12, #3752]
	ldr r7, [r12, #3756]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3896]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #48]
	ldr r5, [r12, #3760]
	ldr r7, [r12, #3764]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3900]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #52]
	ldr r5, [r12, #3768]
	ldr r7, [r12, #3772]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3904]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #56]
	ldr r5, [r12, #3776]
	ldr r7, [r12, #3780]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3908]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #60]
	ldr r4, [r12, #3976]
	ldr r5, [r12, #3980]
	ldr r6, [r12, #3984]
	ldr r7, [r12, #3988]
	ldr r8, [r12, #3992]
	ldr r9, [r12, #3996]
	ldr lr, [r12, #4000]
	bx lr
