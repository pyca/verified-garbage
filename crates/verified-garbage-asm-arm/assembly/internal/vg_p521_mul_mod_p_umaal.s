// The functions of `src/internal/vg_p521_mul_mod_p_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_mul_mod_p_umaal:
	mov r12, r0
	str r4, [r12, #3960]
	str r5, [r12, #3964]
	str r6, [r12, #3968]
	str r7, [r12, #3972]
	str r8, [r12, #3976]
	str r9, [r12, #3980]
	str lr, [r12, #3984]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3888]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3892]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3896]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3900]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3904]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3908]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3912]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3916]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3920]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3924]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3928]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3932]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3936]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3940]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3944]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3948]
	movw r4, #511
	movt r4, #0
	str r4, [r12, #3952]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3956]
	add lr, r12, r1
	add r1, r12, r2
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
	str r7, [r12, #3596]
	mov r9, #18
20:
	ldr r2, [r1, #0]
	mov r3, #0
	ldr r7, [r4, #0]
	ldr r5, [r12, #3520]
	umaal r5, r3, r2, r7
	str r5, [r12, #3520]
	ldr r7, [r4, #4]
	ldr r5, [r12, #3524]
	umaal r5, r3, r2, r7
	str r5, [r12, #3524]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3528]
	umaal r5, r3, r2, r7
	str r5, [r12, #3528]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3532]
	umaal r5, r3, r2, r7
	str r5, [r12, #3532]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3536]
	umaal r5, r3, r2, r7
	str r5, [r12, #3536]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3540]
	umaal r5, r3, r2, r7
	str r5, [r12, #3540]
	ldr r7, [r4, #24]
	ldr r5, [r12, #3544]
	umaal r5, r3, r2, r7
	str r5, [r12, #3544]
	ldr r7, [r4, #28]
	ldr r5, [r12, #3548]
	umaal r5, r3, r2, r7
	str r5, [r12, #3548]
	ldr r7, [r4, #32]
	ldr r5, [r12, #3552]
	umaal r5, r3, r2, r7
	str r5, [r12, #3552]
	ldr r7, [r4, #36]
	ldr r5, [r12, #3556]
	umaal r5, r3, r2, r7
	str r5, [r12, #3556]
	ldr r7, [r4, #40]
	ldr r5, [r12, #3560]
	umaal r5, r3, r2, r7
	str r5, [r12, #3560]
	ldr r7, [r4, #44]
	ldr r5, [r12, #3564]
	umaal r5, r3, r2, r7
	str r5, [r12, #3564]
	ldr r7, [r4, #48]
	ldr r5, [r12, #3568]
	umaal r5, r3, r2, r7
	str r5, [r12, #3568]
	ldr r7, [r4, #52]
	ldr r5, [r12, #3572]
	umaal r5, r3, r2, r7
	str r5, [r12, #3572]
	ldr r7, [r4, #56]
	ldr r5, [r12, #3576]
	umaal r5, r3, r2, r7
	str r5, [r12, #3576]
	ldr r7, [r4, #60]
	ldr r5, [r12, #3580]
	umaal r5, r3, r2, r7
	str r5, [r12, #3580]
	ldr r7, [r4, #64]
	ldr r5, [r12, #3584]
	umaal r5, r3, r2, r7
	str r5, [r12, #3584]
	ldr r7, [r4, #68]
	ldr r5, [r12, #3588]
	umaal r5, r3, r2, r7
	str r5, [r12, #3588]
	ldr r5, [r12, #3592]
	ldr r6, [r12, #3596]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3592]
	str r6, [r12, #3596]
	ldr r2, [r12, #3520]
	movw r7, #1
	movt r7, #0
	mul r2, r2, r7
	mov r3, #0
	ldr r7, [r12, #3888]
	ldr r5, [r12, #3520]
	umaal r5, r3, r2, r7
	str r5, [r12, #3520]
	ldr r7, [r12, #3892]
	ldr r5, [r12, #3524]
	umaal r5, r3, r2, r7
	str r5, [r12, #3524]
	ldr r7, [r12, #3896]
	ldr r5, [r12, #3528]
	umaal r5, r3, r2, r7
	str r5, [r12, #3528]
	ldr r7, [r12, #3900]
	ldr r5, [r12, #3532]
	umaal r5, r3, r2, r7
	str r5, [r12, #3532]
	ldr r7, [r12, #3904]
	ldr r5, [r12, #3536]
	umaal r5, r3, r2, r7
	str r5, [r12, #3536]
	ldr r7, [r12, #3908]
	ldr r5, [r12, #3540]
	umaal r5, r3, r2, r7
	str r5, [r12, #3540]
	ldr r7, [r12, #3912]
	ldr r5, [r12, #3544]
	umaal r5, r3, r2, r7
	str r5, [r12, #3544]
	ldr r7, [r12, #3916]
	ldr r5, [r12, #3548]
	umaal r5, r3, r2, r7
	str r5, [r12, #3548]
	ldr r7, [r12, #3920]
	ldr r5, [r12, #3552]
	umaal r5, r3, r2, r7
	str r5, [r12, #3552]
	ldr r7, [r12, #3924]
	ldr r5, [r12, #3556]
	umaal r5, r3, r2, r7
	str r5, [r12, #3556]
	ldr r7, [r12, #3928]
	ldr r5, [r12, #3560]
	umaal r5, r3, r2, r7
	str r5, [r12, #3560]
	ldr r7, [r12, #3932]
	ldr r5, [r12, #3564]
	umaal r5, r3, r2, r7
	str r5, [r12, #3564]
	ldr r7, [r12, #3936]
	ldr r5, [r12, #3568]
	umaal r5, r3, r2, r7
	str r5, [r12, #3568]
	ldr r7, [r12, #3940]
	ldr r5, [r12, #3572]
	umaal r5, r3, r2, r7
	str r5, [r12, #3572]
	ldr r7, [r12, #3944]
	ldr r5, [r12, #3576]
	umaal r5, r3, r2, r7
	str r5, [r12, #3576]
	ldr r7, [r12, #3948]
	ldr r5, [r12, #3580]
	umaal r5, r3, r2, r7
	str r5, [r12, #3580]
	ldr r7, [r12, #3952]
	ldr r5, [r12, #3584]
	umaal r5, r3, r2, r7
	str r5, [r12, #3584]
	ldr r7, [r12, #3956]
	ldr r5, [r12, #3588]
	umaal r5, r3, r2, r7
	str r5, [r12, #3588]
	ldr r5, [r12, #3592]
	ldr r6, [r12, #3596]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3592]
	str r6, [r12, #3596]
	ldr r5, [r12, #3524]
	str r5, [r12, #3520]
	ldr r5, [r12, #3528]
	str r5, [r12, #3524]
	ldr r5, [r12, #3532]
	str r5, [r12, #3528]
	ldr r5, [r12, #3536]
	str r5, [r12, #3532]
	ldr r5, [r12, #3540]
	str r5, [r12, #3536]
	ldr r5, [r12, #3544]
	str r5, [r12, #3540]
	ldr r5, [r12, #3548]
	str r5, [r12, #3544]
	ldr r5, [r12, #3552]
	str r5, [r12, #3548]
	ldr r5, [r12, #3556]
	str r5, [r12, #3552]
	ldr r5, [r12, #3560]
	str r5, [r12, #3556]
	ldr r5, [r12, #3564]
	str r5, [r12, #3560]
	ldr r5, [r12, #3568]
	str r5, [r12, #3564]
	ldr r5, [r12, #3572]
	str r5, [r12, #3568]
	ldr r5, [r12, #3576]
	str r5, [r12, #3572]
	ldr r5, [r12, #3580]
	str r5, [r12, #3576]
	ldr r5, [r12, #3584]
	str r5, [r12, #3580]
	ldr r5, [r12, #3588]
	str r5, [r12, #3584]
	ldr r5, [r12, #3592]
	str r5, [r12, #3588]
	ldr r5, [r12, #3596]
	str r5, [r12, #3592]
	mov r5, #0
	str r5, [r12, #3596]
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	movw r6, #65535
	ldr r7, [r12, #3520]
	and r7, r7, r6
	str r7, [r12, #3600]
	ldr r7, [r12, #3520]
	lsr r7, r7, #16
	str r7, [r12, #3604]
	ldr r7, [r12, #3524]
	and r7, r7, r6
	str r7, [r12, #3608]
	ldr r7, [r12, #3524]
	lsr r7, r7, #16
	str r7, [r12, #3612]
	ldr r7, [r12, #3528]
	and r7, r7, r6
	str r7, [r12, #3616]
	ldr r7, [r12, #3528]
	lsr r7, r7, #16
	str r7, [r12, #3620]
	ldr r7, [r12, #3532]
	and r7, r7, r6
	str r7, [r12, #3624]
	ldr r7, [r12, #3532]
	lsr r7, r7, #16
	str r7, [r12, #3628]
	ldr r7, [r12, #3536]
	and r7, r7, r6
	str r7, [r12, #3632]
	ldr r7, [r12, #3536]
	lsr r7, r7, #16
	str r7, [r12, #3636]
	ldr r7, [r12, #3540]
	and r7, r7, r6
	str r7, [r12, #3640]
	ldr r7, [r12, #3540]
	lsr r7, r7, #16
	str r7, [r12, #3644]
	ldr r7, [r12, #3544]
	and r7, r7, r6
	str r7, [r12, #3648]
	ldr r7, [r12, #3544]
	lsr r7, r7, #16
	str r7, [r12, #3652]
	ldr r7, [r12, #3548]
	and r7, r7, r6
	str r7, [r12, #3656]
	ldr r7, [r12, #3548]
	lsr r7, r7, #16
	str r7, [r12, #3660]
	ldr r7, [r12, #3552]
	and r7, r7, r6
	str r7, [r12, #3664]
	ldr r7, [r12, #3552]
	lsr r7, r7, #16
	str r7, [r12, #3668]
	ldr r7, [r12, #3556]
	and r7, r7, r6
	str r7, [r12, #3672]
	ldr r7, [r12, #3556]
	lsr r7, r7, #16
	str r7, [r12, #3676]
	ldr r7, [r12, #3560]
	and r7, r7, r6
	str r7, [r12, #3680]
	ldr r7, [r12, #3560]
	lsr r7, r7, #16
	str r7, [r12, #3684]
	ldr r7, [r12, #3564]
	and r7, r7, r6
	str r7, [r12, #3688]
	ldr r7, [r12, #3564]
	lsr r7, r7, #16
	str r7, [r12, #3692]
	ldr r7, [r12, #3568]
	and r7, r7, r6
	str r7, [r12, #3696]
	ldr r7, [r12, #3568]
	lsr r7, r7, #16
	str r7, [r12, #3700]
	ldr r7, [r12, #3572]
	and r7, r7, r6
	str r7, [r12, #3704]
	ldr r7, [r12, #3572]
	lsr r7, r7, #16
	str r7, [r12, #3708]
	ldr r7, [r12, #3576]
	and r7, r7, r6
	str r7, [r12, #3712]
	ldr r7, [r12, #3576]
	lsr r7, r7, #16
	str r7, [r12, #3716]
	ldr r7, [r12, #3580]
	and r7, r7, r6
	str r7, [r12, #3720]
	ldr r7, [r12, #3580]
	lsr r7, r7, #16
	str r7, [r12, #3724]
	ldr r7, [r12, #3584]
	and r7, r7, r6
	str r7, [r12, #3728]
	ldr r7, [r12, #3584]
	lsr r7, r7, #16
	str r7, [r12, #3732]
	ldr r7, [r12, #3588]
	and r7, r7, r6
	str r7, [r12, #3736]
	ldr r7, [r12, #3588]
	lsr r7, r7, #16
	str r7, [r12, #3740]
	ldr r7, [r12, #3592]
	and r7, r7, r6
	str r7, [r12, #3744]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #3888]
	ldr r5, [r12, #3600]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3604]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3816]
	ldr r7, [r12, #3892]
	ldr r5, [r12, #3608]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3612]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3820]
	ldr r7, [r12, #3896]
	ldr r5, [r12, #3616]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3620]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3824]
	ldr r7, [r12, #3900]
	ldr r5, [r12, #3624]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3628]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3828]
	ldr r7, [r12, #3904]
	ldr r5, [r12, #3632]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3636]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3832]
	ldr r7, [r12, #3908]
	ldr r5, [r12, #3640]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3644]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3836]
	ldr r7, [r12, #3912]
	ldr r5, [r12, #3648]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3652]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3840]
	ldr r7, [r12, #3916]
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
	str r8, [r12, #3844]
	ldr r7, [r12, #3920]
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
	str r8, [r12, #3848]
	ldr r7, [r12, #3924]
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
	str r8, [r12, #3852]
	ldr r7, [r12, #3928]
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
	str r8, [r12, #3856]
	ldr r7, [r12, #3932]
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
	str r8, [r12, #3860]
	ldr r7, [r12, #3936]
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
	str r8, [r12, #3864]
	ldr r7, [r12, #3940]
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
	str r8, [r12, #3868]
	ldr r7, [r12, #3944]
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
	str r8, [r12, #3872]
	ldr r7, [r12, #3948]
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
	str r8, [r12, #3876]
	ldr r7, [r12, #3952]
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
	str r8, [r12, #3880]
	ldr r7, [r12, #3956]
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
	str r8, [r12, #3884]
	ldr r5, [r12, #3744]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3600]
	ldr r7, [r12, #3604]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3816]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3608]
	ldr r7, [r12, #3612]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3820]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3616]
	ldr r7, [r12, #3620]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3824]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3624]
	ldr r7, [r12, #3628]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3828]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3632]
	ldr r7, [r12, #3636]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3832]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3640]
	ldr r7, [r12, #3644]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3836]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3648]
	ldr r7, [r12, #3652]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3840]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3656]
	ldr r7, [r12, #3660]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3844]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r5, [r12, #3664]
	ldr r7, [r12, #3668]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3848]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #32]
	ldr r5, [r12, #3672]
	ldr r7, [r12, #3676]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3852]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #36]
	ldr r5, [r12, #3680]
	ldr r7, [r12, #3684]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3856]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #40]
	ldr r5, [r12, #3688]
	ldr r7, [r12, #3692]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3860]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #44]
	ldr r5, [r12, #3696]
	ldr r7, [r12, #3700]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3864]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #48]
	ldr r5, [r12, #3704]
	ldr r7, [r12, #3708]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3868]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #52]
	ldr r5, [r12, #3712]
	ldr r7, [r12, #3716]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3872]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #56]
	ldr r5, [r12, #3720]
	ldr r7, [r12, #3724]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3876]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #60]
	ldr r5, [r12, #3728]
	ldr r7, [r12, #3732]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3880]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #64]
	ldr r5, [r12, #3736]
	ldr r7, [r12, #3740]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3884]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #68]
	ldr r4, [r12, #3960]
	ldr r5, [r12, #3964]
	ldr r6, [r12, #3968]
	ldr r7, [r12, #3972]
	ldr r8, [r12, #3976]
	ldr r9, [r12, #3980]
	ldr lr, [r12, #3984]
	bx lr
