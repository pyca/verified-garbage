// The functions of `src/internal/vg_p384_mul_mod_n_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_mul_mod_n_umaal:
	mov r12, r0
	str r4, [r12, #4008]
	str r5, [r12, #4012]
	str r6, [r12, #4016]
	str r7, [r12, #4020]
	str r8, [r12, #4024]
	str r9, [r12, #4028]
	str lr, [r12, #4032]
	movw r4, #10611
	movt r4, #52421
	str r4, [r12, #3960]
	movw r4, #6506
	movt r4, #60652
	str r4, [r12, #3964]
	movw r4, #42874
	movt r4, #18608
	str r4, [r12, #3968]
	movw r4, #3506
	movt r4, #22554
	str r4, [r12, #3972]
	movw r4, #11743
	movt r4, #62519
	str r4, [r12, #3976]
	movw r4, #19841
	movt r4, #51043
	str r4, [r12, #3980]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3984]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3988]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3992]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #3996]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4000]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4004]
	add lr, r12, r1
	add r1, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3712]
	str r7, [r12, #3716]
	str r7, [r12, #3720]
	str r7, [r12, #3724]
	str r7, [r12, #3728]
	str r7, [r12, #3732]
	str r7, [r12, #3736]
	str r7, [r12, #3740]
	str r7, [r12, #3744]
	str r7, [r12, #3748]
	str r7, [r12, #3752]
	str r7, [r12, #3756]
	str r7, [r12, #3760]
	str r7, [r12, #3764]
	mov r9, #12
20:
	ldr r2, [r1, #0]
	mov r3, #0
	ldr r7, [r4, #0]
	ldr r5, [r12, #3712]
	umaal r5, r3, r2, r7
	str r5, [r12, #3712]
	ldr r7, [r4, #4]
	ldr r5, [r12, #3716]
	umaal r5, r3, r2, r7
	str r5, [r12, #3716]
	ldr r7, [r4, #8]
	ldr r5, [r12, #3720]
	umaal r5, r3, r2, r7
	str r5, [r12, #3720]
	ldr r7, [r4, #12]
	ldr r5, [r12, #3724]
	umaal r5, r3, r2, r7
	str r5, [r12, #3724]
	ldr r7, [r4, #16]
	ldr r5, [r12, #3728]
	umaal r5, r3, r2, r7
	str r5, [r12, #3728]
	ldr r7, [r4, #20]
	ldr r5, [r12, #3732]
	umaal r5, r3, r2, r7
	str r5, [r12, #3732]
	ldr r7, [r4, #24]
	ldr r5, [r12, #3736]
	umaal r5, r3, r2, r7
	str r5, [r12, #3736]
	ldr r7, [r4, #28]
	ldr r5, [r12, #3740]
	umaal r5, r3, r2, r7
	str r5, [r12, #3740]
	ldr r7, [r4, #32]
	ldr r5, [r12, #3744]
	umaal r5, r3, r2, r7
	str r5, [r12, #3744]
	ldr r7, [r4, #36]
	ldr r5, [r12, #3748]
	umaal r5, r3, r2, r7
	str r5, [r12, #3748]
	ldr r7, [r4, #40]
	ldr r5, [r12, #3752]
	umaal r5, r3, r2, r7
	str r5, [r12, #3752]
	ldr r7, [r4, #44]
	ldr r5, [r12, #3756]
	umaal r5, r3, r2, r7
	str r5, [r12, #3756]
	ldr r5, [r12, #3760]
	ldr r6, [r12, #3764]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3760]
	str r6, [r12, #3764]
	ldr r2, [r12, #3712]
	movw r7, #56389
	movt r7, #59535
	mul r2, r2, r7
	mov r3, #0
	ldr r7, [r12, #3960]
	ldr r5, [r12, #3712]
	umaal r5, r3, r2, r7
	str r5, [r12, #3712]
	ldr r7, [r12, #3964]
	ldr r5, [r12, #3716]
	umaal r5, r3, r2, r7
	str r5, [r12, #3716]
	ldr r7, [r12, #3968]
	ldr r5, [r12, #3720]
	umaal r5, r3, r2, r7
	str r5, [r12, #3720]
	ldr r7, [r12, #3972]
	ldr r5, [r12, #3724]
	umaal r5, r3, r2, r7
	str r5, [r12, #3724]
	ldr r7, [r12, #3976]
	ldr r5, [r12, #3728]
	umaal r5, r3, r2, r7
	str r5, [r12, #3728]
	ldr r7, [r12, #3980]
	ldr r5, [r12, #3732]
	umaal r5, r3, r2, r7
	str r5, [r12, #3732]
	ldr r7, [r12, #3984]
	ldr r5, [r12, #3736]
	umaal r5, r3, r2, r7
	str r5, [r12, #3736]
	ldr r7, [r12, #3988]
	ldr r5, [r12, #3740]
	umaal r5, r3, r2, r7
	str r5, [r12, #3740]
	ldr r7, [r12, #3992]
	ldr r5, [r12, #3744]
	umaal r5, r3, r2, r7
	str r5, [r12, #3744]
	ldr r7, [r12, #3996]
	ldr r5, [r12, #3748]
	umaal r5, r3, r2, r7
	str r5, [r12, #3748]
	ldr r7, [r12, #4000]
	ldr r5, [r12, #3752]
	umaal r5, r3, r2, r7
	str r5, [r12, #3752]
	ldr r7, [r12, #4004]
	ldr r5, [r12, #3756]
	umaal r5, r3, r2, r7
	str r5, [r12, #3756]
	ldr r5, [r12, #3760]
	ldr r6, [r12, #3764]
	adds r5, r5, r3
	adc r6, r6, #0
	str r5, [r12, #3760]
	str r6, [r12, #3764]
	ldr r5, [r12, #3716]
	str r5, [r12, #3712]
	ldr r5, [r12, #3720]
	str r5, [r12, #3716]
	ldr r5, [r12, #3724]
	str r5, [r12, #3720]
	ldr r5, [r12, #3728]
	str r5, [r12, #3724]
	ldr r5, [r12, #3732]
	str r5, [r12, #3728]
	ldr r5, [r12, #3736]
	str r5, [r12, #3732]
	ldr r5, [r12, #3740]
	str r5, [r12, #3736]
	ldr r5, [r12, #3744]
	str r5, [r12, #3740]
	ldr r5, [r12, #3748]
	str r5, [r12, #3744]
	ldr r5, [r12, #3752]
	str r5, [r12, #3748]
	ldr r5, [r12, #3756]
	str r5, [r12, #3752]
	ldr r5, [r12, #3760]
	str r5, [r12, #3756]
	ldr r5, [r12, #3764]
	str r5, [r12, #3760]
	mov r5, #0
	str r5, [r12, #3764]
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	movw r6, #65535
	ldr r7, [r12, #3712]
	and r7, r7, r6
	str r7, [r12, #3768]
	ldr r7, [r12, #3712]
	lsr r7, r7, #16
	str r7, [r12, #3772]
	ldr r7, [r12, #3716]
	and r7, r7, r6
	str r7, [r12, #3776]
	ldr r7, [r12, #3716]
	lsr r7, r7, #16
	str r7, [r12, #3780]
	ldr r7, [r12, #3720]
	and r7, r7, r6
	str r7, [r12, #3784]
	ldr r7, [r12, #3720]
	lsr r7, r7, #16
	str r7, [r12, #3788]
	ldr r7, [r12, #3724]
	and r7, r7, r6
	str r7, [r12, #3792]
	ldr r7, [r12, #3724]
	lsr r7, r7, #16
	str r7, [r12, #3796]
	ldr r7, [r12, #3728]
	and r7, r7, r6
	str r7, [r12, #3800]
	ldr r7, [r12, #3728]
	lsr r7, r7, #16
	str r7, [r12, #3804]
	ldr r7, [r12, #3732]
	and r7, r7, r6
	str r7, [r12, #3808]
	ldr r7, [r12, #3732]
	lsr r7, r7, #16
	str r7, [r12, #3812]
	ldr r7, [r12, #3736]
	and r7, r7, r6
	str r7, [r12, #3816]
	ldr r7, [r12, #3736]
	lsr r7, r7, #16
	str r7, [r12, #3820]
	ldr r7, [r12, #3740]
	and r7, r7, r6
	str r7, [r12, #3824]
	ldr r7, [r12, #3740]
	lsr r7, r7, #16
	str r7, [r12, #3828]
	ldr r7, [r12, #3744]
	and r7, r7, r6
	str r7, [r12, #3832]
	ldr r7, [r12, #3744]
	lsr r7, r7, #16
	str r7, [r12, #3836]
	ldr r7, [r12, #3748]
	and r7, r7, r6
	str r7, [r12, #3840]
	ldr r7, [r12, #3748]
	lsr r7, r7, #16
	str r7, [r12, #3844]
	ldr r7, [r12, #3752]
	and r7, r7, r6
	str r7, [r12, #3848]
	ldr r7, [r12, #3752]
	lsr r7, r7, #16
	str r7, [r12, #3852]
	ldr r7, [r12, #3756]
	and r7, r7, r6
	str r7, [r12, #3856]
	ldr r7, [r12, #3756]
	lsr r7, r7, #16
	str r7, [r12, #3860]
	ldr r7, [r12, #3760]
	and r7, r7, r6
	str r7, [r12, #3864]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #3960]
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
	str r8, [r12, #3912]
	ldr r7, [r12, #3964]
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
	str r8, [r12, #3916]
	ldr r7, [r12, #3968]
	ldr r5, [r12, #3784]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3788]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3920]
	ldr r7, [r12, #3972]
	ldr r5, [r12, #3792]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3796]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3924]
	ldr r7, [r12, #3976]
	ldr r5, [r12, #3800]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3804]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3928]
	ldr r7, [r12, #3980]
	ldr r5, [r12, #3808]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3812]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3932]
	ldr r7, [r12, #3984]
	ldr r5, [r12, #3816]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3820]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3936]
	ldr r7, [r12, #3988]
	ldr r5, [r12, #3824]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3828]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3940]
	ldr r7, [r12, #3992]
	ldr r5, [r12, #3832]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3836]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3944]
	ldr r7, [r12, #3996]
	ldr r5, [r12, #3840]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3844]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3948]
	ldr r7, [r12, #4000]
	ldr r5, [r12, #3848]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3852]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3952]
	ldr r7, [r12, #4004]
	ldr r5, [r12, #3856]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3860]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3956]
	ldr r5, [r12, #3864]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3768]
	ldr r7, [r12, #3772]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3912]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3776]
	ldr r7, [r12, #3780]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3916]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3784]
	ldr r7, [r12, #3788]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3920]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3792]
	ldr r7, [r12, #3796]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3924]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3800]
	ldr r7, [r12, #3804]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3928]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3808]
	ldr r7, [r12, #3812]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3932]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3816]
	ldr r7, [r12, #3820]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3936]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3824]
	ldr r7, [r12, #3828]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3940]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r5, [r12, #3832]
	ldr r7, [r12, #3836]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3944]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #32]
	ldr r5, [r12, #3840]
	ldr r7, [r12, #3844]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3948]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #36]
	ldr r5, [r12, #3848]
	ldr r7, [r12, #3852]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3952]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #40]
	ldr r5, [r12, #3856]
	ldr r7, [r12, #3860]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3956]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #44]
	ldr r4, [r12, #4008]
	ldr r5, [r12, #4012]
	ldr r6, [r12, #4016]
	ldr r7, [r12, #4020]
	ldr r8, [r12, #4024]
	ldr r9, [r12, #4028]
	ldr lr, [r12, #4032]
	bx lr
