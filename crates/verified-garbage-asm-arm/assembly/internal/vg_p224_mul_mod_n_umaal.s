// The functions of `src/internal/vg_p224_mul_mod_n_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_mul_mod_n_umaal:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #10813
	movt r4, #23644
	str r4, [r12, #4008]
	movw r4, #10565
	movt r4, #5085
	str r4, [r12, #4012]
	movw r4, #61502
	movt r4, #57528
	str r4, [r12, #4016]
	movw r4, #5794
	movt r4, #65535
	str r4, [r12, #4020]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4024]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4028]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4032]
	movw r4, #0
	movt r4, #0
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
	movw r7, #49899
	movt r7, #27167
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
	movw r6, #65535
	ldr r7, [r12, #3840]
	and r7, r7, r6
	str r7, [r12, #3880]
	ldr r7, [r12, #3840]
	lsr r7, r7, #16
	str r7, [r12, #3884]
	ldr r7, [r12, #3844]
	and r7, r7, r6
	str r7, [r12, #3888]
	ldr r7, [r12, #3844]
	lsr r7, r7, #16
	str r7, [r12, #3892]
	ldr r7, [r12, #3848]
	and r7, r7, r6
	str r7, [r12, #3896]
	ldr r7, [r12, #3848]
	lsr r7, r7, #16
	str r7, [r12, #3900]
	ldr r7, [r12, #3852]
	and r7, r7, r6
	str r7, [r12, #3904]
	ldr r7, [r12, #3852]
	lsr r7, r7, #16
	str r7, [r12, #3908]
	ldr r7, [r12, #3856]
	and r7, r7, r6
	str r7, [r12, #3912]
	ldr r7, [r12, #3856]
	lsr r7, r7, #16
	str r7, [r12, #3916]
	ldr r7, [r12, #3860]
	and r7, r7, r6
	str r7, [r12, #3920]
	ldr r7, [r12, #3860]
	lsr r7, r7, #16
	str r7, [r12, #3924]
	ldr r7, [r12, #3864]
	and r7, r7, r6
	str r7, [r12, #3928]
	ldr r7, [r12, #3864]
	lsr r7, r7, #16
	str r7, [r12, #3932]
	ldr r7, [r12, #3868]
	and r7, r7, r6
	str r7, [r12, #3936]
	ldr r7, [r12, #3868]
	lsr r7, r7, #16
	str r7, [r12, #3940]
	ldr r7, [r12, #3872]
	and r7, r7, r6
	str r7, [r12, #3944]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
	ldr r5, [r12, #3880]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3884]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3976]
	ldr r7, [r12, #4012]
	ldr r5, [r12, #3888]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3892]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3980]
	ldr r7, [r12, #4016]
	ldr r5, [r12, #3896]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3900]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3904]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3908]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3912]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3916]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
	ldr r5, [r12, #3920]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3924]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3928]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3932]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3936]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3940]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4004]
	ldr r5, [r12, #3944]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3880]
	ldr r7, [r12, #3884]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3888]
	ldr r7, [r12, #3892]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3896]
	ldr r7, [r12, #3900]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3904]
	ldr r7, [r12, #3908]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3912]
	ldr r7, [r12, #3916]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3920]
	ldr r7, [r12, #3924]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3928]
	ldr r7, [r12, #3932]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3936]
	ldr r7, [r12, #3940]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4004]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r4, [r12, #4040]
	ldr r5, [r12, #4044]
	ldr r6, [r12, #4048]
	ldr r7, [r12, #4052]
	ldr r8, [r12, #4056]
	ldr r9, [r12, #4060]
	ldr lr, [r12, #4064]
	bx lr
