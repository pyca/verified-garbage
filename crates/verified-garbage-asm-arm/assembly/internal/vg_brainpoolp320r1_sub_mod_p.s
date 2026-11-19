// The functions of `src/internal/vg_brainpoolp320r1_sub_mod_p.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_sub_mod_p:
	mov r12, r0
	str r4, [r12, #4024]
	str r5, [r12, #4028]
	str r6, [r12, #4032]
	str r7, [r12, #4036]
	str r8, [r12, #4040]
	str r9, [r12, #4044]
	str lr, [r12, #4048]
	movw r4, #11815
	movt r4, #61875
	str r4, [r12, #3984]
	movw r4, #4785
	movt r4, #64724
	str r4, [r12, #3988]
	movw r4, #60456
	movt r4, #30867
	str r4, [r12, #3992]
	movw r4, #47596
	movt r4, #20370
	str r4, [r12, #3996]
	movw r4, #3567
	movt r4, #63220
	str r4, [r12, #4000]
	movw r4, #53158
	movt r4, #63887
	str r4, [r12, #4004]
	movw r4, #57445
	movt r4, #53761
	str r4, [r12, #4008]
	movw r4, #30814
	movt r4, #57660
	str r4, [r12, #4012]
	movw r4, #20407
	movt r4, #14012
	str r4, [r12, #4016]
	movw r4, #18208
	movt r4, #54110
	str r4, [r12, #4020]
	add lr, r12, r1
	add r1, r12, r2
	add r2, r12, r3
	movw r6, #65535
	mov r3, #1
	ldr r7, [r1, #0]
	ldr r8, [r2, #0]
	ldr r9, [r12, #3984]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3776]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3780]
	lsr r3, r4, #16
	ldr r7, [r1, #4]
	ldr r8, [r2, #4]
	ldr r9, [r12, #3988]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3784]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3788]
	lsr r3, r4, #16
	ldr r7, [r1, #8]
	ldr r8, [r2, #8]
	ldr r9, [r12, #3992]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3792]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3796]
	lsr r3, r4, #16
	ldr r7, [r1, #12]
	ldr r8, [r2, #12]
	ldr r9, [r12, #3996]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3800]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3804]
	lsr r3, r4, #16
	ldr r7, [r1, #16]
	ldr r8, [r2, #16]
	ldr r9, [r12, #4000]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3808]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3812]
	lsr r3, r4, #16
	ldr r7, [r1, #20]
	ldr r8, [r2, #20]
	ldr r9, [r12, #4004]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3816]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3820]
	lsr r3, r4, #16
	ldr r7, [r1, #24]
	ldr r8, [r2, #24]
	ldr r9, [r12, #4008]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3824]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3828]
	lsr r3, r4, #16
	ldr r7, [r1, #28]
	ldr r8, [r2, #28]
	ldr r9, [r12, #4012]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3832]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3836]
	lsr r3, r4, #16
	ldr r7, [r1, #32]
	ldr r8, [r2, #32]
	ldr r9, [r12, #4016]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3840]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3844]
	lsr r3, r4, #16
	ldr r7, [r1, #36]
	ldr r8, [r2, #36]
	ldr r9, [r12, #4020]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3848]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3852]
	lsr r3, r4, #16
	sub r3, r3, #1
	str r3, [r12, #3856]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #3984]
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
	str r8, [r12, #3944]
	ldr r7, [r12, #3988]
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
	str r8, [r12, #3948]
	ldr r7, [r12, #3992]
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
	str r8, [r12, #3952]
	ldr r7, [r12, #3996]
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
	str r8, [r12, #3956]
	ldr r7, [r12, #4000]
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
	str r8, [r12, #3960]
	ldr r7, [r12, #4004]
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
	str r8, [r12, #3964]
	ldr r7, [r12, #4008]
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
	str r8, [r12, #3968]
	ldr r7, [r12, #4012]
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
	str r8, [r12, #3972]
	ldr r7, [r12, #4016]
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
	str r8, [r12, #3976]
	ldr r7, [r12, #4020]
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
	str r8, [r12, #3980]
	ldr r5, [r12, #3856]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3776]
	ldr r7, [r12, #3780]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3944]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3784]
	ldr r7, [r12, #3788]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3948]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3792]
	ldr r7, [r12, #3796]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3952]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3800]
	ldr r7, [r12, #3804]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3956]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3808]
	ldr r7, [r12, #3812]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3960]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3816]
	ldr r7, [r12, #3820]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3964]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3824]
	ldr r7, [r12, #3828]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3968]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3832]
	ldr r7, [r12, #3836]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3972]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #28]
	ldr r5, [r12, #3840]
	ldr r7, [r12, #3844]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #32]
	ldr r5, [r12, #3848]
	ldr r7, [r12, #3852]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #36]
	ldr r4, [r12, #4024]
	ldr r5, [r12, #4028]
	ldr r6, [r12, #4032]
	ldr r7, [r12, #4036]
	ldr r8, [r12, #4040]
	ldr r9, [r12, #4044]
	ldr lr, [r12, #4048]
	bx lr
