// The functions of `src/internal/vg_brainpoolp256r1_sub_mod_n.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp256r1_sub_mod_n:
	mov r12, r0
	str r4, [r12, #4040]
	str r5, [r12, #4044]
	str r6, [r12, #4048]
	str r7, [r12, #4052]
	str r8, [r12, #4056]
	str r9, [r12, #4060]
	str lr, [r12, #4064]
	movw r4, #22183
	movt r4, #38728
	str r4, [r12, #4008]
	movw r4, #3714
	movt r4, #36894
	str r4, [r12, #4012]
	movw r4, #42743
	movt r4, #46433
	str r4, [r12, #4016]
	movw r4, #31395
	movt r4, #35897
	str r4, [r12, #4020]
	movw r4, #36209
	movt r4, #40323
	str r4, [r12, #4024]
	movw r4, #2704
	movt r4, #15974
	str r4, [r12, #4028]
	movw r4, #43452
	movt r4, #41454
	str r4, [r12, #4032]
	movw r4, #22491
	movt r4, #43515
	str r4, [r12, #4036]
	add lr, r12, r1
	add r1, r12, r2
	add r2, r12, r3
	movw r6, #65535
	mov r3, #1
	ldr r7, [r1, #0]
	ldr r8, [r2, #0]
	ldr r9, [r12, #4008]
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
	ldr r7, [r1, #4]
	ldr r8, [r2, #4]
	ldr r9, [r12, #4012]
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
	ldr r7, [r1, #8]
	ldr r8, [r2, #8]
	ldr r9, [r12, #4016]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3856]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3860]
	lsr r3, r4, #16
	ldr r7, [r1, #12]
	ldr r8, [r2, #12]
	ldr r9, [r12, #4020]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3864]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3868]
	lsr r3, r4, #16
	ldr r7, [r1, #16]
	ldr r8, [r2, #16]
	ldr r9, [r12, #4024]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3872]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3876]
	lsr r3, r4, #16
	ldr r7, [r1, #20]
	ldr r8, [r2, #20]
	ldr r9, [r12, #4028]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3880]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3884]
	lsr r3, r4, #16
	ldr r7, [r1, #24]
	ldr r8, [r2, #24]
	ldr r9, [r12, #4032]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3888]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3892]
	lsr r3, r4, #16
	ldr r7, [r1, #28]
	ldr r8, [r2, #28]
	ldr r9, [r12, #4036]
	and r4, r7, r6
	and r5, r9, r6
	add r4, r4, r5
	add r4, r4, r6
	and r5, r8, r6
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3896]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r9, #16
	add r4, r4, r5
	add r4, r4, r6
	lsr r5, r8, #16
	sub r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r12, #3900]
	lsr r3, r4, #16
	sub r3, r3, #1
	str r3, [r12, #3904]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4008]
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
	ldr r7, [r12, #4012]
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
	ldr r7, [r12, #4016]
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
	str r8, [r12, #3984]
	ldr r7, [r12, #4020]
	ldr r5, [r12, #3864]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3868]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3988]
	ldr r7, [r12, #4024]
	ldr r5, [r12, #3872]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3876]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #3992]
	ldr r7, [r12, #4028]
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
	str r8, [r12, #3996]
	ldr r7, [r12, #4032]
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
	str r8, [r12, #4000]
	ldr r7, [r12, #4036]
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
	str r8, [r12, #4004]
	ldr r5, [r12, #3904]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3840]
	ldr r7, [r12, #3844]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3976]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3848]
	ldr r7, [r12, #3852]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3980]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3856]
	ldr r7, [r12, #3860]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3984]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3864]
	ldr r7, [r12, #3868]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3988]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3872]
	ldr r7, [r12, #3876]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3992]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3880]
	ldr r7, [r12, #3884]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #3996]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r5, [r12, #3888]
	ldr r7, [r12, #3892]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4000]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #24]
	ldr r5, [r12, #3896]
	ldr r7, [r12, #3900]
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
