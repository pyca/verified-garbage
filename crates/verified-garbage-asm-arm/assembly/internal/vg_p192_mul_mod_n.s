// The functions of `src/internal/vg_p192_mul_mod_n.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p192_mul_mod_n:
	mov r12, r0
	str r4, [r12, #4056]
	str r5, [r12, #4060]
	str r6, [r12, #4064]
	str r7, [r12, #4068]
	str r8, [r12, #4072]
	str r9, [r12, #4076]
	str lr, [r12, #4080]
	movw r4, #10289
	movt r4, #46290
	str r4, [r12, #4032]
	movw r4, #51633
	movt r4, #5227
	str r4, [r12, #4036]
	movw r4, #63542
	movt r4, #39390
	str r4, [r12, #4040]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4044]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4048]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #4052]
	add lr, r12, r1
	add r1, r12, r2
	add r4, r12, r3
	mov r7, #0
	str r7, [r12, #3904]
	str r7, [r12, #3908]
	str r7, [r12, #3912]
	str r7, [r12, #3916]
	str r7, [r12, #3920]
	str r7, [r12, #3924]
	str r7, [r12, #3928]
	str r7, [r12, #3932]
	str r7, [r12, #3936]
	str r7, [r12, #3940]
	str r7, [r12, #3944]
	str r7, [r12, #3948]
	str r7, [r12, #3952]
	str r7, [r12, #3956]
	str r7, [r12, #3960]
	str r7, [r12, #3964]
	str r7, [r12, #3968]
	str r7, [r12, #3972]
	str r7, [r12, #3976]
	str r7, [r12, #3980]
	str r7, [r12, #3984]
	str r7, [r12, #3988]
	str r7, [r12, #3992]
	str r7, [r12, #3996]
	str r7, [r12, #4000]
	str r7, [r12, #4004]
	movw r6, #65535
	mov r0, r12
	mov r1, r1
	mov r9, #6
20:
	ldr r8, [r1, #0]
	and r2, r8, r6
	mov r3, #0
	ldr r7, [r4, #0]
	and r7, r7, r6
	ldr r5, [r0, #3904]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	lsr r3, r5, #16
	ldr r7, [r4, #0]
	lsr r7, r7, #16
	ldr r5, [r0, #3908]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3908]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	and r7, r7, r6
	ldr r5, [r0, #3912]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3912]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	lsr r7, r7, #16
	ldr r5, [r0, #3916]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3916]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	and r7, r7, r6
	ldr r5, [r0, #3920]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3920]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	lsr r7, r7, #16
	ldr r5, [r0, #3924]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3924]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	and r7, r7, r6
	ldr r5, [r0, #3928]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3928]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	lsr r7, r7, #16
	ldr r5, [r0, #3932]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3932]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	and r7, r7, r6
	ldr r5, [r0, #3936]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3936]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	lsr r7, r7, #16
	ldr r5, [r0, #3940]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3940]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	and r7, r7, r6
	ldr r5, [r0, #3944]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3944]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	lsr r7, r7, #16
	ldr r5, [r0, #3948]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3948]
	lsr r3, r5, #16
	ldr r5, [r0, #3952]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3952]
	ldr r7, [r0, #3956]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3956]
	ldr r2, [r0, #3904]
	movw r7, #53039
	mul r2, r2, r7
	and r2, r2, r6
	mov r3, #0
	ldr r7, [r12, #4032]
	and r7, r7, r6
	ldr r5, [r0, #3904]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	lsr r7, r7, #16
	ldr r5, [r0, #3908]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3908]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	and r7, r7, r6
	ldr r5, [r0, #3912]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3912]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	lsr r7, r7, #16
	ldr r5, [r0, #3916]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3916]
	lsr r3, r5, #16
	ldr r7, [r12, #4040]
	and r7, r7, r6
	ldr r5, [r0, #3920]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3920]
	lsr r3, r5, #16
	ldr r7, [r12, #4040]
	lsr r7, r7, #16
	ldr r5, [r0, #3924]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3924]
	lsr r3, r5, #16
	ldr r7, [r12, #4044]
	and r7, r7, r6
	ldr r5, [r0, #3928]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3928]
	lsr r3, r5, #16
	ldr r7, [r12, #4044]
	lsr r7, r7, #16
	ldr r5, [r0, #3932]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3932]
	lsr r3, r5, #16
	ldr r7, [r12, #4048]
	and r7, r7, r6
	ldr r5, [r0, #3936]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3936]
	lsr r3, r5, #16
	ldr r7, [r12, #4048]
	lsr r7, r7, #16
	ldr r5, [r0, #3940]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3940]
	lsr r3, r5, #16
	ldr r7, [r12, #4052]
	and r7, r7, r6
	ldr r5, [r0, #3944]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3944]
	lsr r3, r5, #16
	ldr r7, [r12, #4052]
	lsr r7, r7, #16
	ldr r5, [r0, #3948]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3948]
	lsr r3, r5, #16
	ldr r5, [r0, #3952]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3952]
	ldr r7, [r0, #3956]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3956]
	add r0, r0, #4
	lsr r2, r8, #16
	mov r3, #0
	ldr r7, [r4, #0]
	and r7, r7, r6
	ldr r5, [r0, #3904]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	lsr r3, r5, #16
	ldr r7, [r4, #0]
	lsr r7, r7, #16
	ldr r5, [r0, #3908]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3908]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	and r7, r7, r6
	ldr r5, [r0, #3912]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3912]
	lsr r3, r5, #16
	ldr r7, [r4, #4]
	lsr r7, r7, #16
	ldr r5, [r0, #3916]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3916]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	and r7, r7, r6
	ldr r5, [r0, #3920]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3920]
	lsr r3, r5, #16
	ldr r7, [r4, #8]
	lsr r7, r7, #16
	ldr r5, [r0, #3924]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3924]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	and r7, r7, r6
	ldr r5, [r0, #3928]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3928]
	lsr r3, r5, #16
	ldr r7, [r4, #12]
	lsr r7, r7, #16
	ldr r5, [r0, #3932]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3932]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	and r7, r7, r6
	ldr r5, [r0, #3936]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3936]
	lsr r3, r5, #16
	ldr r7, [r4, #16]
	lsr r7, r7, #16
	ldr r5, [r0, #3940]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3940]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	and r7, r7, r6
	ldr r5, [r0, #3944]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3944]
	lsr r3, r5, #16
	ldr r7, [r4, #20]
	lsr r7, r7, #16
	ldr r5, [r0, #3948]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3948]
	lsr r3, r5, #16
	ldr r5, [r0, #3952]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3952]
	ldr r7, [r0, #3956]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3956]
	ldr r2, [r0, #3904]
	movw r7, #53039
	mul r2, r2, r7
	and r2, r2, r6
	mov r3, #0
	ldr r7, [r12, #4032]
	and r7, r7, r6
	ldr r5, [r0, #3904]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3904]
	lsr r3, r5, #16
	ldr r7, [r12, #4032]
	lsr r7, r7, #16
	ldr r5, [r0, #3908]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3908]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	and r7, r7, r6
	ldr r5, [r0, #3912]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3912]
	lsr r3, r5, #16
	ldr r7, [r12, #4036]
	lsr r7, r7, #16
	ldr r5, [r0, #3916]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3916]
	lsr r3, r5, #16
	ldr r7, [r12, #4040]
	and r7, r7, r6
	ldr r5, [r0, #3920]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3920]
	lsr r3, r5, #16
	ldr r7, [r12, #4040]
	lsr r7, r7, #16
	ldr r5, [r0, #3924]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3924]
	lsr r3, r5, #16
	ldr r7, [r12, #4044]
	and r7, r7, r6
	ldr r5, [r0, #3928]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3928]
	lsr r3, r5, #16
	ldr r7, [r12, #4044]
	lsr r7, r7, #16
	ldr r5, [r0, #3932]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3932]
	lsr r3, r5, #16
	ldr r7, [r12, #4048]
	and r7, r7, r6
	ldr r5, [r0, #3936]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3936]
	lsr r3, r5, #16
	ldr r7, [r12, #4048]
	lsr r7, r7, #16
	ldr r5, [r0, #3940]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3940]
	lsr r3, r5, #16
	ldr r7, [r12, #4052]
	and r7, r7, r6
	ldr r5, [r0, #3944]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3944]
	lsr r3, r5, #16
	ldr r7, [r12, #4052]
	lsr r7, r7, #16
	ldr r5, [r0, #3948]
	mla r5, r2, r7, r5
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3948]
	lsr r3, r5, #16
	ldr r5, [r0, #3952]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r0, #3952]
	ldr r7, [r0, #3956]
	add r7, r7, r5, lsr #16
	str r7, [r0, #3956]
	add r0, r0, #4
	add r1, r1, #4
	subs r9, r9, #1
	bne 20b
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #4032]
	ldr r5, [r12, #3952]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3956]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4008]
	ldr r7, [r12, #4036]
	ldr r5, [r12, #3960]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3964]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4012]
	ldr r7, [r12, #4040]
	ldr r5, [r12, #3968]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3972]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4016]
	ldr r7, [r12, #4044]
	ldr r5, [r12, #3976]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3980]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4020]
	ldr r7, [r12, #4048]
	ldr r5, [r12, #3984]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3988]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4024]
	ldr r7, [r12, #4052]
	ldr r5, [r12, #3992]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r8, r5, r6
	ldr r5, [r12, #3996]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r8, r8, r5, lsl #16
	str r8, [r12, #4028]
	ldr r5, [r12, #4000]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	ldr r5, [r12, #3952]
	ldr r7, [r12, #3956]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4008]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #0]
	ldr r5, [r12, #3960]
	ldr r7, [r12, #3964]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4012]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #4]
	ldr r5, [r12, #3968]
	ldr r7, [r12, #3972]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4016]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #8]
	ldr r5, [r12, #3976]
	ldr r7, [r12, #3980]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4020]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #12]
	ldr r5, [r12, #3984]
	ldr r7, [r12, #3988]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4024]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #16]
	ldr r5, [r12, #3992]
	ldr r7, [r12, #3996]
	orr r5, r5, r7, lsl #16
	ldr r7, [r12, #4028]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [lr, #20]
	ldr r4, [r12, #4056]
	ldr r5, [r12, #4060]
	ldr r6, [r12, #4064]
	ldr r7, [r12, #4068]
	ldr r8, [r12, #4072]
	ldr r9, [r12, #4076]
	ldr lr, [r12, #4080]
	bx lr
