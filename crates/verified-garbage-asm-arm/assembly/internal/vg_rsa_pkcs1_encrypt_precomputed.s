// The functions of `src/internal/vg_rsa_pkcs1_encrypt_precomputed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_encrypt_precomputed:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #1056
	add r12, sp, #0
	add r0, r12, #32
	ldr r1, [sp, #1128]
	ldr lr, [sp, #1132]
	mov r2, #0
	strb r2, [r0, #0]
	mov r2, #2
	strb r2, [r0, #1]
	add r0, r0, #2
	mov r3, #0
20:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	sub r2, r2, #1
	orr r3, r3, r2, lsr #31
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 20b
	mov r2, #0
	strb r2, [r0, #0]
	add r0, r0, #1
	add r12, sp, #0
	str r3, [r12, #24]
	ldr r1, [sp, #1120]
	ldr lr, [sp, #1124]
	cmp lr, #0
	beq 21f
23:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 23b
	b 22f
21:
22:
	add r12, sp, #0
	ldr r0, [sp, #1112]
	str r0, [r12, #0]
	ldr r0, [sp, #1116]
	str r0, [r12, #4]
	add r0, r12, #32
	str r0, [r12, #8]
	ldr r0, [sp, #1068]
	str r0, [r12, #12]
	ldr r0, [sp, #1136]
	str r0, [r12, #16]
	ldr r0, [sp, #1140]
	str r0, [r12, #20]
	ldr r0, [sp, #1056]
	ldr r1, [sp, #1068]
	ldr r2, [sp, #1144]
	ldr r3, [sp, #1148]
	bl {vg_rsa_public_precomputed_checked}
	add r12, sp, #0
	ldr r3, [sp, #24]
	sub r2, r3, #1
	and r3, r0, r2
	ldr r0, [sp, #1056]
	ldr lr, [sp, #1068]
24:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 24b
	add r12, sp, #0
	add r0, r12, #32
	ldr lr, [sp, #1068]
	mov r2, #0
25:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 25b
	mov r0, r3
	add sp, sp, #1056
	ldr r4, [sp, #16]
	ldr r5, [sp, #20]
	ldr r6, [sp, #24]
	ldr r7, [sp, #28]
	ldr r8, [sp, #32]
	ldr r9, [sp, #36]
	ldr r10, [sp, #40]
	ldr r11, [sp, #44]
	ldr lr, [sp, #52]
	ldr r12, [sp], #56
	bx lr
