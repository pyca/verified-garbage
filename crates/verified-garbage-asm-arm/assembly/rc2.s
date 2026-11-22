// The functions of `src/rc2.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	sub sp, sp, #592
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #592]
	str lr, [r12, #0]
	ldr lr, [sp, #596]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	sub r12, r1, #1
	lsr r12, r12, #7
	cmp r12, #0
	bne 20f
	sub r12, r2, #1
	lsr r12, r12, #10
	cmp r12, #0
	bne 22f
	ldr r12, [sp, #0]
	cmp r12, #8
	bne 24f
	b 25f
24:
	mov r0, #3
25:
	b 23f
22:
	mov r0, #2
23:
	b 21f
20:
	mov r0, #1
21:
	bne 26f
	ldr r12, [sp, #8]
	str lr, [r12, #512]
	ldr lr, [r3, #0]
	ldr r3, [r3, #4]
	ldr r12, [sp, #4]
	str lr, [r12, #128]
	str r3, [r12, #132]
	mov r3, r12
	ldr r12, [sp, #8]
	push {r12, lr}
	bl {vg_rc2_expand_key}
	ldr r12, [sp], #8
	ldr r12, [sp, #8]
	ldr lr, [r12, #512]
	mov r0, #0
	b 27f
26:
27:
	add sp, sp, #592
	sub sp, sp, #600
	add r12, sp, #0
	mov r2, #0
	mov r3, #18
28:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 28b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #600
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
