// The functions of `src/cast5_ofb.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_ofb:
	sub sp, sp, #328
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #328]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	str r8, [r12, #16]
	mov r4, r0
	mov r11, r1
	mov r5, r2
	mov r6, r3
	ldr r7, [sp, #0]
	mov r8, r12
	ldr r9, [r5, #0]
	str r9, [r8, #40]
	ldr r9, [r5, #4]
	str r9, [r8, #44]
	cmp r7, #0
	beq 20f
22:
	mov r0, r4
	mov r1, r11
	add r2, r8, #40
	mov r3, #1
	add r12, r8, #56
	push {r12, lr}
	bl {vg_cast5_ecb_encrypt_entry}
	ldr r12, [sp], #8
	ldr r9, [r6, #0]
	ldr r10, [r8, #40]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #44]
	eor r9, r9, r10
	str r9, [r6, #4]
	add r6, r6, #8
	subs r7, r7, #1
	bne 22b
	b 21f
20:
21:
	ldr r9, [r8, #40]
	str r9, [r5, #0]
	ldr r9, [r8, #44]
	str r9, [r5, #4]
	ldr r4, [r8, #0]
	ldr r5, [r8, #4]
	ldr r6, [r8, #8]
	ldr r7, [r8, #12]
	ldr r9, [r8, #20]
	ldr r10, [r8, #24]
	ldr r11, [r8, #28]
	ldr lr, [r8, #32]
	ldr r8, [r8, #16]
	add sp, sp, #328
	sub sp, sp, #336
	add r12, sp, #0
	mov r2, #0
	mov r3, #10
23:
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
	bne 23b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	add sp, sp, #336
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_cast5_ofb_final:
	sub sp, sp, #328
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #328]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	str r8, [r12, #16]
	mov r4, r0
	mov r11, r1
	mov r5, r2
	mov r6, r3
	ldr r7, [sp, #0]
	mov r8, r12
	ldr r9, [r5, #0]
	str r9, [r8, #40]
	ldr r9, [r5, #4]
	str r9, [r8, #44]
	cmp r7, #0
	beq 20f
22:
	mov r0, r4
	mov r1, r11
	add r2, r8, #40
	mov r3, #1
	add r12, r8, #56
	push {r12, lr}
	bl {vg_cast5_ecb_encrypt_entry}
	ldr r12, [sp], #8
	lsr r9, r7, #3
	cmp r9, #0
	beq 23f
	ldr r9, [r6, #0]
	ldr r10, [r8, #40]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #44]
	eor r9, r9, r10
	str r9, [r6, #4]
	add r6, r6, #8
	subs r7, r7, #8
	b 24f
23:
	add r0, r8, #40
25:
	ldrb r9, [r6, #0]
	ldrb r10, [r0, #0]
	eor r9, r9, r10
	strb r9, [r6, #0]
	add r0, r0, #1
	add r6, r6, #1
	subs r7, r7, #1
	bne 25b
24:
	bne 22b
	b 21f
20:
21:
	ldr r9, [r8, #40]
	str r9, [r5, #0]
	ldr r9, [r8, #44]
	str r9, [r5, #4]
	ldr r4, [r8, #0]
	ldr r5, [r8, #4]
	ldr r6, [r8, #8]
	ldr r7, [r8, #12]
	ldr r9, [r8, #20]
	ldr r10, [r8, #24]
	ldr r11, [r8, #28]
	ldr lr, [r8, #32]
	ldr r8, [r8, #16]
	add sp, sp, #328
	sub sp, sp, #336
	add r12, sp, #0
	mov r2, #0
	mov r3, #10
26:
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
	bne 26b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	add sp, sp, #336
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
