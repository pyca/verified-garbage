// The functions of `src/triple_des_cfb.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_triple_des_cfb64_encrypt:
	sub sp, sp, #64
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
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
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r8, r12
	ldr r9, [r5, #0]
	str r9, [r8, #40]
	ldr r9, [r5, #4]
	str r9, [r8, #44]
	cmp r7, #0
	beq 20f
22:
	mov r0, r4
	add r1, r8, #40
	mov r2, #1
	bl {vg_triple_des_ecb_encrypt}
	ldr r9, [r6, #0]
	ldr r10, [r8, #40]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #44]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r6, #0]
	str r9, [r8, #40]
	ldr r9, [r6, #4]
	str r9, [r8, #44]
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
	add r12, sp, #8
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	add sp, sp, #64
	bx lr

vg_triple_des_cfb64_decrypt:
	sub sp, sp, #64
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
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
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r8, r12
	ldr r9, [r5, #0]
	str r9, [r8, #40]
	ldr r9, [r5, #4]
	str r9, [r8, #44]
	cmp r7, #0
	beq 20f
22:
	ldr r9, [r6, #0]
	str r9, [r8, #48]
	ldr r9, [r6, #4]
	str r9, [r8, #52]
	mov r0, r4
	add r1, r8, #40
	mov r2, #1
	bl {vg_triple_des_ecb_encrypt}
	ldr r9, [r6, #0]
	ldr r10, [r8, #40]
	eor r9, r9, r10
	str r9, [r6, #0]
	ldr r9, [r6, #4]
	ldr r10, [r8, #44]
	eor r9, r9, r10
	str r9, [r6, #4]
	ldr r9, [r8, #48]
	str r9, [r8, #40]
	ldr r9, [r8, #52]
	str r9, [r8, #44]
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
	add r12, sp, #8
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	add sp, sp, #64
	bx lr
