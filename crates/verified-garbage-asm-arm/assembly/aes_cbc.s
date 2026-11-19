// The functions of `src/aes_cbc.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_encrypt:
	push {r4, r5, r6, lr}
	sub sp, sp, #8
	add r12, sp, #0
	ldr lr, [sp, #24]
	str lr, [r12, #0]
	ldr lr, [sp, #28]
	str lr, [r12, #4]
	ldr r4, [sp, #4]
	bl {vg_aes_cbc_encrypt_unwiped}
	add sp, sp, #8
	mov r5, r0
	mov r6, r1
	mov r0, r4
	movw r1, #2176
	movt r1, #0
	bl {vg_zeroize_core}
	mov r0, r5
	mov r1, r6
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	sub sp, sp, #32
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add sp, sp, #32
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_aes_cbc_decrypt:
	push {r4, r5, r6, lr}
	sub sp, sp, #8
	add r12, sp, #0
	ldr lr, [sp, #24]
	str lr, [r12, #0]
	ldr lr, [sp, #28]
	str lr, [r12, #4]
	ldr r4, [sp, #4]
	bl {vg_aes_cbc_decrypt_unwiped}
	add sp, sp, #8
	mov r5, r0
	mov r6, r1
	mov r0, r4
	movw r1, #2176
	movt r1, #0
	bl {vg_zeroize_core}
	mov r0, r5
	mov r1, r6
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	sub sp, sp, #32
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add sp, sp, #32
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
