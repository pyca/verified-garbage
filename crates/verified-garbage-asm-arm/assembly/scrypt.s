// The functions of `src/scrypt.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt:
	ldr r12, [sp, #20]
	str lr, [r12, #0]
	ldr lr, [sp, #0]
	add r12, r12, lr, lsl #7
	add r12, r12, #1920
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r8, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	ldr lr, [sp, #20]
	ldr lr, [lr, #0]
	str lr, [r12, #32]
	mov r8, r0
	mov r9, r1
	ldr r6, [sp, #0]
	ldr r7, [sp, #20]
	ldr r4, [sp, #4]
	ldr r5, [sp, #8]
	add r5, r4, r5, lsl #7
	mov r10, #1
	mov r11, r4
	sub r12, r5, r4
	mov lr, r7
	push {r10, r11, r12, lr}
	bl {vg_pbkdf2_hmac_sha256_scratch}
	ldr r12, [sp], #16
20:
	mov r0, r4
	mov r1, r6
	ldr r2, [sp, #12]
	ldr r3, [sp, #16]
	mov r12, r7
	add lr, r6, #2
	push {r12, lr}
	bl {vg_scrypt_romix}
	ldr r12, [sp], #8
	add r4, r4, r6, lsl #7
	cmp r4, r5
	bne 20b
	mov r0, r8
	mov r1, r9
	ldr r2, [sp, #4]
	ldr r3, [sp, #8]
	lsl r3, r3, #7
	mov r10, #1
	ldr r11, [sp, #28]
	ldr r12, [sp, #32]
	mov lr, r7
	push {r10, r11, r12, lr}
	bl {vg_pbkdf2_hmac_sha256_scratch}
	ldr r12, [sp], #16
	add r12, r7, r6, lsl #7
	add r12, r12, #1920
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r8, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	bx lr
