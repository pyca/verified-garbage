// The functions of `src/aes_ecb.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ecb_encrypt:
	push {r4, r5, r6, lr}
	sub sp, sp, #8
	add r12, sp, #0
	ldr lr, [sp, #24]
	str lr, [r12, #0]
	ldr r4, [sp, #0]
	bl {vg_aes_encrypt_blocks}
	add sp, sp, #8
	mov r5, r0
	mov r6, r1
	mov r0, r4
	movw r1, #2048
	movt r1, #0
	bl {vg_zeroize}
	mov r0, r5
	mov r1, r6
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	bx lr

vg_aes_ecb_decrypt:
	push {r4, r5, r6, lr}
	sub sp, sp, #8
	add r12, sp, #0
	ldr lr, [sp, #24]
	str lr, [r12, #0]
	ldr r4, [sp, #0]
	bl {vg_aes_decrypt_blocks}
	add sp, sp, #8
	mov r5, r0
	mov r6, r1
	mov r0, r4
	movw r1, #2048
	movt r1, #0
	bl {vg_zeroize}
	mov r0, r5
	mov r1, r6
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	bx lr
