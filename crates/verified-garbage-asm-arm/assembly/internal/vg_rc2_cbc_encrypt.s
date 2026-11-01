// The functions of `src/internal/vg_rc2_cbc_encrypt.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_encrypt:
	ldr r12, [sp, #0]
	str r4, [r12, #264]
	str r5, [r12, #268]
	str r6, [r12, #272]
	str r7, [r12, #276]
	str lr, [r12, #280]
	mov r4, r1
	mov r5, r3
	mov r1, r2
	mov r2, r12
	cmp r5, #0
	beq 20f
22:
	ldr r12, [r1, #0]
	ldr r3, [r1, #4]
	ldr r6, [r4, #0]
	ldr r7, [r4, #4]
	eor r12, r12, r6
	eor r3, r3, r7
	str r12, [r1, #0]
	str r3, [r1, #4]
	bl {vg_rc2_encrypt_block}
	ldr r12, [r1, #0]
	ldr r3, [r1, #4]
	str r12, [r4, #0]
	str r3, [r4, #4]
	add r1, r1, #8
	sub r5, r5, #1
	cmp r5, #0
	bne 22b
	b 21f
20:
21:
	ldr r4, [r2, #264]
	ldr r5, [r2, #268]
	ldr r6, [r2, #272]
	ldr r7, [r2, #276]
	ldr lr, [r2, #280]
	bx lr
