// The functions of `src/mlkem768.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_keygen:
	push {r4, r5, r6, lr}
	mov r4, r3
	bl {vg_mlkem768_keygen_body}
	mov r5, r0
	mov r6, r1
	mov r0, r4
	movw r1, #32768
	movt r1, #0
	bl {vg_zeroize}
	mov r0, r5
	mov r1, r6
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	bx lr

vg_mlkem768_encaps:
	push {r4, r5, r6, lr}
	sub sp, sp, #8
	add r12, sp, #0
	ldr lr, [sp, #24]
	str lr, [r12, #0]
	ldr r4, [sp, #0]
	bl {vg_mlkem768_encaps_body}
	add sp, sp, #8
	mov r5, r0
	mov r6, r1
	mov r0, r4
	movw r1, #32768
	movt r1, #0
	bl {vg_zeroize}
	mov r0, r5
	mov r1, r6
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	bx lr

vg_mlkem768_encaps_h:
	push {r4, r5, r6, lr}
	sub sp, sp, #8
	add r12, sp, #0
	ldr lr, [sp, #24]
	str lr, [r12, #0]
	ldr lr, [sp, #28]
	str lr, [r12, #4]
	ldr r4, [sp, #4]
	bl {vg_mlkem768_encaps_h_body}
	add sp, sp, #8
	mov r5, r0
	mov r6, r1
	mov r0, r4
	movw r1, #32768
	movt r1, #0
	bl {vg_zeroize}
	mov r0, r5
	mov r1, r6
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	bx lr

vg_mlkem768_decaps:
	push {r4, r5, r6, lr}
	mov r4, r3
	bl {vg_mlkem768_decaps_body}
	mov r5, r0
	mov r6, r1
	mov r0, r4
	movw r1, #32768
	movt r1, #0
	bl {vg_zeroize}
	mov r0, r5
	mov r1, r6
	ldr r5, [sp, #4]
	ldr r6, [sp, #8]
	ldr lr, [sp, #12]
	ldr r4, [sp], #16
	bx lr

vg_mlkem768_check_ek:
	mov r1, #384
	mov r2, #0
20:
	ldrb r3, [r0, #1]
	lsl r3, r3, #28
	lsr r3, r3, #20
	ldrb r12, [r0, #0]
	add r3, r3, r12
	mov r12, #3328
	sub r12, r12, r3
	add r2, r2, r12, lsr #31
	ldrb r3, [r0, #1]
	lsr r3, r3, #4
	ldrb r12, [r0, #2]
	add r3, r3, r12, lsl #4
	mov r12, #3328
	sub r12, r12, r3
	add r2, r2, r12, lsr #31
	add r0, r0, #3
	subs r1, r1, #1
	bne 20b
	mov r3, #0
	sub r3, r3, r2
	lsr r3, r3, #31
	mov r0, #1
	sub r0, r0, r3
	bx lr
