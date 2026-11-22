// The functions of `src/internal/vg_sha512_digest_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha512_digest_core:
	sub sp, sp, #568
	add r3, sp, #0
	mov r12, r3
	str r4, [r12, #272]
	str r5, [r12, #276]
	str r6, [r12, #280]
	str r7, [r12, #284]
	str r8, [r12, #288]
	str r9, [r12, #292]
	str r10, [r12, #296]
	str lr, [r12, #300]
	str r11, [r12, #304]
	mov r11, r12
	mov r8, r0
	mov r9, r1
	mov r5, r2
	movw r12, #308
	add r4, r11, r12
	mov r0, r4
	bl {vg_sha512_init_core}
	mov r0, r4
	mov r1, r8
	mov r7, r9
	mov r10, r11
	mov r2, #0
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_sha512_update_scratch}
	ldr r1, [sp], #16
	mov r0, r4
	mov r2, r9
	mov r3, #0
	movw r12, #500
	add r1, r11, r12
	mov r12, r11
	push {r1, r12}
	bl {vg_sha512_finalize_scratch}
	ldr r1, [sp], #8
	mov r8, #0
	movw r9, #64
20:
	add r2, r11, r8
	ldrb r12, [r2, #500]
	add r2, r5, r8
	strb r12, [r2, #0]
	add r8, r8, #1
	subs r9, r9, #1
	bne 20b
	ldr r4, [r11, #272]
	ldr r5, [r11, #276]
	ldr r6, [r11, #280]
	ldr r7, [r11, #284]
	ldr r8, [r11, #288]
	ldr r9, [r11, #292]
	ldr r10, [r11, #296]
	ldr lr, [r11, #300]
	ldr r11, [r11, #304]
	add sp, sp, #568
	bx lr
