// The functions of `src/pbkdf2_sha224.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_sha224:
	sub sp, sp, #1632
	add r12, sp, #0
	str lr, [r12, #16]
	ldr lr, [sp, #1632]
	str lr, [r12, #0]
	ldr lr, [sp, #1636]
	str lr, [r12, #4]
	ldr lr, [sp, #1640]
	str lr, [r12, #8]
	add lr, sp, #20
	str lr, [r12, #12]
	ldr lr, [sp, #16]
	ldr r12, [sp, #12]
	str r4, [r12, #832]
	str r5, [r12, #836]
	str r6, [r12, #840]
	str r7, [r12, #844]
	str r8, [r12, #848]
	str r9, [r12, #852]
	str r10, [r12, #856]
	str lr, [r12, #860]
	str r11, [r12, #864]
	mov r11, r12
	mov r8, r0
	mov r9, r1
	mov r5, r2
	mov r6, r3
	subs r12, r9, #65
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 20f
	movw r12, #1156
	add r4, r11, r12
	mov r0, r4
	bl {vg_sha224_init}
	mov r0, r4
	mov r1, r8
	mov r7, r9
	mov r10, r11
	mov r2, #0
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_sha256_update_scratch}
	ldr r1, [sp], #16
	mov r0, r4
	movw r12, #1308
	add r1, r11, r12
	mov r12, r11
	mov r2, r9
	mov r3, #0
	push {r1, r12}
	bl {vg_sha256_finalize_scratch}
	ldr r1, [sp], #8
	movw r12, #1308
	add r2, r11, r12
	movw r3, #28
	b 21f
20:
	mov r2, r8
	mov r3, r9
21:
	movw r12, #868
	add r0, r11, r12
	movw r12, #964
	add r1, r11, r12
	mov r12, r11
	push {r12, lr}
	bl {vg_hmac_sha224_init_scratch}
	ldr r12, [sp], #8
	mov r8, #0
	movw r9, #96
22:
	add r2, r11, r8
	ldrb r12, [r2, #868]
	add r2, r11, r8
	strb r12, [r2, #1060]
	add r8, r8, #1
	subs r9, r9, #1
	bne 22b
	movw r12, #1060
	add r0, r11, r12
	mov r1, r5
	mov r7, r6
	mov r10, r11
	movw r2, #64
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_sha256_update_scratch}
	ldr r1, [sp], #16
	mov r12, #1
	rev r12, r12
	str r12, [r11, #1340]
	mov r4, #0
	ldr r12, [sp, #8]
	cmp r12, #0
	beq 23f
25:
	mov r8, #0
	movw r9, #96
26:
	add r2, r11, r8
	ldrb r12, [r2, #1060]
	add r2, r11, r8
	strb r12, [r2, #1156]
	add r8, r8, #1
	subs r9, r9, #1
	bne 26b
	movw r12, #1156
	add r0, r11, r12
	movw r12, #1340
	add r1, r11, r12
	mov r7, #4
	mov r10, r11
	add r2, r6, #64
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_sha256_update_scratch}
	ldr r1, [sp], #16
	movw r12, #1156
	add r0, r11, r12
	movw r12, #964
	add r1, r11, r12
	movw r12, #1252
	add r10, r11, r12
	mov r12, r11
	add r2, r6, #68
	mov r3, #0
	push {r10, r12}
	bl {vg_hmac_sha224_finalize_scratch}
	ldr r12, [sp], #8
	mov r8, #0
	movw r9, #28
27:
	add r2, r11, r8
	ldrb r12, [r2, #1252]
	add r2, r11, r8
	strb r12, [r2, #1280]
	add r8, r8, #1
	subs r9, r9, #1
	bne 27b
	movw r12, #868
	add r0, r11, r12
	movw r12, #1252
	add r1, r11, r12
	movw r12, #1280
	add r3, r11, r12
	ldr r2, [sp, #0]
	sub r2, r2, #1
	mov r12, r11
	push {r12, lr}
	bl {vg_pbkdf2_hmac_sha224_iterate}
	ldr r12, [sp], #8
	ldr r12, [sp, #8]
	sub r9, r12, r4
	subs r12, r9, #28
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 28f
	movw r9, #28
	b 29f
28:
29:
	ldr r10, [sp, #4]
	add r10, r10, r4
	mov r8, #0
210:
	add r2, r11, r8
	ldrb r12, [r2, #1280]
	add r2, r10, r8
	strb r12, [r2, #0]
	add r8, r8, #1
	subs r9, r9, #1
	bne 210b
	add r4, r4, r8
	ldr r12, [r11, #1340]
	rev r12, r12
	add r12, r12, #1
	rev r12, r12
	str r12, [r11, #1340]
	ldr r12, [sp, #8]
	cmp r4, r12
	bne 25b
	b 24f
23:
24:
	ldr r4, [r11, #832]
	ldr r5, [r11, #836]
	ldr r6, [r11, #840]
	ldr r7, [r11, #844]
	ldr r8, [r11, #848]
	ldr r9, [r11, #852]
	ldr r10, [r11, #856]
	ldr lr, [r11, #860]
	ldr r11, [r11, #864]
	add sp, sp, #1632
	bx lr
