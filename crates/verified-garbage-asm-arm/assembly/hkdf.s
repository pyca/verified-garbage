// The functions of `src/hkdf.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hkdf_key:
	sub sp, sp, #3424
	add r12, sp, #0
	str lr, [r12, #3408]
	ldr lr, [r3, #0]
	mov r3, r1
	mov r1, r0
	mov r0, r2
	mov r2, r1
	add r1, r0, #192
	push {r12, lr}
	blx lr
	ldr r12, [sp], #8
	add r12, sp, #0
	ldr lr, [r12, #3408]
	add sp, sp, #3424
	sub sp, sp, #3456
	add r12, sp, #0
	mov r2, #0
	mov r3, #108
20:
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
	bne 20b
	add sp, sp, #3456
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_hkdf_extract:
	sub sp, sp, #3824
	add r12, sp, #0
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r10, [r12, #16]
	str lr, [r12, #20]
	mov r4, r2
	mov r7, r3
	ldr r6, [r12, #3824]
	ldr r5, [r12, #3832]
	mov r2, r0
	mov r3, r1
	add r0, r12, #32
	add r1, r12, #224
	add r12, r12, #416
	ldr lr, [r5, #0]
	push {r12, lr}
	blx lr
	ldr r12, [sp], #8
	add r12, sp, #0
	add r0, r12, #32
	mov r1, r4
	ldr r2, [r5, #20]
	mov r3, #0
	add r10, r12, #416
	ldr lr, [r5, #4]
	push {r1, r7, r10, r12}
	blx lr
	ldr r1, [sp], #16
	add r12, sp, #0
	add r0, r12, #32
	add r1, r12, #224
	ldr r2, [r5, #20]
	add r2, r2, r7
	mov r3, #0
	mov r10, r6
	add r12, r12, #416
	ldr lr, [r5, #8]
	push {r10, r12}
	blx lr
	ldr r12, [sp], #8
	add r12, sp, #0
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r10, [r12, #16]
	ldr lr, [r12, #20]
	add sp, sp, #3824
	sub sp, sp, #3856
	add r12, sp, #0
	mov r2, #0
	mov r3, #120
20:
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
	bne 20b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	add sp, sp, #3856
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_hkdf_expand:
	sub sp, sp, #2176
	add r12, sp, #0
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r8, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r8, r3
	ldr r9, [r12, #2176]
	ldr r11, [r12, #2180]
	mov r0, #1
	str r0, [r12, #40]
	mov r0, #0
	str r0, [r12, #44]
	cmp r9, #0
	beq 20f
22:
	add r12, sp, #0
	mov r1, r4
	add r2, r12, #112
	mov r3, #192
23:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 23b
	add r12, sp, #0
	add r0, r12, #112
	add r1, r12, #48
	ldr r7, [r12, #44]
	ldr r2, [r11, #20]
	mov r3, #0
	add r10, r12, #304
	ldr lr, [r11, #4]
	push {r1, r7, r10, r12}
	blx lr
	ldr r1, [sp], #16
	add r12, sp, #0
	add r0, r12, #112
	mov r1, r5
	mov r7, r6
	ldr r2, [r11, #20]
	ldr r3, [r12, #44]
	add r2, r2, r3
	mov r3, #0
	add r10, r12, #304
	ldr lr, [r11, #4]
	push {r1, r7, r10, r12}
	blx lr
	ldr r1, [sp], #16
	add r12, sp, #0
	add r0, r12, #112
	add r1, r12, #40
	mov r7, #1
	ldr r2, [r11, #20]
	ldr r3, [r12, #44]
	add r2, r2, r3
	add r2, r2, r6
	mov r3, #0
	add r10, r12, #304
	ldr lr, [r11, #4]
	push {r1, r7, r10, r12}
	blx lr
	ldr r1, [sp], #16
	add r12, sp, #0
	add r0, r12, #112
	add r1, r4, #192
	ldr r2, [r11, #20]
	ldr r3, [r12, #44]
	add r2, r2, r3
	add r2, r2, r6
	add r2, r2, #1
	mov r3, #0
	add r10, r12, #48
	add r12, r12, #304
	ldr lr, [r11, #8]
	push {r10, r12}
	blx lr
	ldr r12, [sp], #8
	add r12, sp, #0
	ldr r3, [r11, #16]
	subs r0, r3, r9
	mov r1, #0
	adc r1, r1, #0
	sub r1, r1, #1
	and r0, r0, r1
	add r3, r9, r0
	mov r7, r3
	add r1, r12, #48
	mov r2, r8
24:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 24b
	add r12, sp, #0
	add r8, r8, r7
	sub r9, r9, r7
	ldr r0, [r11, #16]
	str r0, [r12, #44]
	ldr r0, [r12, #40]
	add r0, r0, #1
	str r0, [r12, #40]
	cmp r9, #0
	bne 22b
	b 21f
20:
21:
	add r12, sp, #0
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r8, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	add sp, sp, #2176
	sub sp, sp, #2208
	add r12, sp, #0
	mov r2, #0
	mov r3, #69
25:
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
	bne 25b
	add sp, sp, #2208
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
