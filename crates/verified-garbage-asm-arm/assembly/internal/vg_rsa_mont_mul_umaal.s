// The functions of `src/internal/vg_rsa_mont_mul_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_mont_mul_umaal:
	push {r0, r4, r5, r6, r7, r8, r9, r10, r11, lr}
	ldr r12, [sp, #40]
	add r2, r0, r2, lsl #3
	ldr r10, [r2, #64]
	add r3, r0, r3, lsl #3
	ldr r8, [r3, #64]
	add r12, r0, r12, lsl #3
	ldr r9, [r12, #64]
	ldr r5, [r0, #88]
	ldr r6, [r0, #80]
	ldr r7, [r0, #48]
	add r7, r7, r7
	ldr r11, [r0, #64]
	ldr r12, [r0, #56]
	str r7, [r5, #0]
	str r9, [r5, #4]
	str r11, [r5, #8]
	str r12, [r5, #12]
	str r8, [r5, #16]
	str r7, [r5, #20]
	str r10, [r5, #24]
	str r6, [r5, #28]
	mov r0, r6
	mov lr, r7
	add lr, lr, #2
	mov r3, #0
20:
	str r3, [r0, #0]
	add r0, r0, #4
	subs lr, lr, #1
	bne 20b
	mov r0, r5
21:
	ldr r3, [r0, #16]
	ldr r1, [r3, #0]
	ldr r9, [r3, #4]
	ldr lr, [r0, #0]
	ldr r12, [r0, #4]
	ldr r4, [r0, #8]
	ldr r2, [r0, #12]
	mov r10, r2
	ldr r0, [r0, #28]
	mov r7, #0
	mov r8, #0
	mov r5, #0
	mov r11, #0
	ldr r6, [r0, #0]
	ldr r3, [r12, #0]
	umaal r6, r7, r3, r1
	mul r2, r2, r6
	ldr r3, [r4, #0]
	umaal r6, r8, r3, r2
	ldr r6, [r0, #4]
	ldr r3, [r12, #4]
	umaal r6, r7, r3, r1
	ldr r3, [r4, #4]
	umaal r6, r8, r3, r2
	ldr r3, [r12, #0]
	umaal r6, r5, r3, r9
	mul r10, r10, r6
	ldr r3, [r4, #0]
	umaal r6, r11, r3, r10
	sub lr, lr, #2
22:
	ldr r6, [r0, #8]
	ldr r3, [r12, #8]
	umaal r6, r7, r3, r1
	ldr r3, [r4, #8]
	umaal r6, r8, r3, r2
	ldr r3, [r12, #4]
	umaal r6, r5, r3, r9
	ldr r3, [r4, #4]
	umaal r6, r11, r3, r10
	str r6, [r0, #0]
	ldr r6, [r0, #12]
	ldr r3, [r12, #12]
	umaal r6, r7, r3, r1
	ldr r3, [r4, #12]
	umaal r6, r8, r3, r2
	ldr r3, [r12, #8]
	umaal r6, r5, r3, r9
	ldr r3, [r4, #8]
	umaal r6, r11, r3, r10
	str r6, [r0, #4]
	add r0, r0, #8
	add r12, r12, #8
	add r4, r4, #8
	subs lr, lr, #2
	bne 22b
	ldr r1, [r12, #4]
	ldr r2, [r4, #4]
	ldr r3, [r0, #8]
	ldr r4, [r0, #12]
	adds r3, r3, r7
	adc r4, r4, #0
	adds r3, r3, r8
	adc r4, r4, #0
	umaal r3, r5, r1, r9
	umaal r3, r11, r2, r10
	str r3, [r0, #0]
	mov r3, r4
	mov r4, #0
	adds r3, r3, r5
	adc r4, r4, #0
	adds r3, r3, r11
	adc r4, r4, #0
	str r3, [r0, #4]
	str r4, [r0, #8]
	add r0, r0, #12
	mov r3, #0
	str r3, [r0, #0]
	add r0, r0, #12
	ldr r4, [r0, #16]
	add r4, r4, #8
	str r4, [r0, #16]
	ldr lr, [r0, #20]
	subs lr, lr, #2
	str lr, [r0, #20]
	bne 21b
	ldr r7, [r0, #0]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	ldr r12, [r0, #8]
	mov lr, r7
	mov r11, #0
23:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	subs r3, r1, r2
	mov r4, #1
	adc r4, r4, #0
	subs r3, r3, r11
	adc r4, r4, #0
	eor r11, r4, #3
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 23b
	ldr r1, [r10, #0]
	mov r2, r11
	subs r3, r1, r2
	mov r11, #0
	adc r11, r11, #0
	eor r11, r11, #1
	mov r12, r10
	mov r10, r0
	sub r12, r12, r7, lsl #2
	sub r10, r10, r7, lsl #2
	mov r0, r9
	mov lr, r7
	mov r4, #0
	sub r4, r4, r11
24:
	ldr r1, [r10, #0]
	ldr r2, [r12, #0]
	eor r3, r1, r2
	and r3, r3, r4
	eor r3, r3, r1
	str r3, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 24b
	ldr r4, [sp, #4]
	ldr r5, [sp, #8]
	ldr r6, [sp, #12]
	ldr r7, [sp, #16]
	ldr r8, [sp, #20]
	ldr r9, [sp, #24]
	ldr r10, [sp, #28]
	ldr r11, [sp, #32]
	ldr lr, [sp, #36]
	ldr r12, [sp], #40
	bx lr
