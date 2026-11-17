// The functions of `src/internal/vg_dsa_mulmod_32_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_mulmod_32_umaal:
	mov r12, r0
	str r4, [r12, #8]
	str r5, [r12, #12]
	str r6, [r12, #16]
	str r7, [r12, #20]
	str r8, [r12, #24]
	str r9, [r12, #28]
	str r10, [r12, #32]
	str r11, [r12, #36]
	str lr, [r12, #40]
	mov r4, r12
	mov r0, r12
	movw r1, #428
	bl {vg_dsa_context_32_umaal}
	mov r12, r4
	movw r10, #784
	add r10, r12, r10
	movw r9, #1304
	add r9, r12, r9
	mov r7, #0
20:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 20b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #784
	add r0, r12, r0
	movw r1, #2368
	add r1, r12, r1
21:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #2104
	add r8, r12, r8
	movw r9, #2360
	add r9, r12, r9
22:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 22b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	mul r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #512
	add r9, r12, r9
23:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 23b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #2624
	add r9, r12, r9
	cmp r1, r9
	bne 21b
	mov r3, #1
	mov r2, #1
	movw r10, #1040
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #520
	add r8, r12, r8
	movw r9, #512
	add r9, r12, r9
24:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 24b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1040
	add r10, r12, r10
	movw r8, #520
	add r8, r12, r8
	movw r1, #2896
	add r1, r12, r1
	movw r9, #1296
	add r9, r12, r9
25:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 25b
	movw r10, #784
	add r10, r12, r10
	movw r9, #1304
	add r9, r12, r9
	mov r7, #0
26:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 26b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #784
	add r0, r12, r0
	movw r1, #3160
	add r1, r12, r1
27:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #2896
	add r8, r12, r8
	movw r9, #3152
	add r9, r12, r9
28:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 28b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	mul r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #512
	add r9, r12, r9
29:
	ldr r7, [r8, #0]
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r10, #0]
	ldr r7, [r8, #4]
	ldr r5, [r10, #4]
	umaal r5, r3, r7, r2
	str r5, [r10, #4]
	add r10, r10, #8
	add r8, r8, #8
	cmp r8, r9
	bne 29b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #3416
	add r9, r12, r9
	cmp r1, r9
	bne 27b
	mov r3, #1
	mov r2, #1
	movw r10, #1040
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #520
	add r8, r12, r8
	movw r9, #512
	add r9, r12, r9
210:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 210b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1040
	add r10, r12, r10
	movw r8, #520
	add r8, r12, r8
	movw r1, #2632
	add r1, r12, r1
	movw r9, #1296
	add r9, r12, r9
211:
	ldr r5, [r10, #0]
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #4
	add r8, r8, #4
	add r1, r1, #4
	cmp r10, r9
	bne 211b
	ldr r4, [r12, #8]
	ldr r5, [r12, #12]
	ldr r6, [r12, #16]
	ldr r7, [r12, #20]
	ldr r8, [r12, #24]
	ldr r9, [r12, #28]
	ldr r10, [r12, #32]
	ldr r11, [r12, #36]
	ldr lr, [r12, #40]
	bx lr
