// The functions of `src/internal/vg_camellia_ecb_keyed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ecb_keyed:
	ldr r12, [sp, #0]
	str r4, [r12, #2472]
	str r5, [r12, #2476]
	str r6, [r12, #2480]
	str r7, [r12, #2484]
	str r8, [r12, #2488]
	str r9, [r12, #2492]
	str r10, [r12, #2496]
	str r11, [r12, #2500]
	str lr, [r12, #2504]
	mov r8, r12
	cmp r1, #18
	mov r1, r2
	mov r2, r3
	beq 20f
	add lr, r8, #2336
	b 21f
20:
	add lr, r8, #1824
21:
	cmp r2, #0
	beq 22f
24:
	lsr r10, r2, #3
	cmp r10, #0
	bne 25f
	mov r3, r2
	b 26f
25:
	mov r3, #8
26:
	mov r0, r1
	add r12, r8, #2528
27:
	ldr r10, [r0, #0]
	str r10, [r12, #0]
	ldr r10, [r0, #4]
	str r10, [r12, #4]
	ldr r10, [r0, #8]
	str r10, [r12, #8]
	ldr r10, [r0, #12]
	str r10, [r12, #12]
	add r0, r0, #16
	add r12, r12, #16
	subs r3, r3, #1
	bne 27b
	str r1, [r8, #2508]
	str r2, [r8, #2512]
	str lr, [r8, #2468]
	bl {vg_camellia_crypt8}
	ldr r1, [r8, #2508]
	ldr r2, [r8, #2512]
	ldr lr, [r8, #2468]
	lsr r10, r2, #3
	cmp r10, #0
	bne 28f
	mov r3, r2
	b 29f
28:
	mov r3, #8
29:
	add r0, r8, #2528
	mov r12, r1
210:
	ldr r10, [r0, #0]
	str r10, [r12, #0]
	ldr r10, [r0, #4]
	str r10, [r12, #4]
	ldr r10, [r0, #8]
	str r10, [r12, #8]
	ldr r10, [r0, #12]
	str r10, [r12, #12]
	add r0, r0, #16
	add r12, r12, #16
	subs r3, r3, #1
	bne 210b
	lsr r10, r2, #3
	cmp r10, #0
	bne 211f
	mov r3, r2
	b 212f
211:
	mov r3, #8
212:
	add r1, r1, #128
	subs r2, r2, r3
	bne 24b
	b 23f
22:
23:
	mov r12, r8
	ldr r4, [r12, #2472]
	ldr r5, [r12, #2476]
	ldr r6, [r12, #2480]
	ldr r7, [r12, #2484]
	ldr r8, [r12, #2488]
	ldr r9, [r12, #2492]
	ldr r10, [r12, #2496]
	ldr r11, [r12, #2500]
	ldr lr, [r12, #2504]
	bx lr
