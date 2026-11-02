// The functions of `src/internal/vg_dsa_mulmod_48.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_mulmod_48:
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
	movw r1, #620
	bl {vg_dsa_context_48}
	mov r12, r4
	movw r10, #1040
	add r10, r12, r10
	movw r9, #2584
	add r9, r12, r9
	mov r7, #0
20:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 20b
	movw r6, #65535
	movw r0, #1040
	add r0, r12, r0
	movw r1, #3392
	add r1, r12, r1
21:
	ldr r2, [r1, #0]
	and r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #3000
	add r8, r12, r8
	movw r9, #3384
	add r9, r12, r9
22:
	ldr r7, [r8, #0]
	and r4, r7, r6
	ldr r5, [r10, #0]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #0]
	lsr r3, r5, #16
	lsr r4, r7, #16
	ldr r5, [r10, #4]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #4]
	lsr r3, r5, #16
	add r10, r10, #8
	add r8, r8, #4
	cmp r8, r9
	bne 22b
	ldr r5, [r10, #0]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r5, lsr #16
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	ldr r4, [r12, #0]
	mul r2, r2, r4
	and r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #640
	add r9, r12, r9
23:
	ldr r7, [r8, #0]
	and r4, r7, r6
	ldr r5, [r10, #0]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #0]
	lsr r3, r5, #16
	lsr r4, r7, #16
	ldr r5, [r10, #4]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #4]
	lsr r3, r5, #16
	add r10, r10, #8
	add r8, r8, #4
	cmp r8, r9
	bne 23b
	ldr r5, [r10, #0]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r5, lsr #16
	str r7, [r10, #4]
	add r0, r0, #4
	ldr r2, [r1, #0]
	lsr r2, r2, #16
	mov r3, #0
	mov r10, r0
	movw r8, #3000
	add r8, r12, r8
	movw r9, #3384
	add r9, r12, r9
24:
	ldr r7, [r8, #0]
	and r4, r7, r6
	ldr r5, [r10, #0]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #0]
	lsr r3, r5, #16
	lsr r4, r7, #16
	ldr r5, [r10, #4]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #4]
	lsr r3, r5, #16
	add r10, r10, #8
	add r8, r8, #4
	cmp r8, r9
	bne 24b
	ldr r5, [r10, #0]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r5, lsr #16
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	ldr r4, [r12, #0]
	mul r2, r2, r4
	and r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #640
	add r9, r12, r9
25:
	ldr r7, [r8, #0]
	and r4, r7, r6
	ldr r5, [r10, #0]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #0]
	lsr r3, r5, #16
	lsr r4, r7, #16
	ldr r5, [r10, #4]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #4]
	lsr r3, r5, #16
	add r10, r10, #8
	add r8, r8, #4
	cmp r8, r9
	bne 25b
	ldr r5, [r10, #0]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r5, lsr #16
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #3776
	add r9, r12, r9
	cmp r1, r9
	bne 21b
	movw r6, #65535
	mov r3, #1
	movw r10, #1808
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #648
	add r8, r12, r8
	movw r9, #640
	add r9, r12, r9
26:
	ldr r7, [r1, #0]
	ldr r5, [r10, #0]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r2, r5, r6
	ldr r5, [r10, #4]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r2, r2, r5, lsl #16
	str r2, [r8, #0]
	add r10, r10, #8
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 26b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1808
	add r10, r12, r10
	movw r8, #648
	add r8, r12, r8
	movw r1, #4176
	add r1, r12, r1
	movw r9, #1032
	add r9, r12, r9
27:
	ldr r5, [r10, #0]
	ldr r7, [r10, #4]
	orr r5, r5, r7, lsl #16
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #8
	add r8, r8, #4
	add r1, r1, #4
	cmp r8, r9
	bne 27b
	movw r10, #1040
	add r10, r12, r10
	movw r9, #2584
	add r9, r12, r9
	mov r7, #0
28:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 28b
	movw r6, #65535
	movw r0, #1040
	add r0, r12, r0
	movw r1, #4568
	add r1, r12, r1
29:
	ldr r2, [r1, #0]
	and r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #4176
	add r8, r12, r8
	movw r9, #4560
	add r9, r12, r9
210:
	ldr r7, [r8, #0]
	and r4, r7, r6
	ldr r5, [r10, #0]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #0]
	lsr r3, r5, #16
	lsr r4, r7, #16
	ldr r5, [r10, #4]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #4]
	lsr r3, r5, #16
	add r10, r10, #8
	add r8, r8, #4
	cmp r8, r9
	bne 210b
	ldr r5, [r10, #0]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r5, lsr #16
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	ldr r4, [r12, #0]
	mul r2, r2, r4
	and r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #640
	add r9, r12, r9
211:
	ldr r7, [r8, #0]
	and r4, r7, r6
	ldr r5, [r10, #0]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #0]
	lsr r3, r5, #16
	lsr r4, r7, #16
	ldr r5, [r10, #4]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #4]
	lsr r3, r5, #16
	add r10, r10, #8
	add r8, r8, #4
	cmp r8, r9
	bne 211b
	ldr r5, [r10, #0]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r5, lsr #16
	str r7, [r10, #4]
	add r0, r0, #4
	ldr r2, [r1, #0]
	lsr r2, r2, #16
	mov r3, #0
	mov r10, r0
	movw r8, #4176
	add r8, r12, r8
	movw r9, #4560
	add r9, r12, r9
212:
	ldr r7, [r8, #0]
	and r4, r7, r6
	ldr r5, [r10, #0]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #0]
	lsr r3, r5, #16
	lsr r4, r7, #16
	ldr r5, [r10, #4]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #4]
	lsr r3, r5, #16
	add r10, r10, #8
	add r8, r8, #4
	cmp r8, r9
	bne 212b
	ldr r5, [r10, #0]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r5, lsr #16
	str r7, [r10, #4]
	ldr r2, [r0, #0]
	ldr r4, [r12, #0]
	mul r2, r2, r4
	and r2, r2, r6
	mov r3, #0
	mov r10, r0
	movw r8, #256
	add r8, r12, r8
	movw r9, #640
	add r9, r12, r9
213:
	ldr r7, [r8, #0]
	and r4, r7, r6
	ldr r5, [r10, #0]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #0]
	lsr r3, r5, #16
	lsr r4, r7, #16
	ldr r5, [r10, #4]
	mla r5, r2, r4, r5
	add r5, r5, r3
	and r4, r5, r6
	str r4, [r10, #4]
	lsr r3, r5, #16
	add r10, r10, #8
	add r8, r8, #4
	cmp r8, r9
	bne 213b
	ldr r5, [r10, #0]
	add r5, r5, r3
	and r7, r5, r6
	str r7, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r5, lsr #16
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #4952
	add r9, r12, r9
	cmp r1, r9
	bne 29b
	movw r6, #65535
	mov r3, #1
	movw r10, #1808
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #648
	add r8, r12, r8
	movw r9, #640
	add r9, r12, r9
214:
	ldr r7, [r1, #0]
	ldr r5, [r10, #0]
	and r4, r7, r6
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	and r2, r5, r6
	ldr r5, [r10, #4]
	lsr r4, r7, #16
	add r5, r5, r6
	sub r5, r5, r4
	add r5, r5, r3
	lsr r3, r5, #16
	orr r2, r2, r5, lsl #16
	str r2, [r8, #0]
	add r10, r10, #8
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 214b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1808
	add r10, r12, r10
	movw r8, #648
	add r8, r12, r8
	movw r1, #3784
	add r1, r12, r1
	movw r9, #1032
	add r9, r12, r9
215:
	ldr r5, [r10, #0]
	ldr r7, [r10, #4]
	orr r5, r5, r7, lsl #16
	ldr r7, [r8, #0]
	eor r7, r7, r5
	and r7, r7, r3
	eor r5, r5, r7
	str r5, [r1, #0]
	add r10, r10, #8
	add r8, r8, #4
	add r1, r1, #4
	cmp r8, r9
	bne 215b
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
