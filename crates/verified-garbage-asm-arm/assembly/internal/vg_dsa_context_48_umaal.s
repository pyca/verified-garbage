// The functions of `src/internal/vg_dsa_context_48_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_context_48_umaal:
	mov r12, r0
	str r4, [r12, #3784]
	str r5, [r12, #3788]
	str r6, [r12, #3792]
	str r7, [r12, #3796]
	str r8, [r12, #3800]
	str r9, [r12, #3804]
	str r10, [r12, #3808]
	str lr, [r12, #3812]
	movw r1, #256
	add r1, r12, r1
	ldr r5, [r1, #0]
	movw r6, #65535
	and r5, r5, r6
	mov r7, r5
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mul r4, r5, r7
	movw r2, #2
	sub r4, r2, r4
	mul r7, r7, r4
	mov r4, #0
	sub r4, r4, r7
	and r4, r4, r6
	str r4, [r12, #0]
	movw r10, #2608
	add r10, r12, r10
	movw r9, #2992
	add r9, r12, r9
	mov r7, #0
20:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 20b
	movw r10, #2608
	add r10, r12, r10
	mov r4, #1
	str r4, [r10, #0]
	ldr r4, [r12, #636]
	lsr r4, r4, #31
	cmp r4, #0
	bne 21f
	ldr r4, [r12, #632]
	lsr r4, r4, #31
	cmp r4, #0
	bne 23f
	ldr r4, [r12, #624]
	lsr r4, r4, #31
	cmp r4, #0
	bne 25f
	movw r10, #3000
	add r10, r12, r10
	movw r9, #3384
	add r9, r12, r9
	mov r7, #0
27:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 27b
	movw r10, #3000
	add r10, r12, r10
	mov r4, #1
	str r4, [r10, #0]
	movw lr, #3120
	b 26f
25:
	movw r10, #3000
	add r10, r12, r10
	movw r9, #3384
	add r9, r12, r9
	mov r7, #0
28:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 28b
	movw r10, #3000
	add r10, r12, r10
	mov r4, #1
	lsl r4, r4, #31
	str r4, [r10, #368]
	movw lr, #145
26:
	b 24f
23:
	movw r10, #3000
	add r10, r12, r10
	movw r9, #3384
	add r9, r12, r9
	mov r7, #0
29:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 29b
	movw r10, #3000
	add r10, r12, r10
	mov r4, #1
	lsl r4, r4, #31
	str r4, [r10, #376]
	movw lr, #81
24:
	b 22f
21:
	movw r10, #3000
	add r10, r12, r10
	movw r9, #3384
	add r9, r12, r9
	mov r7, #0
210:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 210b
	movw r10, #3000
	add r10, r12, r10
	mov r4, #1
	lsl r4, r4, #31
	str r4, [r10, #380]
	movw lr, #49
22:
211:
	movw r6, #65535
	mov r3, #0
	movw r10, #3000
	add r10, r12, r10
	movw r0, #3000
	add r0, r12, r0
	movw r8, #1040
	add r8, r12, r8
	movw r9, #3384
	add r9, r12, r9
212:
	ldr r7, [r10, #0]
	ldr r2, [r0, #0]
	and r4, r7, r6
	and r5, r2, r6
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #0]
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r2, #16
	add r4, r4, r5
	add r4, r4, r3
	and r5, r4, r6
	str r5, [r8, #4]
	lsr r3, r4, #16
	add r10, r10, #4
	add r0, r0, #4
	add r8, r8, #8
	cmp r10, r9
	bne 212b
	str r3, [r8, #0]
	movw r6, #65535
	mov r3, #1
	movw r10, #1040
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #648
	add r8, r12, r8
	movw r9, #640
	add r9, r12, r9
213:
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
	bne 213b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1040
	add r10, r12, r10
	movw r8, #648
	add r8, r12, r8
	movw r1, #3000
	add r1, r12, r1
	movw r9, #1032
	add r9, r12, r9
214:
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
	bne 214b
	subs lr, lr, #1
	bne 211b
	mov lr, #6
215:
	movw r10, #1040
	add r10, r12, r10
	movw r9, #1816
	add r9, r12, r9
	mov r7, #0
216:
	str r7, [r10, #0]
	add r10, r10, #4
	cmp r10, r9
	bne 216b
	movw r5, #256
	add r5, r12, r5
	ldr r5, [r5, #0]
	ldr r4, [r12, #0]
	mul r6, r5, r4
	add r6, r6, #2
	mul r6, r6, r4
	mov r4, #0
	movw r0, #1040
	add r0, r12, r0
	movw r1, #3000
	add r1, r12, r1
217:
	ldr r2, [r1, #0]
	mov r3, #0
	mov r10, r0
	movw r8, #3000
	add r8, r12, r8
	movw r9, #3384
	add r9, r12, r9
218:
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
	bne 218b
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
	movw r9, #640
	add r9, r12, r9
219:
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
	bne 219b
	ldr r5, [r10, #0]
	umaal r5, r3, r4, r4
	str r5, [r10, #0]
	ldr r7, [r10, #4]
	add r7, r7, r3
	str r7, [r10, #4]
	add r0, r0, #4
	add r1, r1, #4
	movw r9, #3384
	add r9, r12, r9
	cmp r1, r9
	bne 217b
	mov r3, #1
	mov r2, #1
	movw r10, #1424
	add r10, r12, r10
	movw r1, #256
	add r1, r12, r1
	movw r8, #648
	add r8, r12, r8
	movw r9, #640
	add r9, r12, r9
220:
	ldr r7, [r1, #0]
	mvn r7, r7
	ldr r5, [r10, #0]
	umaal r5, r3, r7, r2
	str r5, [r8, #0]
	add r10, r10, #4
	add r1, r1, #4
	add r8, r8, #4
	cmp r1, r9
	bne 220b
	ldr r5, [r10, #0]
	add r3, r3, r5
	mov r4, #0
	sub r3, r4, r3
	movw r10, #1424
	add r10, r12, r10
	movw r8, #648
	add r8, r12, r8
	movw r1, #3000
	add r1, r12, r1
	movw r9, #1808
	add r9, r12, r9
221:
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
	bne 221b
	subs lr, lr, #1
	bne 215b
	ldr r4, [r12, #3784]
	ldr r5, [r12, #3788]
	ldr r6, [r12, #3792]
	ldr r7, [r12, #3796]
	ldr r8, [r12, #3800]
	ldr r9, [r12, #3804]
	ldr r10, [r12, #3808]
	ldr lr, [r12, #3812]
	bx lr
