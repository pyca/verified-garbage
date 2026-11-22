// The functions of `src/internal/vg_miller_rabin_round.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_miller_rabin_round:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #9
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #9
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
20:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 20b
	mov r0, #11
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #12
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
21:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 21b
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #5
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
22:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 22b
	mov r1, #14
	str r1, [r8, #140]
23:
	ldr r0, [sp, #0]
	sub sp, sp, #8
	mov r2, #6
	mov r3, #6
	mov lr, #5
	add r12, sp, #0
	str lr, [r12, #0]
	ldr r1, [r0, #48]
	add r1, r1, #6
	lsl r1, r1, #3
	bl {vg_rsa_mont_mul}
	add sp, sp, #8
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	ldr lr, [r8, #140]
	mov r0, #27
	sub r0, r0, lr
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #6
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #6
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
24:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 24b
	ldr r1, [r8, #140]
	subs r1, r1, #1
	str r1, [r8, #140]
	bne 23b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
25:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 25b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
26:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 26b
	mov r1, #0
	str r1, [r8, #136]
	lsl r1, r9, #3
	sub r1, r1, #16
	str r1, [r8, #140]
27:
	ldr r1, [r8, #140]
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	lsr r1, r1, #3
	sub r1, r1, #1
	add r0, r0, r1, lsl #2
	ldr r2, [r0, #0]
	str r2, [r8, #116]
28:
	mov r1, #0
	str r1, [r8, #148]
	mov r1, #4
	str r1, [r8, #144]
29:
	ldr r0, [sp, #0]
	sub sp, sp, #8
	mov r2, #6
	mov r3, #6
	mov lr, #6
	add r12, sp, #0
	str lr, [r12, #0]
	ldr r1, [r0, #48]
	add r1, r1, #6
	lsl r1, r1, #3
	bl {vg_rsa_mont_mul}
	add sp, sp, #8
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #8
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
210:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 210b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #92]
	ldr r1, [r8, #144]
	ldr r2, [r8, #148]
	sub r2, r2, r1
	lsr r2, r2, #31
	ldr r3, [r8, #92]
	and r3, r3, r2
	ldr r4, [r8, #136]
	orr r4, r4, r3
	str r4, [r8, #136]
	subs r1, r1, #1
	str r1, [r8, #144]
	bne 29b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #11
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #11
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
211:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 211b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #1
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #12
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
212:
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
	bne 212b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #13
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
213:
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
	bne 213b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #3
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #14
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
214:
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
	bne 214b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #4
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #15
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
215:
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
	bne 215b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #5
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #16
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
216:
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
	bne 216b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #6
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #17
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
217:
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
	bne 217b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #7
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #18
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
218:
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
	bne 218b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #8
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #19
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
219:
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
	bne 219b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #9
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #20
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
220:
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
	bne 220b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #10
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #21
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
221:
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
	bne 221b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #11
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #22
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
222:
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
	bne 222b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #12
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #23
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
223:
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
	bne 223b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #13
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #24
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
224:
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
	bne 224b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #14
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #5
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #25
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
225:
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
	bne 225b
	ldr r1, [r8, #116]
	lsr r1, r1, #28
	eor r1, r1, #15
	sub r1, r1, #1
	lsr r1, r1, #31
	str r1, [r8, #88]
	mov r0, #5
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #8
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #26
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	ldr r11, [r8, #88]
	mov r4, #0
	sub r4, r4, r11
226:
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
	bne 226b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r10, #10
	mla r10, r10, r7, r8
	add r10, r10, #160
	mov r12, #10
	mla r12, r12, r7, r8
	add r12, r12, #160
	mov lr, r9
	mov r11, #0
	mov r4, #0
	sub r4, r4, r11
227:
	ldr r1, [r10, #0]
	str r1, [r0, #0]
	add r10, r10, #4
	add r0, r0, #4
	add r12, r12, #4
	subs lr, lr, #1
	bne 227b
	mov r0, #8
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	ldr r0, [sp, #0]
	sub sp, sp, #8
	mov r2, #6
	mov r3, #6
	mov lr, #5
	add r12, sp, #0
	str lr, [r12, #0]
	ldr r1, [r0, #48]
	add r1, r1, #6
	lsl r1, r1, #3
	bl {vg_rsa_mont_mul}
	add sp, sp, #8
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #11
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
228:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 228b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #88]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #8
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
229:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 229b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #92]
	ldr r1, [r8, #116]
	lsr r2, r1, #28
	sub r2, r2, #1
	lsr r2, r2, #31
	eor r3, r2, #1
	ldr r4, [r8, #88]
	ldr r5, [r8, #92]
	orr r4, r4, r5
	and r4, r4, r3
	ldr r5, [r8, #136]
	and r5, r5, r2
	orr r4, r4, r5
	str r4, [r8, #136]
	lsl r1, r1, #4
	str r1, [r8, #116]
	ldr r1, [r8, #140]
	sub r1, r1, #1
	str r1, [r8, #140]
	and r1, r1, #7
	cmp r1, #0
	bne 28b
	ldr r1, [r8, #140]
	cmp r1, #0
	bne 27b
	mov r0, #27
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	ldr r1, [r0, #0]
	ldr r2, [r0, #4]
	orr r1, r1, r2
	orr r1, r1, r1, lsr #16
	orr r1, r1, r1, lsr #8
	orr r1, r1, r1, lsr #4
	lsr r2, r1, #1
	and r2, r2, #1
	lsr r3, r1, #2
	and r3, r3, #1
	lsr r4, r1, #3
	and r4, r4, #1
	add r4, r4, r2
	add r4, r4, r2, lsl #1
	add r4, r4, r3, lsl #1
	str r4, [r8, #148]
	mov r1, #3
	str r1, [r8, #144]
230:
	ldr r0, [sp, #0]
	sub sp, sp, #8
	mov r2, #6
	mov r3, #6
	mov lr, #6
	add r12, sp, #0
	str lr, [r12, #0]
	ldr r1, [r0, #48]
	add r1, r1, #6
	lsl r1, r1, #3
	bl {vg_rsa_mont_mul}
	add sp, sp, #8
	ldr r0, [sp, #0]
	add r8, r0, #96
	ldr r9, [r0, #48]
	lsl r9, r9, #1
	add r9, r9, #2
	add r7, r9, #2
	lsl r7, r7, #2
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	add r0, r0, r9, lsl #2
	sub r0, r0, #8
	mov r1, #0
	str r1, [r0, #0]
	str r1, [r0, #4]
	mov r0, #6
	mla r0, r0, r7, r8
	add r0, r0, #160
	mov r1, #8
	mla r1, r1, r7, r8
	add r1, r1, #160
	mov lr, r9
	mov r2, #0
231:
	ldr r3, [r0, #0]
	ldr r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #4
	add r1, r1, #4
	subs lr, lr, #1
	bne 231b
	mov r1, #0
	sub r1, r1, r2
	orr r1, r1, r2
	lsr r1, r1, #31
	eor r1, r1, #1
	str r1, [r8, #92]
	ldr r1, [r8, #144]
	ldr r2, [r8, #148]
	sub r2, r2, r1
	lsr r2, r2, #31
	ldr r3, [r8, #92]
	and r3, r3, r2
	ldr r4, [r8, #136]
	orr r4, r4, r3
	str r4, [r8, #136]
	subs r1, r1, #1
	str r1, [r8, #144]
	bne 230b
	ldr r0, [r8, #136]
	ldr r4, [sp, #16]
	ldr r5, [sp, #20]
	ldr r6, [sp, #24]
	ldr r7, [sp, #28]
	ldr r8, [sp, #32]
	ldr r9, [sp, #36]
	ldr r10, [sp, #40]
	ldr r11, [sp, #44]
	ldr lr, [sp, #52]
	ldr r12, [sp], #56
	bx lr
