// The functions of `src/internal/vg_rc2_expand_key.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_expand_key:
	ldr r12, [sp, #0]
	str r8, [r12, #0]
	str r4, [r12, #4]
	str r5, [r12, #8]
	str r6, [r12, #12]
	str r7, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	mov r8, r12
	mov r4, r0
	mov r5, r1
	mov r6, r3
	mov r7, r2
	movw r0, #0
20:
	add lr, r4, r0
	ldrb r12, [lr, #0]
	add lr, r6, r0
	strb r12, [lr, #0]
	add r0, r0, #1
	cmp r0, r5
	bne 20b
	cmp r0, #128
	bne 21f
	b 22f
21:
23:
	add lr, r6, r0
	sub lr, lr, #1
	ldrb r12, [lr, #0]
	sub r9, r0, r5
	add lr, r6, r9
	ldrb r3, [lr, #0]
	add r12, r12, r3
	lsl r12, r12, #24
	lsr r12, r12, #24
	movw r3, #0
	movw lr, #:lower16:({VG_RC2_PITABLE}
	movt lr, #:upper16:({VG_RC2_PITABLE}
2:
	add lr, pc
3:
	mov r9, #0
24:
	ldr r10, [lr, #0]
	eor r11, r12, r9
	sub r11, r11, #4
	lsr r11, r11, #8
	orr r11, r11, r11, lsl #8
	and r10, r10, r11
	orr r3, r3, r10
	add lr, lr, #4
	cmp r9, #252
	add r9, r9, #4
	bne 24b
	and lr, r12, #3
	sub r10, lr, #1
	lsr r10, r10, #8
	and r12, r10, r3
	eor r10, lr, #1
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #8
	orr r12, r12, r10
	eor r10, lr, #2
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #16
	orr r12, r12, r10
	eor r10, lr, #3
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #24
	orr r12, r12, r10
	and r12, r12, #255
	add lr, r6, r0
	strb r12, [lr, #0]
	add r0, r0, #1
	cmp r0, #128
	bne 23b
22:
	add r1, r7, #7
	lsr r1, r1, #3
	movw r0, #128
	sub r0, r0, r1
	mov r9, r7
	lsl r9, r9, #29
	lsr r9, r9, #29
	movw r2, #255
	cmp r9, #1
	beq 25f
	b 26f
25:
	movw r2, #1
26:
	cmp r9, #2
	beq 27f
	b 28f
27:
	movw r2, #3
28:
	cmp r9, #3
	beq 29f
	b 210f
29:
	movw r2, #7
210:
	cmp r9, #4
	beq 211f
	b 212f
211:
	movw r2, #15
212:
	cmp r9, #5
	beq 213f
	b 214f
213:
	movw r2, #31
214:
	cmp r9, #6
	beq 215f
	b 216f
215:
	movw r2, #63
216:
	cmp r9, #7
	beq 217f
	b 218f
217:
	movw r2, #127
218:
	add lr, r6, r0
	ldrb r12, [lr, #0]
	and r12, r12, r2
	lsl r12, r12, #24
	lsr r12, r12, #24
	movw r3, #0
	movw lr, #:lower16:({VG_RC2_PITABLE}
	movt lr, #:upper16:({VG_RC2_PITABLE}
2:
	add lr, pc
3:
	mov r9, #0
219:
	ldr r10, [lr, #0]
	eor r11, r12, r9
	sub r11, r11, #4
	lsr r11, r11, #8
	orr r11, r11, r11, lsl #8
	and r10, r10, r11
	orr r3, r3, r10
	add lr, lr, #4
	cmp r9, #252
	add r9, r9, #4
	bne 219b
	and lr, r12, #3
	sub r10, lr, #1
	lsr r10, r10, #8
	and r12, r10, r3
	eor r10, lr, #1
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #8
	orr r12, r12, r10
	eor r10, lr, #2
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #16
	orr r12, r12, r10
	eor r10, lr, #3
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #24
	orr r12, r12, r10
	and r12, r12, #255
	add lr, r6, r0
	strb r12, [lr, #0]
	cmp r0, #0
	bne 220f
	b 221f
220:
222:
	sub r0, r0, #1
	add lr, r6, r0
	add lr, lr, #1
	ldrb r12, [lr, #0]
	add r9, r0, r1
	add lr, r6, r9
	ldrb r3, [lr, #0]
	eor r12, r12, r3
	lsl r12, r12, #24
	lsr r12, r12, #24
	movw r3, #0
	movw lr, #:lower16:({VG_RC2_PITABLE}
	movt lr, #:upper16:({VG_RC2_PITABLE}
2:
	add lr, pc
3:
	mov r9, #0
223:
	ldr r10, [lr, #0]
	eor r11, r12, r9
	sub r11, r11, #4
	lsr r11, r11, #8
	orr r11, r11, r11, lsl #8
	and r10, r10, r11
	orr r3, r3, r10
	add lr, lr, #4
	cmp r9, #252
	add r9, r9, #4
	bne 223b
	and lr, r12, #3
	sub r10, lr, #1
	lsr r10, r10, #8
	and r12, r10, r3
	eor r10, lr, #1
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #8
	orr r12, r12, r10
	eor r10, lr, #2
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #16
	orr r12, r12, r10
	eor r10, lr, #3
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #24
	orr r12, r12, r10
	and r12, r12, #255
	add lr, r6, r0
	strb r12, [lr, #0]
	cmp r0, #0
	bne 222b
221:
	mov r12, r8
	ldr r8, [r12, #0]
	ldr r4, [r12, #4]
	ldr r5, [r12, #8]
	ldr r6, [r12, #12]
	ldr r7, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	bx lr
