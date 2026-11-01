// The functions of `src/internal/vg_blake2b_update_scratch.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_update_scratch:
	ldr r12, [sp, #8]
	str r4, [r12, #512]
	str r5, [r12, #516]
	str r6, [r12, #520]
	str r7, [r12, #524]
	str r8, [r12, #528]
	str r9, [r12, #532]
	str r10, [r12, #536]
	str r11, [r12, #540]
	str lr, [r12, #544]
	mov r4, r0
	mov r5, r12
	ldr r6, [sp, #0]
	ldr r7, [sp, #4]
	mov r9, r2
	mov r10, r3
	sub r8, r9, #1
	and r8, r8, #127
	add r8, r8, #1
	orr r12, r9, r10
	cmp r12, #0
	beq 20f
	b 21f
20:
	mov r8, #0
21:
	cmp r8, #0
	beq 22f
	mov r11, #128
	sub r11, r11, r8
	lsr r12, r7, #7
	cmp r12, #0
	beq 24f
	b 25f
24:
	add r12, r7, r8
	lsr r12, r12, #7
	cmp r12, #0
	beq 26f
	b 27f
26:
	mov r11, r7
27:
25:
	sub r7, r7, r11
	adds r9, r9, r11
	adc r10, r10, #0
	cmp r11, #0
	beq 28f
210:
	ldrb r12, [r6, #0]
	add r1, r4, r8
	strb r12, [r1, #64]
	add r6, r6, #1
	add r8, r8, #1
	subs r11, r11, #1
	bne 210b
	b 29f
28:
29:
	b 23f
22:
23:
	mov r2, #0
	cmp r7, #0
	beq 211f
	cmp r8, #0
	beq 213f
	mov r2, #1
	b 214f
213:
214:
	b 212f
211:
212:
	mov r0, r4
	mov r12, #0
	mov lr, r5
	add r1, r4, #64
	mov r3, r9
	mov r11, r10
	push {r3, r11, r12, lr}
	bl {vg_blake2b_compress}
	ldr r3, [sp], #16
	cmp r7, #0
	beq 215f
	mov r8, #0
	sub r2, r7, #1
	lsr r2, r2, #7
	mov r1, r6
	b 216f
215:
	mov r2, #0
	mov r1, r4
216:
	mov r0, r4
	mov r12, #0
	mov lr, r5
	adds r3, r9, #128
	adc r11, r10, #0
	push {r3, r11, r12, lr}
	bl {vg_blake2b_compress}
	ldr r3, [sp], #16
	cmp r7, #0
	beq 217f
	sub r11, r7, #1
	and r11, r11, #127
	add r11, r11, #1
	sub r12, r7, r11
	add r6, r6, r12
	sub r7, r7, r12
	adds r9, r9, r12
	adc r10, r10, #0
	sub r7, r7, r11
	adds r9, r9, r11
	adc r10, r10, #0
	cmp r11, #0
	beq 219f
221:
	ldrb r12, [r6, #0]
	add r1, r4, r8
	strb r12, [r1, #64]
	add r6, r6, #1
	add r8, r8, #1
	subs r11, r11, #1
	bne 221b
	b 220f
219:
220:
	b 218f
217:
218:
	mov r3, r5
	ldr r4, [r3, #512]
	ldr r5, [r3, #516]
	ldr r6, [r3, #520]
	ldr r7, [r3, #524]
	ldr r8, [r3, #528]
	ldr r9, [r3, #532]
	ldr r10, [r3, #536]
	ldr r11, [r3, #540]
	ldr lr, [r3, #544]
	bx lr
