// The functions of `src/md5.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_init:
	movw r12, #8961
	movt r12, #26437
	str r12, [r0, #0]
	movw r12, #43913
	movt r12, #61389
	str r12, [r0, #4]
	movw r12, #56574
	movt r12, #39098
	str r12, [r0, #8]
	movw r12, #21622
	movt r12, #4146
	str r12, [r0, #12]
	bx lr

vg_md5_update:
	sub sp, sp, #128
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #128]
	str lr, [r12, #0]
	ldr lr, [sp, #132]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	ldr r12, [sp, #8]
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r7, [r12, #76]
	str r8, [r12, #80]
	str r9, [r12, #84]
	str r10, [r12, #88]
	str r11, [r12, #92]
	str lr, [r12, #96]
	mov r3, r12
	and r4, r2, #63
	ldr r5, [sp, #0]
	ldr r6, [sp, #4]
	cmp r6, #0
	beq 20f
22:
	mov r7, #0
	cmp r4, #0
	beq 23f
	mov r8, #64
	sub r8, r8, r4
	lsr r12, r6, #6
	cmp r12, #0
	beq 25f
	b 26f
25:
	add r12, r6, r4
	lsr r12, r12, #6
	cmp r12, #0
	beq 27f
	b 28f
27:
	mov r8, r6
28:
26:
	sub r6, r6, r8
29:
	ldrb r12, [r5, #0]
	add r1, r0, r4
	strb r12, [r1, #16]
	add r5, r5, #1
	add r4, r4, #1
	subs r8, r8, #1
	bne 29b
	cmp r4, #64
	beq 210f
	b 211f
210:
	add r1, r0, #16
	mov r4, #0
	mov r7, #1
211:
	b 24f
23:
	lsr r12, r6, #6
	cmp r12, #0
	beq 212f
	mov r1, r5
	lsr r7, r6, #6
	lsl r12, r7, #6
	add r5, r5, r12
	sub r6, r6, r12
	b 213f
212:
	mov r8, #64
	sub r8, r8, r4
	lsr r12, r6, #6
	cmp r12, #0
	beq 214f
	b 215f
214:
	add r12, r6, r4
	lsr r12, r12, #6
	cmp r12, #0
	beq 216f
	b 217f
216:
	mov r8, r6
217:
215:
	sub r6, r6, r8
218:
	ldrb r12, [r5, #0]
	add r1, r0, r4
	strb r12, [r1, #16]
	add r5, r5, #1
	add r4, r4, #1
	subs r8, r8, #1
	bne 218b
	cmp r4, #64
	beq 219f
	b 220f
219:
	add r1, r0, #16
	mov r4, #0
	mov r7, #1
220:
213:
24:
	cmp r7, #0
	beq 221f
	mov r2, r7
	bl {vg_md5_compress}
	b 222f
221:
222:
	cmp r6, #0
	bne 22b
	b 21f
20:
21:
	ldr r4, [r3, #64]
	ldr r5, [r3, #68]
	ldr r6, [r3, #72]
	ldr r7, [r3, #76]
	ldr r8, [r3, #80]
	ldr r9, [r3, #84]
	ldr r10, [r3, #88]
	ldr r11, [r3, #92]
	ldr lr, [r3, #96]
	add sp, sp, #128
	bx lr

vg_md5_finalize:
	sub sp, sp, #128
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #128]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #64]
	str r5, [r12, #68]
	str r6, [r12, #72]
	str r7, [r12, #76]
	str r8, [r12, #80]
	str r9, [r12, #84]
	str r10, [r12, #88]
	str r11, [r12, #92]
	str lr, [r12, #96]
	mov r4, r2
	mov r5, r3
	mov r3, r12
	ldr r6, [sp, #0]
	and r7, r4, #63
	mov r12, #128
	add r1, r0, r7
	strb r12, [r1, #16]
	add r7, r7, #1
	add r8, r7, #7
	lsr r8, r8, #6
20:
	mov r9, #64
	cmp r8, #0
	beq 21f
	b 22f
21:
	mov r9, #56
22:
	mov r12, #0
	subs r9, r9, r7
	beq 23f
25:
	add r1, r0, r7
	strb r12, [r1, #16]
	add r7, r7, #1
	subs r9, r9, #1
	bne 25b
	b 24f
23:
24:
	cmp r8, #0
	beq 26f
	b 27f
26:
	lsl r9, r4, #3
	str r9, [r0, #72]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	str r9, [r0, #76]
27:
	add r1, r0, #16
	mov r2, #1
	bl {vg_md5_compress}
	mov r7, #0
	subs r8, r8, #1
	beq 20b
	ldr r9, [r0, #0]
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	str r9, [r6, #12]
	ldr r4, [r3, #64]
	ldr r5, [r3, #68]
	ldr r6, [r3, #72]
	ldr r7, [r3, #76]
	ldr r8, [r3, #80]
	ldr r9, [r3, #84]
	ldr r10, [r3, #88]
	ldr r11, [r3, #92]
	ldr lr, [r3, #96]
	add sp, sp, #128
	bx lr
