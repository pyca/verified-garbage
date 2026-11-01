// The functions of `src/blake2b.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blake2b_init:
	movw r12, #58983
	movt r12, #27145
	str r12, [r0, #4]
	movw r12, #42811
	movt r12, #33994
	str r12, [r0, #8]
	movw r12, #44677
	movt r12, #47975
	str r12, [r0, #12]
	movw r12, #63531
	movt r12, #65172
	str r12, [r0, #16]
	movw r12, #62322
	movt r12, #15470
	str r12, [r0, #20]
	movw r12, #14065
	movt r12, #24349
	str r12, [r0, #24]
	movw r12, #62778
	movt r12, #42319
	str r12, [r0, #28]
	movw r12, #33489
	movt r12, #44518
	str r12, [r0, #32]
	movw r12, #21119
	movt r12, #20750
	str r12, [r0, #36]
	movw r12, #27679
	movt r12, #11070
	str r12, [r0, #40]
	movw r12, #26764
	movt r12, #39685
	str r12, [r0, #44]
	movw r12, #48491
	movt r12, #64321
	str r12, [r0, #48]
	movw r12, #55723
	movt r12, #8067
	str r12, [r0, #52]
	movw r12, #8569
	movt r12, #4990
	str r12, [r0, #56]
	movw r12, #52505
	movt r12, #23520
	str r12, [r0, #60]
	movw r12, #51464
	movt r12, #62141
	eor r12, r12, r3, lsl #8
	eor r12, r12, r1
	str r12, [r0, #0]
	cmp r3, #0
	beq 20f
	mov r12, #0
	str r12, [r0, #64]
	str r12, [r0, #68]
	str r12, [r0, #72]
	str r12, [r0, #76]
	str r12, [r0, #80]
	str r12, [r0, #84]
	str r12, [r0, #88]
	str r12, [r0, #92]
	str r12, [r0, #96]
	str r12, [r0, #100]
	str r12, [r0, #104]
	str r12, [r0, #108]
	str r12, [r0, #112]
	str r12, [r0, #116]
	str r12, [r0, #120]
	str r12, [r0, #124]
	str r12, [r0, #128]
	str r12, [r0, #132]
	str r12, [r0, #136]
	str r12, [r0, #140]
	str r12, [r0, #144]
	str r12, [r0, #148]
	str r12, [r0, #152]
	str r12, [r0, #156]
	str r12, [r0, #160]
	str r12, [r0, #164]
	str r12, [r0, #168]
	str r12, [r0, #172]
	str r12, [r0, #176]
	str r12, [r0, #180]
	str r12, [r0, #184]
	str r12, [r0, #188]
	add r1, r0, #64
22:
	ldrb r12, [r2, #0]
	strb r12, [r1, #0]
	add r2, r2, #1
	add r1, r1, #1
	subs r3, r3, #1
	bne 22b
	b 21f
20:
21:
	bx lr

vg_blake2b_update:
	sub sp, sp, #592
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #592]
	str lr, [r12, #0]
	ldr lr, [sp, #596]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
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
	add sp, sp, #592
	bx lr

vg_blake2b_finalize:
	sub sp, sp, #592
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #592]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
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
	mov r12, #0
	mov r11, #128
	subs r11, r11, r8
	beq 22f
24:
	add r1, r4, r8
	strb r12, [r1, #64]
	add r8, r8, #1
	subs r11, r11, #1
	bne 24b
	b 23f
22:
23:
	mov r0, r4
	add r1, r4, #64
	mov r2, #1
	mov r3, r9
	mov r11, r10
	mov r12, #1
	mov lr, r5
	push {r3, r11, r12, lr}
	bl {vg_blake2b_compress}
	ldr r3, [sp], #16
	ldr r12, [r4, #0]
	str r12, [r6, #0]
	ldr r12, [r4, #4]
	str r12, [r6, #4]
	ldr r12, [r4, #8]
	str r12, [r6, #8]
	ldr r12, [r4, #12]
	str r12, [r6, #12]
	ldr r12, [r4, #16]
	str r12, [r6, #16]
	ldr r12, [r4, #20]
	str r12, [r6, #20]
	ldr r12, [r4, #24]
	str r12, [r6, #24]
	ldr r12, [r4, #28]
	str r12, [r6, #28]
	ldr r12, [r4, #32]
	str r12, [r6, #32]
	ldr r12, [r4, #36]
	str r12, [r6, #36]
	ldr r12, [r4, #40]
	str r12, [r6, #40]
	ldr r12, [r4, #44]
	str r12, [r6, #44]
	ldr r12, [r4, #48]
	str r12, [r6, #48]
	ldr r12, [r4, #52]
	str r12, [r6, #52]
	ldr r12, [r4, #56]
	str r12, [r6, #56]
	ldr r12, [r4, #60]
	str r12, [r6, #60]
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
	add sp, sp, #592
	bx lr
