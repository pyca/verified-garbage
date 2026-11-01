// The functions of `src/chacha20.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_init:
	ldr r3, [r1, #0]
	str r3, [r0, #16]
	ldr r3, [r1, #4]
	str r3, [r0, #20]
	ldr r3, [r1, #8]
	str r3, [r0, #24]
	ldr r3, [r1, #12]
	str r3, [r0, #28]
	ldr r3, [r1, #16]
	str r3, [r0, #32]
	ldr r3, [r1, #20]
	str r3, [r0, #36]
	ldr r3, [r1, #24]
	str r3, [r0, #40]
	ldr r3, [r1, #28]
	str r3, [r0, #44]
	mov r1, r2
	ldr r2, [r1, #0]
	ldr r3, [r1, #4]
	ldr r12, [r1, #8]
	ldr r1, [r1, #12]
	str r2, [r0, #48]
	str r3, [r0, #52]
	str r12, [r0, #56]
	str r1, [r0, #60]
	mov r3, #0
	subs r12, r3, r2
	adc r3, r3, #0
	lsr r2, r12, #26
	orr r3, r2, r3, lsl #6
	lsl r12, r12, #6
	str r12, [r0, #128]
	str r3, [r0, #132]
	movw r1, #30821
	movt r1, #24944
	str r1, [r0, #0]
	movw r1, #25710
	movt r1, #13088
	str r1, [r0, #4]
	movw r1, #11570
	movt r1, #31074
	str r1, [r0, #8]
	movw r1, #25972
	movt r1, #27424
	str r1, [r0, #12]
	bx lr

vg_chacha20_set_nonce:
	ldr r2, [r1, #0]
	ldr r3, [r1, #4]
	ldr r12, [r1, #8]
	ldr r1, [r1, #12]
	str r2, [r0, #48]
	str r3, [r0, #52]
	str r12, [r0, #56]
	str r1, [r0, #60]
	mov r3, #0
	subs r12, r3, r2
	adc r3, r3, #0
	lsr r2, r12, #26
	orr r3, r2, r3, lsl #6
	lsl r12, r12, #6
	str r12, [r0, #128]
	str r3, [r0, #132]
	movw r1, #30821
	movt r1, #24944
	str r1, [r0, #0]
	movw r1, #25710
	movt r1, #13088
	str r1, [r0, #4]
	movw r1, #11570
	movt r1, #31074
	str r1, [r0, #8]
	movw r1, #25972
	movt r1, #27424
	str r1, [r0, #12]
	bx lr

vg_chacha20_apply:
	ldr r3, [r0, #128]
	ldr r12, [r0, #132]
	cmp r3, r2
	mov r3, #0
	adc r3, r3, #0
	subs r12, r12, #1
	adc r3, r3, #0
	cmp r3, #0
	beq 20f
	str r4, [r0, #576]
	str r5, [r0, #580]
	str r6, [r0, #584]
	str r7, [r0, #588]
	str lr, [r0, #592]
	ldr r3, [r0, #128]
	ldr r12, [r0, #132]
	subs r3, r3, r2
	movw r4, #65535
	movt r4, #65535
	adc r12, r12, r4
	str r3, [r0, #600]
	str r12, [r0, #604]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	ldr r12, [r4, #128]
	and r12, r12, #63
	cmp r12, r6
	mov r0, #0
	adc r0, r0, #0
	cmp r0, #0
	mov r2, r6
	beq 22f
	b 23f
22:
	mov r2, r12
23:
	add r3, r4, #128
	sub r3, r3, r12
	sub r6, r6, r2
	cmp r2, #0
	beq 24f
26:
	ldrb r0, [r5, #0]
	ldrb r12, [r3, #0]
	eor r0, r0, r12
	strb r0, [r5, #0]
	add r5, r5, #1
	add r3, r3, #1
	subs r2, r2, #1
	bne 26b
	b 25f
24:
25:
	lsr r2, r6, #6
	lsl r2, r2, #6
	cmp r2, #0
	beq 27f
	ldr r0, [r4, #0]
	str r0, [r4, #192]
	ldr r0, [r4, #4]
	str r0, [r4, #196]
	ldr r0, [r4, #8]
	str r0, [r4, #200]
	ldr r0, [r4, #12]
	str r0, [r4, #204]
	ldr r0, [r4, #16]
	str r0, [r4, #208]
	ldr r0, [r4, #20]
	str r0, [r4, #212]
	ldr r0, [r4, #24]
	str r0, [r4, #216]
	ldr r0, [r4, #28]
	str r0, [r4, #220]
	ldr r0, [r4, #32]
	str r0, [r4, #224]
	ldr r0, [r4, #36]
	str r0, [r4, #228]
	ldr r0, [r4, #40]
	str r0, [r4, #232]
	ldr r0, [r4, #44]
	str r0, [r4, #236]
	ldr r0, [r4, #48]
	str r0, [r4, #240]
	ldr r0, [r4, #52]
	str r0, [r4, #244]
	ldr r0, [r4, #56]
	str r0, [r4, #248]
	ldr r0, [r4, #60]
	str r0, [r4, #252]
	ldr r0, [r4, #48]
	lsr r1, r2, #6
	add r0, r0, r1
	str r0, [r4, #48]
	mov r7, r2
	add r0, r4, #192
	mov r1, r5
	add r3, r4, #256
	bl {vg_chacha20_xor}
	add r5, r5, r7
	sub r6, r6, r7
	b 28f
27:
28:
	cmp r6, #0
	beq 29f
	mov r0, r4
	add r1, r4, #64
	bl {vg_chacha20_block}
	ldr r0, [r4, #48]
	add r0, r0, #1
	str r0, [r4, #48]
	add r3, r4, #64
	mov r2, r6
	cmp r2, #0
	beq 211f
213:
	ldrb r0, [r5, #0]
	ldrb r12, [r3, #0]
	eor r0, r0, r12
	strb r0, [r5, #0]
	add r5, r5, #1
	add r3, r3, #1
	subs r2, r2, #1
	bne 213b
	b 212f
211:
212:
	b 210f
29:
210:
	ldr r0, [r4, #600]
	str r0, [r4, #128]
	ldr r0, [r4, #604]
	str r0, [r4, #132]
	ldr lr, [r4, #592]
	ldr r5, [r4, #580]
	ldr r6, [r4, #584]
	ldr r7, [r4, #588]
	ldr r4, [r4, #576]
	mov r0, #1
	b 21f
20:
	mov r0, #0
21:
	bx lr
