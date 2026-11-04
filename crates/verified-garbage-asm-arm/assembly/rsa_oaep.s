// The functions of `src/rsa_oaep.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_decrypt:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	add r12, sp, #0
	ldr r0, [sp, #252]
	str r0, [r12, #64]
	add r12, sp, #0
	ldr r0, [sp, #188]
	str r0, [r12, #0]
	ldr r0, [sp, #192]
	str r0, [r12, #4]
	ldr r0, [sp, #244]
	str r0, [r12, #8]
	ldr r0, [sp, #184]
	str r0, [r12, #12]
	ldr r0, [sp, #196]
	str r0, [r12, #16]
	ldr r0, [sp, #200]
	str r0, [r12, #20]
	ldr r0, [sp, #204]
	str r0, [r12, #24]
	ldr r0, [sp, #208]
	str r0, [r12, #28]
	ldr r0, [sp, #212]
	str r0, [r12, #32]
	ldr r0, [sp, #200]
	str r0, [r12, #36]
	ldr r0, [sp, #220]
	str r0, [r12, #40]
	ldr r0, [sp, #208]
	str r0, [r12, #44]
	ldr r0, [sp, #228]
	str r0, [r12, #48]
	ldr r0, [sp, #200]
	str r0, [r12, #52]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #56]
	ldr r0, [sp, #256]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #60]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #184]
	ldr r2, [sp, #140]
	ldr r3, [sp, #184]
	bl {vg_rsa_private_checked}
	ldr r1, [sp, #260]
	ldr r1, [r1, #16]
	cmp r1, #16
	beq 20f
	cmp r1, #20
	beq 22f
	cmp r1, #28
	beq 24f
	cmp r1, #32
	beq 26f
	cmp r1, #48
	beq 28f
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #130
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 210f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #64
	ldr r2, [sp, #64]
	movw lr, #65
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #65
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
212:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
213:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 213b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 212b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #65
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #64
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
214:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
215:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 215b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 214b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #64
216:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 216b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #129
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #129
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
217:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 217b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
218:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 218b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #129
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #129
	sub lr, lr, r2
219:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 219b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
220:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
221:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 221b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 220b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
222:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 222b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
223:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 223b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #130
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 211f
210:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
224:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 224b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
211:
	b 29f
28:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #98
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 225f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #48
	ldr r2, [sp, #64]
	movw lr, #49
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #49
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
227:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
228:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 228b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 227b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #49
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #49
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #48
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
229:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
230:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 230b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 229b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #49
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #48
231:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 231b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #97
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #97
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
232:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 232b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
233:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 233b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #97
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #97
	sub lr, lr, r2
234:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 234b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
235:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
236:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 236b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 235b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
237:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 237b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
238:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 238b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #98
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 226f
225:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
239:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 239b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
226:
29:
	b 27f
26:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #66
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 240f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #32
	ldr r2, [sp, #64]
	movw lr, #33
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #33
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
242:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
243:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 243b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 242b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #33
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #32
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
244:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
245:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 245b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 244b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #32
246:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 246b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #65
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
247:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 247b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
248:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 248b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #65
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #65
	sub lr, lr, r2
249:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 249b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
250:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
251:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 251b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 250b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
252:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 252b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
253:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 253b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #66
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 241f
240:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
254:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 254b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
241:
27:
	b 25f
24:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #58
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 255f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #28
	ldr r2, [sp, #64]
	movw lr, #29
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #29
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
257:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
258:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 258b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 257b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #29
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #29
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #28
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
259:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
260:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 260b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 259b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #29
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #28
261:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 261b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #57
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #57
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
262:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 262b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
263:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 263b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #57
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #57
	sub lr, lr, r2
264:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 264b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
265:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
266:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 266b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 265b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
267:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 267b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
268:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 268b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #58
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 256f
255:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
269:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 269b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
256:
25:
	b 23f
22:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #42
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 270f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #20
	ldr r2, [sp, #64]
	movw lr, #21
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #21
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
272:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
273:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 273b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 272b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #21
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #21
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #20
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
274:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
275:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 275b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 274b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #21
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #20
276:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 276b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #41
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #41
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
277:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 277b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
278:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 278b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #41
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #41
	sub lr, lr, r2
279:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 279b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
280:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
281:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 281b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 280b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
282:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 282b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
283:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 283b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #42
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 271f
270:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
284:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 284b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
271:
23:
	b 21f
20:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #34
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 285f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #16
	ldr r2, [sp, #64]
	movw lr, #17
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #17
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
287:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
288:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 288b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 287b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #17
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #17
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #16
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
289:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
290:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 290b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 289b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #17
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #16
291:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 291b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #33
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
292:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 292b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
293:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 293b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #33
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #33
	sub lr, lr, r2
294:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 294b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
295:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
296:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 296b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 295b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
297:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 297b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
298:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 298b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #34
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 286f
285:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
299:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 299b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
286:
21:
	add sp, sp, #128
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

vg_rsa_oaep_encrypt_precomputed:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	ldr r1, [sp, #232]
	ldr r1, [r1, #16]
	cmp r1, #16
	beq 20f
	cmp r1, #20
	beq 22f
	cmp r1, #28
	beq 24f
	cmp r1, #32
	beq 26f
	cmp r1, #48
	beq 28f
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #130
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 210f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
212:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 212b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #64
213:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 213b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #64
214:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 214b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 215f
217:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 217b
	b 216f
215:
216:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #65
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #64
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
218:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
219:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 219b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 218b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #64
	ldr r2, [sp, #64]
	movw lr, #65
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #65
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
220:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
221:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 221b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 220b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked}
	b 211f
210:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
222:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 222b
	movw r0, #0
211:
	b 29f
28:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #98
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 223f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
225:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 225b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #48
226:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 226b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #49
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #48
227:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 227b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 228f
230:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 230b
	b 229f
228:
229:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #49
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #49
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #48
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
231:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
232:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 232b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 231b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #48
	ldr r2, [sp, #64]
	movw lr, #49
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #49
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
233:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
234:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 234b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 233b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked}
	b 224f
223:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
235:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 235b
	movw r0, #0
224:
29:
	b 27f
26:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #66
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 236f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
238:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 238b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #32
239:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 239b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #32
240:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 240b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 241f
243:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 243b
	b 242f
241:
242:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #33
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #32
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
244:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
245:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 245b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 244b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #32
	ldr r2, [sp, #64]
	movw lr, #33
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #33
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
246:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
247:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 247b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 246b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked}
	b 237f
236:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
248:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 248b
	movw r0, #0
237:
27:
	b 25f
24:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #58
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 249f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
251:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 251b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #28
252:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 252b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #29
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #28
253:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 253b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 254f
256:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 256b
	b 255f
254:
255:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #29
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #29
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #28
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
257:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
258:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 258b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 257b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #28
	ldr r2, [sp, #64]
	movw lr, #29
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #29
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
259:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
260:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 260b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 259b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked}
	b 250f
249:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
261:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 261b
	movw r0, #0
250:
25:
	b 23f
22:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #42
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 262f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
264:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 264b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #20
265:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 265b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #21
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #20
266:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 266b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 267f
269:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 269b
	b 268f
267:
268:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #21
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #21
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #20
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
270:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
271:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 271b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 270b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #20
	ldr r2, [sp, #64]
	movw lr, #21
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #21
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
272:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
273:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 273b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 272b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked}
	b 263f
262:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
274:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 274b
	movw r0, #0
263:
23:
	b 21f
20:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #34
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 275f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
277:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 277b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #16
278:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 278b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #17
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #16
279:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 279b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 280f
282:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 282b
	b 281f
280:
281:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #17
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #17
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #16
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
283:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
284:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 284b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 283b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #16
	ldr r2, [sp, #64]
	movw lr, #17
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #17
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
285:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
286:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 286b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 285b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked}
	b 276f
275:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
287:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 287b
	movw r0, #0
276:
21:
	add sp, sp, #128
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

vg_rsa_oaep_decrypt_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	add r12, sp, #0
	ldr r0, [sp, #252]
	str r0, [r12, #64]
	add r12, sp, #0
	ldr r0, [sp, #188]
	str r0, [r12, #0]
	ldr r0, [sp, #192]
	str r0, [r12, #4]
	ldr r0, [sp, #244]
	str r0, [r12, #8]
	ldr r0, [sp, #184]
	str r0, [r12, #12]
	ldr r0, [sp, #196]
	str r0, [r12, #16]
	ldr r0, [sp, #200]
	str r0, [r12, #20]
	ldr r0, [sp, #204]
	str r0, [r12, #24]
	ldr r0, [sp, #208]
	str r0, [r12, #28]
	ldr r0, [sp, #212]
	str r0, [r12, #32]
	ldr r0, [sp, #200]
	str r0, [r12, #36]
	ldr r0, [sp, #220]
	str r0, [r12, #40]
	ldr r0, [sp, #208]
	str r0, [r12, #44]
	ldr r0, [sp, #228]
	str r0, [r12, #48]
	ldr r0, [sp, #200]
	str r0, [r12, #52]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #56]
	ldr r0, [sp, #256]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #60]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #184]
	ldr r2, [sp, #140]
	ldr r3, [sp, #184]
	bl {vg_rsa_private_checked_umaal}
	ldr r1, [sp, #260]
	ldr r1, [r1, #16]
	cmp r1, #16
	beq 20f
	cmp r1, #20
	beq 22f
	cmp r1, #28
	beq 24f
	cmp r1, #32
	beq 26f
	cmp r1, #48
	beq 28f
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #130
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 210f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #64
	ldr r2, [sp, #64]
	movw lr, #65
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #65
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
212:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
213:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 213b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 212b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #65
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #64
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
214:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
215:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 215b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 214b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #64
216:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 216b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #129
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #129
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
217:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 217b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
218:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 218b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #129
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #129
	sub lr, lr, r2
219:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 219b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
220:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
221:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 221b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 220b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
222:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 222b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
223:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 223b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #130
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 211f
210:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
224:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 224b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
211:
	b 29f
28:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #98
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 225f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #48
	ldr r2, [sp, #64]
	movw lr, #49
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #49
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
227:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
228:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 228b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 227b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #49
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #49
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #48
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
229:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
230:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 230b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 229b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #49
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #48
231:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 231b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #97
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #97
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
232:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 232b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
233:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 233b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #97
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #97
	sub lr, lr, r2
234:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 234b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
235:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
236:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 236b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 235b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
237:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 237b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
238:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 238b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #98
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 226f
225:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
239:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 239b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
226:
29:
	b 27f
26:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #66
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 240f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #32
	ldr r2, [sp, #64]
	movw lr, #33
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #33
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
242:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
243:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 243b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 242b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #33
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #32
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
244:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
245:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 245b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 244b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #32
246:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 246b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #65
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
247:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 247b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
248:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 248b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #65
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #65
	sub lr, lr, r2
249:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 249b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
250:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
251:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 251b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 250b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
252:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 252b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
253:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 253b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #66
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 241f
240:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
254:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 254b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
241:
27:
	b 25f
24:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #58
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 255f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #28
	ldr r2, [sp, #64]
	movw lr, #29
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #29
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
257:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
258:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 258b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 257b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #29
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #29
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #28
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
259:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
260:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 260b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 259b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #29
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #28
261:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 261b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #57
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #57
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
262:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 262b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
263:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 263b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #57
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #57
	sub lr, lr, r2
264:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 264b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
265:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
266:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 266b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 265b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
267:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 267b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
268:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 268b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #58
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 256f
255:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
269:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 269b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
256:
25:
	b 23f
22:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #42
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 270f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #20
	ldr r2, [sp, #64]
	movw lr, #21
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #21
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
272:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
273:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 273b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 272b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #21
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #21
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #20
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
274:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
275:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 275b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 274b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #21
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #20
276:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 276b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #41
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #41
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
277:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 277b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
278:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 278b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #41
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #41
	sub lr, lr, r2
279:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 279b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
280:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
281:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 281b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 280b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
282:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 282b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
283:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 283b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #42
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 271f
270:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
284:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 284b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
271:
23:
	b 21f
20:
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #184]
	movw r1, #34
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 285f
	add r12, sp, #0
	ldr r0, [sp, #260]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr r7, [sp, #240]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #240]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #16
	ldr r2, [sp, #64]
	movw lr, #17
	add r2, r2, lr
	ldr r3, [sp, #184]
	movw r4, #17
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
287:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
288:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 288b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 287b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #17
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw r2, #17
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #16
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #264]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
289:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
290:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 290b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 289b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #17
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3392
	add r1, r1, lr
	movw r2, #0
	movw lr, #16
291:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 291b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldrb r3, [r0, #0]
	orr r2, r2, r3
	add r12, sp, #0
	str r2, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr lr, [sp, #184]
	movw r1, #33
	sub lr, lr, r1
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
292:
	ldrb r2, [r0, #0]
	sub r3, r2, #1
	lsr r3, r3, #31
	sub r8, r3, #1
	and r8, r8, r6
	and r9, r1, r8
	orr r4, r4, r9
	and r9, r2, r8
	orr r5, r5, r9
	sub r9, r7, r3
	and r6, r6, r9
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 292b
	add r12, sp, #0
	ldr r1, [sp, #100]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r1, [r12, #100]
	str r4, [r12, #104]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
293:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 293b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #33
	add r1, r1, lr
	ldr lr, [sp, #184]
	movw r2, #33
	sub lr, lr, r2
294:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 294b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
295:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	movw lr, #1024
296:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 296b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	sub r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 295b
	add r12, sp, #0
	ldr r0, [sp, #84]
	eor r0, r0, #1
	sub r0, r0, #1
	lsr r0, r0, #31
	ldr r1, [sp, #100]
	sub r1, r1, #1
	lsr r1, r1, #31
	and r0, r0, r1
	movw r1, #0
	sub r0, r1, r0
	str r0, [r12, #88]
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
297:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 297b
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	ldr r2, [sp, #88]
298:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 298b
	add r12, sp, #0
	ldr r3, [sp, #184]
	movw r1, #34
	sub r3, r3, r1
	ldr r1, [sp, #104]
	sub r3, r3, r1
	ldr r1, [sp, #88]
	and r3, r3, r1
	ldr r1, [sp, #136]
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
	ldr r1, [sp, #88]
	and r1, r1, #1
	orr r0, r0, r1
	b 286f
285:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
	movw r2, #0
299:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 299b
	add r12, sp, #0
	ldr r1, [sp, #136]
	movw r3, #0
	movw r2, #0
	str r3, [r1, #0]
	str r2, [r1, #4]
	add r12, sp, #0
	ldr r1, [sp, #84]
	eor r1, r1, #2
	sub r1, r1, #1
	lsr r1, r1, #31
	lsl r0, r1, #1
286:
21:
	add sp, sp, #128
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

vg_rsa_oaep_encrypt_precomputed_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	ldr r1, [sp, #232]
	ldr r1, [r1, #16]
	cmp r1, #16
	beq 20f
	cmp r1, #20
	beq 22f
	cmp r1, #28
	beq 24f
	cmp r1, #32
	beq 26f
	cmp r1, #48
	beq 28f
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #130
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 210f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
212:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 212b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #64
213:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 213b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #64
214:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 214b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 215f
217:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 217b
	b 216f
215:
216:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #65
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #65
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #64
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
218:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
219:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 219b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 218b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #64
	ldr r2, [sp, #64]
	movw lr, #65
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #65
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
220:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
221:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 221b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 220b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked_umaal}
	b 211f
210:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
222:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 222b
	movw r0, #0
211:
	b 29f
28:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #98
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 223f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
225:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 225b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #48
226:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 226b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #49
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #48
227:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 227b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 228f
230:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 230b
	b 229f
228:
229:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #49
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #49
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #48
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
231:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
232:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 232b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 231b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #48
	ldr r2, [sp, #64]
	movw lr, #49
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #49
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
233:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
234:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 234b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 233b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked_umaal}
	b 224f
223:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
235:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 235b
	movw r0, #0
224:
29:
	b 27f
26:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #66
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 236f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
238:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 238b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #32
239:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 239b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #32
240:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 240b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 241f
243:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 243b
	b 242f
241:
242:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #33
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #33
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #32
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
244:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
245:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 245b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 244b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #32
	ldr r2, [sp, #64]
	movw lr, #33
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #33
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
246:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
247:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 247b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 246b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked_umaal}
	b 237f
236:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
248:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 248b
	movw r0, #0
237:
27:
	b 25f
24:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #58
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 249f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
251:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 251b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #28
252:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 252b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #29
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #28
253:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 253b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 254f
256:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 256b
	b 255f
254:
255:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #29
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #29
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #28
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
257:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
258:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 258b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 257b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #28
	ldr r2, [sp, #64]
	movw lr, #29
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #29
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
259:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
260:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 260b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 259b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked_umaal}
	b 250f
249:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
261:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 261b
	movw r0, #0
250:
25:
	b 23f
22:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #42
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 262f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
264:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 264b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #20
265:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 265b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #21
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #20
266:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 266b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 267f
269:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 269b
	b 268f
267:
268:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #21
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #21
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #20
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
270:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
271:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 271b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 270b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #20
	ldr r2, [sp, #64]
	movw lr, #21
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #21
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
272:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
273:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 273b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 272b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked_umaal}
	b 263f
262:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
274:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 274b
	movw r0, #0
263:
23:
	b 21f
20:
	add r12, sp, #0
	ldr r0, [sp, #216]
	str r0, [r12, #64]
	ldr r0, [sp, #140]
	movw r1, #34
	sub r0, r0, r1
	lsr r1, r0, #31
	ldr r2, [sp, #204]
	orr r1, r1, r2, lsr #10
	sub r3, r0, r2
	orr r1, r1, r3, lsr #31
	cmp r1, #0
	bne 275f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
277:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 277b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	ldr r1, [sp, #208]
	movw lr, #16
278:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 278b
	add r12, sp, #0
	ldr r0, [sp, #232]
	str r0, [r12, #120]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #192]
	ldr r7, [sp, #196]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #196]
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #17
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	movw lr, #16
279:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 279b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	ldr lr, [sp, #204]
	sub r0, r0, lr
	sub r0, r0, #1
	ldr r1, [sp, #200]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 280f
282:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 282b
	b 281f
280:
281:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #17
	add r0, r0, lr
	ldr r1, [sp, #140]
	movw r2, #17
	sub r1, r1, r2
	ldr r2, [sp, #64]
	movw lr, #1
	add r2, r2, lr
	movw r3, #16
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
283:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
284:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 284b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 283b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1
	add r0, r0, lr
	movw r1, #16
	ldr r2, [sp, #64]
	movw lr, #17
	add r2, r2, lr
	ldr r3, [sp, #140]
	movw r4, #17
	sub r3, r3, r4
	str r0, [r12, #76]
	str r1, [r12, #80]
	str r2, [r12, #68]
	str r3, [r12, #72]
	add r12, sp, #0
	ldr r0, [sp, #236]
	str r0, [r12, #120]
	ldr r0, [r0, #16]
	str r0, [r12, #124]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
285:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r4, [sp, #120]
	ldr r4, [r4, #0]
	blx r4
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #68]
	ldr r7, [sp, #72]
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	movw r2, #0
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3456
	add r0, r0, lr
	ldr r1, [sp, #92]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3456
	add r1, r1, lr
	movw r7, #4
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	movw r3, #0
	ldr r4, [sp, #120]
	ldr r4, [r4, #4]
	push {r1, r7, r10, r12}
	blx r4
	ldr r1, [sp], #16
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #3072
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r10, [sp, #64]
	movw lr, #3520
	add r10, r10, lr
	ldr r2, [sp, #72]
	add r2, r2, #4
	movw r3, #0
	mov r12, r10
	ldr r4, [sp, #120]
	ldr r4, [r4, #8]
	push {r1, r12}
	blx r4
	ldr r1, [sp], #8
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r2, [sp, #96]
	add r0, r0, r2
	ldr r1, [sp, #64]
	movw lr, #3328
	add r1, r1, lr
	ldr r3, [sp, #80]
	sub r3, r3, r2
	ldr r4, [sp, #124]
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
286:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 286b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	ldr r1, [sp, #124]
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #80]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 285b
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #0
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #220]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #224]
	ldr r3, [sp, #228]
	bl {vg_rsa_public_precomputed_checked_umaal}
	b 276f
275:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
287:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 287b
	movw r0, #0
276:
21:
	add sp, sp, #128
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
