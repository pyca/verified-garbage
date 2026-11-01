// The functions of `src/rsa_pss_sha512_256_mgf1_sha512_256.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha512_256_mgf1_sha512_256_sign:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	add r12, sp, #0
	ldr r0, [sp, #244]
	str r0, [r12, #64]
	ldr r0, [sp, #136]
	ldr r1, [sp, #140]
	ldr r2, [sp, #240]
	movw r11, #33
	ldrb r3, [r0, #0]
	lsr r4, r3, #1
	orr r4, r4, r4, lsr #1
	orr r4, r4, r4, lsr #2
	orr r4, r4, r4, lsr #4
	sub r5, r4, #1
	lsr r5, r5, #31
	movw r6, #0
	sub r6, r6, r5
	and r6, r6, #255
	orr r4, r4, r6
	sub r6, r1, r5
	sub r7, r6, r11
	str r4, [r12, #72]
	str r5, [r12, #68]
	str r7, [r12, #76]
	sub r8, r3, #1
	lsr r8, r8, #31
	sub r9, r7, #1
	orr r8, r8, r9, lsr #31
	sub r9, r9, r2
	orr r8, r8, r9, lsr #31
	orr r8, r8, r2, lsr #31
	cmp r8, #0
	bne 20f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
22:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 22b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2056
	add r0, r0, lr
	ldr r1, [sp, #232]
	movw lr, #32
23:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 23b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2088
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr lr, [sp, #240]
	cmp lr, #0
	beq 24f
26:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 26b
	b 25f
24:
25:
	add r12, sp, #0
	ldr r0, [sp, #240]
	movw r1, #40
	add r0, r0, r1
	str r0, [r12, #80]
	movw r1, #16
	add r0, r0, r1
	lsr r0, r0, #7
	add r0, r0, #1
	str r0, [r12, #84]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
27:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 27b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
28:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 28b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
29:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
210:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 210b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 29b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
211:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 211b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #76]
	add r0, r0, lr
	ldr r1, [sp, #240]
	sub r0, r0, r1
	sub r0, r0, #1
	ldr r1, [sp, #236]
	ldr lr, [sp, #240]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 212f
214:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 214b
	b 213f
212:
213:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #76]
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #832
	add r1, r1, lr
	movw lr, #32
215:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 215b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	sub r0, r0, #1
	movw r1, #188
	strb r1, [r0, #0]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
216:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
217:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 217b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	movw lr, #32
218:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 218b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2080
	add r0, r0, lr
	ldr r1, [sp, #92]
	movw r2, #36
	str r2, [r12, #80]
	movw r2, #1
	str r2, [r12, #84]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
219:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 219b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
220:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 220b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
221:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
222:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 222b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 221b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #96]
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #832
	add r1, r1, lr
	ldr r2, [sp, #96]
	ldr r3, [sp, #76]
	sub r3, r3, r2
	movw r4, #32
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
223:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 223b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	movw r1, #32
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #76]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 216b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr r1, [sp, #72]
	ldrb r2, [r0, #0]
	and r2, r2, r1
	strb r2, [r0, #0]
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #192]
	str r0, [r12, #16]
	ldr r0, [sp, #196]
	str r0, [r12, #20]
	ldr r0, [sp, #200]
	str r0, [r12, #24]
	ldr r0, [sp, #204]
	str r0, [r12, #28]
	ldr r0, [sp, #208]
	str r0, [r12, #32]
	ldr r0, [sp, #196]
	str r0, [r12, #36]
	ldr r0, [sp, #216]
	str r0, [r12, #40]
	ldr r0, [sp, #204]
	str r0, [r12, #44]
	ldr r0, [sp, #224]
	str r0, [r12, #48]
	ldr r0, [sp, #196]
	str r0, [r12, #52]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #56]
	ldr r0, [sp, #248]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #60]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #136]
	ldr r3, [sp, #140]
	bl {vg_rsa_private_checked}
	b 21f
20:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
224:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 224b
	movw r0, #0
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

vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_precomputed:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	add r12, sp, #0
	ldr r0, [sp, #204]
	str r0, [r12, #64]
	ldr r0, [sp, #128]
	ldr r1, [sp, #132]
	ldr r2, [sp, #196]
	ldr r10, [sp, #200]
	movw r11, #33
	ldrb r3, [r0, #0]
	lsr r4, r3, #1
	orr r4, r4, r4, lsr #1
	orr r4, r4, r4, lsr #2
	orr r4, r4, r4, lsr #4
	sub r5, r4, #1
	lsr r5, r5, #31
	movw r6, #0
	sub r6, r6, r5
	and r6, r6, #255
	orr r4, r4, r6
	sub r6, r1, r5
	sub r7, r6, r11
	str r4, [r12, #72]
	str r5, [r12, #68]
	str r7, [r12, #76]
	sub r8, r3, #1
	lsr r8, r8, #31
	sub r9, r7, #1
	orr r8, r8, r9, lsr #31
	movw r3, #0
	sub r3, r3, r10
	orr r3, r3, r10
	lsr r3, r3, #31
	str r3, [r12, #120]
	sub r10, r3, #1
	and r2, r2, r10
	sub r9, r9, r2
	orr r8, r8, r9, lsr #31
	orr r8, r8, r2, lsr #31
	cmp r8, #0
	bne 20f
	add r12, sp, #0
	ldr r0, [sp, #136]
	str r0, [r12, #0]
	ldr r0, [sp, #140]
	str r0, [r12, #4]
	ldr r0, [sp, #188]
	str r0, [r12, #8]
	ldr r0, [sp, #132]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #208]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #132]
	ldr r2, [sp, #212]
	ldr r3, [sp, #216]
	bl {vg_rsa_public_precomputed_checked}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #132]
	add r7, r0, r1
	sub r7, r7, #1
	ldr r4, [sp, #68]
	add r6, r0, r4
	ldr r5, [sp, #72]
	ldrb r8, [r7, #0]
	eor r8, r8, #188
	ldrb r9, [r0, #0]
	movw r10, #0
	sub r10, r10, r4
	and r9, r9, r10
	orr r8, r8, r9
	ldrb r9, [r6, #0]
	eor r10, r5, #255
	and r9, r9, r10
	orr r8, r8, r9
	str r8, [r12, #100]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
22:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
23:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 23b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	movw lr, #32
24:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 24b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2080
	add r0, r0, lr
	ldr r1, [sp, #92]
	movw r2, #36
	str r2, [r12, #80]
	movw r2, #1
	str r2, [r12, #84]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
25:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 25b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
26:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 26b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
27:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
28:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 28b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 27b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #96]
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #832
	add r1, r1, lr
	ldr r2, [sp, #96]
	ldr r3, [sp, #76]
	sub r3, r3, r2
	movw r4, #32
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
29:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 29b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	movw r1, #32
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #76]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 22b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr r1, [sp, #72]
	ldrb r2, [r0, #0]
	and r2, r2, r1
	strb r2, [r0, #0]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #76]
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
210:
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
	bne 210b
	add r12, sp, #0
	ldr r1, [sp, #100]
	ldr r2, [sp, #76]
	ldr r3, [sp, #196]
	ldr r8, [sp, #120]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r4, [r12, #104]
	sub r2, r2, r4
	sub r2, r2, #1
	eor r2, r2, r3
	sub r8, r8, #1
	and r2, r2, r8
	orr r1, r1, r2
	str r1, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #120]
	cmp r0, #0
	beq 211f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
213:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 213b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2056
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw lr, #32
214:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 214b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2088
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
215:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 215b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
216:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2088
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	ldr lr, [sp, #76]
217:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 217b
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
	bne 216b
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r1, [sp, #104]
	sub r0, r0, r1
	movw r1, #39
	add r0, r0, r1
	str r0, [r12, #80]
	ldr r0, [sp, #76]
	movw r1, #55
	add r0, r0, r1
	lsr r0, r0, #7
	add r0, r0, #1
	str r0, [r12, #84]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
218:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 218b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
219:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 219b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
220:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
221:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 221b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 220b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	movw r2, #0
	movw lr, #32
222:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 222b
	add r12, sp, #0
	ldr r0, [sp, #100]
	orr r0, r0, r2
	movw r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	eor r0, r0, #1
	b 212f
211:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
223:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 223b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2056
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw lr, #32
224:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 224b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2088
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	ldr r2, [sp, #196]
	sub r1, r1, r2
	ldr lr, [sp, #196]
	cmp lr, #0
	beq 225f
227:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 227b
	b 226f
225:
226:
	add r12, sp, #0
	ldr r0, [sp, #196]
	movw r1, #40
	add r0, r0, r1
	str r0, [r12, #80]
	movw r1, #16
	add r0, r0, r1
	lsr r0, r0, #7
	add r0, r0, #1
	str r0, [r12, #84]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
228:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 228b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
229:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 229b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
230:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
231:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 231b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 230b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	movw r2, #0
	movw lr, #32
232:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 232b
	add r12, sp, #0
	ldr r0, [sp, #100]
	orr r0, r0, r2
	movw r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	eor r0, r0, #1
212:
	b 21f
20:
	movw r0, #0
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

vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	add r12, sp, #0
	ldr r0, [sp, #244]
	str r0, [r12, #64]
	ldr r0, [sp, #136]
	ldr r1, [sp, #140]
	ldr r2, [sp, #240]
	movw r11, #33
	ldrb r3, [r0, #0]
	lsr r4, r3, #1
	orr r4, r4, r4, lsr #1
	orr r4, r4, r4, lsr #2
	orr r4, r4, r4, lsr #4
	sub r5, r4, #1
	lsr r5, r5, #31
	movw r6, #0
	sub r6, r6, r5
	and r6, r6, #255
	orr r4, r4, r6
	sub r6, r1, r5
	sub r7, r6, r11
	str r4, [r12, #72]
	str r5, [r12, #68]
	str r7, [r12, #76]
	sub r8, r3, #1
	lsr r8, r8, #31
	sub r9, r7, #1
	orr r8, r8, r9, lsr #31
	sub r9, r9, r2
	orr r8, r8, r9, lsr #31
	orr r8, r8, r2, lsr #31
	cmp r8, #0
	bne 20f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
22:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 22b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2056
	add r0, r0, lr
	ldr r1, [sp, #232]
	movw lr, #32
23:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 23b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2088
	add r0, r0, lr
	ldr r1, [sp, #236]
	ldr lr, [sp, #240]
	cmp lr, #0
	beq 24f
26:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 26b
	b 25f
24:
25:
	add r12, sp, #0
	ldr r0, [sp, #240]
	movw r1, #40
	add r0, r0, r1
	str r0, [r12, #80]
	movw r1, #16
	add r0, r0, r1
	lsr r0, r0, #7
	add r0, r0, #1
	str r0, [r12, #84]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
27:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 27b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
28:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 28b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
29:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
210:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 210b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 29b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	movw r2, #0
	ldr lr, [sp, #140]
211:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 211b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #76]
	add r0, r0, lr
	ldr r1, [sp, #240]
	sub r0, r0, r1
	sub r0, r0, #1
	ldr r1, [sp, #236]
	ldr lr, [sp, #240]
	movw r2, #1
	strb r2, [r0, #0]
	add r0, r0, #1
	cmp lr, #0
	beq 212f
214:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 214b
	b 213f
212:
213:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #76]
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #832
	add r1, r1, lr
	movw lr, #32
215:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 215b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #140]
	add r0, r0, r1
	sub r0, r0, #1
	movw r1, #188
	strb r1, [r0, #0]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
216:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
217:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 217b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	movw lr, #32
218:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 218b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2080
	add r0, r0, lr
	ldr r1, [sp, #92]
	movw r2, #36
	str r2, [r12, #80]
	movw r2, #1
	str r2, [r12, #84]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
219:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 219b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
220:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 220b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
221:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
222:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 222b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 221b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #96]
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #832
	add r1, r1, lr
	ldr r2, [sp, #96]
	ldr r3, [sp, #76]
	sub r3, r3, r2
	movw r4, #32
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
223:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 223b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	movw r1, #32
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #76]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 216b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr r1, [sp, #72]
	ldrb r2, [r0, #0]
	and r2, r2, r1
	strb r2, [r0, #0]
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	str r0, [r12, #8]
	ldr r0, [sp, #140]
	str r0, [r12, #12]
	ldr r0, [sp, #192]
	str r0, [r12, #16]
	ldr r0, [sp, #196]
	str r0, [r12, #20]
	ldr r0, [sp, #200]
	str r0, [r12, #24]
	ldr r0, [sp, #204]
	str r0, [r12, #28]
	ldr r0, [sp, #208]
	str r0, [r12, #32]
	ldr r0, [sp, #196]
	str r0, [r12, #36]
	ldr r0, [sp, #216]
	str r0, [r12, #40]
	ldr r0, [sp, #204]
	str r0, [r12, #44]
	ldr r0, [sp, #224]
	str r0, [r12, #48]
	ldr r0, [sp, #196]
	str r0, [r12, #52]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #56]
	ldr r0, [sp, #248]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #60]
	ldr r0, [sp, #128]
	ldr r1, [sp, #140]
	ldr r2, [sp, #136]
	ldr r3, [sp, #140]
	bl {vg_rsa_private_checked_umaal}
	b 21f
20:
	add r12, sp, #0
	ldr r0, [sp, #128]
	ldr lr, [sp, #140]
	movw r2, #0
224:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 224b
	movw r0, #0
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

vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_precomputed_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	add r12, sp, #0
	ldr r0, [sp, #204]
	str r0, [r12, #64]
	ldr r0, [sp, #128]
	ldr r1, [sp, #132]
	ldr r2, [sp, #196]
	ldr r10, [sp, #200]
	movw r11, #33
	ldrb r3, [r0, #0]
	lsr r4, r3, #1
	orr r4, r4, r4, lsr #1
	orr r4, r4, r4, lsr #2
	orr r4, r4, r4, lsr #4
	sub r5, r4, #1
	lsr r5, r5, #31
	movw r6, #0
	sub r6, r6, r5
	and r6, r6, #255
	orr r4, r4, r6
	sub r6, r1, r5
	sub r7, r6, r11
	str r4, [r12, #72]
	str r5, [r12, #68]
	str r7, [r12, #76]
	sub r8, r3, #1
	lsr r8, r8, #31
	sub r9, r7, #1
	orr r8, r8, r9, lsr #31
	movw r3, #0
	sub r3, r3, r10
	orr r3, r3, r10
	lsr r3, r3, #31
	str r3, [r12, #120]
	sub r10, r3, #1
	and r2, r2, r10
	sub r9, r9, r2
	orr r8, r8, r9, lsr #31
	orr r8, r8, r2, lsr #31
	cmp r8, #0
	bne 20f
	add r12, sp, #0
	ldr r0, [sp, #136]
	str r0, [r12, #0]
	ldr r0, [sp, #140]
	str r0, [r12, #4]
	ldr r0, [sp, #188]
	str r0, [r12, #8]
	ldr r0, [sp, #132]
	str r0, [r12, #12]
	ldr r0, [sp, #64]
	movw lr, #8192
	add r0, r0, lr
	str r0, [r12, #16]
	ldr r0, [sp, #208]
	movw r1, #1024
	sub r0, r0, r1
	str r0, [r12, #20]
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #132]
	ldr r2, [sp, #212]
	ldr r3, [sp, #216]
	bl {vg_rsa_public_precomputed_checked_umaal}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #132]
	add r7, r0, r1
	sub r7, r7, #1
	ldr r4, [sp, #68]
	add r6, r0, r4
	ldr r5, [sp, #72]
	ldrb r8, [r7, #0]
	eor r8, r8, #188
	ldrb r9, [r0, #0]
	movw r10, #0
	sub r10, r10, r4
	and r9, r9, r10
	orr r8, r8, r9
	ldrb r9, [r6, #0]
	eor r10, r5, #255
	and r9, r9, r10
	orr r8, r8, r9
	str r8, [r12, #100]
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #92]
	str r0, [r12, #96]
22:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
23:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 23b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	movw lr, #32
24:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 24b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2080
	add r0, r0, lr
	ldr r1, [sp, #92]
	movw r2, #36
	str r2, [r12, #80]
	movw r2, #1
	str r2, [r12, #84]
	lsr r2, r1, #24
	strb r2, [r0, #0]
	lsr r2, r1, #16
	strb r2, [r0, #1]
	lsr r2, r1, #8
	strb r2, [r0, #2]
	strb r1, [r0, #3]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
25:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 25b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
26:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 26b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
27:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
28:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 28b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 27b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #96]
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #832
	add r1, r1, lr
	ldr r2, [sp, #96]
	ldr r3, [sp, #76]
	sub r3, r3, r2
	movw r4, #32
	sub r5, r3, r4
	lsr r5, r5, #31
	movw r6, #0
	sub r5, r6, r5
	eor r6, r3, r4
	and r6, r6, r5
	eor lr, r4, r6
29:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 29b
	add r12, sp, #0
	ldr r0, [sp, #92]
	add r0, r0, #1
	str r0, [r12, #92]
	ldr r0, [sp, #96]
	movw r1, #32
	add r0, r0, r1
	str r0, [r12, #96]
	ldr r1, [sp, #76]
	sub r0, r0, r1
	lsr r0, r0, #31
	cmp r0, #0
	bne 22b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr r1, [sp, #72]
	ldrb r2, [r0, #0]
	and r2, r2, r1
	strb r2, [r0, #0]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #68]
	add r0, r0, lr
	ldr lr, [sp, #76]
	movw r1, #0
	movw r4, #0
	movw r5, #0
	movw r7, #0
	sub r6, r7, #1
210:
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
	bne 210b
	add r12, sp, #0
	ldr r1, [sp, #100]
	ldr r2, [sp, #76]
	ldr r3, [sp, #196]
	ldr r8, [sp, #120]
	eor r5, r5, #1
	orr r5, r5, r6, lsr #31
	orr r1, r1, r5
	str r4, [r12, #104]
	sub r2, r2, r4
	sub r2, r2, #1
	eor r2, r2, r3
	sub r8, r8, #1
	and r2, r2, r8
	orr r1, r1, r2
	str r1, [r12, #100]
	add r12, sp, #0
	ldr r0, [sp, #120]
	cmp r0, #0
	beq 211f
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
213:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 213b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2056
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw lr, #32
214:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 214b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2088
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
215:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 215b
	add r12, sp, #0
	ldr r0, [sp, #104]
	add r0, r0, #1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
	movw r0, #10
	str r0, [r12, #116]
216:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2088
	add r0, r0, lr
	ldr r1, [sp, #112]
	add r1, r0, r1
	ldr r2, [sp, #108]
	and r2, r2, #1
	movw r3, #0
	sub r2, r3, r2
	ldr lr, [sp, #76]
217:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 217b
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
	bne 216b
	add r12, sp, #0
	ldr r0, [sp, #76]
	ldr r1, [sp, #104]
	sub r0, r0, r1
	movw r1, #39
	add r0, r0, r1
	str r0, [r12, #80]
	ldr r0, [sp, #76]
	movw r1, #55
	add r0, r0, r1
	lsr r0, r0, #7
	add r0, r0, #1
	str r0, [r12, #84]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
218:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 218b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
219:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 219b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
220:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
221:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 221b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 220b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	movw r2, #0
	movw lr, #32
222:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 222b
	add r12, sp, #0
	ldr r0, [sp, #100]
	orr r0, r0, r2
	movw r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	eor r0, r0, #1
	b 212f
211:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	movw r2, #0
	movw lr, #2048
223:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 223b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2056
	add r0, r0, lr
	ldr r1, [sp, #184]
	movw lr, #32
224:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 224b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2088
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	ldr r2, [sp, #196]
	sub r1, r1, r2
	ldr lr, [sp, #196]
	cmp lr, #0
	beq 225f
227:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 227b
	b 226f
225:
226:
	add r12, sp, #0
	ldr r0, [sp, #196]
	movw r1, #40
	add r0, r0, r1
	str r0, [r12, #80]
	movw r1, #16
	add r0, r0, r1
	lsr r0, r0, #7
	add r0, r0, #1
	str r0, [r12, #84]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	bl {vg_sha512_256_init}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #896
	add r0, r0, lr
	movw r2, #0
	movw lr, #128
228:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 228b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r4, [sp, #80]
	movw r5, #0
	mov r9, #0
	str r9, [r0, #176]
	lsr r9, r5, #29
	rev r9, r9
	str r9, [r0, #180]
	lsl r9, r5, #3
	orr r9, r9, r4, lsr #29
	rev r9, r9
	str r9, [r0, #184]
	lsl r9, r4, #3
	rev r9, r9
	str r9, [r0, #188]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #2048
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #896
	add r6, r6, lr
	movw r1, #0
	ldr r4, [sp, #80]
	movw r5, #16
	add r5, r4, r5
	lsr r5, r5, #7
	movw r7, #0
	movw r9, #127
	ldr lr, [sp, #84]
	lsl lr, lr, #7
229:
	ldrb r2, [r0, #0]
	eor r3, r1, r4
	sub r3, r3, #1
	lsr r3, r3, #31
	orr r2, r2, r3, lsl #7
	lsr r3, r1, #7
	eor r3, r3, r5
	sub r3, r3, #1
	lsr r3, r3, #31
	sub r3, r7, r3
	and r8, r1, r9
	add r8, r8, r6
	ldrb r8, [r8, #0]
	and r8, r8, r3
	orr r2, r2, r8
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 229b
	add r12, sp, #0
	movw r0, #0
	str r0, [r12, #88]
230:
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r3, [sp, #64]
	movw lr, #0
	add r3, r3, lr
	ldr r6, [sp, #64]
	movw lr, #2048
	add r6, r6, lr
	ldr r1, [sp, #88]
	lsl r1, r1, #7
	add r6, r6, r1
	mov r1, r6
	mov r2, #1
	bl {vg_sha512_compress}
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #512
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #768
	add r1, r1, lr
	ldr r2, [sp, #88]
	lsl r2, r2, #7
	ldr r3, [sp, #80]
	movw r4, #16
	add r3, r3, r4
	lsr r3, r3, #7
	lsl r3, r3, #7
	eor r2, r2, r3
	sub r2, r2, #1
	lsr r2, r2, #31
	movw r3, #0
	sub r2, r3, r2
	movw lr, #64
231:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r3, r3, r4
	and r3, r3, r2
	eor r4, r4, r3
	strb r4, [r1, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 231b
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #1
	str r0, [r12, #88]
	ldr r1, [sp, #84]
	cmp r0, r1
	bne 230b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #768
	add r0, r0, lr
	ldr r6, [sp, #64]
	movw lr, #832
	add r6, r6, lr
	ldr r9, [r0, #0]
	ldr r10, [r0, #4]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #0]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	ldr r10, [r0, #12]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #8]
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	ldr r10, [r0, #20]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #16]
	str r9, [r6, #20]
	ldr r9, [r0, #24]
	ldr r10, [r0, #28]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #24]
	str r9, [r6, #28]
	ldr r9, [r0, #32]
	ldr r10, [r0, #36]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #32]
	str r9, [r6, #36]
	ldr r9, [r0, #40]
	ldr r10, [r0, #44]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #40]
	str r9, [r6, #44]
	ldr r9, [r0, #48]
	ldr r10, [r0, #52]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #48]
	str r9, [r6, #52]
	ldr r9, [r0, #56]
	ldr r10, [r0, #60]
	rev r10, r10
	rev r9, r9
	str r10, [r6, #56]
	str r9, [r6, #60]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #832
	add r0, r0, lr
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr lr, [sp, #68]
	add r1, r1, lr
	ldr lr, [sp, #76]
	add r1, r1, lr
	movw r2, #0
	movw lr, #32
232:
	ldrb r3, [r0, #0]
	ldrb r12, [r1, #0]
	eor r3, r3, r12
	orr r2, r2, r3
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 232b
	add r12, sp, #0
	ldr r0, [sp, #100]
	orr r0, r0, r2
	movw r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	eor r0, r0, #1
212:
	b 21f
20:
	movw r0, #0
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
