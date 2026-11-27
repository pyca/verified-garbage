// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_decrypt_precomputed_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #192]
	str r0, [r12, #8]
	ldr r0, [sp, #196]
	str r0, [r12, #12]
	ldr r0, [sp, #200]
	str r0, [r12, #16]
	ldr r0, [sp, #204]
	str r0, [r12, #20]
	ldr r0, [sp, #208]
	str r0, [r12, #24]
	ldr r0, [sp, #212]
	str r0, [r12, #28]
	ldr r0, [sp, #216]
	str r0, [r12, #32]
	ldr r0, [sp, #220]
	str r0, [r12, #36]
	ldr r0, [sp, #224]
	str r0, [r12, #40]
	ldr r0, [sp, #228]
	str r0, [r12, #44]
	ldr r0, [sp, #232]
	str r0, [r12, #48]
	ldr r0, [sp, #236]
	str r0, [r12, #52]
	ldr r0, [sp, #240]
	str r0, [r12, #56]
	ldr r0, [sp, #244]
	str r0, [r12, #60]
	ldr r0, [sp, #248]
	str r0, [r12, #64]
	ldr r0, [sp, #252]
	str r0, [r12, #68]
	ldr r0, [sp, #256]
	str r0, [r12, #72]
	ldr r0, [sp, #260]
	str r0, [r12, #76]
	ldr r0, [sp, #264]
	str r0, [r12, #80]
	ldr r0, [sp, #128]
	ldr r1, [sp, #132]
	ldr r2, [sp, #136]
	ldr r3, [sp, #140]
	bl {vg_rsa_pkcs1_decrypt_precomputed_body_umaal}
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #252]
	str r0, [r12, #64]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #184]
	add r0, r0, lr
	movw r2, #0
20:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 20b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #128]
	ldr lr, [sp, #184]
21:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 21b
	add r12, sp, #0
	ldr r1, [sp, #136]
	ldr r1, [r1, #0]
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #116]
	sub r0, r0, r1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
22:
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
	ldr lr, [sp, #184]
23:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 23b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	lsr r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 22b
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
24:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 24b
	add r12, sp, #0
	ldr r0, [sp, #84]
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
	sub sp, sp, #3824
	add r12, sp, #0
	mov r2, #0
	mov r3, #119
25:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 25b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	add sp, sp, #3824
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_rsa_pkcs1_encrypt_random_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #1088
	add r12, sp, #0
	ldr r1, [sp, #1164]
	ldr r8, [sp, #1168]
	ldr r3, [sp, #1144]
	ldr r4, [sp, #1160]
	sub r3, r3, r4
	sub r3, r3, #3
	add r0, r12, #40
	mov r4, #0
	mov r5, #0
	cmp r8, #0
	bne 20f
	b 21f
20:
22:
	ldrb r6, [r1, #0]
	add r1, r1, #1
	add r4, r4, #1
	cmp r6, #0
	bne 23f
	b 24f
23:
	strb r6, [r0, #0]
	add r0, r0, #1
	add r5, r5, #1
24:
	cmp r5, r3
	beq 25f
	cmp r4, r8
	b 26f
25:
	cmp r5, r5
26:
	bne 22b
21:
	cmp r5, r3
	beq 27f
	add r12, sp, #0
	ldr r0, [sp, #1088]
	ldr lr, [sp, #1144]
	mov r2, #0
29:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 29b
	cmp r5, #0
	beq 210f
	add r12, sp, #0
	add r0, r12, #40
	mov lr, r5
212:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 212b
	b 211f
210:
211:
	ldr r7, [sp, #1096]
	add r6, r3, #128
	cmp r8, r6
	beq 213f
	add r9, r3, r8
	sub r9, r9, r5
	sub r10, r6, r9
	lsr r10, r10, #31
	sub r10, r10, #1
	sub r11, r9, r6
	and r11, r11, r10
	add r11, r11, r6
	mov r10, #0
	str r10, [r7, #0]
	str r10, [r7, #4]
	str r11, [r7, #8]
	str r10, [r7, #12]
	mov r0, #0
	b 214f
213:
	mov r9, #0
	str r8, [r7, #0]
	str r9, [r7, #4]
	str r9, [r7, #8]
	str r9, [r7, #12]
	mov r0, #3
214:
	b 28f
27:
	ldr r7, [sp, #1096]
	mov r6, #0
	str r4, [r7, #0]
	str r6, [r7, #4]
	str r6, [r7, #8]
	str r6, [r7, #12]
	add r12, sp, #0
	ldr r0, [sp, #1148]
	str r0, [r12, #0]
	ldr r0, [sp, #1152]
	str r0, [r12, #4]
	ldr r0, [sp, #1156]
	str r0, [r12, #8]
	ldr r0, [sp, #1160]
	str r0, [r12, #12]
	add r0, r12, #40
	str r0, [r12, #16]
	str r3, [r12, #20]
	ldr r0, [sp, #1172]
	str r0, [r12, #24]
	ldr r0, [sp, #1176]
	str r0, [r12, #28]
	ldr r0, [sp, #1180]
	str r0, [r12, #32]
	ldr r0, [sp, #1184]
	str r0, [r12, #36]
	ldr r0, [sp, #1088]
	ldr r1, [sp, #1144]
	ldr r2, [sp, #1100]
	ldr r3, [sp, #1144]
	bl {vg_rsa_pkcs1_encrypt_precomputed_umaal}
	mov r4, #2
	sub r4, r4, r0
	add r12, sp, #0
	add r0, r12, #40
	ldr r1, [sp, #1144]
	ldr r2, [sp, #1160]
	sub lr, r1, r2
	sub lr, lr, #3
	mov r2, #0
215:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 215b
	mov r0, r4
28:
	add sp, sp, #1088
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
	sub sp, sp, #2368
	add r12, sp, #0
	mov r2, #0
	mov r3, #74
216:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 216b
	add sp, sp, #2368
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_rsa_pkcs1_decrypt_precomputed:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #128
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #0]
	ldr r0, [sp, #188]
	str r0, [r12, #4]
	ldr r0, [sp, #192]
	str r0, [r12, #8]
	ldr r0, [sp, #196]
	str r0, [r12, #12]
	ldr r0, [sp, #200]
	str r0, [r12, #16]
	ldr r0, [sp, #204]
	str r0, [r12, #20]
	ldr r0, [sp, #208]
	str r0, [r12, #24]
	ldr r0, [sp, #212]
	str r0, [r12, #28]
	ldr r0, [sp, #216]
	str r0, [r12, #32]
	ldr r0, [sp, #220]
	str r0, [r12, #36]
	ldr r0, [sp, #224]
	str r0, [r12, #40]
	ldr r0, [sp, #228]
	str r0, [r12, #44]
	ldr r0, [sp, #232]
	str r0, [r12, #48]
	ldr r0, [sp, #236]
	str r0, [r12, #52]
	ldr r0, [sp, #240]
	str r0, [r12, #56]
	ldr r0, [sp, #244]
	str r0, [r12, #60]
	ldr r0, [sp, #248]
	str r0, [r12, #64]
	ldr r0, [sp, #252]
	str r0, [r12, #68]
	ldr r0, [sp, #256]
	str r0, [r12, #72]
	ldr r0, [sp, #260]
	str r0, [r12, #76]
	ldr r0, [sp, #264]
	str r0, [r12, #80]
	ldr r0, [sp, #128]
	ldr r1, [sp, #132]
	ldr r2, [sp, #136]
	ldr r3, [sp, #140]
	bl {vg_rsa_pkcs1_decrypt_precomputed_body}
	add r12, sp, #0
	str r0, [r12, #84]
	ldr r0, [sp, #252]
	str r0, [r12, #64]
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr lr, [sp, #184]
	add r0, r0, lr
	movw r2, #0
20:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 20b
	add r12, sp, #0
	ldr r0, [sp, #64]
	movw lr, #1024
	add r0, r0, lr
	ldr r1, [sp, #128]
	ldr lr, [sp, #184]
21:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 21b
	add r12, sp, #0
	ldr r1, [sp, #136]
	ldr r1, [r1, #0]
	add r12, sp, #0
	ldr r0, [sp, #184]
	str r0, [r12, #116]
	sub r0, r0, r1
	str r0, [r12, #108]
	movw r0, #1
	str r0, [r12, #112]
22:
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
	ldr lr, [sp, #184]
23:
	ldrb r3, [r0, #0]
	ldrb r4, [r1, #0]
	eor r4, r4, r3
	and r4, r4, r2
	eor r3, r3, r4
	strb r3, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 23b
	add r12, sp, #0
	ldr r0, [sp, #108]
	lsr r0, r0, #1
	str r0, [r12, #108]
	ldr r0, [sp, #112]
	add r0, r0, r0
	str r0, [r12, #112]
	ldr r0, [sp, #116]
	lsr r0, r0, #1
	str r0, [r12, #116]
	cmp r0, #0
	bne 22b
	add r12, sp, #0
	ldr r1, [sp, #64]
	movw lr, #1024
	add r1, r1, lr
	ldr r0, [sp, #128]
	ldr lr, [sp, #184]
24:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 24b
	add r12, sp, #0
	ldr r0, [sp, #84]
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
	sub sp, sp, #3824
	add r12, sp, #0
	mov r2, #0
	mov r3, #119
25:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 25b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	add sp, sp, #3824
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_rsa_pkcs1_encrypt_random:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #1088
	add r12, sp, #0
	ldr r1, [sp, #1164]
	ldr r8, [sp, #1168]
	ldr r3, [sp, #1144]
	ldr r4, [sp, #1160]
	sub r3, r3, r4
	sub r3, r3, #3
	add r0, r12, #40
	mov r4, #0
	mov r5, #0
	cmp r8, #0
	bne 20f
	b 21f
20:
22:
	ldrb r6, [r1, #0]
	add r1, r1, #1
	add r4, r4, #1
	cmp r6, #0
	bne 23f
	b 24f
23:
	strb r6, [r0, #0]
	add r0, r0, #1
	add r5, r5, #1
24:
	cmp r5, r3
	beq 25f
	cmp r4, r8
	b 26f
25:
	cmp r5, r5
26:
	bne 22b
21:
	cmp r5, r3
	beq 27f
	add r12, sp, #0
	ldr r0, [sp, #1088]
	ldr lr, [sp, #1144]
	mov r2, #0
29:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 29b
	cmp r5, #0
	beq 210f
	add r12, sp, #0
	add r0, r12, #40
	mov lr, r5
212:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 212b
	b 211f
210:
211:
	ldr r7, [sp, #1096]
	add r6, r3, #128
	cmp r8, r6
	beq 213f
	add r9, r3, r8
	sub r9, r9, r5
	sub r10, r6, r9
	lsr r10, r10, #31
	sub r10, r10, #1
	sub r11, r9, r6
	and r11, r11, r10
	add r11, r11, r6
	mov r10, #0
	str r10, [r7, #0]
	str r10, [r7, #4]
	str r11, [r7, #8]
	str r10, [r7, #12]
	mov r0, #0
	b 214f
213:
	mov r9, #0
	str r8, [r7, #0]
	str r9, [r7, #4]
	str r9, [r7, #8]
	str r9, [r7, #12]
	mov r0, #3
214:
	b 28f
27:
	ldr r7, [sp, #1096]
	mov r6, #0
	str r4, [r7, #0]
	str r6, [r7, #4]
	str r6, [r7, #8]
	str r6, [r7, #12]
	add r12, sp, #0
	ldr r0, [sp, #1148]
	str r0, [r12, #0]
	ldr r0, [sp, #1152]
	str r0, [r12, #4]
	ldr r0, [sp, #1156]
	str r0, [r12, #8]
	ldr r0, [sp, #1160]
	str r0, [r12, #12]
	add r0, r12, #40
	str r0, [r12, #16]
	str r3, [r12, #20]
	ldr r0, [sp, #1172]
	str r0, [r12, #24]
	ldr r0, [sp, #1176]
	str r0, [r12, #28]
	ldr r0, [sp, #1180]
	str r0, [r12, #32]
	ldr r0, [sp, #1184]
	str r0, [r12, #36]
	ldr r0, [sp, #1088]
	ldr r1, [sp, #1144]
	ldr r2, [sp, #1100]
	ldr r3, [sp, #1144]
	bl {vg_rsa_pkcs1_encrypt_precomputed}
	mov r4, #2
	sub r4, r4, r0
	add r12, sp, #0
	add r0, r12, #40
	ldr r1, [sp, #1144]
	ldr r2, [sp, #1160]
	sub lr, r1, r2
	sub lr, lr, #3
	mov r2, #0
215:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 215b
	mov r0, r4
28:
	add sp, sp, #1088
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
	sub sp, sp, #2368
	add r12, sp, #0
	mov r2, #0
	mov r3, #74
216:
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	add r12, r12, #32
	subs r3, r3, #1
	bne 216b
	add sp, sp, #2368
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
