// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_decrypt:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #88
	add r12, sp, #0
	ldr r0, [sp, #148]
	str r0, [r12, #0]
	ldr r0, [sp, #152]
	str r0, [r12, #4]
	ldr r0, [sp, #164]
	str r0, [r12, #8]
	ldr r0, [sp, #144]
	str r0, [r12, #12]
	ldr r0, [sp, #172]
	str r0, [r12, #16]
	ldr r0, [sp, #176]
	str r0, [r12, #20]
	ldr r0, [sp, #180]
	str r0, [r12, #24]
	ldr r0, [sp, #184]
	str r0, [r12, #28]
	ldr r0, [sp, #188]
	str r0, [r12, #32]
	ldr r0, [sp, #192]
	str r0, [r12, #36]
	ldr r0, [sp, #196]
	str r0, [r12, #40]
	ldr r0, [sp, #200]
	str r0, [r12, #44]
	ldr r0, [sp, #204]
	str r0, [r12, #48]
	ldr r0, [sp, #208]
	str r0, [r12, #52]
	ldr r0, [sp, #212]
	str r0, [r12, #56]
	ldr r0, [sp, #216]
	str r0, [r12, #60]
	ldr r0, [sp, #88]
	ldr r1, [sp, #144]
	ldr r2, [sp, #100]
	ldr r3, [sp, #144]
	bl {vg_rsa_private_checked}
	add r12, sp, #0
	str r0, [r12, #64]
	ldr r0, [sp, #212]
	add r0, r0, #1552
	ldr lr, [sp, #144]
	mov r2, #0
20:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 20b
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r0, r0, #1552
	ldr r2, [sp, #144]
	add r0, r0, r2
	ldr lr, [sp, #160]
	sub r0, r0, lr
	ldr r1, [sp, #156]
21:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 21b
	add r12, sp, #0
	ldr r0, [sp, #212]
	bl {vg_sha256_init}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #1552
	str r1, [r12, #0]
	ldr r1, [sp, #144]
	str r1, [r12, #4]
	mov r2, #0
	mov r3, #0
	bl {vg_sha256_update}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #208
	str r1, [r12, #0]
	ldr r2, [sp, #144]
	mov r3, #0
	bl {vg_sha256_finalize}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #96
	add r2, r0, #208
	mov r3, #32
	bl {vg_hmac_sha256_init}
	add r12, sp, #0
	ldr r0, [sp, #212]
	ldr r1, [sp, #164]
	str r1, [r12, #0]
	ldr r1, [sp, #144]
	str r1, [r12, #4]
	mov r2, #64
	mov r3, #0
	bl {vg_sha256_update}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #240
	str r1, [r12, #0]
	add r1, r0, #96
	ldr r2, [sp, #144]
	add r2, r2, #64
	mov r3, #0
	bl {vg_hmac_sha256_finalize}
	add r12, sp, #0
	mov r0, #0
	str r0, [r12, #68]
	mov r0, #8
	str r0, [r12, #72]
22:
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r0, r0, #192
	ldr r1, [sp, #68]
	ldr r3, [sp, #144]
	mov r2, #0
	strb r2, [r0, #0]
	strb r1, [r0, #1]
	mov r2, #108
	strb r2, [r0, #2]
	mov r2, #101
	strb r2, [r0, #3]
	mov r2, #110
	strb r2, [r0, #4]
	mov r2, #103
	strb r2, [r0, #5]
	mov r2, #116
	strb r2, [r0, #6]
	mov r2, #104
	strb r2, [r0, #7]
	mov r2, #8
	strb r2, [r0, #8]
	mov r2, #0
	strb r2, [r0, #9]
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #96
	add r2, r0, #240
	mov r3, #32
	bl {vg_hmac_sha256_init}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #192
	str r1, [r12, #0]
	mov r1, #10
	str r1, [r12, #4]
	mov r2, #64
	mov r3, #0
	bl {vg_sha256_update}
	add r12, sp, #0
	ldr r0, [sp, #212]
	ldr r2, [sp, #68]
	add r1, r0, #272
	add r1, r1, r2, lsl #5
	str r1, [r12, #0]
	add r1, r0, #96
	mov r2, #74
	mov r3, #0
	bl {vg_hmac_sha256_finalize}
	add r12, sp, #0
	ldr r1, [sp, #68]
	add r1, r1, #1
	str r1, [r12, #68]
	ldr r2, [sp, #72]
	cmp r1, r2
	bne 22b
	add r12, sp, #0
	mov r0, #0
	str r0, [r12, #68]
	ldr r0, [sp, #144]
	add r0, r0, #31
	lsr r0, r0, #5
	str r0, [r12, #72]
23:
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r0, r0, #192
	ldr r1, [sp, #68]
	ldr r3, [sp, #144]
	mov r2, #0
	strb r2, [r0, #0]
	strb r1, [r0, #1]
	mov r2, #109
	strb r2, [r0, #2]
	mov r2, #101
	strb r2, [r0, #3]
	mov r2, #115
	strb r2, [r0, #4]
	mov r2, #115
	strb r2, [r0, #5]
	mov r2, #97
	strb r2, [r0, #6]
	mov r2, #103
	strb r2, [r0, #7]
	mov r2, #101
	strb r2, [r0, #8]
	lsl r2, r3, #3
	lsr r2, r2, #8
	strb r2, [r0, #9]
	lsl r2, r3, #3
	strb r2, [r0, #10]
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #96
	add r2, r0, #240
	mov r3, #32
	bl {vg_hmac_sha256_init}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #192
	str r1, [r12, #0]
	mov r1, #11
	str r1, [r12, #4]
	mov r2, #64
	mov r3, #0
	bl {vg_sha256_update}
	add r12, sp, #0
	ldr r0, [sp, #212]
	ldr r2, [sp, #68]
	add r1, r0, #528
	add r1, r1, r2, lsl #5
	str r1, [r12, #0]
	add r1, r0, #96
	mov r2, #75
	mov r3, #0
	bl {vg_hmac_sha256_finalize}
	add r12, sp, #0
	ldr r1, [sp, #68]
	add r1, r1, #1
	str r1, [r12, #68]
	ldr r2, [sp, #72]
	cmp r1, r2
	bne 23b
	add r12, sp, #0
	ldr r1, [sp, #144]
	sub r1, r1, #11
	mov r0, #0
24:
	add r0, r0, r0
	add r0, r0, #1
	sub r2, r0, r1
	lsr r2, r2, #31
	cmp r2, #0
	bne 24b
	add r12, sp, #0
	str r0, [r12, #80]
	ldr r0, [sp, #212]
	add r0, r0, #272
	ldr r4, [sp, #80]
	ldr r5, [sp, #144]
	sub r5, r5, #11
	mov r6, #0
	mov lr, #128
25:
	ldrb r2, [r0, #0]
	ldrb r3, [r0, #1]
	add r2, r3, r2, lsl #8
	and r2, r2, r4
	sub r3, r5, r2
	lsr r3, r3, #31
	sub r3, r3, #1
	eor r7, r6, r2
	and r7, r7, r3
	eor r6, r6, r7
	add r0, r0, #2
	subs lr, lr, #1
	bne 25b
	add r12, sp, #0
	str r6, [r12, #76]
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #2
	ldr lr, [sp, #144]
	sub lr, lr, #2
	mov r1, #2
	mov r4, #0
	mov r5, #0
	mov r6, #0
26:
	ldrb r2, [r0, #0]
	sub r2, r2, #1
	lsr r2, r2, #31
	eor r3, r4, #1
	and r3, r3, r2
	sub r3, r6, r3
	and r3, r3, r1
	orr r5, r5, r3
	orr r4, r4, r2
	add r1, r1, #1
	add r0, r0, #1
	subs lr, lr, #1
	bne 26b
	add r12, sp, #0
	ldr r0, [sp, #88]
	ldr r7, [sp, #144]
	ldr r8, [sp, #76]
	ldr r9, [sp, #64]
	ldrb r2, [r0, #0]
	sub r2, r2, #1
	lsr r2, r2, #31
	ldrb r3, [r0, #1]
	eor r3, r3, #2
	sub r3, r3, #1
	lsr r3, r3, #31
	and r2, r2, r3
	and r2, r2, r4
	sub r3, r5, #10
	lsr r3, r3, #31
	eor r3, r3, #1
	and r2, r2, r3
	sub r3, r7, r5
	sub r3, r3, #1
	eor r3, r3, r8
	sub r10, r6, r2
	and r3, r3, r10
	eor r3, r3, r8
	eor r11, r9, #1
	sub r11, r11, #1
	lsr r11, r11, #31
	sub r11, r6, r11
	sub r9, r7, r3
	and r3, r3, r11
	add r12, sp, #0
	ldr r1, [sp, #96]
	str r3, [r1, #0]
	str r6, [r1, #4]
	add r12, sp, #0
	ldr r0, [sp, #88]
	ldr r1, [sp, #212]
	add r1, r1, #528
	mov r4, #0
	ldr lr, [sp, #144]
27:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	and r2, r2, r10
	eor r2, r2, r3
	sub r5, r4, r9
	lsr r5, r5, #31
	sub r5, r5, #1
	and r5, r5, r11
	and r2, r2, r5
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	add r4, r4, #1
	subs lr, lr, #1
	bne 27b
	add r12, sp, #0
	ldr r0, [sp, #64]
	add sp, sp, #88
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

vg_rsa_pkcs1_encrypt_precomputed:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #1056
	add r12, sp, #0
	add r0, r12, #32
	ldr r1, [sp, #1128]
	ldr lr, [sp, #1132]
	mov r2, #0
	strb r2, [r0, #0]
	mov r2, #2
	strb r2, [r0, #1]
	add r0, r0, #2
	mov r3, #0
20:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	sub r2, r2, #1
	orr r3, r3, r2, lsr #31
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 20b
	mov r2, #0
	strb r2, [r0, #0]
	add r0, r0, #1
	add r12, sp, #0
	str r3, [r12, #24]
	ldr r1, [sp, #1120]
	ldr lr, [sp, #1124]
	cmp lr, #0
	beq 21f
23:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 23b
	b 22f
21:
22:
	add r12, sp, #0
	ldr r0, [sp, #1112]
	str r0, [r12, #0]
	ldr r0, [sp, #1116]
	str r0, [r12, #4]
	add r0, r12, #32
	str r0, [r12, #8]
	ldr r0, [sp, #1068]
	str r0, [r12, #12]
	ldr r0, [sp, #1136]
	str r0, [r12, #16]
	ldr r0, [sp, #1140]
	str r0, [r12, #20]
	ldr r0, [sp, #1056]
	ldr r1, [sp, #1068]
	ldr r2, [sp, #1144]
	ldr r3, [sp, #1148]
	bl {vg_rsa_public_precomputed_checked}
	add r12, sp, #0
	ldr r3, [sp, #24]
	sub r2, r3, #1
	and r3, r0, r2
	ldr r0, [sp, #1056]
	ldr lr, [sp, #1068]
24:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 24b
	add r12, sp, #0
	add r0, r12, #32
	ldr lr, [sp, #1068]
	mov r2, #0
25:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 25b
	mov r0, r3
	add sp, sp, #1056
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

vg_rsa_pkcs1_decrypt_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #88
	add r12, sp, #0
	ldr r0, [sp, #148]
	str r0, [r12, #0]
	ldr r0, [sp, #152]
	str r0, [r12, #4]
	ldr r0, [sp, #164]
	str r0, [r12, #8]
	ldr r0, [sp, #144]
	str r0, [r12, #12]
	ldr r0, [sp, #172]
	str r0, [r12, #16]
	ldr r0, [sp, #176]
	str r0, [r12, #20]
	ldr r0, [sp, #180]
	str r0, [r12, #24]
	ldr r0, [sp, #184]
	str r0, [r12, #28]
	ldr r0, [sp, #188]
	str r0, [r12, #32]
	ldr r0, [sp, #192]
	str r0, [r12, #36]
	ldr r0, [sp, #196]
	str r0, [r12, #40]
	ldr r0, [sp, #200]
	str r0, [r12, #44]
	ldr r0, [sp, #204]
	str r0, [r12, #48]
	ldr r0, [sp, #208]
	str r0, [r12, #52]
	ldr r0, [sp, #212]
	str r0, [r12, #56]
	ldr r0, [sp, #216]
	str r0, [r12, #60]
	ldr r0, [sp, #88]
	ldr r1, [sp, #144]
	ldr r2, [sp, #100]
	ldr r3, [sp, #144]
	bl {vg_rsa_private_checked_umaal}
	add r12, sp, #0
	str r0, [r12, #64]
	ldr r0, [sp, #212]
	add r0, r0, #1552
	ldr lr, [sp, #144]
	mov r2, #0
20:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 20b
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r0, r0, #1552
	ldr r2, [sp, #144]
	add r0, r0, r2
	ldr lr, [sp, #160]
	sub r0, r0, lr
	ldr r1, [sp, #156]
21:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 21b
	add r12, sp, #0
	ldr r0, [sp, #212]
	bl {vg_sha256_init}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #1552
	str r1, [r12, #0]
	ldr r1, [sp, #144]
	str r1, [r12, #4]
	mov r2, #0
	mov r3, #0
	bl {vg_sha256_update}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #208
	str r1, [r12, #0]
	ldr r2, [sp, #144]
	mov r3, #0
	bl {vg_sha256_finalize}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #96
	add r2, r0, #208
	mov r3, #32
	bl {vg_hmac_sha256_init}
	add r12, sp, #0
	ldr r0, [sp, #212]
	ldr r1, [sp, #164]
	str r1, [r12, #0]
	ldr r1, [sp, #144]
	str r1, [r12, #4]
	mov r2, #64
	mov r3, #0
	bl {vg_sha256_update}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #240
	str r1, [r12, #0]
	add r1, r0, #96
	ldr r2, [sp, #144]
	add r2, r2, #64
	mov r3, #0
	bl {vg_hmac_sha256_finalize}
	add r12, sp, #0
	mov r0, #0
	str r0, [r12, #68]
	mov r0, #8
	str r0, [r12, #72]
22:
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r0, r0, #192
	ldr r1, [sp, #68]
	ldr r3, [sp, #144]
	mov r2, #0
	strb r2, [r0, #0]
	strb r1, [r0, #1]
	mov r2, #108
	strb r2, [r0, #2]
	mov r2, #101
	strb r2, [r0, #3]
	mov r2, #110
	strb r2, [r0, #4]
	mov r2, #103
	strb r2, [r0, #5]
	mov r2, #116
	strb r2, [r0, #6]
	mov r2, #104
	strb r2, [r0, #7]
	mov r2, #8
	strb r2, [r0, #8]
	mov r2, #0
	strb r2, [r0, #9]
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #96
	add r2, r0, #240
	mov r3, #32
	bl {vg_hmac_sha256_init}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #192
	str r1, [r12, #0]
	mov r1, #10
	str r1, [r12, #4]
	mov r2, #64
	mov r3, #0
	bl {vg_sha256_update}
	add r12, sp, #0
	ldr r0, [sp, #212]
	ldr r2, [sp, #68]
	add r1, r0, #272
	add r1, r1, r2, lsl #5
	str r1, [r12, #0]
	add r1, r0, #96
	mov r2, #74
	mov r3, #0
	bl {vg_hmac_sha256_finalize}
	add r12, sp, #0
	ldr r1, [sp, #68]
	add r1, r1, #1
	str r1, [r12, #68]
	ldr r2, [sp, #72]
	cmp r1, r2
	bne 22b
	add r12, sp, #0
	mov r0, #0
	str r0, [r12, #68]
	ldr r0, [sp, #144]
	add r0, r0, #31
	lsr r0, r0, #5
	str r0, [r12, #72]
23:
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r0, r0, #192
	ldr r1, [sp, #68]
	ldr r3, [sp, #144]
	mov r2, #0
	strb r2, [r0, #0]
	strb r1, [r0, #1]
	mov r2, #109
	strb r2, [r0, #2]
	mov r2, #101
	strb r2, [r0, #3]
	mov r2, #115
	strb r2, [r0, #4]
	mov r2, #115
	strb r2, [r0, #5]
	mov r2, #97
	strb r2, [r0, #6]
	mov r2, #103
	strb r2, [r0, #7]
	mov r2, #101
	strb r2, [r0, #8]
	lsl r2, r3, #3
	lsr r2, r2, #8
	strb r2, [r0, #9]
	lsl r2, r3, #3
	strb r2, [r0, #10]
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #96
	add r2, r0, #240
	mov r3, #32
	bl {vg_hmac_sha256_init}
	add r12, sp, #0
	ldr r0, [sp, #212]
	add r1, r0, #192
	str r1, [r12, #0]
	mov r1, #11
	str r1, [r12, #4]
	mov r2, #64
	mov r3, #0
	bl {vg_sha256_update}
	add r12, sp, #0
	ldr r0, [sp, #212]
	ldr r2, [sp, #68]
	add r1, r0, #528
	add r1, r1, r2, lsl #5
	str r1, [r12, #0]
	add r1, r0, #96
	mov r2, #75
	mov r3, #0
	bl {vg_hmac_sha256_finalize}
	add r12, sp, #0
	ldr r1, [sp, #68]
	add r1, r1, #1
	str r1, [r12, #68]
	ldr r2, [sp, #72]
	cmp r1, r2
	bne 23b
	add r12, sp, #0
	ldr r1, [sp, #144]
	sub r1, r1, #11
	mov r0, #0
24:
	add r0, r0, r0
	add r0, r0, #1
	sub r2, r0, r1
	lsr r2, r2, #31
	cmp r2, #0
	bne 24b
	add r12, sp, #0
	str r0, [r12, #80]
	ldr r0, [sp, #212]
	add r0, r0, #272
	ldr r4, [sp, #80]
	ldr r5, [sp, #144]
	sub r5, r5, #11
	mov r6, #0
	mov lr, #128
25:
	ldrb r2, [r0, #0]
	ldrb r3, [r0, #1]
	add r2, r3, r2, lsl #8
	and r2, r2, r4
	sub r3, r5, r2
	lsr r3, r3, #31
	sub r3, r3, #1
	eor r7, r6, r2
	and r7, r7, r3
	eor r6, r6, r7
	add r0, r0, #2
	subs lr, lr, #1
	bne 25b
	add r12, sp, #0
	str r6, [r12, #76]
	add r12, sp, #0
	ldr r0, [sp, #88]
	add r0, r0, #2
	ldr lr, [sp, #144]
	sub lr, lr, #2
	mov r1, #2
	mov r4, #0
	mov r5, #0
	mov r6, #0
26:
	ldrb r2, [r0, #0]
	sub r2, r2, #1
	lsr r2, r2, #31
	eor r3, r4, #1
	and r3, r3, r2
	sub r3, r6, r3
	and r3, r3, r1
	orr r5, r5, r3
	orr r4, r4, r2
	add r1, r1, #1
	add r0, r0, #1
	subs lr, lr, #1
	bne 26b
	add r12, sp, #0
	ldr r0, [sp, #88]
	ldr r7, [sp, #144]
	ldr r8, [sp, #76]
	ldr r9, [sp, #64]
	ldrb r2, [r0, #0]
	sub r2, r2, #1
	lsr r2, r2, #31
	ldrb r3, [r0, #1]
	eor r3, r3, #2
	sub r3, r3, #1
	lsr r3, r3, #31
	and r2, r2, r3
	and r2, r2, r4
	sub r3, r5, #10
	lsr r3, r3, #31
	eor r3, r3, #1
	and r2, r2, r3
	sub r3, r7, r5
	sub r3, r3, #1
	eor r3, r3, r8
	sub r10, r6, r2
	and r3, r3, r10
	eor r3, r3, r8
	eor r11, r9, #1
	sub r11, r11, #1
	lsr r11, r11, #31
	sub r11, r6, r11
	sub r9, r7, r3
	and r3, r3, r11
	add r12, sp, #0
	ldr r1, [sp, #96]
	str r3, [r1, #0]
	str r6, [r1, #4]
	add r12, sp, #0
	ldr r0, [sp, #88]
	ldr r1, [sp, #212]
	add r1, r1, #528
	mov r4, #0
	ldr lr, [sp, #144]
27:
	ldrb r2, [r0, #0]
	ldrb r3, [r1, #0]
	eor r2, r2, r3
	and r2, r2, r10
	eor r2, r2, r3
	sub r5, r4, r9
	lsr r5, r5, #31
	sub r5, r5, #1
	and r5, r5, r11
	and r2, r2, r5
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	add r4, r4, #1
	subs lr, lr, #1
	bne 27b
	add r12, sp, #0
	ldr r0, [sp, #64]
	add sp, sp, #88
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

vg_rsa_pkcs1_encrypt_precomputed_umaal:
	push {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr}
	sub sp, sp, #1056
	add r12, sp, #0
	add r0, r12, #32
	ldr r1, [sp, #1128]
	ldr lr, [sp, #1132]
	mov r2, #0
	strb r2, [r0, #0]
	mov r2, #2
	strb r2, [r0, #1]
	add r0, r0, #2
	mov r3, #0
20:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	sub r2, r2, #1
	orr r3, r3, r2, lsr #31
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 20b
	mov r2, #0
	strb r2, [r0, #0]
	add r0, r0, #1
	add r12, sp, #0
	str r3, [r12, #24]
	ldr r1, [sp, #1120]
	ldr lr, [sp, #1124]
	cmp lr, #0
	beq 21f
23:
	ldrb r2, [r1, #0]
	strb r2, [r0, #0]
	add r0, r0, #1
	add r1, r1, #1
	subs lr, lr, #1
	bne 23b
	b 22f
21:
22:
	add r12, sp, #0
	ldr r0, [sp, #1112]
	str r0, [r12, #0]
	ldr r0, [sp, #1116]
	str r0, [r12, #4]
	add r0, r12, #32
	str r0, [r12, #8]
	ldr r0, [sp, #1068]
	str r0, [r12, #12]
	ldr r0, [sp, #1136]
	str r0, [r12, #16]
	ldr r0, [sp, #1140]
	str r0, [r12, #20]
	ldr r0, [sp, #1056]
	ldr r1, [sp, #1068]
	ldr r2, [sp, #1144]
	ldr r3, [sp, #1148]
	bl {vg_rsa_public_precomputed_checked_umaal}
	add r12, sp, #0
	ldr r3, [sp, #24]
	sub r2, r3, #1
	and r3, r0, r2
	ldr r0, [sp, #1056]
	ldr lr, [sp, #1068]
24:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 24b
	add r12, sp, #0
	add r0, r12, #32
	ldr lr, [sp, #1068]
	mov r2, #0
25:
	ldrb r1, [r0, #0]
	and r1, r1, r2
	strb r1, [r0, #0]
	add r0, r0, #1
	subs lr, lr, #1
	bne 25b
	mov r0, r3
	add sp, sp, #1056
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
