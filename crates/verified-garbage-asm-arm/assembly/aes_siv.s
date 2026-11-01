// The functions of `src/aes_siv.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_siv_init:
	sub sp, sp, #2560
	add r3, sp, #0
	str r4, [r3, #2176]
	str r5, [r3, #2180]
	str r6, [r3, #2184]
	str lr, [r3, #2192]
	str r11, [r3, #2188]
	mov r4, r0
	lsr r5, r1, #1
	mov r6, r2
	mov r11, r3
	mov r1, r5
	bl {vg_aes_expand_key_scratch}
	mov r0, r6
	lsr r1, r5, #2
	add r1, r1, #6
	add r2, r6, #240
	mov r3, r11
	bl {vg_cmac_aes_subkeys}
	add r0, r4, r5
	mov r1, r5
	add r2, r6, #272
	mov r3, r11
	bl {vg_aes_expand_key_scratch}
	ldr r4, [r11, #2176]
	ldr r5, [r11, #2180]
	ldr r6, [r11, #2184]
	ldr lr, [r11, #2192]
	ldr r11, [r11, #2188]
	add sp, sp, #2560
	bx lr

vg_aes_siv_encrypt:
	sub sp, sp, #2608
	add r12, sp, #0
	str lr, [r12, #16]
	ldr lr, [sp, #2608]
	str lr, [r12, #0]
	ldr lr, [sp, #2612]
	str lr, [r12, #4]
	ldr lr, [sp, #2616]
	str lr, [r12, #8]
	add lr, sp, #20
	str lr, [r12, #12]
	ldr lr, [sp, #16]
	ldr r12, [sp, #12]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	mov r10, r0
	mov r9, r1
	mov r8, r2
	mov r7, r3
	mov r12, #0
	str r12, [r11, #16]
	str r12, [r11, #20]
	str r12, [r11, #24]
	str r12, [r11, #28]
	mov r12, #0
	str r12, [r11, #2560]
	str r12, [r11, #2564]
	str r12, [r11, #2568]
	str r12, [r11, #2572]
	mov r0, r10
	mov r1, r9
	add r2, r11, #2560
	add lr, r11, #256
	add r3, r11, #16
	mov r12, #16
	push {r12, lr}
	bl {vg_cmac_aes_finalize}
	ldr r12, [sp], #8
	cmp r7, #0
	beq 20f
22:
	ldr r6, [r8, #0]
	ldr r5, [r8, #4]
	mov r12, #0
	str r12, [r11, #176]
	str r12, [r11, #180]
	str r12, [r11, #184]
	str r12, [r11, #188]
	mov r4, #0
	cmp r5, #0
	beq 23f
	sub r4, r5, #1
	lsr r4, r4, #4
	lsl r4, r4, #4
	b 24f
23:
24:
	mov r0, r10
	mov r1, r9
	add r2, r11, #176
	add lr, r11, #256
	mov r3, r6
	lsr r12, r4, #4
	push {r12, lr}
	bl {vg_cmac_aes_update}
	ldr r12, [sp], #8
	mov r0, r10
	mov r1, r9
	add r2, r11, #176
	add lr, r11, #256
	add r3, r6, r4
	sub r12, r5, r4
	push {r12, lr}
	bl {vg_cmac_aes_finalize}
	ldr r12, [sp], #8
	mov r6, r11
	ldr r0, [r6, #2560]
	ldr r1, [r6, #2564]
	ldr r2, [r6, #2568]
	ldr r3, [r6, #2572]
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	lsr r12, r0, #31
	mov r4, #0
	sub r12, r4, r12
	and r12, r12, #135
	lsl r0, r0, #1
	orr r0, r0, r1, lsr #31
	lsl r1, r1, #1
	orr r1, r1, r2, lsr #31
	lsl r2, r2, #1
	orr r2, r2, r3, lsr #31
	lsl r3, r3, #1
	eor r3, r3, r12
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	str r0, [r6, #2560]
	str r1, [r6, #2564]
	str r2, [r6, #2568]
	str r3, [r6, #2572]
	ldr r12, [r11, #2560]
	ldr lr, [r11, #176]
	eor r12, r12, lr
	str r12, [r11, #2560]
	ldr r12, [r11, #2564]
	ldr lr, [r11, #180]
	eor r12, r12, lr
	str r12, [r11, #2564]
	ldr r12, [r11, #2568]
	ldr lr, [r11, #184]
	eor r12, r12, lr
	str r12, [r11, #2568]
	ldr r12, [r11, #2572]
	ldr lr, [r11, #188]
	eor r12, r12, lr
	str r12, [r11, #2572]
	add r8, r8, #8
	subs r7, r7, #1
	bne 22b
	b 21f
20:
21:
	ldr r6, [sp, #0]
	ldr r5, [sp, #4]
	lsr r12, r5, #4
	cmp r12, #0
	beq 25f
	sub r12, r5, #1
	lsr r12, r12, #4
	mov r4, #0
	cmp r12, #0
	beq 27f
	sub r12, r12, #1
	lsl r4, r12, #4
	b 28f
27:
28:
	add r1, r6, r4
	add r2, r11, #32
	sub r3, r5, r4
29:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 29b
	sub r0, r5, r4
	add r0, r11, r0
	ldr r12, [r0, #16]
	ldr lr, [r11, #2560]
	eor r12, r12, lr
	str r12, [r0, #16]
	ldr r12, [r0, #20]
	ldr lr, [r11, #2564]
	eor r12, r12, lr
	str r12, [r0, #20]
	ldr r12, [r0, #24]
	ldr lr, [r11, #2568]
	eor r12, r12, lr
	str r12, [r0, #24]
	ldr r12, [r0, #28]
	ldr lr, [r11, #2572]
	eor r12, r12, lr
	str r12, [r0, #28]
	mov r12, #0
	str r12, [r11, #0]
	str r12, [r11, #4]
	str r12, [r11, #8]
	str r12, [r11, #12]
	mov r0, r10
	mov r1, r9
	add r2, r11, #0
	add lr, r11, #256
	mov r3, r6
	lsr r12, r4, #4
	push {r12, lr}
	bl {vg_cmac_aes_update}
	ldr r12, [sp], #8
	sub r12, r5, #1
	lsr r12, r12, #4
	mov r7, #0
	cmp r12, #0
	beq 210f
	mov r7, #1
	b 211f
210:
211:
	mov r0, r10
	mov r1, r9
	add r2, r11, #0
	add lr, r11, #256
	add r3, r11, #32
	mov r12, r7
	push {r12, lr}
	bl {vg_cmac_aes_update}
	ldr r12, [sp], #8
	mov r0, r10
	mov r1, r9
	add r2, r11, #0
	add lr, r11, #256
	add r3, r11, #32
	add r3, r3, r7, lsl #4
	sub r12, r5, r4
	sub r12, r12, r7, lsl #4
	push {r12, lr}
	bl {vg_cmac_aes_finalize}
	ldr r12, [sp], #8
	b 26f
25:
	mov r12, #0
	str r12, [r11, #32]
	str r12, [r11, #36]
	str r12, [r11, #40]
	str r12, [r11, #44]
	mov r1, r6
	add r2, r11, #32
	mov r3, r5
	cmp r5, #0
	beq 212f
214:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 214b
	b 213f
212:
213:
	add r2, r11, r5
	mov r12, #128
	strb r12, [r2, #32]
	mov r6, r11
	ldr r0, [r6, #2560]
	ldr r1, [r6, #2564]
	ldr r2, [r6, #2568]
	ldr r3, [r6, #2572]
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	lsr r12, r0, #31
	mov r4, #0
	sub r12, r4, r12
	and r12, r12, #135
	lsl r0, r0, #1
	orr r0, r0, r1, lsr #31
	lsl r1, r1, #1
	orr r1, r1, r2, lsr #31
	lsl r2, r2, #1
	orr r2, r2, r3, lsr #31
	lsl r3, r3, #1
	eor r3, r3, r12
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	str r0, [r6, #192]
	str r1, [r6, #196]
	str r2, [r6, #200]
	str r3, [r6, #204]
	ldr r12, [r11, #32]
	ldr lr, [r11, #192]
	eor r12, r12, lr
	str r12, [r11, #32]
	ldr r12, [r11, #36]
	ldr lr, [r11, #196]
	eor r12, r12, lr
	str r12, [r11, #36]
	ldr r12, [r11, #40]
	ldr lr, [r11, #200]
	eor r12, r12, lr
	str r12, [r11, #40]
	ldr r12, [r11, #44]
	ldr lr, [r11, #204]
	eor r12, r12, lr
	str r12, [r11, #44]
	mov r12, #0
	str r12, [r11, #0]
	str r12, [r11, #4]
	str r12, [r11, #8]
	str r12, [r11, #12]
	mov r0, r10
	mov r1, r9
	add r2, r11, #0
	add lr, r11, #256
	add r3, r11, #32
	mov r12, #16
	push {r12, lr}
	bl {vg_cmac_aes_finalize}
	ldr r12, [sp], #8
26:
	ldr r0, [r11, #0]
	str r0, [r11, #96]
	ldr r0, [r11, #4]
	str r0, [r11, #100]
	ldr r0, [r11, #8]
	orr r0, r0, #128
	eor r0, r0, #128
	str r0, [r11, #104]
	ldr r0, [r11, #12]
	orr r0, r0, #128
	eor r0, r0, #128
	str r0, [r11, #108]
	ldr r6, [sp, #0]
	ldr r5, [sp, #4]
	lsr r12, r5, #4
	cmp r12, #0
	beq 215f
	add r0, r10, #272
	mov r1, r9
	add r2, r11, #96
	add lr, r11, #256
	mov r3, r6
	push {r12, lr}
	bl {vg_aes_ctr32}
	ldr r12, [sp], #8
	b 216f
215:
216:
	and r4, r5, #15
	cmp r4, #0
	beq 217f
	mov r12, #0
	str r12, [r11, #80]
	str r12, [r11, #84]
	str r12, [r11, #88]
	str r12, [r11, #92]
	add r0, r10, #272
	mov r1, r9
	add r2, r11, #96
	add lr, r11, #256
	add r3, r11, #80
	mov r12, #1
	push {r12, lr}
	bl {vg_aes_ctr32}
	ldr r12, [sp], #8
	add r1, r11, #80
	sub r2, r5, r4
	add r2, r2, r6
	mov r3, r4
219:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 219b
	b 218f
217:
218:
	ldr r1, [sp, #8]
	ldr r0, [r11, #0]
	str r0, [r1, #0]
	ldr r0, [r11, #4]
	str r0, [r1, #4]
	ldr r0, [r11, #8]
	str r0, [r1, #8]
	ldr r0, [r11, #12]
	str r0, [r1, #12]
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #2608
	bx lr

vg_aes_siv_decrypt:
	sub sp, sp, #2608
	add r12, sp, #0
	str lr, [r12, #16]
	ldr lr, [sp, #2608]
	str lr, [r12, #0]
	ldr lr, [sp, #2612]
	str lr, [r12, #4]
	ldr lr, [sp, #2616]
	str lr, [r12, #8]
	add lr, sp, #20
	str lr, [r12, #12]
	ldr lr, [sp, #16]
	ldr r12, [sp, #12]
	str r4, [r12, #128]
	str r5, [r12, #132]
	str r6, [r12, #136]
	str r7, [r12, #140]
	str r8, [r12, #144]
	str r9, [r12, #148]
	str r10, [r12, #152]
	str r11, [r12, #156]
	str lr, [r12, #160]
	mov r11, r12
	mov r10, r0
	mov r9, r1
	mov r8, r2
	mov r7, r3
	mov r12, #0
	str r12, [r11, #16]
	str r12, [r11, #20]
	str r12, [r11, #24]
	str r12, [r11, #28]
	mov r12, #0
	str r12, [r11, #2560]
	str r12, [r11, #2564]
	str r12, [r11, #2568]
	str r12, [r11, #2572]
	mov r0, r10
	mov r1, r9
	add r2, r11, #2560
	add lr, r11, #256
	add r3, r11, #16
	mov r12, #16
	push {r12, lr}
	bl {vg_cmac_aes_finalize}
	ldr r12, [sp], #8
	cmp r7, #0
	beq 20f
22:
	ldr r6, [r8, #0]
	ldr r5, [r8, #4]
	mov r12, #0
	str r12, [r11, #176]
	str r12, [r11, #180]
	str r12, [r11, #184]
	str r12, [r11, #188]
	mov r4, #0
	cmp r5, #0
	beq 23f
	sub r4, r5, #1
	lsr r4, r4, #4
	lsl r4, r4, #4
	b 24f
23:
24:
	mov r0, r10
	mov r1, r9
	add r2, r11, #176
	add lr, r11, #256
	mov r3, r6
	lsr r12, r4, #4
	push {r12, lr}
	bl {vg_cmac_aes_update}
	ldr r12, [sp], #8
	mov r0, r10
	mov r1, r9
	add r2, r11, #176
	add lr, r11, #256
	add r3, r6, r4
	sub r12, r5, r4
	push {r12, lr}
	bl {vg_cmac_aes_finalize}
	ldr r12, [sp], #8
	mov r6, r11
	ldr r0, [r6, #2560]
	ldr r1, [r6, #2564]
	ldr r2, [r6, #2568]
	ldr r3, [r6, #2572]
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	lsr r12, r0, #31
	mov r4, #0
	sub r12, r4, r12
	and r12, r12, #135
	lsl r0, r0, #1
	orr r0, r0, r1, lsr #31
	lsl r1, r1, #1
	orr r1, r1, r2, lsr #31
	lsl r2, r2, #1
	orr r2, r2, r3, lsr #31
	lsl r3, r3, #1
	eor r3, r3, r12
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	str r0, [r6, #2560]
	str r1, [r6, #2564]
	str r2, [r6, #2568]
	str r3, [r6, #2572]
	ldr r12, [r11, #2560]
	ldr lr, [r11, #176]
	eor r12, r12, lr
	str r12, [r11, #2560]
	ldr r12, [r11, #2564]
	ldr lr, [r11, #180]
	eor r12, r12, lr
	str r12, [r11, #2564]
	ldr r12, [r11, #2568]
	ldr lr, [r11, #184]
	eor r12, r12, lr
	str r12, [r11, #2568]
	ldr r12, [r11, #2572]
	ldr lr, [r11, #188]
	eor r12, r12, lr
	str r12, [r11, #2572]
	add r8, r8, #8
	subs r7, r7, #1
	bne 22b
	b 21f
20:
21:
	ldr r6, [sp, #0]
	ldr r5, [sp, #4]
	ldr r1, [sp, #8]
	ldr r0, [r1, #0]
	str r0, [r11, #0]
	ldr r0, [r1, #4]
	str r0, [r11, #4]
	ldr r0, [r1, #8]
	str r0, [r11, #8]
	ldr r0, [r1, #12]
	str r0, [r11, #12]
	ldr r0, [r11, #0]
	str r0, [r11, #96]
	ldr r0, [r11, #4]
	str r0, [r11, #100]
	ldr r0, [r11, #8]
	orr r0, r0, #128
	eor r0, r0, #128
	str r0, [r11, #104]
	ldr r0, [r11, #12]
	orr r0, r0, #128
	eor r0, r0, #128
	str r0, [r11, #108]
	ldr r6, [sp, #0]
	ldr r5, [sp, #4]
	lsr r12, r5, #4
	cmp r12, #0
	beq 25f
	add r0, r10, #272
	mov r1, r9
	add r2, r11, #96
	add lr, r11, #256
	mov r3, r6
	push {r12, lr}
	bl {vg_aes_ctr32}
	ldr r12, [sp], #8
	b 26f
25:
26:
	and r4, r5, #15
	cmp r4, #0
	beq 27f
	mov r12, #0
	str r12, [r11, #80]
	str r12, [r11, #84]
	str r12, [r11, #88]
	str r12, [r11, #92]
	add r0, r10, #272
	mov r1, r9
	add r2, r11, #96
	add lr, r11, #256
	add r3, r11, #80
	mov r12, #1
	push {r12, lr}
	bl {vg_aes_ctr32}
	ldr r12, [sp], #8
	add r1, r11, #80
	sub r2, r5, r4
	add r2, r2, r6
	mov r3, r4
29:
	ldrb r12, [r2, #0]
	ldrb r0, [r1, #0]
	eor r12, r12, r0
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 29b
	b 28f
27:
28:
	ldr r6, [sp, #0]
	ldr r5, [sp, #4]
	lsr r12, r5, #4
	cmp r12, #0
	beq 210f
	sub r12, r5, #1
	lsr r12, r12, #4
	mov r4, #0
	cmp r12, #0
	beq 212f
	sub r12, r12, #1
	lsl r4, r12, #4
	b 213f
212:
213:
	add r1, r6, r4
	add r2, r11, #32
	sub r3, r5, r4
214:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 214b
	sub r0, r5, r4
	add r0, r11, r0
	ldr r12, [r0, #16]
	ldr lr, [r11, #2560]
	eor r12, r12, lr
	str r12, [r0, #16]
	ldr r12, [r0, #20]
	ldr lr, [r11, #2564]
	eor r12, r12, lr
	str r12, [r0, #20]
	ldr r12, [r0, #24]
	ldr lr, [r11, #2568]
	eor r12, r12, lr
	str r12, [r0, #24]
	ldr r12, [r0, #28]
	ldr lr, [r11, #2572]
	eor r12, r12, lr
	str r12, [r0, #28]
	mov r12, #0
	str r12, [r11, #112]
	str r12, [r11, #116]
	str r12, [r11, #120]
	str r12, [r11, #124]
	mov r0, r10
	mov r1, r9
	add r2, r11, #112
	add lr, r11, #256
	mov r3, r6
	lsr r12, r4, #4
	push {r12, lr}
	bl {vg_cmac_aes_update}
	ldr r12, [sp], #8
	sub r12, r5, #1
	lsr r12, r12, #4
	mov r7, #0
	cmp r12, #0
	beq 215f
	mov r7, #1
	b 216f
215:
216:
	mov r0, r10
	mov r1, r9
	add r2, r11, #112
	add lr, r11, #256
	add r3, r11, #32
	mov r12, r7
	push {r12, lr}
	bl {vg_cmac_aes_update}
	ldr r12, [sp], #8
	mov r0, r10
	mov r1, r9
	add r2, r11, #112
	add lr, r11, #256
	add r3, r11, #32
	add r3, r3, r7, lsl #4
	sub r12, r5, r4
	sub r12, r12, r7, lsl #4
	push {r12, lr}
	bl {vg_cmac_aes_finalize}
	ldr r12, [sp], #8
	b 211f
210:
	mov r12, #0
	str r12, [r11, #32]
	str r12, [r11, #36]
	str r12, [r11, #40]
	str r12, [r11, #44]
	mov r1, r6
	add r2, r11, #32
	mov r3, r5
	cmp r5, #0
	beq 217f
219:
	ldrb r12, [r1, #0]
	strb r12, [r2, #0]
	add r1, r1, #1
	add r2, r2, #1
	subs r3, r3, #1
	bne 219b
	b 218f
217:
218:
	add r2, r11, r5
	mov r12, #128
	strb r12, [r2, #32]
	mov r6, r11
	ldr r0, [r6, #2560]
	ldr r1, [r6, #2564]
	ldr r2, [r6, #2568]
	ldr r3, [r6, #2572]
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	lsr r12, r0, #31
	mov r4, #0
	sub r12, r4, r12
	and r12, r12, #135
	lsl r0, r0, #1
	orr r0, r0, r1, lsr #31
	lsl r1, r1, #1
	orr r1, r1, r2, lsr #31
	lsl r2, r2, #1
	orr r2, r2, r3, lsr #31
	lsl r3, r3, #1
	eor r3, r3, r12
	rev r0, r0
	rev r1, r1
	rev r2, r2
	rev r3, r3
	str r0, [r6, #192]
	str r1, [r6, #196]
	str r2, [r6, #200]
	str r3, [r6, #204]
	ldr r12, [r11, #32]
	ldr lr, [r11, #192]
	eor r12, r12, lr
	str r12, [r11, #32]
	ldr r12, [r11, #36]
	ldr lr, [r11, #196]
	eor r12, r12, lr
	str r12, [r11, #36]
	ldr r12, [r11, #40]
	ldr lr, [r11, #200]
	eor r12, r12, lr
	str r12, [r11, #40]
	ldr r12, [r11, #44]
	ldr lr, [r11, #204]
	eor r12, r12, lr
	str r12, [r11, #44]
	mov r12, #0
	str r12, [r11, #112]
	str r12, [r11, #116]
	str r12, [r11, #120]
	str r12, [r11, #124]
	mov r0, r10
	mov r1, r9
	add r2, r11, #112
	add lr, r11, #256
	add r3, r11, #32
	mov r12, #16
	push {r12, lr}
	bl {vg_cmac_aes_finalize}
	ldr r12, [sp], #8
211:
	ldr r0, [r11, #0]
	ldr r2, [r11, #112]
	eor r0, r0, r2
	ldr r1, [r11, #4]
	ldr r2, [r11, #116]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r11, #8]
	ldr r2, [r11, #120]
	eor r1, r1, r2
	orr r0, r0, r1
	ldr r1, [r11, #12]
	ldr r2, [r11, #124]
	eor r1, r1, r2
	orr r0, r0, r1
	mov r1, #0
	sub r1, r1, r0
	orr r0, r0, r1
	lsr r0, r0, #31
	mov r1, #1
	sub r0, r1, r0
	ldr r6, [sp, #0]
	ldr r5, [sp, #4]
	mov r1, #0
	sub r1, r1, r0
	cmp r5, #0
	beq 220f
222:
	ldrb r12, [r6, #0]
	and r12, r12, r1
	strb r12, [r6, #0]
	add r6, r6, #1
	subs r5, r5, #1
	bne 222b
	b 221f
220:
221:
	ldr r4, [r11, #128]
	ldr r5, [r11, #132]
	ldr r6, [r11, #136]
	ldr r7, [r11, #140]
	ldr r8, [r11, #144]
	ldr r9, [r11, #148]
	ldr r10, [r11, #152]
	ldr lr, [r11, #160]
	ldr r11, [r11, #156]
	add sp, sp, #2608
	bx lr
