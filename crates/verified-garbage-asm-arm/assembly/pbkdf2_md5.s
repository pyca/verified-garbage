// The functions of `src/pbkdf2_md5.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_pbkdf2_hmac_md5_iterate:
	ldr r12, [sp, #0]
	str r4, [r12, #112]
	str r5, [r12, #116]
	str r6, [r12, #120]
	str r7, [r12, #124]
	str r8, [r12, #128]
	str r9, [r12, #132]
	str r10, [r12, #136]
	str lr, [r12, #140]
	str r11, [r12, #144]
	mov r11, r12
	mov r7, r3
	mov r3, r12
	mov r4, r0
	mov r5, r2
	movw r12, #148
	add r0, r11, r12
	movw r12, #164
	add r6, r11, r12
	ldr r12, [r1, #0]
	str r12, [r6, #0]
	ldr r12, [r1, #4]
	str r12, [r6, #4]
	ldr r12, [r1, #8]
	str r12, [r6, #8]
	ldr r12, [r1, #12]
	str r12, [r6, #12]
	mov r12, #128
	str r12, [r6, #16]
	mov r12, #0
	str r12, [r6, #20]
	str r12, [r6, #24]
	str r12, [r6, #28]
	str r12, [r6, #32]
	str r12, [r6, #36]
	str r12, [r6, #40]
	str r12, [r6, #44]
	str r12, [r6, #48]
	str r12, [r6, #52]
	movw r12, #640
	movt r12, #0
	str r12, [r6, #56]
	movw r12, #0
	movt r12, #0
	str r12, [r6, #60]
	cmp r5, #0
	beq 20f
22:
	ldr r12, [r4, #0]
	str r12, [r0, #0]
	ldr r12, [r4, #4]
	str r12, [r0, #4]
	ldr r12, [r4, #8]
	str r12, [r0, #8]
	ldr r12, [r4, #12]
	str r12, [r0, #12]
	mov r1, r6
	mov r2, #1
	bl {vg_md5_compress}
	ldr r9, [r0, #0]
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	str r9, [r6, #12]
	ldr r12, [r4, #80]
	str r12, [r0, #0]
	ldr r12, [r4, #84]
	str r12, [r0, #4]
	ldr r12, [r4, #88]
	str r12, [r0, #8]
	ldr r12, [r4, #92]
	str r12, [r0, #12]
	mov r1, r6
	mov r2, #1
	bl {vg_md5_compress}
	ldr r9, [r0, #0]
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	str r9, [r6, #12]
	ldr r12, [r6, #0]
	ldr r1, [r7, #0]
	eor r12, r12, r1
	str r12, [r7, #0]
	ldr r12, [r6, #4]
	ldr r1, [r7, #4]
	eor r12, r12, r1
	str r12, [r7, #4]
	ldr r12, [r6, #8]
	ldr r1, [r7, #8]
	eor r12, r12, r1
	str r12, [r7, #8]
	ldr r12, [r6, #12]
	ldr r1, [r7, #12]
	eor r12, r12, r1
	str r12, [r7, #12]
	subs r5, r5, #1
	bne 22b
	b 21f
20:
21:
	ldr r4, [r11, #112]
	ldr r5, [r11, #116]
	ldr r6, [r11, #120]
	ldr r7, [r11, #124]
	ldr r8, [r11, #128]
	ldr r9, [r11, #132]
	ldr r10, [r11, #136]
	ldr lr, [r11, #140]
	ldr r11, [r11, #144]
	bx lr

vg_pbkdf2_hmac_md5:
	sub sp, sp, #1056
	add r12, sp, #0
	str lr, [r12, #16]
	ldr lr, [sp, #1056]
	str lr, [r12, #0]
	ldr lr, [sp, #1060]
	str lr, [r12, #4]
	ldr lr, [sp, #1064]
	str lr, [r12, #8]
	add lr, sp, #20
	str lr, [r12, #12]
	ldr lr, [sp, #16]
	ldr r12, [sp, #12]
	str r4, [r12, #384]
	str r5, [r12, #388]
	str r6, [r12, #392]
	str r7, [r12, #396]
	str r8, [r12, #400]
	str r9, [r12, #404]
	str r10, [r12, #408]
	str lr, [r12, #412]
	str r11, [r12, #416]
	mov r11, r12
	mov r8, r0
	mov r9, r1
	mov r5, r2
	mov r6, r3
	subs r12, r9, #65
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 20f
	movw r12, #660
	add r4, r11, r12
	mov r0, r4
	bl {vg_md5_init}
	mov r0, r4
	mov r1, r8
	mov r7, r9
	mov r10, r11
	mov r2, #0
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_md5_update_scratch}
	ldr r1, [sp], #16
	mov r0, r4
	movw r12, #772
	add r1, r11, r12
	mov r12, r11
	mov r2, r9
	mov r3, #0
	push {r1, r12}
	bl {vg_md5_finalize_scratch}
	ldr r1, [sp], #8
	movw r12, #772
	add r2, r11, r12
	movw r3, #16
	b 21f
20:
	mov r2, r8
	mov r3, r9
21:
	movw r12, #420
	add r0, r11, r12
	movw r12, #500
	add r1, r11, r12
	mov r12, r11
	push {r12, lr}
	bl {vg_hmac_md5_init_scratch}
	ldr r12, [sp], #8
	mov r8, #0
	movw r9, #80
22:
	add r2, r11, r8
	ldrb r12, [r2, #420]
	add r2, r11, r8
	strb r12, [r2, #580]
	add r8, r8, #1
	subs r9, r9, #1
	bne 22b
	movw r12, #580
	add r0, r11, r12
	mov r1, r5
	mov r7, r6
	mov r10, r11
	movw r2, #64
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_md5_update_scratch}
	ldr r1, [sp], #16
	mov r12, #1
	rev r12, r12
	str r12, [r11, #788]
	mov r4, #0
	ldr r12, [sp, #8]
	cmp r12, #0
	beq 23f
25:
	mov r8, #0
	movw r9, #80
26:
	add r2, r11, r8
	ldrb r12, [r2, #580]
	add r2, r11, r8
	strb r12, [r2, #660]
	add r8, r8, #1
	subs r9, r9, #1
	bne 26b
	movw r12, #660
	add r0, r11, r12
	movw r12, #788
	add r1, r11, r12
	mov r7, #4
	mov r10, r11
	add r2, r6, #64
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_md5_update_scratch}
	ldr r1, [sp], #16
	movw r12, #660
	add r0, r11, r12
	movw r12, #500
	add r1, r11, r12
	movw r12, #740
	add r10, r11, r12
	mov r12, r11
	add r2, r6, #68
	mov r3, #0
	push {r10, r12}
	bl {vg_hmac_md5_finalize_scratch}
	ldr r12, [sp], #8
	mov r8, #0
	movw r9, #16
27:
	add r2, r11, r8
	ldrb r12, [r2, #740]
	add r2, r11, r8
	strb r12, [r2, #756]
	add r8, r8, #1
	subs r9, r9, #1
	bne 27b
	movw r12, #420
	add r0, r11, r12
	movw r12, #740
	add r1, r11, r12
	movw r12, #756
	add r3, r11, r12
	ldr r2, [sp, #0]
	sub r2, r2, #1
	mov r12, r11
	push {r12, lr}
	bl {vg_pbkdf2_hmac_md5_iterate}
	ldr r12, [sp], #8
	ldr r12, [sp, #8]
	sub r9, r12, r4
	subs r12, r9, #16
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 28f
	movw r9, #16
	b 29f
28:
29:
	ldr r10, [sp, #4]
	add r10, r10, r4
	mov r8, #0
210:
	add r2, r11, r8
	ldrb r12, [r2, #756]
	add r2, r10, r8
	strb r12, [r2, #0]
	add r8, r8, #1
	subs r9, r9, #1
	bne 210b
	add r4, r4, r8
	ldr r12, [r11, #788]
	rev r12, r12
	add r12, r12, #1
	rev r12, r12
	str r12, [r11, #788]
	ldr r12, [sp, #8]
	cmp r4, r12
	bne 25b
	b 24f
23:
24:
	ldr r4, [r11, #384]
	ldr r5, [r11, #388]
	ldr r6, [r11, #392]
	ldr r7, [r11, #396]
	ldr r8, [r11, #400]
	ldr r9, [r11, #404]
	ldr r10, [r11, #408]
	ldr lr, [r11, #412]
	ldr r11, [r11, #416]
	add sp, sp, #1056
	bx lr
