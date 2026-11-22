// The functions of `src/hmac_md5.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_md5_init:
	subs r12, r3, #65
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	bne 20f
	sub sp, sp, #416
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
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
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r11, r12
	mov r0, r4
	bl {vg_md5_init_core}
	mov r0, r5
	bl {vg_md5_init_core}
	movw r1, #13878
	movt r1, #13878
	str r1, [r4, #16]
	str r1, [r4, #20]
	str r1, [r4, #24]
	str r1, [r4, #28]
	str r1, [r4, #32]
	str r1, [r4, #36]
	str r1, [r4, #40]
	str r1, [r4, #44]
	str r1, [r4, #48]
	str r1, [r4, #52]
	str r1, [r4, #56]
	str r1, [r4, #60]
	str r1, [r4, #64]
	str r1, [r4, #68]
	str r1, [r4, #72]
	str r1, [r4, #76]
	mov r8, r4
	cmp r7, #0
	beq 22f
24:
	ldrb r12, [r6, #0]
	eor r12, r12, #54
	strb r12, [r8, #16]
	add r6, r6, #1
	add r8, r8, #1
	subs r7, r7, #1
	bne 24b
	b 23f
22:
23:
	movw r1, #27242
	movt r1, #27242
	ldr r12, [r4, #16]
	eor r12, r12, r1
	str r12, [r5, #16]
	ldr r12, [r4, #20]
	eor r12, r12, r1
	str r12, [r5, #20]
	ldr r12, [r4, #24]
	eor r12, r12, r1
	str r12, [r5, #24]
	ldr r12, [r4, #28]
	eor r12, r12, r1
	str r12, [r5, #28]
	ldr r12, [r4, #32]
	eor r12, r12, r1
	str r12, [r5, #32]
	ldr r12, [r4, #36]
	eor r12, r12, r1
	str r12, [r5, #36]
	ldr r12, [r4, #40]
	eor r12, r12, r1
	str r12, [r5, #40]
	ldr r12, [r4, #44]
	eor r12, r12, r1
	str r12, [r5, #44]
	ldr r12, [r4, #48]
	eor r12, r12, r1
	str r12, [r5, #48]
	ldr r12, [r4, #52]
	eor r12, r12, r1
	str r12, [r5, #52]
	ldr r12, [r4, #56]
	eor r12, r12, r1
	str r12, [r5, #56]
	ldr r12, [r4, #60]
	eor r12, r12, r1
	str r12, [r5, #60]
	ldr r12, [r4, #64]
	eor r12, r12, r1
	str r12, [r5, #64]
	ldr r12, [r4, #68]
	eor r12, r12, r1
	str r12, [r5, #68]
	ldr r12, [r4, #72]
	eor r12, r12, r1
	str r12, [r5, #72]
	ldr r12, [r4, #76]
	eor r12, r12, r1
	str r12, [r5, #76]
	mov r0, r4
	add r6, r4, #16
	mov r3, r11
	mov r1, r6
	mov r2, #1
	bl {vg_md5_compress}
	mov r0, r5
	add r6, r5, #16
	mov r1, r6
	mov r2, #1
	bl {vg_md5_compress}
	ldr r4, [r11, #112]
	ldr r5, [r11, #116]
	ldr r6, [r11, #120]
	ldr r7, [r11, #124]
	ldr r8, [r11, #128]
	ldr r9, [r11, #132]
	ldr r10, [r11, #136]
	ldr lr, [r11, #140]
	ldr r11, [r11, #144]
	add sp, sp, #416
21:
	sub sp, sp, #1088
	add r12, sp, #0
	mov r2, #0
	mov r3, #34
27:
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
	bne 27b
	add sp, sp, #1088
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
20:
	sub sp, sp, #1056
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
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
	mov r8, r2
	mov r9, r3
	mov r5, r0
	mov r6, r1
	subs r12, r9, #65
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	beq 25f
	movw r12, #660
	add r4, r11, r12
	mov r0, r4
	bl {vg_md5_init_core}
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
	b 26f
25:
	mov r2, r8
	mov r3, r9
26:
	mov r0, r5
	mov r1, r6
	mov r12, r11
	push {r12, lr}
	bl {vg_hmac_md5_init_scratch}
	ldr r12, [sp], #8
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
	b 21b

vg_hmac_md5_finalize:
	sub sp, sp, #416
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #416]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #112]
	str r5, [r12, #116]
	str r6, [r12, #120]
	str r7, [r12, #124]
	str r8, [r12, #128]
	str r9, [r12, #132]
	str r10, [r12, #136]
	str lr, [r12, #140]
	str r11, [r12, #144]
	mov r5, r1
	ldr r7, [sp, #0]
	mov r11, r12
	movw r12, #164
	add r1, r11, r12
	mov r12, r11
	push {r1, r12}
	bl {vg_md5_finalize_scratch}
	ldr r1, [sp], #8
	mov r3, r11
	movw r12, #148
	add r0, r11, r12
	movw r12, #164
	add r6, r11, r12
	ldr r12, [r5, #0]
	str r12, [r0, #0]
	ldr r12, [r5, #4]
	str r12, [r0, #4]
	ldr r12, [r5, #8]
	str r12, [r0, #8]
	ldr r12, [r5, #12]
	str r12, [r0, #12]
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
	mov r1, r6
	mov r2, #1
	bl {vg_md5_compress}
	mov r6, r7
	ldr r9, [r0, #0]
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	str r9, [r6, #12]
	ldr r4, [r11, #112]
	ldr r5, [r11, #116]
	ldr r6, [r11, #120]
	ldr r7, [r11, #124]
	ldr r8, [r11, #128]
	ldr r9, [r11, #132]
	ldr r10, [r11, #136]
	ldr lr, [r11, #140]
	ldr r11, [r11, #144]
	add sp, sp, #416
	sub sp, sp, #432
	add r12, sp, #0
	mov r2, #0
	mov r3, #13
20:
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
	bne 20b
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	add sp, sp, #432
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
