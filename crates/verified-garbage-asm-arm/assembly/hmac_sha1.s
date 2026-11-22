// The functions of `src/hmac_sha1.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha1_init:
	subs r12, r3, #65
	mov r12, #0
	adc r12, r12, #0
	cmp r12, #0
	bne 20f
	sub sp, sp, #480
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #160]
	str r5, [r12, #164]
	str r6, [r12, #168]
	str r7, [r12, #172]
	str r8, [r12, #176]
	str r9, [r12, #180]
	str r10, [r12, #184]
	str lr, [r12, #188]
	str r11, [r12, #192]
	mov r4, r0
	mov r5, r1
	mov r6, r2
	mov r7, r3
	mov r11, r12
	mov r0, r4
	bl {vg_sha1_init_core}
	mov r0, r5
	bl {vg_sha1_init_core}
	movw r1, #13878
	movt r1, #13878
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
	str r1, [r4, #80]
	mov r8, r4
	cmp r7, #0
	beq 22f
24:
	ldrb r12, [r6, #0]
	eor r12, r12, #54
	strb r12, [r8, #20]
	add r6, r6, #1
	add r8, r8, #1
	subs r7, r7, #1
	bne 24b
	b 23f
22:
23:
	movw r1, #27242
	movt r1, #27242
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
	ldr r12, [r4, #80]
	eor r12, r12, r1
	str r12, [r5, #80]
	mov r0, r4
	add r6, r4, #20
	mov r3, r11
	mov r1, r6
	mov r2, #1
	bl {vg_sha1_compress}
	mov r0, r5
	add r6, r5, #20
	mov r1, r6
	mov r2, #1
	bl {vg_sha1_compress}
	ldr r4, [r11, #160]
	ldr r5, [r11, #164]
	ldr r6, [r11, #168]
	ldr r7, [r11, #172]
	ldr r8, [r11, #176]
	ldr r9, [r11, #180]
	ldr r10, [r11, #184]
	ldr lr, [r11, #188]
	ldr r11, [r11, #192]
	add sp, sp, #480
21:
	sub sp, sp, #1184
	add r12, sp, #0
	mov r2, #0
	mov r3, #37
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
	add sp, sp, #1184
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
20:
	sub sp, sp, #1152
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #448]
	str r5, [r12, #452]
	str r6, [r12, #456]
	str r7, [r12, #460]
	str r8, [r12, #464]
	str r9, [r12, #468]
	str r10, [r12, #472]
	str lr, [r12, #476]
	str r11, [r12, #480]
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
	movw r12, #736
	add r4, r11, r12
	mov r0, r4
	bl {vg_sha1_init_core}
	mov r0, r4
	mov r1, r8
	mov r7, r9
	mov r10, r11
	mov r2, #0
	mov r3, #0
	push {r1, r7, r10, r12}
	bl {vg_sha1_update_scratch}
	ldr r1, [sp], #16
	mov r0, r4
	movw r12, #860
	add r1, r11, r12
	mov r12, r11
	mov r2, r9
	mov r3, #0
	push {r1, r12}
	bl {vg_sha1_finalize_scratch}
	ldr r1, [sp], #8
	movw r12, #860
	add r2, r11, r12
	movw r3, #20
	b 26f
25:
	mov r2, r8
	mov r3, r9
26:
	mov r0, r5
	mov r1, r6
	mov r12, r11
	push {r12, lr}
	bl {vg_hmac_sha1_init_scratch}
	ldr r12, [sp], #8
	ldr r4, [r11, #448]
	ldr r5, [r11, #452]
	ldr r6, [r11, #456]
	ldr r7, [r11, #460]
	ldr r8, [r11, #464]
	ldr r9, [r11, #468]
	ldr r10, [r11, #472]
	ldr lr, [r11, #476]
	ldr r11, [r11, #480]
	add sp, sp, #1152
	b 21b

vg_hmac_sha1_finalize:
	sub sp, sp, #480
	add r12, sp, #0
	str lr, [r12, #8]
	ldr lr, [sp, #480]
	str lr, [r12, #0]
	add lr, sp, #12
	str lr, [r12, #4]
	ldr lr, [sp, #8]
	ldr r12, [sp, #4]
	str r4, [r12, #160]
	str r5, [r12, #164]
	str r6, [r12, #168]
	str r7, [r12, #172]
	str r8, [r12, #176]
	str r9, [r12, #180]
	str r10, [r12, #184]
	str lr, [r12, #188]
	str r11, [r12, #192]
	mov r5, r1
	ldr r7, [sp, #0]
	mov r11, r12
	movw r12, #216
	add r1, r11, r12
	mov r12, r11
	push {r1, r12}
	bl {vg_sha1_finalize_scratch}
	ldr r1, [sp], #8
	mov r3, r11
	movw r12, #196
	add r0, r11, r12
	movw r12, #216
	add r6, r11, r12
	ldr r12, [r5, #0]
	str r12, [r0, #0]
	ldr r12, [r5, #4]
	str r12, [r0, #4]
	ldr r12, [r5, #8]
	str r12, [r0, #8]
	ldr r12, [r5, #12]
	str r12, [r0, #12]
	ldr r12, [r5, #16]
	str r12, [r0, #16]
	mov r12, #128
	str r12, [r6, #20]
	mov r12, #0
	str r12, [r6, #24]
	str r12, [r6, #28]
	str r12, [r6, #32]
	str r12, [r6, #36]
	str r12, [r6, #40]
	str r12, [r6, #44]
	str r12, [r6, #48]
	str r12, [r6, #52]
	movw r12, #0
	movt r12, #0
	str r12, [r6, #56]
	movw r12, #0
	movt r12, #40962
	str r12, [r6, #60]
	mov r1, r6
	mov r2, #1
	bl {vg_sha1_compress}
	mov r6, r7
	ldr r9, [r0, #0]
	rev r9, r9
	str r9, [r6, #0]
	ldr r9, [r0, #4]
	rev r9, r9
	str r9, [r6, #4]
	ldr r9, [r0, #8]
	rev r9, r9
	str r9, [r6, #8]
	ldr r9, [r0, #12]
	rev r9, r9
	str r9, [r6, #12]
	ldr r9, [r0, #16]
	rev r9, r9
	str r9, [r6, #16]
	ldr r4, [r11, #160]
	ldr r5, [r11, #164]
	ldr r6, [r11, #168]
	ldr r7, [r11, #172]
	ldr r8, [r11, #176]
	ldr r9, [r11, #180]
	ldr r10, [r11, #184]
	ldr lr, [r11, #188]
	ldr r11, [r11, #192]
	add sp, sp, #480
	sub sp, sp, #496
	add r12, sp, #0
	mov r2, #0
	mov r3, #15
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
	add sp, sp, #496
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
