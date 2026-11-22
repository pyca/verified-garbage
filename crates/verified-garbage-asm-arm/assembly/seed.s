// The functions of `src/seed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_expand_key:
	sub sp, sp, #752
	add r2, sp, #0
	str r4, [r2, #704]
	str r5, [r2, #708]
	str r6, [r2, #712]
	str r7, [r2, #716]
	str r8, [r2, #720]
	str r9, [r2, #724]
	str r10, [r2, #728]
	str r11, [r2, #732]
	str lr, [r2, #736]
	mov r8, r2
	mov r9, r1
	ldr r4, [r0, #0]
	rev r4, r4
	ldr r5, [r0, #4]
	rev r5, r5
	ldr r6, [r0, #8]
	rev r6, r6
	ldr r7, [r0, #12]
	rev r7, r7
	add r10, r4, r6
	movw r11, #31161
	movt r11, #40503
	sub r10, r10, r11
	str r10, [r8, #224]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #228]
	lsr r10, r4, #8
	orr r10, r10, r5, lsl #24
	lsr r11, r5, #8
	orr r5, r11, r4, lsl #24
	mov r4, r10
	add r10, r4, r6
	movw r11, #62323
	movt r11, #15470
	sub r10, r10, r11
	str r10, [r8, #232]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #236]
	lsl r10, r6, #8
	orr r10, r10, r7, lsr #24
	lsl r11, r7, #8
	orr r7, r11, r6, lsr #24
	mov r6, r10
	add r10, r4, r6
	movw r11, #59110
	movt r11, #30941
	sub r10, r10, r11
	str r10, [r8, #240]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #244]
	lsr r10, r4, #8
	orr r10, r10, r5, lsl #24
	lsr r11, r5, #8
	orr r5, r11, r4, lsl #24
	mov r4, r10
	add r10, r4, r6
	movw r11, #52684
	movt r11, #61883
	sub r10, r10, r11
	str r10, [r8, #248]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #252]
	lsl r10, r6, #8
	orr r10, r10, r7, lsr #24
	lsl r11, r7, #8
	orr r7, r11, r6, lsr #24
	mov r6, r10
	add r10, r4, r6
	movw r11, #39833
	movt r11, #58231
	sub r10, r10, r11
	str r10, [r8, #256]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #260]
	lsr r10, r4, #8
	orr r10, r10, r5, lsl #24
	lsr r11, r5, #8
	orr r5, r11, r4, lsl #24
	mov r4, r10
	add r10, r4, r6
	movw r11, #14131
	movt r11, #50927
	sub r10, r10, r11
	str r10, [r8, #264]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #268]
	lsl r10, r6, #8
	orr r10, r10, r7, lsr #24
	lsl r11, r7, #8
	orr r7, r11, r6, lsr #24
	mov r6, r10
	add r10, r4, r6
	movw r11, #28263
	movt r11, #36318
	sub r10, r10, r11
	str r10, [r8, #272]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #276]
	lsr r10, r4, #8
	orr r10, r10, r5, lsl #24
	lsr r11, r5, #8
	orr r5, r11, r4, lsl #24
	mov r4, r10
	add r10, r4, r6
	movw r11, #56527
	movt r11, #7100
	sub r10, r10, r11
	str r10, [r8, #280]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #284]
	lsl r10, r6, #8
	orr r10, r10, r7, lsr #24
	lsl r11, r7, #8
	orr r7, r11, r6, lsr #24
	mov r6, r10
	add r10, r4, r6
	movw r11, #47518
	movt r11, #14201
	sub r10, r10, r11
	str r10, [r8, #288]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #292]
	lsr r10, r4, #8
	orr r10, r10, r5, lsl #24
	lsr r11, r5, #8
	orr r5, r11, r4, lsl #24
	mov r4, r10
	add r10, r4, r6
	movw r11, #29500
	movt r11, #28403
	sub r10, r10, r11
	str r10, [r8, #296]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #300]
	lsl r10, r6, #8
	orr r10, r10, r7, lsr #24
	lsl r11, r7, #8
	orr r7, r11, r6, lsr #24
	mov r6, r10
	add r10, r4, r6
	movw r11, #59000
	movt r11, #56806
	sub r10, r10, r11
	str r10, [r8, #304]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #308]
	lsr r10, r4, #8
	orr r10, r10, r5, lsl #24
	lsr r11, r5, #8
	orr r5, r11, r4, lsl #24
	mov r4, r10
	add r10, r4, r6
	movw r11, #52465
	movt r11, #48077
	sub r10, r10, r11
	str r10, [r8, #312]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #316]
	lsl r10, r6, #8
	orr r10, r10, r7, lsr #24
	lsl r11, r7, #8
	orr r7, r11, r6, lsr #24
	mov r6, r10
	add r10, r4, r6
	movw r11, #39395
	movt r11, #30619
	sub r10, r10, r11
	str r10, [r8, #320]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #324]
	lsr r10, r4, #8
	orr r10, r10, r5, lsl #24
	lsr r11, r5, #8
	orr r5, r11, r4, lsl #24
	mov r4, r10
	add r10, r4, r6
	movw r11, #13254
	movt r11, #61239
	sub r10, r10, r11
	str r10, [r8, #328]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #332]
	lsl r10, r6, #8
	orr r10, r10, r7, lsr #24
	lsl r11, r7, #8
	orr r7, r11, r6, lsr #24
	mov r6, r10
	add r10, r4, r6
	movw r11, #26509
	movt r11, #56942
	sub r10, r10, r11
	str r10, [r8, #336]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #340]
	lsr r10, r4, #8
	orr r10, r10, r5, lsl #24
	lsr r11, r5, #8
	orr r5, r11, r4, lsl #24
	mov r4, r10
	add r10, r4, r6
	movw r11, #53019
	movt r11, #48348
	sub r10, r10, r11
	str r10, [r8, #344]
	sub r10, r5, r7
	add r10, r10, r11
	str r10, [r8, #348]
	lsl r10, r6, #8
	orr r10, r10, r7, lsr #24
	lsl r11, r7, #8
	orr r7, r11, r6, lsr #24
	mov r6, r10
	ldr r10, [r8, #224]
	str r10, [r8, #160]
	ldr r10, [r8, #228]
	str r10, [r8, #164]
	ldr r10, [r8, #232]
	str r10, [r8, #168]
	ldr r10, [r8, #236]
	str r10, [r8, #172]
	ldr r10, [r8, #240]
	str r10, [r8, #176]
	ldr r10, [r8, #244]
	str r10, [r8, #180]
	ldr r10, [r8, #248]
	str r10, [r8, #184]
	ldr r10, [r8, #252]
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	str r10, [r9, #0]
	ldr r10, [r8, #164]
	str r10, [r9, #4]
	ldr r10, [r8, #168]
	str r10, [r9, #8]
	ldr r10, [r8, #172]
	str r10, [r9, #12]
	ldr r10, [r8, #176]
	str r10, [r9, #16]
	ldr r10, [r8, #180]
	str r10, [r9, #20]
	ldr r10, [r8, #184]
	str r10, [r9, #24]
	ldr r10, [r8, #188]
	str r10, [r9, #28]
	ldr r10, [r8, #256]
	str r10, [r8, #160]
	ldr r10, [r8, #260]
	str r10, [r8, #164]
	ldr r10, [r8, #264]
	str r10, [r8, #168]
	ldr r10, [r8, #268]
	str r10, [r8, #172]
	ldr r10, [r8, #272]
	str r10, [r8, #176]
	ldr r10, [r8, #276]
	str r10, [r8, #180]
	ldr r10, [r8, #280]
	str r10, [r8, #184]
	ldr r10, [r8, #284]
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	str r10, [r9, #32]
	ldr r10, [r8, #164]
	str r10, [r9, #36]
	ldr r10, [r8, #168]
	str r10, [r9, #40]
	ldr r10, [r8, #172]
	str r10, [r9, #44]
	ldr r10, [r8, #176]
	str r10, [r9, #48]
	ldr r10, [r8, #180]
	str r10, [r9, #52]
	ldr r10, [r8, #184]
	str r10, [r9, #56]
	ldr r10, [r8, #188]
	str r10, [r9, #60]
	ldr r10, [r8, #288]
	str r10, [r8, #160]
	ldr r10, [r8, #292]
	str r10, [r8, #164]
	ldr r10, [r8, #296]
	str r10, [r8, #168]
	ldr r10, [r8, #300]
	str r10, [r8, #172]
	ldr r10, [r8, #304]
	str r10, [r8, #176]
	ldr r10, [r8, #308]
	str r10, [r8, #180]
	ldr r10, [r8, #312]
	str r10, [r8, #184]
	ldr r10, [r8, #316]
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	str r10, [r9, #64]
	ldr r10, [r8, #164]
	str r10, [r9, #68]
	ldr r10, [r8, #168]
	str r10, [r9, #72]
	ldr r10, [r8, #172]
	str r10, [r9, #76]
	ldr r10, [r8, #176]
	str r10, [r9, #80]
	ldr r10, [r8, #180]
	str r10, [r9, #84]
	ldr r10, [r8, #184]
	str r10, [r9, #88]
	ldr r10, [r8, #188]
	str r10, [r9, #92]
	ldr r10, [r8, #320]
	str r10, [r8, #160]
	ldr r10, [r8, #324]
	str r10, [r8, #164]
	ldr r10, [r8, #328]
	str r10, [r8, #168]
	ldr r10, [r8, #332]
	str r10, [r8, #172]
	ldr r10, [r8, #336]
	str r10, [r8, #176]
	ldr r10, [r8, #340]
	str r10, [r8, #180]
	ldr r10, [r8, #344]
	str r10, [r8, #184]
	ldr r10, [r8, #348]
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	str r10, [r9, #96]
	ldr r10, [r8, #164]
	str r10, [r9, #100]
	ldr r10, [r8, #168]
	str r10, [r9, #104]
	ldr r10, [r8, #172]
	str r10, [r9, #108]
	ldr r10, [r8, #176]
	str r10, [r9, #112]
	ldr r10, [r8, #180]
	str r10, [r9, #116]
	ldr r10, [r8, #184]
	str r10, [r9, #120]
	ldr r10, [r8, #188]
	str r10, [r9, #124]
	mov r12, r8
	ldr r4, [r12, #704]
	ldr r5, [r12, #708]
	ldr r6, [r12, #712]
	ldr r7, [r12, #716]
	ldr r8, [r12, #720]
	ldr r9, [r12, #724]
	ldr r10, [r12, #728]
	ldr r11, [r12, #732]
	ldr lr, [r12, #736]
	add sp, sp, #752
	sub sp, sp, #752
	add r12, sp, #0
	mov r2, #0
	mov r3, #23
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
	add sp, sp, #752
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_seed_ecb_encrypt:
	push {r4, lr}
	mov r4, lr
	bl {vg_seed_ecb_encrypt_core}
	mov lr, r4
	ldr r4, [sp], #8
	sub sp, sp, #760
	add r12, sp, #0
	mov r2, #0
	mov r3, #23
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
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #760
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_seed_ecb_decrypt:
	push {r4, lr}
	mov r4, lr
	bl {vg_seed_ecb_decrypt_core}
	mov lr, r4
	ldr r4, [sp], #8
	sub sp, sp, #760
	add r12, sp, #0
	mov r2, #0
	mov r3, #23
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
	str r2, [r12, #16]
	str r2, [r12, #20]
	add sp, sp, #760
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
