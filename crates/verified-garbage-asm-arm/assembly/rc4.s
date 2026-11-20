// The functions of `src/rc4.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc4_init:
	sub sp, sp, #64
	add r3, sp, #0
	sub r12, r1, #1
	lsr r12, r12, #8
	cmp r12, #0
	bne 20f
	str r4, [r3, #0]
	str r5, [r3, #4]
	str r6, [r3, #8]
	str r7, [r3, #12]
	str r8, [r3, #16]
	str r9, [r3, #20]
	str r10, [r3, #24]
	str r11, [r3, #28]
	mov r12, r2
	mov r4, #0
22:
	add r9, r12, r4
	strb r4, [r9, #0]
	add r4, r4, #1
	cmp r4, #256
	bne 22b
	mov r4, #0
	mov r2, #0
	mov r5, #0
	movw r10, #65535
	movt r10, #65535
23:
	add r9, r12, r4
	ldrb r11, [r9, #0]
	add r5, r5, r11
	add r9, r0, r2
	ldrb r9, [r9, #0]
	add r5, r5, r9
	and r5, r5, #255
	mov r6, r5
	lsl r11, r6, #28
	lsr r11, r11, #31
	add r10, r11, #1
	lsl r11, r6, #27
	lsr r11, r11, #31
	lsl r9, r10, #2
	sub r9, r9, r10
	mla r10, r9, r11, r10
	lsl r11, r6, #26
	lsr r11, r11, #31
	lsl r9, r10, #4
	sub r9, r9, r10
	mla r10, r9, r11, r10
	lsl r11, r6, #25
	lsr r11, r11, #31
	lsl r9, r10, #8
	sub r9, r9, r10
	mla r10, r9, r11, r10
	lsl r11, r6, #24
	lsr r11, r11, #31
	lsl r9, r10, #16
	sub r9, r9, r10
	mla r10, r9, r11, r10
	mov r7, #0
	mov r8, #0
	lsl r11, r10, #31
	lsr r11, r11, #31
	ldr r9, [r12, #0]
	mla r7, r9, r11, r7
	ldr r9, [r12, #4]
	mla r8, r9, r11, r8
	lsl r11, r10, #30
	lsr r11, r11, #31
	ldr r9, [r12, #8]
	mla r7, r9, r11, r7
	ldr r9, [r12, #12]
	mla r8, r9, r11, r8
	lsl r11, r10, #29
	lsr r11, r11, #31
	ldr r9, [r12, #16]
	mla r7, r9, r11, r7
	ldr r9, [r12, #20]
	mla r8, r9, r11, r8
	lsl r11, r10, #28
	lsr r11, r11, #31
	ldr r9, [r12, #24]
	mla r7, r9, r11, r7
	ldr r9, [r12, #28]
	mla r8, r9, r11, r8
	lsl r11, r10, #27
	lsr r11, r11, #31
	ldr r9, [r12, #32]
	mla r7, r9, r11, r7
	ldr r9, [r12, #36]
	mla r8, r9, r11, r8
	lsl r11, r10, #26
	lsr r11, r11, #31
	ldr r9, [r12, #40]
	mla r7, r9, r11, r7
	ldr r9, [r12, #44]
	mla r8, r9, r11, r8
	lsl r11, r10, #25
	lsr r11, r11, #31
	ldr r9, [r12, #48]
	mla r7, r9, r11, r7
	ldr r9, [r12, #52]
	mla r8, r9, r11, r8
	lsl r11, r10, #24
	lsr r11, r11, #31
	ldr r9, [r12, #56]
	mla r7, r9, r11, r7
	ldr r9, [r12, #60]
	mla r8, r9, r11, r8
	lsl r11, r10, #23
	lsr r11, r11, #31
	ldr r9, [r12, #64]
	mla r7, r9, r11, r7
	ldr r9, [r12, #68]
	mla r8, r9, r11, r8
	lsl r11, r10, #22
	lsr r11, r11, #31
	ldr r9, [r12, #72]
	mla r7, r9, r11, r7
	ldr r9, [r12, #76]
	mla r8, r9, r11, r8
	lsl r11, r10, #21
	lsr r11, r11, #31
	ldr r9, [r12, #80]
	mla r7, r9, r11, r7
	ldr r9, [r12, #84]
	mla r8, r9, r11, r8
	lsl r11, r10, #20
	lsr r11, r11, #31
	ldr r9, [r12, #88]
	mla r7, r9, r11, r7
	ldr r9, [r12, #92]
	mla r8, r9, r11, r8
	lsl r11, r10, #19
	lsr r11, r11, #31
	ldr r9, [r12, #96]
	mla r7, r9, r11, r7
	ldr r9, [r12, #100]
	mla r8, r9, r11, r8
	lsl r11, r10, #18
	lsr r11, r11, #31
	ldr r9, [r12, #104]
	mla r7, r9, r11, r7
	ldr r9, [r12, #108]
	mla r8, r9, r11, r8
	lsl r11, r10, #17
	lsr r11, r11, #31
	ldr r9, [r12, #112]
	mla r7, r9, r11, r7
	ldr r9, [r12, #116]
	mla r8, r9, r11, r8
	lsl r11, r10, #16
	lsr r11, r11, #31
	ldr r9, [r12, #120]
	mla r7, r9, r11, r7
	ldr r9, [r12, #124]
	mla r8, r9, r11, r8
	lsl r11, r10, #15
	lsr r11, r11, #31
	ldr r9, [r12, #128]
	mla r7, r9, r11, r7
	ldr r9, [r12, #132]
	mla r8, r9, r11, r8
	lsl r11, r10, #14
	lsr r11, r11, #31
	ldr r9, [r12, #136]
	mla r7, r9, r11, r7
	ldr r9, [r12, #140]
	mla r8, r9, r11, r8
	lsl r11, r10, #13
	lsr r11, r11, #31
	ldr r9, [r12, #144]
	mla r7, r9, r11, r7
	ldr r9, [r12, #148]
	mla r8, r9, r11, r8
	lsl r11, r10, #12
	lsr r11, r11, #31
	ldr r9, [r12, #152]
	mla r7, r9, r11, r7
	ldr r9, [r12, #156]
	mla r8, r9, r11, r8
	lsl r11, r10, #11
	lsr r11, r11, #31
	ldr r9, [r12, #160]
	mla r7, r9, r11, r7
	ldr r9, [r12, #164]
	mla r8, r9, r11, r8
	lsl r11, r10, #10
	lsr r11, r11, #31
	ldr r9, [r12, #168]
	mla r7, r9, r11, r7
	ldr r9, [r12, #172]
	mla r8, r9, r11, r8
	lsl r11, r10, #9
	lsr r11, r11, #31
	ldr r9, [r12, #176]
	mla r7, r9, r11, r7
	ldr r9, [r12, #180]
	mla r8, r9, r11, r8
	lsl r11, r10, #8
	lsr r11, r11, #31
	ldr r9, [r12, #184]
	mla r7, r9, r11, r7
	ldr r9, [r12, #188]
	mla r8, r9, r11, r8
	lsl r11, r10, #7
	lsr r11, r11, #31
	ldr r9, [r12, #192]
	mla r7, r9, r11, r7
	ldr r9, [r12, #196]
	mla r8, r9, r11, r8
	lsl r11, r10, #6
	lsr r11, r11, #31
	ldr r9, [r12, #200]
	mla r7, r9, r11, r7
	ldr r9, [r12, #204]
	mla r8, r9, r11, r8
	lsl r11, r10, #5
	lsr r11, r11, #31
	ldr r9, [r12, #208]
	mla r7, r9, r11, r7
	ldr r9, [r12, #212]
	mla r8, r9, r11, r8
	lsl r11, r10, #4
	lsr r11, r11, #31
	ldr r9, [r12, #216]
	mla r7, r9, r11, r7
	ldr r9, [r12, #220]
	mla r8, r9, r11, r8
	lsl r11, r10, #3
	lsr r11, r11, #31
	ldr r9, [r12, #224]
	mla r7, r9, r11, r7
	ldr r9, [r12, #228]
	mla r8, r9, r11, r8
	lsl r11, r10, #2
	lsr r11, r11, #31
	ldr r9, [r12, #232]
	mla r7, r9, r11, r7
	ldr r9, [r12, #236]
	mla r8, r9, r11, r8
	lsl r11, r10, #1
	lsr r11, r11, #31
	ldr r9, [r12, #240]
	mla r7, r9, r11, r7
	ldr r9, [r12, #244]
	mla r8, r9, r11, r8
	lsr r11, r10, #31
	ldr r9, [r12, #248]
	mla r7, r9, r11, r7
	ldr r9, [r12, #252]
	mla r8, r9, r11, r8
	lsl r11, r6, #29
	lsr r11, r11, #31
	sub r8, r8, r7
	mla r7, r8, r11, r7
	lsl r11, r6, #31
	lsr r11, r11, #31
	lsl r8, r11, #8
	sub r8, r8, r11
	add r8, r8, #1
	lsl r11, r6, #30
	lsr r11, r11, #31
	lsl r9, r11, #16
	sub r9, r9, r11
	add r9, r9, #1
	mul r8, r8, r9
	add r9, r12, r4
	ldrb r11, [r9, #0]
	mul r11, r11, r8
	lsl r9, r8, #8
	sub r9, r9, r8
	bic r8, r7, r9
	orr r8, r8, r11
	sub r8, r8, r7
	lsl r11, r6, #31
	lsr r11, r11, #31
	lsr r9, r7, #8
	sub r9, r9, r7
	mla r7, r9, r11, r7
	lsl r11, r6, #30
	lsr r11, r11, #31
	lsr r9, r7, #16
	sub r9, r9, r7
	mla r7, r9, r11, r7
	and r7, r7, #255
	lsl r9, r6, #29
	lsr r9, r9, #31
	mul r11, r8, r9
	sub r8, r8, r11
	lsl r9, r10, #31
	lsr r9, r9, #31
	ldr r6, [r12, #0]
	mla r6, r8, r9, r6
	str r6, [r12, #0]
	ldr r6, [r12, #4]
	mla r6, r11, r9, r6
	str r6, [r12, #4]
	lsl r9, r10, #30
	lsr r9, r9, #31
	ldr r6, [r12, #8]
	mla r6, r8, r9, r6
	str r6, [r12, #8]
	ldr r6, [r12, #12]
	mla r6, r11, r9, r6
	str r6, [r12, #12]
	lsl r9, r10, #29
	lsr r9, r9, #31
	ldr r6, [r12, #16]
	mla r6, r8, r9, r6
	str r6, [r12, #16]
	ldr r6, [r12, #20]
	mla r6, r11, r9, r6
	str r6, [r12, #20]
	lsl r9, r10, #28
	lsr r9, r9, #31
	ldr r6, [r12, #24]
	mla r6, r8, r9, r6
	str r6, [r12, #24]
	ldr r6, [r12, #28]
	mla r6, r11, r9, r6
	str r6, [r12, #28]
	lsl r9, r10, #27
	lsr r9, r9, #31
	ldr r6, [r12, #32]
	mla r6, r8, r9, r6
	str r6, [r12, #32]
	ldr r6, [r12, #36]
	mla r6, r11, r9, r6
	str r6, [r12, #36]
	lsl r9, r10, #26
	lsr r9, r9, #31
	ldr r6, [r12, #40]
	mla r6, r8, r9, r6
	str r6, [r12, #40]
	ldr r6, [r12, #44]
	mla r6, r11, r9, r6
	str r6, [r12, #44]
	lsl r9, r10, #25
	lsr r9, r9, #31
	ldr r6, [r12, #48]
	mla r6, r8, r9, r6
	str r6, [r12, #48]
	ldr r6, [r12, #52]
	mla r6, r11, r9, r6
	str r6, [r12, #52]
	lsl r9, r10, #24
	lsr r9, r9, #31
	ldr r6, [r12, #56]
	mla r6, r8, r9, r6
	str r6, [r12, #56]
	ldr r6, [r12, #60]
	mla r6, r11, r9, r6
	str r6, [r12, #60]
	lsl r9, r10, #23
	lsr r9, r9, #31
	ldr r6, [r12, #64]
	mla r6, r8, r9, r6
	str r6, [r12, #64]
	ldr r6, [r12, #68]
	mla r6, r11, r9, r6
	str r6, [r12, #68]
	lsl r9, r10, #22
	lsr r9, r9, #31
	ldr r6, [r12, #72]
	mla r6, r8, r9, r6
	str r6, [r12, #72]
	ldr r6, [r12, #76]
	mla r6, r11, r9, r6
	str r6, [r12, #76]
	lsl r9, r10, #21
	lsr r9, r9, #31
	ldr r6, [r12, #80]
	mla r6, r8, r9, r6
	str r6, [r12, #80]
	ldr r6, [r12, #84]
	mla r6, r11, r9, r6
	str r6, [r12, #84]
	lsl r9, r10, #20
	lsr r9, r9, #31
	ldr r6, [r12, #88]
	mla r6, r8, r9, r6
	str r6, [r12, #88]
	ldr r6, [r12, #92]
	mla r6, r11, r9, r6
	str r6, [r12, #92]
	lsl r9, r10, #19
	lsr r9, r9, #31
	ldr r6, [r12, #96]
	mla r6, r8, r9, r6
	str r6, [r12, #96]
	ldr r6, [r12, #100]
	mla r6, r11, r9, r6
	str r6, [r12, #100]
	lsl r9, r10, #18
	lsr r9, r9, #31
	ldr r6, [r12, #104]
	mla r6, r8, r9, r6
	str r6, [r12, #104]
	ldr r6, [r12, #108]
	mla r6, r11, r9, r6
	str r6, [r12, #108]
	lsl r9, r10, #17
	lsr r9, r9, #31
	ldr r6, [r12, #112]
	mla r6, r8, r9, r6
	str r6, [r12, #112]
	ldr r6, [r12, #116]
	mla r6, r11, r9, r6
	str r6, [r12, #116]
	lsl r9, r10, #16
	lsr r9, r9, #31
	ldr r6, [r12, #120]
	mla r6, r8, r9, r6
	str r6, [r12, #120]
	ldr r6, [r12, #124]
	mla r6, r11, r9, r6
	str r6, [r12, #124]
	lsl r9, r10, #15
	lsr r9, r9, #31
	ldr r6, [r12, #128]
	mla r6, r8, r9, r6
	str r6, [r12, #128]
	ldr r6, [r12, #132]
	mla r6, r11, r9, r6
	str r6, [r12, #132]
	lsl r9, r10, #14
	lsr r9, r9, #31
	ldr r6, [r12, #136]
	mla r6, r8, r9, r6
	str r6, [r12, #136]
	ldr r6, [r12, #140]
	mla r6, r11, r9, r6
	str r6, [r12, #140]
	lsl r9, r10, #13
	lsr r9, r9, #31
	ldr r6, [r12, #144]
	mla r6, r8, r9, r6
	str r6, [r12, #144]
	ldr r6, [r12, #148]
	mla r6, r11, r9, r6
	str r6, [r12, #148]
	lsl r9, r10, #12
	lsr r9, r9, #31
	ldr r6, [r12, #152]
	mla r6, r8, r9, r6
	str r6, [r12, #152]
	ldr r6, [r12, #156]
	mla r6, r11, r9, r6
	str r6, [r12, #156]
	lsl r9, r10, #11
	lsr r9, r9, #31
	ldr r6, [r12, #160]
	mla r6, r8, r9, r6
	str r6, [r12, #160]
	ldr r6, [r12, #164]
	mla r6, r11, r9, r6
	str r6, [r12, #164]
	lsl r9, r10, #10
	lsr r9, r9, #31
	ldr r6, [r12, #168]
	mla r6, r8, r9, r6
	str r6, [r12, #168]
	ldr r6, [r12, #172]
	mla r6, r11, r9, r6
	str r6, [r12, #172]
	lsl r9, r10, #9
	lsr r9, r9, #31
	ldr r6, [r12, #176]
	mla r6, r8, r9, r6
	str r6, [r12, #176]
	ldr r6, [r12, #180]
	mla r6, r11, r9, r6
	str r6, [r12, #180]
	lsl r9, r10, #8
	lsr r9, r9, #31
	ldr r6, [r12, #184]
	mla r6, r8, r9, r6
	str r6, [r12, #184]
	ldr r6, [r12, #188]
	mla r6, r11, r9, r6
	str r6, [r12, #188]
	lsl r9, r10, #7
	lsr r9, r9, #31
	ldr r6, [r12, #192]
	mla r6, r8, r9, r6
	str r6, [r12, #192]
	ldr r6, [r12, #196]
	mla r6, r11, r9, r6
	str r6, [r12, #196]
	lsl r9, r10, #6
	lsr r9, r9, #31
	ldr r6, [r12, #200]
	mla r6, r8, r9, r6
	str r6, [r12, #200]
	ldr r6, [r12, #204]
	mla r6, r11, r9, r6
	str r6, [r12, #204]
	lsl r9, r10, #5
	lsr r9, r9, #31
	ldr r6, [r12, #208]
	mla r6, r8, r9, r6
	str r6, [r12, #208]
	ldr r6, [r12, #212]
	mla r6, r11, r9, r6
	str r6, [r12, #212]
	lsl r9, r10, #4
	lsr r9, r9, #31
	ldr r6, [r12, #216]
	mla r6, r8, r9, r6
	str r6, [r12, #216]
	ldr r6, [r12, #220]
	mla r6, r11, r9, r6
	str r6, [r12, #220]
	lsl r9, r10, #3
	lsr r9, r9, #31
	ldr r6, [r12, #224]
	mla r6, r8, r9, r6
	str r6, [r12, #224]
	ldr r6, [r12, #228]
	mla r6, r11, r9, r6
	str r6, [r12, #228]
	lsl r9, r10, #2
	lsr r9, r9, #31
	ldr r6, [r12, #232]
	mla r6, r8, r9, r6
	str r6, [r12, #232]
	ldr r6, [r12, #236]
	mla r6, r11, r9, r6
	str r6, [r12, #236]
	lsl r9, r10, #1
	lsr r9, r9, #31
	ldr r6, [r12, #240]
	mla r6, r8, r9, r6
	str r6, [r12, #240]
	ldr r6, [r12, #244]
	mla r6, r11, r9, r6
	str r6, [r12, #244]
	lsr r9, r10, #31
	ldr r6, [r12, #248]
	mla r6, r8, r9, r6
	str r6, [r12, #248]
	ldr r6, [r12, #252]
	mla r6, r11, r9, r6
	str r6, [r12, #252]
	movw r10, #65535
	movt r10, #65535
	add r2, r2, #1
	cmp r2, r1
	adc r9, r10, #0
	and r2, r2, r9
	add r9, r12, r4
	strb r7, [r9, #0]
	add r4, r4, #1
	cmp r4, #256
	bne 23b
	mov r9, #0
	strb r9, [r12, #256]
	strb r9, [r12, #257]
	ldr r4, [r3, #0]
	ldr r5, [r3, #4]
	ldr r6, [r3, #8]
	ldr r7, [r3, #12]
	ldr r8, [r3, #16]
	ldr r9, [r3, #20]
	ldr r10, [r3, #24]
	ldr r11, [r3, #28]
	mov r0, #0
	b 21f
20:
	mov r0, #1
21:
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	str r2, [r12, #56]
	str r2, [r12, #60]
	add sp, sp, #64
	sub sp, sp, #64
	add r12, sp, #0
	mov r2, #0
	mov r3, #2
24:
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
	bne 24b
	add sp, sp, #64
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_rc4_apply:
	sub sp, sp, #64
	add r3, sp, #0
	ldrb r12, [r0, #256]
	cmp r2, #0
	beq 20f
	str r4, [r3, #0]
	str r5, [r3, #4]
	str r6, [r3, #8]
	str r7, [r3, #12]
	str r8, [r3, #16]
	str r9, [r3, #20]
	str r10, [r3, #24]
	str r11, [r3, #28]
	mov r4, r12
	mov r12, r0
	ldrb r5, [r12, #257]
	mov r0, #0
	movw r10, #65535
	movt r10, #65535
22:
	add r4, r4, #1
	and r4, r4, #255
	add r9, r12, r4
	ldrb r11, [r9, #0]
	add r5, r5, r11
	and r5, r5, #255
	mov r6, r5
	lsl r11, r6, #28
	lsr r11, r11, #31
	add r10, r11, #1
	lsl r11, r6, #27
	lsr r11, r11, #31
	lsl r9, r10, #2
	sub r9, r9, r10
	mla r10, r9, r11, r10
	lsl r11, r6, #26
	lsr r11, r11, #31
	lsl r9, r10, #4
	sub r9, r9, r10
	mla r10, r9, r11, r10
	lsl r11, r6, #25
	lsr r11, r11, #31
	lsl r9, r10, #8
	sub r9, r9, r10
	mla r10, r9, r11, r10
	lsl r11, r6, #24
	lsr r11, r11, #31
	lsl r9, r10, #16
	sub r9, r9, r10
	mla r10, r9, r11, r10
	mov r7, #0
	mov r8, #0
	lsl r11, r10, #31
	lsr r11, r11, #31
	ldr r9, [r12, #0]
	mla r7, r9, r11, r7
	ldr r9, [r12, #4]
	mla r8, r9, r11, r8
	lsl r11, r10, #30
	lsr r11, r11, #31
	ldr r9, [r12, #8]
	mla r7, r9, r11, r7
	ldr r9, [r12, #12]
	mla r8, r9, r11, r8
	lsl r11, r10, #29
	lsr r11, r11, #31
	ldr r9, [r12, #16]
	mla r7, r9, r11, r7
	ldr r9, [r12, #20]
	mla r8, r9, r11, r8
	lsl r11, r10, #28
	lsr r11, r11, #31
	ldr r9, [r12, #24]
	mla r7, r9, r11, r7
	ldr r9, [r12, #28]
	mla r8, r9, r11, r8
	lsl r11, r10, #27
	lsr r11, r11, #31
	ldr r9, [r12, #32]
	mla r7, r9, r11, r7
	ldr r9, [r12, #36]
	mla r8, r9, r11, r8
	lsl r11, r10, #26
	lsr r11, r11, #31
	ldr r9, [r12, #40]
	mla r7, r9, r11, r7
	ldr r9, [r12, #44]
	mla r8, r9, r11, r8
	lsl r11, r10, #25
	lsr r11, r11, #31
	ldr r9, [r12, #48]
	mla r7, r9, r11, r7
	ldr r9, [r12, #52]
	mla r8, r9, r11, r8
	lsl r11, r10, #24
	lsr r11, r11, #31
	ldr r9, [r12, #56]
	mla r7, r9, r11, r7
	ldr r9, [r12, #60]
	mla r8, r9, r11, r8
	lsl r11, r10, #23
	lsr r11, r11, #31
	ldr r9, [r12, #64]
	mla r7, r9, r11, r7
	ldr r9, [r12, #68]
	mla r8, r9, r11, r8
	lsl r11, r10, #22
	lsr r11, r11, #31
	ldr r9, [r12, #72]
	mla r7, r9, r11, r7
	ldr r9, [r12, #76]
	mla r8, r9, r11, r8
	lsl r11, r10, #21
	lsr r11, r11, #31
	ldr r9, [r12, #80]
	mla r7, r9, r11, r7
	ldr r9, [r12, #84]
	mla r8, r9, r11, r8
	lsl r11, r10, #20
	lsr r11, r11, #31
	ldr r9, [r12, #88]
	mla r7, r9, r11, r7
	ldr r9, [r12, #92]
	mla r8, r9, r11, r8
	lsl r11, r10, #19
	lsr r11, r11, #31
	ldr r9, [r12, #96]
	mla r7, r9, r11, r7
	ldr r9, [r12, #100]
	mla r8, r9, r11, r8
	lsl r11, r10, #18
	lsr r11, r11, #31
	ldr r9, [r12, #104]
	mla r7, r9, r11, r7
	ldr r9, [r12, #108]
	mla r8, r9, r11, r8
	lsl r11, r10, #17
	lsr r11, r11, #31
	ldr r9, [r12, #112]
	mla r7, r9, r11, r7
	ldr r9, [r12, #116]
	mla r8, r9, r11, r8
	lsl r11, r10, #16
	lsr r11, r11, #31
	ldr r9, [r12, #120]
	mla r7, r9, r11, r7
	ldr r9, [r12, #124]
	mla r8, r9, r11, r8
	lsl r11, r10, #15
	lsr r11, r11, #31
	ldr r9, [r12, #128]
	mla r7, r9, r11, r7
	ldr r9, [r12, #132]
	mla r8, r9, r11, r8
	lsl r11, r10, #14
	lsr r11, r11, #31
	ldr r9, [r12, #136]
	mla r7, r9, r11, r7
	ldr r9, [r12, #140]
	mla r8, r9, r11, r8
	lsl r11, r10, #13
	lsr r11, r11, #31
	ldr r9, [r12, #144]
	mla r7, r9, r11, r7
	ldr r9, [r12, #148]
	mla r8, r9, r11, r8
	lsl r11, r10, #12
	lsr r11, r11, #31
	ldr r9, [r12, #152]
	mla r7, r9, r11, r7
	ldr r9, [r12, #156]
	mla r8, r9, r11, r8
	lsl r11, r10, #11
	lsr r11, r11, #31
	ldr r9, [r12, #160]
	mla r7, r9, r11, r7
	ldr r9, [r12, #164]
	mla r8, r9, r11, r8
	lsl r11, r10, #10
	lsr r11, r11, #31
	ldr r9, [r12, #168]
	mla r7, r9, r11, r7
	ldr r9, [r12, #172]
	mla r8, r9, r11, r8
	lsl r11, r10, #9
	lsr r11, r11, #31
	ldr r9, [r12, #176]
	mla r7, r9, r11, r7
	ldr r9, [r12, #180]
	mla r8, r9, r11, r8
	lsl r11, r10, #8
	lsr r11, r11, #31
	ldr r9, [r12, #184]
	mla r7, r9, r11, r7
	ldr r9, [r12, #188]
	mla r8, r9, r11, r8
	lsl r11, r10, #7
	lsr r11, r11, #31
	ldr r9, [r12, #192]
	mla r7, r9, r11, r7
	ldr r9, [r12, #196]
	mla r8, r9, r11, r8
	lsl r11, r10, #6
	lsr r11, r11, #31
	ldr r9, [r12, #200]
	mla r7, r9, r11, r7
	ldr r9, [r12, #204]
	mla r8, r9, r11, r8
	lsl r11, r10, #5
	lsr r11, r11, #31
	ldr r9, [r12, #208]
	mla r7, r9, r11, r7
	ldr r9, [r12, #212]
	mla r8, r9, r11, r8
	lsl r11, r10, #4
	lsr r11, r11, #31
	ldr r9, [r12, #216]
	mla r7, r9, r11, r7
	ldr r9, [r12, #220]
	mla r8, r9, r11, r8
	lsl r11, r10, #3
	lsr r11, r11, #31
	ldr r9, [r12, #224]
	mla r7, r9, r11, r7
	ldr r9, [r12, #228]
	mla r8, r9, r11, r8
	lsl r11, r10, #2
	lsr r11, r11, #31
	ldr r9, [r12, #232]
	mla r7, r9, r11, r7
	ldr r9, [r12, #236]
	mla r8, r9, r11, r8
	lsl r11, r10, #1
	lsr r11, r11, #31
	ldr r9, [r12, #240]
	mla r7, r9, r11, r7
	ldr r9, [r12, #244]
	mla r8, r9, r11, r8
	lsr r11, r10, #31
	ldr r9, [r12, #248]
	mla r7, r9, r11, r7
	ldr r9, [r12, #252]
	mla r8, r9, r11, r8
	lsl r11, r6, #29
	lsr r11, r11, #31
	sub r8, r8, r7
	mla r7, r8, r11, r7
	lsl r11, r6, #31
	lsr r11, r11, #31
	lsl r8, r11, #8
	sub r8, r8, r11
	add r8, r8, #1
	lsl r11, r6, #30
	lsr r11, r11, #31
	lsl r9, r11, #16
	sub r9, r9, r11
	add r9, r9, #1
	mul r8, r8, r9
	add r9, r12, r4
	ldrb r11, [r9, #0]
	mul r11, r11, r8
	lsl r9, r8, #8
	sub r9, r9, r8
	bic r8, r7, r9
	orr r8, r8, r11
	sub r8, r8, r7
	lsl r11, r6, #31
	lsr r11, r11, #31
	lsr r9, r7, #8
	sub r9, r9, r7
	mla r7, r9, r11, r7
	lsl r11, r6, #30
	lsr r11, r11, #31
	lsr r9, r7, #16
	sub r9, r9, r7
	mla r7, r9, r11, r7
	and r7, r7, #255
	lsl r9, r6, #29
	lsr r9, r9, #31
	mul r11, r8, r9
	sub r8, r8, r11
	lsl r9, r10, #31
	lsr r9, r9, #31
	ldr r6, [r12, #0]
	mla r6, r8, r9, r6
	str r6, [r12, #0]
	ldr r6, [r12, #4]
	mla r6, r11, r9, r6
	str r6, [r12, #4]
	lsl r9, r10, #30
	lsr r9, r9, #31
	ldr r6, [r12, #8]
	mla r6, r8, r9, r6
	str r6, [r12, #8]
	ldr r6, [r12, #12]
	mla r6, r11, r9, r6
	str r6, [r12, #12]
	lsl r9, r10, #29
	lsr r9, r9, #31
	ldr r6, [r12, #16]
	mla r6, r8, r9, r6
	str r6, [r12, #16]
	ldr r6, [r12, #20]
	mla r6, r11, r9, r6
	str r6, [r12, #20]
	lsl r9, r10, #28
	lsr r9, r9, #31
	ldr r6, [r12, #24]
	mla r6, r8, r9, r6
	str r6, [r12, #24]
	ldr r6, [r12, #28]
	mla r6, r11, r9, r6
	str r6, [r12, #28]
	lsl r9, r10, #27
	lsr r9, r9, #31
	ldr r6, [r12, #32]
	mla r6, r8, r9, r6
	str r6, [r12, #32]
	ldr r6, [r12, #36]
	mla r6, r11, r9, r6
	str r6, [r12, #36]
	lsl r9, r10, #26
	lsr r9, r9, #31
	ldr r6, [r12, #40]
	mla r6, r8, r9, r6
	str r6, [r12, #40]
	ldr r6, [r12, #44]
	mla r6, r11, r9, r6
	str r6, [r12, #44]
	lsl r9, r10, #25
	lsr r9, r9, #31
	ldr r6, [r12, #48]
	mla r6, r8, r9, r6
	str r6, [r12, #48]
	ldr r6, [r12, #52]
	mla r6, r11, r9, r6
	str r6, [r12, #52]
	lsl r9, r10, #24
	lsr r9, r9, #31
	ldr r6, [r12, #56]
	mla r6, r8, r9, r6
	str r6, [r12, #56]
	ldr r6, [r12, #60]
	mla r6, r11, r9, r6
	str r6, [r12, #60]
	lsl r9, r10, #23
	lsr r9, r9, #31
	ldr r6, [r12, #64]
	mla r6, r8, r9, r6
	str r6, [r12, #64]
	ldr r6, [r12, #68]
	mla r6, r11, r9, r6
	str r6, [r12, #68]
	lsl r9, r10, #22
	lsr r9, r9, #31
	ldr r6, [r12, #72]
	mla r6, r8, r9, r6
	str r6, [r12, #72]
	ldr r6, [r12, #76]
	mla r6, r11, r9, r6
	str r6, [r12, #76]
	lsl r9, r10, #21
	lsr r9, r9, #31
	ldr r6, [r12, #80]
	mla r6, r8, r9, r6
	str r6, [r12, #80]
	ldr r6, [r12, #84]
	mla r6, r11, r9, r6
	str r6, [r12, #84]
	lsl r9, r10, #20
	lsr r9, r9, #31
	ldr r6, [r12, #88]
	mla r6, r8, r9, r6
	str r6, [r12, #88]
	ldr r6, [r12, #92]
	mla r6, r11, r9, r6
	str r6, [r12, #92]
	lsl r9, r10, #19
	lsr r9, r9, #31
	ldr r6, [r12, #96]
	mla r6, r8, r9, r6
	str r6, [r12, #96]
	ldr r6, [r12, #100]
	mla r6, r11, r9, r6
	str r6, [r12, #100]
	lsl r9, r10, #18
	lsr r9, r9, #31
	ldr r6, [r12, #104]
	mla r6, r8, r9, r6
	str r6, [r12, #104]
	ldr r6, [r12, #108]
	mla r6, r11, r9, r6
	str r6, [r12, #108]
	lsl r9, r10, #17
	lsr r9, r9, #31
	ldr r6, [r12, #112]
	mla r6, r8, r9, r6
	str r6, [r12, #112]
	ldr r6, [r12, #116]
	mla r6, r11, r9, r6
	str r6, [r12, #116]
	lsl r9, r10, #16
	lsr r9, r9, #31
	ldr r6, [r12, #120]
	mla r6, r8, r9, r6
	str r6, [r12, #120]
	ldr r6, [r12, #124]
	mla r6, r11, r9, r6
	str r6, [r12, #124]
	lsl r9, r10, #15
	lsr r9, r9, #31
	ldr r6, [r12, #128]
	mla r6, r8, r9, r6
	str r6, [r12, #128]
	ldr r6, [r12, #132]
	mla r6, r11, r9, r6
	str r6, [r12, #132]
	lsl r9, r10, #14
	lsr r9, r9, #31
	ldr r6, [r12, #136]
	mla r6, r8, r9, r6
	str r6, [r12, #136]
	ldr r6, [r12, #140]
	mla r6, r11, r9, r6
	str r6, [r12, #140]
	lsl r9, r10, #13
	lsr r9, r9, #31
	ldr r6, [r12, #144]
	mla r6, r8, r9, r6
	str r6, [r12, #144]
	ldr r6, [r12, #148]
	mla r6, r11, r9, r6
	str r6, [r12, #148]
	lsl r9, r10, #12
	lsr r9, r9, #31
	ldr r6, [r12, #152]
	mla r6, r8, r9, r6
	str r6, [r12, #152]
	ldr r6, [r12, #156]
	mla r6, r11, r9, r6
	str r6, [r12, #156]
	lsl r9, r10, #11
	lsr r9, r9, #31
	ldr r6, [r12, #160]
	mla r6, r8, r9, r6
	str r6, [r12, #160]
	ldr r6, [r12, #164]
	mla r6, r11, r9, r6
	str r6, [r12, #164]
	lsl r9, r10, #10
	lsr r9, r9, #31
	ldr r6, [r12, #168]
	mla r6, r8, r9, r6
	str r6, [r12, #168]
	ldr r6, [r12, #172]
	mla r6, r11, r9, r6
	str r6, [r12, #172]
	lsl r9, r10, #9
	lsr r9, r9, #31
	ldr r6, [r12, #176]
	mla r6, r8, r9, r6
	str r6, [r12, #176]
	ldr r6, [r12, #180]
	mla r6, r11, r9, r6
	str r6, [r12, #180]
	lsl r9, r10, #8
	lsr r9, r9, #31
	ldr r6, [r12, #184]
	mla r6, r8, r9, r6
	str r6, [r12, #184]
	ldr r6, [r12, #188]
	mla r6, r11, r9, r6
	str r6, [r12, #188]
	lsl r9, r10, #7
	lsr r9, r9, #31
	ldr r6, [r12, #192]
	mla r6, r8, r9, r6
	str r6, [r12, #192]
	ldr r6, [r12, #196]
	mla r6, r11, r9, r6
	str r6, [r12, #196]
	lsl r9, r10, #6
	lsr r9, r9, #31
	ldr r6, [r12, #200]
	mla r6, r8, r9, r6
	str r6, [r12, #200]
	ldr r6, [r12, #204]
	mla r6, r11, r9, r6
	str r6, [r12, #204]
	lsl r9, r10, #5
	lsr r9, r9, #31
	ldr r6, [r12, #208]
	mla r6, r8, r9, r6
	str r6, [r12, #208]
	ldr r6, [r12, #212]
	mla r6, r11, r9, r6
	str r6, [r12, #212]
	lsl r9, r10, #4
	lsr r9, r9, #31
	ldr r6, [r12, #216]
	mla r6, r8, r9, r6
	str r6, [r12, #216]
	ldr r6, [r12, #220]
	mla r6, r11, r9, r6
	str r6, [r12, #220]
	lsl r9, r10, #3
	lsr r9, r9, #31
	ldr r6, [r12, #224]
	mla r6, r8, r9, r6
	str r6, [r12, #224]
	ldr r6, [r12, #228]
	mla r6, r11, r9, r6
	str r6, [r12, #228]
	lsl r9, r10, #2
	lsr r9, r9, #31
	ldr r6, [r12, #232]
	mla r6, r8, r9, r6
	str r6, [r12, #232]
	ldr r6, [r12, #236]
	mla r6, r11, r9, r6
	str r6, [r12, #236]
	lsl r9, r10, #1
	lsr r9, r9, #31
	ldr r6, [r12, #240]
	mla r6, r8, r9, r6
	str r6, [r12, #240]
	ldr r6, [r12, #244]
	mla r6, r11, r9, r6
	str r6, [r12, #244]
	lsr r9, r10, #31
	ldr r6, [r12, #248]
	mla r6, r8, r9, r6
	str r6, [r12, #248]
	ldr r6, [r12, #252]
	mla r6, r11, r9, r6
	str r6, [r12, #252]
	movw r10, #65535
	movt r10, #65535
	add r9, r12, r4
	ldrb r11, [r9, #0]
	add r9, r12, r4
	strb r7, [r9, #0]
	add r6, r7, r11
	and r6, r6, #255
	lsl r11, r6, #28
	lsr r11, r11, #31
	add r10, r11, #1
	lsl r11, r6, #27
	lsr r11, r11, #31
	lsl r9, r10, #2
	sub r9, r9, r10
	mla r10, r9, r11, r10
	lsl r11, r6, #26
	lsr r11, r11, #31
	lsl r9, r10, #4
	sub r9, r9, r10
	mla r10, r9, r11, r10
	lsl r11, r6, #25
	lsr r11, r11, #31
	lsl r9, r10, #8
	sub r9, r9, r10
	mla r10, r9, r11, r10
	lsl r11, r6, #24
	lsr r11, r11, #31
	lsl r9, r10, #16
	sub r9, r9, r10
	mla r10, r9, r11, r10
	mov r7, #0
	mov r8, #0
	lsl r11, r10, #31
	lsr r11, r11, #31
	ldr r9, [r12, #0]
	mla r7, r9, r11, r7
	ldr r9, [r12, #4]
	mla r8, r9, r11, r8
	lsl r11, r10, #30
	lsr r11, r11, #31
	ldr r9, [r12, #8]
	mla r7, r9, r11, r7
	ldr r9, [r12, #12]
	mla r8, r9, r11, r8
	lsl r11, r10, #29
	lsr r11, r11, #31
	ldr r9, [r12, #16]
	mla r7, r9, r11, r7
	ldr r9, [r12, #20]
	mla r8, r9, r11, r8
	lsl r11, r10, #28
	lsr r11, r11, #31
	ldr r9, [r12, #24]
	mla r7, r9, r11, r7
	ldr r9, [r12, #28]
	mla r8, r9, r11, r8
	lsl r11, r10, #27
	lsr r11, r11, #31
	ldr r9, [r12, #32]
	mla r7, r9, r11, r7
	ldr r9, [r12, #36]
	mla r8, r9, r11, r8
	lsl r11, r10, #26
	lsr r11, r11, #31
	ldr r9, [r12, #40]
	mla r7, r9, r11, r7
	ldr r9, [r12, #44]
	mla r8, r9, r11, r8
	lsl r11, r10, #25
	lsr r11, r11, #31
	ldr r9, [r12, #48]
	mla r7, r9, r11, r7
	ldr r9, [r12, #52]
	mla r8, r9, r11, r8
	lsl r11, r10, #24
	lsr r11, r11, #31
	ldr r9, [r12, #56]
	mla r7, r9, r11, r7
	ldr r9, [r12, #60]
	mla r8, r9, r11, r8
	lsl r11, r10, #23
	lsr r11, r11, #31
	ldr r9, [r12, #64]
	mla r7, r9, r11, r7
	ldr r9, [r12, #68]
	mla r8, r9, r11, r8
	lsl r11, r10, #22
	lsr r11, r11, #31
	ldr r9, [r12, #72]
	mla r7, r9, r11, r7
	ldr r9, [r12, #76]
	mla r8, r9, r11, r8
	lsl r11, r10, #21
	lsr r11, r11, #31
	ldr r9, [r12, #80]
	mla r7, r9, r11, r7
	ldr r9, [r12, #84]
	mla r8, r9, r11, r8
	lsl r11, r10, #20
	lsr r11, r11, #31
	ldr r9, [r12, #88]
	mla r7, r9, r11, r7
	ldr r9, [r12, #92]
	mla r8, r9, r11, r8
	lsl r11, r10, #19
	lsr r11, r11, #31
	ldr r9, [r12, #96]
	mla r7, r9, r11, r7
	ldr r9, [r12, #100]
	mla r8, r9, r11, r8
	lsl r11, r10, #18
	lsr r11, r11, #31
	ldr r9, [r12, #104]
	mla r7, r9, r11, r7
	ldr r9, [r12, #108]
	mla r8, r9, r11, r8
	lsl r11, r10, #17
	lsr r11, r11, #31
	ldr r9, [r12, #112]
	mla r7, r9, r11, r7
	ldr r9, [r12, #116]
	mla r8, r9, r11, r8
	lsl r11, r10, #16
	lsr r11, r11, #31
	ldr r9, [r12, #120]
	mla r7, r9, r11, r7
	ldr r9, [r12, #124]
	mla r8, r9, r11, r8
	lsl r11, r10, #15
	lsr r11, r11, #31
	ldr r9, [r12, #128]
	mla r7, r9, r11, r7
	ldr r9, [r12, #132]
	mla r8, r9, r11, r8
	lsl r11, r10, #14
	lsr r11, r11, #31
	ldr r9, [r12, #136]
	mla r7, r9, r11, r7
	ldr r9, [r12, #140]
	mla r8, r9, r11, r8
	lsl r11, r10, #13
	lsr r11, r11, #31
	ldr r9, [r12, #144]
	mla r7, r9, r11, r7
	ldr r9, [r12, #148]
	mla r8, r9, r11, r8
	lsl r11, r10, #12
	lsr r11, r11, #31
	ldr r9, [r12, #152]
	mla r7, r9, r11, r7
	ldr r9, [r12, #156]
	mla r8, r9, r11, r8
	lsl r11, r10, #11
	lsr r11, r11, #31
	ldr r9, [r12, #160]
	mla r7, r9, r11, r7
	ldr r9, [r12, #164]
	mla r8, r9, r11, r8
	lsl r11, r10, #10
	lsr r11, r11, #31
	ldr r9, [r12, #168]
	mla r7, r9, r11, r7
	ldr r9, [r12, #172]
	mla r8, r9, r11, r8
	lsl r11, r10, #9
	lsr r11, r11, #31
	ldr r9, [r12, #176]
	mla r7, r9, r11, r7
	ldr r9, [r12, #180]
	mla r8, r9, r11, r8
	lsl r11, r10, #8
	lsr r11, r11, #31
	ldr r9, [r12, #184]
	mla r7, r9, r11, r7
	ldr r9, [r12, #188]
	mla r8, r9, r11, r8
	lsl r11, r10, #7
	lsr r11, r11, #31
	ldr r9, [r12, #192]
	mla r7, r9, r11, r7
	ldr r9, [r12, #196]
	mla r8, r9, r11, r8
	lsl r11, r10, #6
	lsr r11, r11, #31
	ldr r9, [r12, #200]
	mla r7, r9, r11, r7
	ldr r9, [r12, #204]
	mla r8, r9, r11, r8
	lsl r11, r10, #5
	lsr r11, r11, #31
	ldr r9, [r12, #208]
	mla r7, r9, r11, r7
	ldr r9, [r12, #212]
	mla r8, r9, r11, r8
	lsl r11, r10, #4
	lsr r11, r11, #31
	ldr r9, [r12, #216]
	mla r7, r9, r11, r7
	ldr r9, [r12, #220]
	mla r8, r9, r11, r8
	lsl r11, r10, #3
	lsr r11, r11, #31
	ldr r9, [r12, #224]
	mla r7, r9, r11, r7
	ldr r9, [r12, #228]
	mla r8, r9, r11, r8
	lsl r11, r10, #2
	lsr r11, r11, #31
	ldr r9, [r12, #232]
	mla r7, r9, r11, r7
	ldr r9, [r12, #236]
	mla r8, r9, r11, r8
	lsl r11, r10, #1
	lsr r11, r11, #31
	ldr r9, [r12, #240]
	mla r7, r9, r11, r7
	ldr r9, [r12, #244]
	mla r8, r9, r11, r8
	lsr r11, r10, #31
	ldr r9, [r12, #248]
	mla r7, r9, r11, r7
	ldr r9, [r12, #252]
	mla r8, r9, r11, r8
	lsl r11, r6, #29
	lsr r11, r11, #31
	sub r8, r8, r7
	mla r7, r8, r11, r7
	lsl r11, r6, #31
	lsr r11, r11, #31
	lsr r9, r7, #8
	sub r9, r9, r7
	mla r7, r9, r11, r7
	lsl r11, r6, #30
	lsr r11, r11, #31
	lsr r9, r7, #16
	sub r9, r9, r7
	mla r7, r9, r11, r7
	and r7, r7, #255
	movw r10, #65535
	movt r10, #65535
	add r9, r1, r0
	ldrb r11, [r9, #0]
	eor r11, r11, r7
	strb r11, [r9, #0]
	add r0, r0, #1
	cmp r0, r2
	bne 22b
	strb r4, [r12, #256]
	strb r5, [r12, #257]
	ldr r4, [r3, #0]
	ldr r5, [r3, #4]
	ldr r6, [r3, #8]
	ldr r7, [r3, #12]
	ldr r8, [r3, #16]
	ldr r9, [r3, #20]
	ldr r10, [r3, #24]
	ldr r11, [r3, #28]
	b 21f
20:
21:
	add r12, sp, #0
	mov r2, #0
	str r2, [r12, #0]
	str r2, [r12, #4]
	str r2, [r12, #8]
	str r2, [r12, #12]
	str r2, [r12, #16]
	str r2, [r12, #20]
	str r2, [r12, #24]
	str r2, [r12, #28]
	str r2, [r12, #32]
	str r2, [r12, #36]
	str r2, [r12, #40]
	str r2, [r12, #44]
	str r2, [r12, #48]
	str r2, [r12, #52]
	str r2, [r12, #56]
	str r2, [r12, #60]
	add sp, sp, #64
	sub sp, sp, #64
	add r12, sp, #0
	mov r2, #0
	mov r3, #2
23:
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
	bne 23b
	add sp, sp, #64
	mov r0, #0
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
