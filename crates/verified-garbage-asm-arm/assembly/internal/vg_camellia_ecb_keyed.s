// The functions of `src/internal/vg_camellia_ecb_keyed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_ecb_keyed:
	ldr r12, [sp, #0]
	str r4, [r12, #2472]
	str r5, [r12, #2476]
	str r6, [r12, #2480]
	str r7, [r12, #2484]
	str r8, [r12, #2488]
	str r9, [r12, #2492]
	str r10, [r12, #2496]
	str r11, [r12, #2500]
	str lr, [r12, #2504]
	mov r8, r12
	cmp r1, #18
	mov r1, r2
	mov r2, r3
	beq 20f
	add lr, r8, #2336
	b 21f
20:
	add lr, r8, #1824
21:
	cmp r2, #0
	beq 22f
24:
	lsr r10, r2, #3
	cmp r10, #0
	bne 25f
	mov r3, r2
	b 26f
25:
	mov r3, #8
26:
	mov r0, r1
	add r12, r8, #2528
27:
	ldr r10, [r0, #0]
	str r10, [r12, #0]
	ldr r10, [r0, #4]
	str r10, [r12, #4]
	ldr r10, [r0, #8]
	str r10, [r12, #8]
	ldr r10, [r0, #12]
	str r10, [r12, #12]
	add r0, r0, #16
	add r12, r12, #16
	subs r3, r3, #1
	bne 27b
	str r1, [r8, #2508]
	str r2, [r8, #2512]
	str lr, [r8, #2468]
	add r12, r8, #2528
	ldr r0, [r12, #0]
	ldr r1, [r12, #16]
	ldr r2, [r12, #32]
	ldr r3, [r12, #48]
	ldr r4, [r12, #64]
	ldr r5, [r12, #80]
	ldr r6, [r12, #96]
	ldr r7, [r12, #112]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #160]
	str r1, [r8, #164]
	str r2, [r8, #168]
	str r3, [r8, #172]
	str r4, [r8, #176]
	str r5, [r8, #180]
	str r6, [r8, #184]
	str r7, [r8, #188]
	ldr r0, [r12, #4]
	ldr r1, [r12, #20]
	ldr r2, [r12, #36]
	ldr r3, [r12, #52]
	ldr r4, [r12, #68]
	ldr r5, [r12, #84]
	ldr r6, [r12, #100]
	ldr r7, [r12, #116]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #192]
	str r1, [r8, #196]
	str r2, [r8, #200]
	str r3, [r8, #204]
	str r4, [r8, #208]
	str r5, [r8, #212]
	str r6, [r8, #216]
	str r7, [r8, #220]
	ldr r0, [r12, #8]
	ldr r1, [r12, #24]
	ldr r2, [r12, #40]
	ldr r3, [r12, #56]
	ldr r4, [r12, #72]
	ldr r5, [r12, #88]
	ldr r6, [r12, #104]
	ldr r7, [r12, #120]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #224]
	str r1, [r8, #228]
	str r2, [r8, #232]
	str r3, [r8, #236]
	str r4, [r8, #240]
	str r5, [r8, #244]
	str r6, [r8, #248]
	str r7, [r8, #252]
	ldr r0, [r12, #12]
	ldr r1, [r12, #28]
	ldr r2, [r12, #44]
	ldr r3, [r12, #60]
	ldr r4, [r12, #76]
	ldr r5, [r12, #92]
	ldr r6, [r12, #108]
	ldr r7, [r12, #124]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #256]
	str r1, [r8, #260]
	str r2, [r8, #264]
	str r3, [r8, #268]
	str r4, [r8, #272]
	str r5, [r8, #276]
	str r6, [r8, #280]
	str r7, [r8, #284]
	add r9, r8, #288
	ldr r11, [r8, #160]
	ldr r10, [r9, #0]
	eor r11, r11, r10
	str r11, [r8, #160]
	ldr r11, [r8, #164]
	ldr r10, [r9, #4]
	eor r11, r11, r10
	str r11, [r8, #164]
	ldr r11, [r8, #168]
	ldr r10, [r9, #8]
	eor r11, r11, r10
	str r11, [r8, #168]
	ldr r11, [r8, #172]
	ldr r10, [r9, #12]
	eor r11, r11, r10
	str r11, [r8, #172]
	ldr r11, [r8, #176]
	ldr r10, [r9, #16]
	eor r11, r11, r10
	str r11, [r8, #176]
	ldr r11, [r8, #180]
	ldr r10, [r9, #20]
	eor r11, r11, r10
	str r11, [r8, #180]
	ldr r11, [r8, #184]
	ldr r10, [r9, #24]
	eor r11, r11, r10
	str r11, [r8, #184]
	ldr r11, [r8, #188]
	ldr r10, [r9, #28]
	eor r11, r11, r10
	str r11, [r8, #188]
	ldr r11, [r8, #192]
	ldr r10, [r9, #32]
	eor r11, r11, r10
	str r11, [r8, #192]
	ldr r11, [r8, #196]
	ldr r10, [r9, #36]
	eor r11, r11, r10
	str r11, [r8, #196]
	ldr r11, [r8, #200]
	ldr r10, [r9, #40]
	eor r11, r11, r10
	str r11, [r8, #200]
	ldr r11, [r8, #204]
	ldr r10, [r9, #44]
	eor r11, r11, r10
	str r11, [r8, #204]
	ldr r11, [r8, #208]
	ldr r10, [r9, #48]
	eor r11, r11, r10
	str r11, [r8, #208]
	ldr r11, [r8, #212]
	ldr r10, [r9, #52]
	eor r11, r11, r10
	str r11, [r8, #212]
	ldr r11, [r8, #216]
	ldr r10, [r9, #56]
	eor r11, r11, r10
	str r11, [r8, #216]
	ldr r11, [r8, #220]
	ldr r10, [r9, #60]
	eor r11, r11, r10
	str r11, [r8, #220]
	ldr r11, [r8, #224]
	ldr r10, [r9, #64]
	eor r11, r11, r10
	str r11, [r8, #224]
	ldr r11, [r8, #228]
	ldr r10, [r9, #68]
	eor r11, r11, r10
	str r11, [r8, #228]
	ldr r11, [r8, #232]
	ldr r10, [r9, #72]
	eor r11, r11, r10
	str r11, [r8, #232]
	ldr r11, [r8, #236]
	ldr r10, [r9, #76]
	eor r11, r11, r10
	str r11, [r8, #236]
	ldr r11, [r8, #240]
	ldr r10, [r9, #80]
	eor r11, r11, r10
	str r11, [r8, #240]
	ldr r11, [r8, #244]
	ldr r10, [r9, #84]
	eor r11, r11, r10
	str r11, [r8, #244]
	ldr r11, [r8, #248]
	ldr r10, [r9, #88]
	eor r11, r11, r10
	str r11, [r8, #248]
	ldr r11, [r8, #252]
	ldr r10, [r9, #92]
	eor r11, r11, r10
	str r11, [r8, #252]
	ldr r11, [r8, #256]
	ldr r10, [r9, #96]
	eor r11, r11, r10
	str r11, [r8, #256]
	ldr r11, [r8, #260]
	ldr r10, [r9, #100]
	eor r11, r11, r10
	str r11, [r8, #260]
	ldr r11, [r8, #264]
	ldr r10, [r9, #104]
	eor r11, r11, r10
	str r11, [r8, #264]
	ldr r11, [r8, #268]
	ldr r10, [r9, #108]
	eor r11, r11, r10
	str r11, [r8, #268]
	ldr r11, [r8, #272]
	ldr r10, [r9, #112]
	eor r11, r11, r10
	str r11, [r8, #272]
	ldr r11, [r8, #276]
	ldr r10, [r9, #116]
	eor r11, r11, r10
	str r11, [r8, #276]
	ldr r11, [r8, #280]
	ldr r10, [r9, #120]
	eor r11, r11, r10
	str r11, [r8, #280]
	ldr r11, [r8, #284]
	ldr r10, [r9, #124]
	eor r11, r11, r10
	str r11, [r8, #284]
	add r9, r9, #128
28:
	add r10, r9, #384
	str r10, [r8, #2464]
29:
	ldr r0, [r8, #160]
	ldr r10, [r9, #0]
	eor r0, r0, r10
	ldr r1, [r8, #164]
	ldr r10, [r9, #4]
	eor r1, r1, r10
	ldr r2, [r8, #168]
	ldr r10, [r9, #8]
	eor r2, r2, r10
	ldr r3, [r8, #172]
	ldr r10, [r9, #12]
	eor r3, r3, r10
	ldr r4, [r8, #176]
	ldr r10, [r9, #16]
	eor r4, r4, r10
	ldr r5, [r8, #180]
	ldr r10, [r9, #20]
	eor r5, r5, r10
	ldr r6, [r8, #184]
	ldr r10, [r9, #24]
	eor r6, r6, r10
	ldr r7, [r8, #188]
	ldr r10, [r9, #28]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #4278190080
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #4278190080
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #4278190080
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #4278190080
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #4278190080
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #4278190080
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #4278190080
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #4278190080
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #65280
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #65280
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #16711680
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #16711680
	eor r7, r7, r10
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #192]
	ldr r10, [r9, #32]
	eor r0, r0, r10
	ldr r1, [r8, #196]
	ldr r10, [r9, #36]
	eor r1, r1, r10
	ldr r2, [r8, #200]
	ldr r10, [r9, #40]
	eor r2, r2, r10
	ldr r3, [r8, #204]
	ldr r10, [r9, #44]
	eor r3, r3, r10
	ldr r4, [r8, #208]
	ldr r10, [r9, #48]
	eor r4, r4, r10
	ldr r5, [r8, #212]
	ldr r10, [r9, #52]
	eor r5, r5, r10
	ldr r6, [r8, #216]
	ldr r10, [r9, #56]
	eor r6, r6, r10
	ldr r7, [r8, #220]
	ldr r10, [r9, #60]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #16711680
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #16711680
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #255
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #255
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #255
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #255
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #255
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #255
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #255
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #255
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #65280
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #65280
	eor r7, r7, r10
	ldr r11, [r8, #128]
	eor r11, r11, r0
	eor r11, r11, r0, ror #16
	eor r0, r0, r11
	eor r0, r0, r11, ror #8
	eor r11, r11, r0, ror #16
	ldr r10, [r8, #224]
	eor r10, r10, r11
	str r10, [r8, #224]
	ldr r10, [r8, #256]
	eor r10, r10, r0
	str r10, [r8, #256]
	ldr r11, [r8, #132]
	eor r11, r11, r1
	eor r11, r11, r1, ror #16
	eor r1, r1, r11
	eor r1, r1, r11, ror #8
	eor r11, r11, r1, ror #16
	ldr r10, [r8, #228]
	eor r10, r10, r11
	str r10, [r8, #228]
	ldr r10, [r8, #260]
	eor r10, r10, r1
	str r10, [r8, #260]
	ldr r11, [r8, #136]
	eor r11, r11, r2
	eor r11, r11, r2, ror #16
	eor r2, r2, r11
	eor r2, r2, r11, ror #8
	eor r11, r11, r2, ror #16
	ldr r10, [r8, #232]
	eor r10, r10, r11
	str r10, [r8, #232]
	ldr r10, [r8, #264]
	eor r10, r10, r2
	str r10, [r8, #264]
	ldr r11, [r8, #140]
	eor r11, r11, r3
	eor r11, r11, r3, ror #16
	eor r3, r3, r11
	eor r3, r3, r11, ror #8
	eor r11, r11, r3, ror #16
	ldr r10, [r8, #236]
	eor r10, r10, r11
	str r10, [r8, #236]
	ldr r10, [r8, #268]
	eor r10, r10, r3
	str r10, [r8, #268]
	ldr r11, [r8, #144]
	eor r11, r11, r4
	eor r11, r11, r4, ror #16
	eor r4, r4, r11
	eor r4, r4, r11, ror #8
	eor r11, r11, r4, ror #16
	ldr r10, [r8, #240]
	eor r10, r10, r11
	str r10, [r8, #240]
	ldr r10, [r8, #272]
	eor r10, r10, r4
	str r10, [r8, #272]
	ldr r11, [r8, #148]
	eor r11, r11, r5
	eor r11, r11, r5, ror #16
	eor r5, r5, r11
	eor r5, r5, r11, ror #8
	eor r11, r11, r5, ror #16
	ldr r10, [r8, #244]
	eor r10, r10, r11
	str r10, [r8, #244]
	ldr r10, [r8, #276]
	eor r10, r10, r5
	str r10, [r8, #276]
	ldr r11, [r8, #152]
	eor r11, r11, r6
	eor r11, r11, r6, ror #16
	eor r6, r6, r11
	eor r6, r6, r11, ror #8
	eor r11, r11, r6, ror #16
	ldr r10, [r8, #248]
	eor r10, r10, r11
	str r10, [r8, #248]
	ldr r10, [r8, #280]
	eor r10, r10, r6
	str r10, [r8, #280]
	ldr r11, [r8, #156]
	eor r11, r11, r7
	eor r11, r11, r7, ror #16
	eor r7, r7, r11
	eor r7, r7, r11, ror #8
	eor r11, r11, r7, ror #16
	ldr r10, [r8, #252]
	eor r10, r10, r11
	str r10, [r8, #252]
	ldr r10, [r8, #284]
	eor r10, r10, r7
	str r10, [r8, #284]
	ldr r0, [r8, #224]
	ldr r10, [r9, #64]
	eor r0, r0, r10
	ldr r1, [r8, #228]
	ldr r10, [r9, #68]
	eor r1, r1, r10
	ldr r2, [r8, #232]
	ldr r10, [r9, #72]
	eor r2, r2, r10
	ldr r3, [r8, #236]
	ldr r10, [r9, #76]
	eor r3, r3, r10
	ldr r4, [r8, #240]
	ldr r10, [r9, #80]
	eor r4, r4, r10
	ldr r5, [r8, #244]
	ldr r10, [r9, #84]
	eor r5, r5, r10
	ldr r6, [r8, #248]
	ldr r10, [r9, #88]
	eor r6, r6, r10
	ldr r7, [r8, #252]
	ldr r10, [r9, #92]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #4278190080
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #4278190080
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #4278190080
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #4278190080
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #4278190080
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #4278190080
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #4278190080
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #4278190080
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #65280
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #65280
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #16711680
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #16711680
	eor r7, r7, r10
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #256]
	ldr r10, [r9, #96]
	eor r0, r0, r10
	ldr r1, [r8, #260]
	ldr r10, [r9, #100]
	eor r1, r1, r10
	ldr r2, [r8, #264]
	ldr r10, [r9, #104]
	eor r2, r2, r10
	ldr r3, [r8, #268]
	ldr r10, [r9, #108]
	eor r3, r3, r10
	ldr r4, [r8, #272]
	ldr r10, [r9, #112]
	eor r4, r4, r10
	ldr r5, [r8, #276]
	ldr r10, [r9, #116]
	eor r5, r5, r10
	ldr r6, [r8, #280]
	ldr r10, [r9, #120]
	eor r6, r6, r10
	ldr r7, [r8, #284]
	ldr r10, [r9, #124]
	eor r7, r7, r10
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #16711680
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #16711680
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #16711680
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #16711680
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #16711680
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #16711680
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #16711680
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #16711680
	eor r0, r0, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r7, r1
	eor r11, r5, r3
	eor r12, r2, r10
	eor lr, r6, r0
	str r10, [r8, #4]
	eor r10, r0, r11
	str r10, [r8, #8]
	eor r10, r4, r1
	str r10, [r8, #12]
	eor r10, r4, r12
	str r10, [r8, #16]
	eor r10, r6, r11
	str r11, [r8, #20]
	eor r11, r2, lr
	str r11, [r8, #24]
	eor r11, r12, lr
	str r11, [r8, #28]
	eor r11, r7, r6
	str r10, [r8, #32]
	eor r10, r7, lr
	str r7, [r8, #36]
	ldr r7, [r8, #0]
	str r2, [r8, #40]
	eor r2, r10, r7
	str r10, [r8, #44]
	eor r10, r6, r3
	str r2, [r8, #48]
	eor r2, r5, r1
	str r6, [r8, #52]
	eor r6, r5, r0
	eor r5, r5, r12
	eor lr, r4, lr
	eor r4, r4, r11
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #40]
	ldr r11, [r8, #8]
	str lr, [r8, #56]
	eor lr, r0, r11
	str r3, [r8, #60]
	ldr r3, [r8, #12]
	eor r0, r0, r3
	eor r0, r0, r7
	str r5, [r8, #40]
	ldr r5, [r8, #32]
	str lr, [r8, #64]
	eor lr, r1, r5
	eor lr, lr, r7
	str lr, [r8, #68]
	ldr lr, [r8, #4]
	str r0, [r8, #72]
	eor r0, lr, r11
	eor lr, lr, r5
	ldr r5, [r8, #20]
	str r0, [r8, #32]
	eor r0, r5, r3
	str lr, [r8, #4]
	ldr lr, [r8, #16]
	str r4, [r8, #76]
	eor r4, r5, lr
	str r4, [r8, #80]
	ldr r4, [r8, #28]
	eor r5, r5, r4
	str r5, [r8, #20]
	eor r5, r12, r11
	eor r5, r5, r7
	eor r12, r12, r10
	eor r12, r12, r7
	eor r11, r11, r3
	eor r11, r11, r7
	eor r6, lr, r6
	eor r6, r6, r7
	ldr r3, [r8, #24]
	eor r2, r3, r2
	eor r2, r2, r7
	eor r3, r3, r0
	eor r3, r3, r7
	ldr r0, [r8, #36]
	ldr r10, [r8, #52]
	str r12, [r8, #24]
	eor r12, r0, r10
	eor r12, r12, r7
	eor r12, r12, r10
	eor r0, r0, r1
	eor r0, r0, r7
	ldr r1, [r8, #72]
	ldr r10, [r8, #76]
	and r7, r1, r10
	and r1, r12, r2
	eor r1, r1, r7
	str r12, [r8, #36]
	and r12, lr, r6
	eor r12, r12, r7
	ldr r7, [r8, #64]
	and lr, r7, r5
	ldr r7, [r8, #4]
	str r5, [r8, #52]
	ldr r5, [r8, #40]
	str r6, [r8, #12]
	and r6, r7, r5
	eor r6, r6, lr
	ldr r7, [r8, #60]
	and r5, r4, r7
	eor r5, r5, lr
	ldr lr, [r8, #56]
	ldr r4, [r8, #80]
	and r7, lr, r4
	and lr, r11, r3
	eor lr, lr, r7
	str r11, [r8, #8]
	ldr r11, [r8, #68]
	str r3, [r8, #84]
	ldr r3, [r8, #48]
	and r4, r11, r3
	eor r4, r4, r7
	eor r1, r1, lr
	eor r12, r12, r4
	eor r6, r6, lr
	eor r5, r5, r4
	ldr r4, [r8, #20]
	eor r1, r1, r4
	ldr r4, [r8, #32]
	eor r12, r12, r4
	eor r6, r6, r0
	ldr r0, [r8, #24]
	eor r5, r5, r0
	eor r0, r1, r12
	and r1, r1, r6
	eor r4, r5, r1
	and lr, r0, r4
	eor lr, lr, r12
	eor r7, r6, r5
	eor r12, r12, r1
	and r12, r12, r7
	eor r12, r12, r5
	eor r6, r6, r12
	eor r7, r4, r12
	and r5, r5, r7
	eor r6, r5, r6
	eor r4, r4, r5
	and r4, lr, r4
	eor r0, r0, r4
	eor r4, r0, r6
	eor r5, lr, r12
	eor r7, lr, r0
	eor r1, r12, r6
	eor r11, r5, r4
	and r10, r1, r10
	and r2, r6, r2
	str r10, [r8, #76]
	ldr r10, [r8, #12]
	and r10, r12, r10
	str r10, [r8, #12]
	ldr r10, [r8, #52]
	and r10, r7, r10
	str r10, [r8, #52]
	ldr r10, [r8, #40]
	and r10, r0, r10
	str r10, [r8, #40]
	ldr r10, [r8, #60]
	and r10, lr, r10
	str r10, [r8, #60]
	ldr r10, [r8, #80]
	and r10, r5, r10
	str r10, [r8, #80]
	ldr r10, [r8, #84]
	and r10, r11, r10
	and r3, r4, r3
	str r3, [r8, #48]
	ldr r3, [r8, #72]
	and r1, r1, r3
	ldr r3, [r8, #36]
	and r6, r6, r3
	ldr r3, [r8, #16]
	and r12, r12, r3
	ldr r3, [r8, #64]
	and r7, r7, r3
	ldr r3, [r8, #4]
	and r0, r0, r3
	ldr r3, [r8, #28]
	and lr, lr, r3
	ldr r3, [r8, #56]
	and r5, r5, r3
	ldr r3, [r8, #8]
	and r11, r11, r3
	ldr r3, [r8, #68]
	and r4, r4, r3
	eor r10, r2, r10
	ldr r3, [r8, #52]
	str r2, [r8, #68]
	ldr r2, [r8, #60]
	eor r3, r3, r2
	ldr r2, [r8, #80]
	str r0, [r8, #52]
	ldr r0, [r8, #48]
	str r6, [r8, #8]
	eor r6, r2, r0
	ldr r0, [r8, #76]
	str r1, [r8, #56]
	eor r1, r0, r11
	eor r12, r12, r10
	str r10, [r8, #28]
	eor r10, r7, r3
	str r3, [r8, #4]
	eor r3, r5, r6
	str r6, [r8, #64]
	ldr r6, [r8, #12]
	eor lr, r6, lr
	eor r2, r2, r4
	str lr, [r8, #80]
	ldr lr, [r8, #48]
	str r4, [r8, #16]
	ldr r4, [r8, #56]
	eor lr, lr, r4
	str lr, [r8, #48]
	ldr lr, [r8, #8]
	eor r4, r4, lr
	str r4, [r8, #56]
	ldr r4, [r8, #52]
	eor r4, r4, r10
	eor r11, r11, r3
	str r11, [r8, #52]
	eor r11, r1, r12
	eor r0, r0, r6
	ldr r6, [r8, #68]
	str r11, [r8, #12]
	ldr r11, [r8, #40]
	eor r6, r6, r11
	ldr r11, [r8, #60]
	eor r11, r11, r1
	eor lr, lr, r2
	eor r7, r7, r12
	ldr r12, [r8, #28]
	eor r5, r5, r12
	ldr r12, [r8, #16]
	ldr r1, [r8, #48]
	eor r12, r12, r1
	str r12, [r8, #16]
	ldr r12, [r8, #4]
	str r7, [r8, #28]
	ldr r7, [r8, #56]
	eor r12, r12, r7
	str r11, [r8, #4]
	ldr r11, [r8, #64]
	eor r11, r11, r0
	ldr r0, [r8, #80]
	eor r10, r10, r0
	eor r3, r3, r7
	eor r0, r0, r1
	eor r2, r2, r5
	ldr r5, [r8, #52]
	eor r1, r4, r5
	ldr r7, [r8, #12]
	eor r4, r4, r7
	eor r5, r5, r12
	ldr r12, [r8, #0]
	eor r5, r5, r12
	eor r7, r7, lr
	eor r7, r7, r12
	ldr lr, [r8, #4]
	eor r6, r6, lr
	ldr lr, [r8, #28]
	eor lr, lr, r0
	eor lr, lr, r12
	ldr r0, [r8, #16]
	eor r0, r0, r4
	eor r0, r0, r12
	eor r10, r10, r2
	eor r3, r3, r6
	eor r6, r3, r12
	str r7, [r8, #0]
	mov r7, r10
	mov r4, r11
	mov r3, lr
	ldr r2, [r8, #0]
	str r1, [r8, #44]
	mov r1, r0
	ldr r0, [r8, #44]
	mov r11, r7
	eor r10, r7, r6
	and r10, r10, #255
	eor r7, r7, r10
	eor r10, r6, r5
	and r10, r10, #255
	eor r6, r6, r10
	eor r10, r5, r4
	and r10, r10, #255
	eor r5, r5, r10
	eor r10, r4, r3
	and r10, r10, #255
	eor r4, r4, r10
	eor r10, r3, r2
	and r10, r10, #255
	eor r3, r3, r10
	eor r10, r2, r1
	and r10, r10, #255
	eor r2, r2, r10
	eor r10, r1, r0
	and r10, r10, #255
	eor r1, r1, r10
	eor r10, r0, r11
	and r10, r10, #255
	eor r0, r0, r10
	mov r11, r0
	eor r10, r0, r1
	and r10, r10, #65280
	eor r0, r0, r10
	eor r10, r1, r2
	and r10, r10, #65280
	eor r1, r1, r10
	eor r10, r2, r3
	and r10, r10, #65280
	eor r2, r2, r10
	eor r10, r3, r4
	and r10, r10, #65280
	eor r3, r3, r10
	eor r10, r4, r5
	and r10, r10, #65280
	eor r4, r4, r10
	eor r10, r5, r6
	and r10, r10, #65280
	eor r5, r5, r10
	eor r10, r6, r7
	and r10, r10, #65280
	eor r6, r6, r10
	eor r10, r7, r11
	and r10, r10, #65280
	eor r7, r7, r10
	ldr r11, [r8, #128]
	eor r11, r11, r0
	eor r11, r11, r0, ror #16
	eor r0, r0, r11
	eor r0, r0, r11, ror #8
	eor r11, r11, r0, ror #16
	ldr r10, [r8, #160]
	eor r10, r10, r11
	str r10, [r8, #160]
	ldr r10, [r8, #192]
	eor r10, r10, r0
	str r10, [r8, #192]
	ldr r11, [r8, #132]
	eor r11, r11, r1
	eor r11, r11, r1, ror #16
	eor r1, r1, r11
	eor r1, r1, r11, ror #8
	eor r11, r11, r1, ror #16
	ldr r10, [r8, #164]
	eor r10, r10, r11
	str r10, [r8, #164]
	ldr r10, [r8, #196]
	eor r10, r10, r1
	str r10, [r8, #196]
	ldr r11, [r8, #136]
	eor r11, r11, r2
	eor r11, r11, r2, ror #16
	eor r2, r2, r11
	eor r2, r2, r11, ror #8
	eor r11, r11, r2, ror #16
	ldr r10, [r8, #168]
	eor r10, r10, r11
	str r10, [r8, #168]
	ldr r10, [r8, #200]
	eor r10, r10, r2
	str r10, [r8, #200]
	ldr r11, [r8, #140]
	eor r11, r11, r3
	eor r11, r11, r3, ror #16
	eor r3, r3, r11
	eor r3, r3, r11, ror #8
	eor r11, r11, r3, ror #16
	ldr r10, [r8, #172]
	eor r10, r10, r11
	str r10, [r8, #172]
	ldr r10, [r8, #204]
	eor r10, r10, r3
	str r10, [r8, #204]
	ldr r11, [r8, #144]
	eor r11, r11, r4
	eor r11, r11, r4, ror #16
	eor r4, r4, r11
	eor r4, r4, r11, ror #8
	eor r11, r11, r4, ror #16
	ldr r10, [r8, #176]
	eor r10, r10, r11
	str r10, [r8, #176]
	ldr r10, [r8, #208]
	eor r10, r10, r4
	str r10, [r8, #208]
	ldr r11, [r8, #148]
	eor r11, r11, r5
	eor r11, r11, r5, ror #16
	eor r5, r5, r11
	eor r5, r5, r11, ror #8
	eor r11, r11, r5, ror #16
	ldr r10, [r8, #180]
	eor r10, r10, r11
	str r10, [r8, #180]
	ldr r10, [r8, #212]
	eor r10, r10, r5
	str r10, [r8, #212]
	ldr r11, [r8, #152]
	eor r11, r11, r6
	eor r11, r11, r6, ror #16
	eor r6, r6, r11
	eor r6, r6, r11, ror #8
	eor r11, r11, r6, ror #16
	ldr r10, [r8, #184]
	eor r10, r10, r11
	str r10, [r8, #184]
	ldr r10, [r8, #216]
	eor r10, r10, r6
	str r10, [r8, #216]
	ldr r11, [r8, #156]
	eor r11, r11, r7
	eor r11, r11, r7, ror #16
	eor r7, r7, r11
	eor r7, r7, r11, ror #8
	eor r11, r11, r7, ror #16
	ldr r10, [r8, #188]
	eor r10, r10, r11
	str r10, [r8, #188]
	ldr r10, [r8, #220]
	eor r10, r10, r7
	str r10, [r8, #220]
	add r9, r9, #128
	ldr r10, [r8, #2464]
	cmp r9, r10
	bne 29b
	ldr r10, [r8, #2468]
	cmp r9, r10
	bne 210f
	b 211f
210:
	ldr r0, [r8, #224]
	ldr r1, [r8, #228]
	ldr r2, [r8, #232]
	ldr r3, [r8, #236]
	ldr r4, [r8, #240]
	ldr r5, [r8, #244]
	ldr r6, [r8, #248]
	ldr r7, [r8, #252]
	ldr r10, [r9, #96]
	ldr r11, [r8, #256]
	orr r10, r10, r11
	eor r0, r0, r10
	ldr r10, [r9, #100]
	ldr r11, [r8, #260]
	orr r10, r10, r11
	eor r1, r1, r10
	ldr r10, [r9, #104]
	ldr r11, [r8, #264]
	orr r10, r10, r11
	eor r2, r2, r10
	ldr r10, [r9, #108]
	ldr r11, [r8, #268]
	orr r10, r10, r11
	eor r3, r3, r10
	ldr r10, [r9, #112]
	ldr r11, [r8, #272]
	orr r10, r10, r11
	eor r4, r4, r10
	ldr r10, [r9, #116]
	ldr r11, [r8, #276]
	orr r10, r10, r11
	eor r5, r5, r10
	ldr r10, [r9, #120]
	ldr r11, [r8, #280]
	orr r10, r10, r11
	eor r6, r6, r10
	ldr r10, [r9, #124]
	ldr r11, [r8, #284]
	orr r10, r10, r11
	eor r7, r7, r10
	ldr r10, [r9, #92]
	and r10, r10, r7
	ldr r11, [r8, #256]
	eor r11, r11, r10, ror #8
	str r11, [r8, #256]
	ldr r10, [r9, #64]
	and r10, r10, r0
	ldr r11, [r8, #260]
	eor r11, r11, r10
	str r11, [r8, #260]
	ldr r10, [r9, #68]
	and r10, r10, r1
	ldr r11, [r8, #264]
	eor r11, r11, r10
	str r11, [r8, #264]
	ldr r10, [r9, #72]
	and r10, r10, r2
	ldr r11, [r8, #268]
	eor r11, r11, r10
	str r11, [r8, #268]
	ldr r10, [r9, #76]
	and r10, r10, r3
	ldr r11, [r8, #272]
	eor r11, r11, r10
	str r11, [r8, #272]
	ldr r10, [r9, #80]
	and r10, r10, r4
	ldr r11, [r8, #276]
	eor r11, r11, r10
	str r11, [r8, #276]
	ldr r10, [r9, #84]
	and r10, r10, r5
	ldr r11, [r8, #280]
	eor r11, r11, r10
	str r11, [r8, #280]
	ldr r10, [r9, #88]
	and r10, r10, r6
	ldr r11, [r8, #284]
	eor r11, r11, r10
	str r11, [r8, #284]
	str r0, [r8, #224]
	str r1, [r8, #228]
	str r2, [r8, #232]
	str r3, [r8, #236]
	str r4, [r8, #240]
	str r5, [r8, #244]
	str r6, [r8, #248]
	str r7, [r8, #252]
	ldr r0, [r8, #160]
	ldr r1, [r8, #164]
	ldr r2, [r8, #168]
	ldr r3, [r8, #172]
	ldr r4, [r8, #176]
	ldr r5, [r8, #180]
	ldr r6, [r8, #184]
	ldr r7, [r8, #188]
	ldr r10, [r9, #28]
	and r10, r10, r7
	ldr r11, [r8, #192]
	eor r11, r11, r10, ror #8
	str r11, [r8, #192]
	ldr r10, [r9, #0]
	and r10, r10, r0
	ldr r11, [r8, #196]
	eor r11, r11, r10
	str r11, [r8, #196]
	ldr r10, [r9, #4]
	and r10, r10, r1
	ldr r11, [r8, #200]
	eor r11, r11, r10
	str r11, [r8, #200]
	ldr r10, [r9, #8]
	and r10, r10, r2
	ldr r11, [r8, #204]
	eor r11, r11, r10
	str r11, [r8, #204]
	ldr r10, [r9, #12]
	and r10, r10, r3
	ldr r11, [r8, #208]
	eor r11, r11, r10
	str r11, [r8, #208]
	ldr r10, [r9, #16]
	and r10, r10, r4
	ldr r11, [r8, #212]
	eor r11, r11, r10
	str r11, [r8, #212]
	ldr r10, [r9, #20]
	and r10, r10, r5
	ldr r11, [r8, #216]
	eor r11, r11, r10
	str r11, [r8, #216]
	ldr r10, [r9, #24]
	and r10, r10, r6
	ldr r11, [r8, #220]
	eor r11, r11, r10
	str r11, [r8, #220]
	ldr r10, [r9, #32]
	ldr r11, [r8, #192]
	orr r10, r10, r11
	eor r0, r0, r10
	ldr r10, [r9, #36]
	ldr r11, [r8, #196]
	orr r10, r10, r11
	eor r1, r1, r10
	ldr r10, [r9, #40]
	ldr r11, [r8, #200]
	orr r10, r10, r11
	eor r2, r2, r10
	ldr r10, [r9, #44]
	ldr r11, [r8, #204]
	orr r10, r10, r11
	eor r3, r3, r10
	ldr r10, [r9, #48]
	ldr r11, [r8, #208]
	orr r10, r10, r11
	eor r4, r4, r10
	ldr r10, [r9, #52]
	ldr r11, [r8, #212]
	orr r10, r10, r11
	eor r5, r5, r10
	ldr r10, [r9, #56]
	ldr r11, [r8, #216]
	orr r10, r10, r11
	eor r6, r6, r10
	ldr r10, [r9, #60]
	ldr r11, [r8, #220]
	orr r10, r10, r11
	eor r7, r7, r10
	str r0, [r8, #160]
	str r1, [r8, #164]
	str r2, [r8, #168]
	str r3, [r8, #172]
	str r4, [r8, #176]
	str r5, [r8, #180]
	str r6, [r8, #184]
	str r7, [r8, #188]
	add r9, r9, #128
211:
	ldr r10, [r8, #2468]
	cmp r9, r10
	bne 28b
	ldr r11, [r8, #224]
	ldr r10, [r9, #0]
	eor r11, r11, r10
	str r11, [r8, #224]
	ldr r11, [r8, #228]
	ldr r10, [r9, #4]
	eor r11, r11, r10
	str r11, [r8, #228]
	ldr r11, [r8, #232]
	ldr r10, [r9, #8]
	eor r11, r11, r10
	str r11, [r8, #232]
	ldr r11, [r8, #236]
	ldr r10, [r9, #12]
	eor r11, r11, r10
	str r11, [r8, #236]
	ldr r11, [r8, #240]
	ldr r10, [r9, #16]
	eor r11, r11, r10
	str r11, [r8, #240]
	ldr r11, [r8, #244]
	ldr r10, [r9, #20]
	eor r11, r11, r10
	str r11, [r8, #244]
	ldr r11, [r8, #248]
	ldr r10, [r9, #24]
	eor r11, r11, r10
	str r11, [r8, #248]
	ldr r11, [r8, #252]
	ldr r10, [r9, #28]
	eor r11, r11, r10
	str r11, [r8, #252]
	ldr r11, [r8, #256]
	ldr r10, [r9, #32]
	eor r11, r11, r10
	str r11, [r8, #256]
	ldr r11, [r8, #260]
	ldr r10, [r9, #36]
	eor r11, r11, r10
	str r11, [r8, #260]
	ldr r11, [r8, #264]
	ldr r10, [r9, #40]
	eor r11, r11, r10
	str r11, [r8, #264]
	ldr r11, [r8, #268]
	ldr r10, [r9, #44]
	eor r11, r11, r10
	str r11, [r8, #268]
	ldr r11, [r8, #272]
	ldr r10, [r9, #48]
	eor r11, r11, r10
	str r11, [r8, #272]
	ldr r11, [r8, #276]
	ldr r10, [r9, #52]
	eor r11, r11, r10
	str r11, [r8, #276]
	ldr r11, [r8, #280]
	ldr r10, [r9, #56]
	eor r11, r11, r10
	str r11, [r8, #280]
	ldr r11, [r8, #284]
	ldr r10, [r9, #60]
	eor r11, r11, r10
	str r11, [r8, #284]
	ldr r11, [r8, #160]
	ldr r10, [r9, #64]
	eor r11, r11, r10
	str r11, [r8, #160]
	ldr r11, [r8, #164]
	ldr r10, [r9, #68]
	eor r11, r11, r10
	str r11, [r8, #164]
	ldr r11, [r8, #168]
	ldr r10, [r9, #72]
	eor r11, r11, r10
	str r11, [r8, #168]
	ldr r11, [r8, #172]
	ldr r10, [r9, #76]
	eor r11, r11, r10
	str r11, [r8, #172]
	ldr r11, [r8, #176]
	ldr r10, [r9, #80]
	eor r11, r11, r10
	str r11, [r8, #176]
	ldr r11, [r8, #180]
	ldr r10, [r9, #84]
	eor r11, r11, r10
	str r11, [r8, #180]
	ldr r11, [r8, #184]
	ldr r10, [r9, #88]
	eor r11, r11, r10
	str r11, [r8, #184]
	ldr r11, [r8, #188]
	ldr r10, [r9, #92]
	eor r11, r11, r10
	str r11, [r8, #188]
	ldr r11, [r8, #192]
	ldr r10, [r9, #96]
	eor r11, r11, r10
	str r11, [r8, #192]
	ldr r11, [r8, #196]
	ldr r10, [r9, #100]
	eor r11, r11, r10
	str r11, [r8, #196]
	ldr r11, [r8, #200]
	ldr r10, [r9, #104]
	eor r11, r11, r10
	str r11, [r8, #200]
	ldr r11, [r8, #204]
	ldr r10, [r9, #108]
	eor r11, r11, r10
	str r11, [r8, #204]
	ldr r11, [r8, #208]
	ldr r10, [r9, #112]
	eor r11, r11, r10
	str r11, [r8, #208]
	ldr r11, [r8, #212]
	ldr r10, [r9, #116]
	eor r11, r11, r10
	str r11, [r8, #212]
	ldr r11, [r8, #216]
	ldr r10, [r9, #120]
	eor r11, r11, r10
	str r11, [r8, #216]
	ldr r11, [r8, #220]
	ldr r10, [r9, #124]
	eor r11, r11, r10
	str r11, [r8, #220]
	ldr r0, [r8, #224]
	ldr r1, [r8, #228]
	ldr r2, [r8, #232]
	ldr r3, [r8, #236]
	ldr r4, [r8, #240]
	ldr r5, [r8, #244]
	ldr r6, [r8, #248]
	ldr r7, [r8, #252]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2528]
	str r1, [r8, #2544]
	str r2, [r8, #2560]
	str r3, [r8, #2576]
	str r4, [r8, #2592]
	str r5, [r8, #2608]
	str r6, [r8, #2624]
	str r7, [r8, #2640]
	ldr r0, [r8, #256]
	ldr r1, [r8, #260]
	ldr r2, [r8, #264]
	ldr r3, [r8, #268]
	ldr r4, [r8, #272]
	ldr r5, [r8, #276]
	ldr r6, [r8, #280]
	ldr r7, [r8, #284]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2532]
	str r1, [r8, #2548]
	str r2, [r8, #2564]
	str r3, [r8, #2580]
	str r4, [r8, #2596]
	str r5, [r8, #2612]
	str r6, [r8, #2628]
	str r7, [r8, #2644]
	ldr r0, [r8, #160]
	ldr r1, [r8, #164]
	ldr r2, [r8, #168]
	ldr r3, [r8, #172]
	ldr r4, [r8, #176]
	ldr r5, [r8, #180]
	ldr r6, [r8, #184]
	ldr r7, [r8, #188]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2536]
	str r1, [r8, #2552]
	str r2, [r8, #2568]
	str r3, [r8, #2584]
	str r4, [r8, #2600]
	str r5, [r8, #2616]
	str r6, [r8, #2632]
	str r7, [r8, #2648]
	ldr r0, [r8, #192]
	ldr r1, [r8, #196]
	ldr r2, [r8, #200]
	ldr r3, [r8, #204]
	ldr r4, [r8, #208]
	ldr r5, [r8, #212]
	ldr r6, [r8, #216]
	ldr r7, [r8, #220]
	movw r11, #21845
	movt r11, #21845
	eor r10, r1, r0, lsr #1
	and r10, r10, r11
	eor r1, r1, r10
	eor r0, r0, r10, ror #31
	eor r10, r3, r2, lsr #1
	and r10, r10, r11
	eor r3, r3, r10
	eor r2, r2, r10, ror #31
	eor r10, r5, r4, lsr #1
	and r10, r10, r11
	eor r5, r5, r10
	eor r4, r4, r10, ror #31
	eor r10, r7, r6, lsr #1
	and r10, r10, r11
	eor r7, r7, r10
	eor r6, r6, r10, ror #31
	movw r11, #13107
	movt r11, #13107
	eor r10, r2, r0, lsr #2
	and r10, r10, r11
	eor r2, r2, r10
	eor r0, r0, r10, ror #30
	eor r10, r3, r1, lsr #2
	and r10, r10, r11
	eor r3, r3, r10
	eor r1, r1, r10, ror #30
	eor r10, r6, r4, lsr #2
	and r10, r10, r11
	eor r6, r6, r10
	eor r4, r4, r10, ror #30
	eor r10, r7, r5, lsr #2
	and r10, r10, r11
	eor r7, r7, r10
	eor r5, r5, r10, ror #30
	movw r11, #3855
	movt r11, #3855
	eor r10, r4, r0, lsr #4
	and r10, r10, r11
	eor r4, r4, r10
	eor r0, r0, r10, ror #28
	eor r10, r5, r1, lsr #4
	and r10, r10, r11
	eor r5, r5, r10
	eor r1, r1, r10, ror #28
	eor r10, r6, r2, lsr #4
	and r10, r10, r11
	eor r6, r6, r10
	eor r2, r2, r10, ror #28
	eor r10, r7, r3, lsr #4
	and r10, r10, r11
	eor r7, r7, r10
	eor r3, r3, r10, ror #28
	str r0, [r8, #2540]
	str r1, [r8, #2556]
	str r2, [r8, #2572]
	str r3, [r8, #2588]
	str r4, [r8, #2604]
	str r5, [r8, #2620]
	str r6, [r8, #2636]
	str r7, [r8, #2652]
	ldr r1, [r8, #2508]
	ldr r2, [r8, #2512]
	ldr lr, [r8, #2468]
	lsr r10, r2, #3
	cmp r10, #0
	bne 212f
	mov r3, r2
	b 213f
212:
	mov r3, #8
213:
	add r0, r8, #2528
	mov r12, r1
214:
	ldr r10, [r0, #0]
	str r10, [r12, #0]
	ldr r10, [r0, #4]
	str r10, [r12, #4]
	ldr r10, [r0, #8]
	str r10, [r12, #8]
	ldr r10, [r0, #12]
	str r10, [r12, #12]
	add r0, r0, #16
	add r12, r12, #16
	subs r3, r3, #1
	bne 214b
	lsr r10, r2, #3
	cmp r10, #0
	bne 215f
	mov r3, r2
	b 216f
215:
	mov r3, #8
216:
	add r1, r1, #128
	subs r2, r2, r3
	bne 24b
	b 23f
22:
23:
	mov r12, r8
	ldr r4, [r12, #2472]
	ldr r5, [r12, #2476]
	ldr r6, [r12, #2480]
	ldr r7, [r12, #2484]
	ldr r8, [r12, #2488]
	ldr r9, [r12, #2492]
	ldr r10, [r12, #2496]
	ldr r11, [r12, #2500]
	ldr lr, [r12, #2504]
	bx lr
