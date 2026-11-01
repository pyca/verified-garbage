// The functions of `src/internal/vg_sm4_ecb.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_ecb:
	sub sp, sp, #1472
	add r12, sp, #0
	str lr, [r12, #4]
	add lr, sp, #8
	str lr, [r12, #0]
	ldr lr, [sp, #4]
	ldr r12, [sp, #0]
	str r4, [r12, #1408]
	str r5, [r12, #1412]
	str r6, [r12, #1416]
	str r7, [r12, #1420]
	str r8, [r12, #1424]
	str r9, [r12, #1428]
	str r10, [r12, #1432]
	str r11, [r12, #1436]
	str lr, [r12, #1440]
	mov r8, r12
	mov r12, r0
	cmp r3, #0
	beq 20f
	add r9, r8, #1376
	mov lr, #32
22:
	ldr r0, [r12, #0]
	rev r0, r0
	movw r11, #257
	movt r11, #257
	and r3, r11, r0
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #0]
	and r3, r11, r0, lsr #1
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #4]
	and r3, r11, r0, lsr #2
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #8]
	and r3, r11, r0, lsr #3
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #12]
	and r3, r11, r0, lsr #4
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #16]
	and r3, r11, r0, lsr #5
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #20]
	and r3, r11, r0, lsr #6
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #24]
	and r3, r11, r0, lsr #7
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #28]
	add r12, r12, #4
	sub r9, r9, #32
	subs lr, lr, #1
	bne 22b
	b 21f
20:
	add r9, r8, #384
	mov lr, #32
23:
	ldr r0, [r12, #0]
	rev r0, r0
	movw r11, #257
	movt r11, #257
	and r3, r11, r0
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #0]
	and r3, r11, r0, lsr #1
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #4]
	and r3, r11, r0, lsr #2
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #8]
	and r3, r11, r0, lsr #3
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #12]
	and r3, r11, r0, lsr #4
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #16]
	and r3, r11, r0, lsr #5
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #20]
	and r3, r11, r0, lsr #6
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #24]
	and r3, r11, r0, lsr #7
	eor r3, r3, r3, ror #31
	eor r3, r3, r3, ror #30
	eor r3, r3, r3, ror #28
	str r3, [r9, #28]
	add r12, r12, #4
	add r9, r9, #32
	subs lr, lr, #1
	bne 23b
21:
	cmp r2, #0
	beq 24f
26:
	lsr r10, r2, #3
	cmp r10, #0
	bne 27f
	mov r3, r2
	b 28f
27:
	mov r3, #8
28:
	mov r0, r1
	add r12, r8, #256
29:
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
	bne 29b
	str r1, [r8, #1444]
	str r2, [r8, #1448]
	ldr r0, [r8, #256]
	ldr r1, [r8, #272]
	ldr r2, [r8, #288]
	ldr r3, [r8, #304]
	ldr r4, [r8, #320]
	ldr r5, [r8, #336]
	ldr r6, [r8, #352]
	ldr r7, [r8, #368]
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
	str r0, [r8, #128]
	str r1, [r8, #132]
	str r2, [r8, #136]
	str r3, [r8, #140]
	str r4, [r8, #144]
	str r5, [r8, #148]
	str r6, [r8, #152]
	str r7, [r8, #156]
	ldr r0, [r8, #260]
	ldr r1, [r8, #276]
	ldr r2, [r8, #292]
	ldr r3, [r8, #308]
	ldr r4, [r8, #324]
	ldr r5, [r8, #340]
	ldr r6, [r8, #356]
	ldr r7, [r8, #372]
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
	ldr r0, [r8, #264]
	ldr r1, [r8, #280]
	ldr r2, [r8, #296]
	ldr r3, [r8, #312]
	ldr r4, [r8, #328]
	ldr r5, [r8, #344]
	ldr r6, [r8, #360]
	ldr r7, [r8, #376]
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
	ldr r0, [r8, #268]
	ldr r1, [r8, #284]
	ldr r2, [r8, #300]
	ldr r3, [r8, #316]
	ldr r4, [r8, #332]
	ldr r5, [r8, #348]
	ldr r6, [r8, #364]
	ldr r7, [r8, #380]
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
	add r9, r8, #384
210:
	ldr r0, [r8, #160]
	ldr r10, [r8, #192]
	eor r0, r0, r10
	ldr r10, [r8, #224]
	eor r0, r0, r10
	ldr r10, [r9, #0]
	eor r0, r0, r10
	ldr r1, [r8, #164]
	ldr r10, [r8, #196]
	eor r1, r1, r10
	ldr r10, [r8, #228]
	eor r1, r1, r10
	ldr r10, [r9, #4]
	eor r1, r1, r10
	ldr r2, [r8, #168]
	ldr r10, [r8, #200]
	eor r2, r2, r10
	ldr r10, [r8, #232]
	eor r2, r2, r10
	ldr r10, [r9, #8]
	eor r2, r2, r10
	ldr r3, [r8, #172]
	ldr r10, [r8, #204]
	eor r3, r3, r10
	ldr r10, [r8, #236]
	eor r3, r3, r10
	ldr r10, [r9, #12]
	eor r3, r3, r10
	ldr r4, [r8, #176]
	ldr r10, [r8, #208]
	eor r4, r4, r10
	ldr r10, [r8, #240]
	eor r4, r4, r10
	ldr r10, [r9, #16]
	eor r4, r4, r10
	ldr r5, [r8, #180]
	ldr r10, [r8, #212]
	eor r5, r5, r10
	ldr r10, [r8, #244]
	eor r5, r5, r10
	ldr r10, [r9, #20]
	eor r5, r5, r10
	ldr r6, [r8, #184]
	ldr r10, [r8, #216]
	eor r6, r6, r10
	ldr r10, [r8, #248]
	eor r6, r6, r10
	ldr r10, [r9, #24]
	eor r6, r6, r10
	ldr r7, [r8, #188]
	ldr r10, [r8, #220]
	eor r7, r7, r10
	ldr r10, [r8, #252]
	eor r7, r7, r10
	ldr r10, [r9, #28]
	eor r7, r7, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r3, r0
	eor r11, r1, r10
	eor r12, r4, r2
	eor r4, r7, r4
	eor lr, r7, r3
	str r0, [r8, #4]
	ldr r0, [r8, #0]
	eor lr, lr, r0
	str r1, [r8, #8]
	eor r1, r11, r4
	eor r4, r6, r4
	str r4, [r8, #12]
	eor r4, r7, r2
	str r4, [r8, #16]
	eor r4, r7, r12
	eor r4, r4, r0
	eor r7, r7, r11
	str r7, [r8, #20]
	eor r7, r5, r12
	eor r2, r6, r2
	eor r3, r3, r7
	str r3, [r8, #24]
	eor r3, r5, r11
	eor r3, r3, r0
	eor r11, r12, r11
	eor r11, r11, r0
	eor r12, r12, r3
	str r12, [r8, #28]
	eor r12, r5, r4
	str r3, [r8, #32]
	and r3, r1, r11
	str r1, [r8, #36]
	eor r1, r6, r12
	str r11, [r8, #40]
	eor r11, r10, r4
	eor r5, r5, lr
	eor r10, r10, r7
	and r7, r2, r5
	str r5, [r8, #44]
	ldr r5, [r8, #8]
	str r3, [r8, #48]
	eor r3, r5, r1
	eor r12, r5, r12
	eor r12, r12, r0
	orr r0, r3, r12
	str r3, [r8, #52]
	ldr r3, [r8, #32]
	str r12, [r8, #56]
	eor r12, r3, r2
	str r7, [r8, #60]
	eor r7, r5, r2
	eor r6, r6, r11
	orr r11, r12, r4
	str r12, [r8, #64]
	and r12, r5, r10
	str r10, [r8, #68]
	ldr r10, [r8, #24]
	str r2, [r8, #72]
	orr r2, r3, r10
	eor lr, r5, lr
	ldr r10, [r8, #12]
	eor r5, r3, r10
	ldr r3, [r8, #20]
	str r5, [r8, #76]
	orr r5, r1, r3
	orr r3, r6, lr
	eor r3, r3, r0
	eor r2, r2, r0
	ldr r0, [r8, #60]
	eor r0, r0, r12
	str r1, [r8, #60]
	ldr r1, [r8, #4]
	eor r10, r1, r10
	eor r1, r1, r4
	str r4, [r8, #4]
	ldr r4, [r8, #48]
	eor r5, r5, r4
	eor r0, r0, r5
	eor r11, r11, r4
	ldr r4, [r8, #28]
	eor r0, r0, r4
	and r4, r7, r1
	eor r2, r2, r5
	eor r3, r3, r11
	ldr r5, [r8, #76]
	eor r3, r3, r5
	ldr r5, [r8, #16]
	eor r2, r2, r5
	eor r4, r4, r12
	ldr r12, [r8, #8]
	eor r10, r12, r10
	eor r4, r4, r11
	and r11, r2, r0
	eor r4, r4, r10
	eor r2, r2, r3
	eor r10, r0, r4
	eor r5, r3, r11
	eor r11, r4, r11
	and r5, r5, r10
	eor r5, r5, r4
	and r10, r2, r11
	eor r12, r11, r5
	and r4, r4, r12
	eor r10, r10, r3
	eor r0, r0, r5
	eor r11, r11, r4
	ldr r3, [r8, #0]
	eor r6, r6, r3
	and r6, r5, r6
	and r11, r10, r11
	eor r2, r2, r11
	eor r11, r5, r3
	orr r11, r11, lr
	eor r4, r4, r0
	eor r4, r4, r3
	eor r0, r10, r5
	eor r5, r5, r4
	eor lr, r10, r2
	ldr r12, [r8, #56]
	orr r12, r5, r12
	and r1, r10, r1
	str r11, [r8, #56]
	ldr r11, [r8, #52]
	orr r5, r5, r11
	ldr r11, [r8, #32]
	orr r11, r4, r11
	str r6, [r8, #32]
	ldr r6, [r8, #24]
	orr r6, r4, r6
	ldr r3, [r8, #40]
	and r3, r0, r3
	and r10, r10, r7
	eor r7, r12, r6
	eor r3, r3, r11
	str r7, [r8, #40]
	ldr r7, [r8, #72]
	and r7, r2, r7
	eor r4, r2, r4
	str r11, [r8, #72]
	eor r11, r7, r3
	str r3, [r8, #24]
	ldr r3, [r8, #64]
	orr r3, r4, r3
	eor r10, r10, r11
	eor r12, r12, r1
	ldr r1, [r8, #44]
	and r2, r2, r1
	ldr r1, [r8, #4]
	orr r1, r4, r1
	ldr r11, [r8, #36]
	and r11, r0, r11
	eor r0, r0, r4
	ldr r4, [r8, #8]
	and r4, lr, r4
	eor r4, r4, r11
	eor r5, r5, r11
	eor r6, r6, r1
	eor r1, r2, r12
	ldr r11, [r8, #0]
	eor r1, r1, r11
	eor r3, r3, r5
	ldr r11, [r8, #60]
	orr r11, r0, r11
	str r2, [r8, #60]
	ldr r2, [r8, #20]
	orr r0, r0, r2
	eor r2, r11, r6
	eor r5, r5, r2
	eor r7, r7, r11
	ldr r11, [r8, #68]
	and lr, lr, r11
	ldr r11, [r8, #32]
	eor r2, r11, r1
	eor r12, lr, r12
	eor r11, r0, r10
	eor r6, r6, r2
	eor r7, r7, r4
	eor r12, r5, r12
	ldr r4, [r8, #24]
	eor r4, r4, r1
	eor r4, r5, r4
	eor r1, r10, r6
	ldr r6, [r8, #56]
	eor r6, r6, r11
	ldr r10, [r8, #72]
	eor r10, r10, r12
	eor r11, r11, r3
	eor r6, r2, r6
	ldr r2, [r8, #40]
	eor r5, r11, r2
	eor lr, lr, r11
	ldr r11, [r8, #32]
	eor r3, r11, r3
	ldr r11, [r8, #60]
	eor r2, r11, lr
	eor r0, r0, r10
	ror r12, r6, #8
	eor r10, r12, r12, ror #8
	eor r10, r10, r12, ror #16
	eor r10, r10, r0
	eor r10, r10, r0, ror #24
	ldr r11, [r8, #128]
	eor r10, r10, r11
	str r10, [r8, #128]
	ror r12, r7, #8
	eor r10, r12, r12, ror #8
	eor r10, r10, r12, ror #16
	eor r10, r10, r1
	eor r10, r10, r1, ror #24
	ldr r11, [r8, #132]
	eor r10, r10, r11
	str r10, [r8, #132]
	eor r10, r0, r0, ror #8
	eor r10, r10, r0, ror #16
	eor r10, r10, r2
	eor r10, r10, r2, ror #24
	ldr r11, [r8, #136]
	eor r10, r10, r11
	str r10, [r8, #136]
	eor r10, r1, r1, ror #8
	eor r10, r10, r1, ror #16
	eor r10, r10, r3
	eor r10, r10, r3, ror #24
	ldr r11, [r8, #140]
	eor r10, r10, r11
	str r10, [r8, #140]
	eor r10, r2, r2, ror #8
	eor r10, r10, r2, ror #16
	eor r10, r10, r4
	eor r10, r10, r4, ror #24
	ldr r11, [r8, #144]
	eor r10, r10, r11
	str r10, [r8, #144]
	eor r10, r3, r3, ror #8
	eor r10, r10, r3, ror #16
	eor r10, r10, r5
	eor r10, r10, r5, ror #24
	ldr r11, [r8, #148]
	eor r10, r10, r11
	str r10, [r8, #148]
	eor r10, r4, r4, ror #8
	eor r10, r10, r4, ror #16
	eor r10, r10, r6
	eor r10, r10, r6, ror #24
	ldr r11, [r8, #152]
	eor r10, r10, r11
	str r10, [r8, #152]
	eor r10, r5, r5, ror #8
	eor r10, r10, r5, ror #16
	eor r10, r10, r7
	eor r10, r10, r7, ror #24
	ldr r11, [r8, #156]
	eor r10, r10, r11
	str r10, [r8, #156]
	ldr r0, [r8, #192]
	ldr r10, [r8, #224]
	eor r0, r0, r10
	ldr r10, [r8, #128]
	eor r0, r0, r10
	ldr r10, [r9, #32]
	eor r0, r0, r10
	ldr r1, [r8, #196]
	ldr r10, [r8, #228]
	eor r1, r1, r10
	ldr r10, [r8, #132]
	eor r1, r1, r10
	ldr r10, [r9, #36]
	eor r1, r1, r10
	ldr r2, [r8, #200]
	ldr r10, [r8, #232]
	eor r2, r2, r10
	ldr r10, [r8, #136]
	eor r2, r2, r10
	ldr r10, [r9, #40]
	eor r2, r2, r10
	ldr r3, [r8, #204]
	ldr r10, [r8, #236]
	eor r3, r3, r10
	ldr r10, [r8, #140]
	eor r3, r3, r10
	ldr r10, [r9, #44]
	eor r3, r3, r10
	ldr r4, [r8, #208]
	ldr r10, [r8, #240]
	eor r4, r4, r10
	ldr r10, [r8, #144]
	eor r4, r4, r10
	ldr r10, [r9, #48]
	eor r4, r4, r10
	ldr r5, [r8, #212]
	ldr r10, [r8, #244]
	eor r5, r5, r10
	ldr r10, [r8, #148]
	eor r5, r5, r10
	ldr r10, [r9, #52]
	eor r5, r5, r10
	ldr r6, [r8, #216]
	ldr r10, [r8, #248]
	eor r6, r6, r10
	ldr r10, [r8, #152]
	eor r6, r6, r10
	ldr r10, [r9, #56]
	eor r6, r6, r10
	ldr r7, [r8, #220]
	ldr r10, [r8, #252]
	eor r7, r7, r10
	ldr r10, [r8, #156]
	eor r7, r7, r10
	ldr r10, [r9, #60]
	eor r7, r7, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r3, r0
	eor r11, r1, r10
	eor r12, r4, r2
	eor r4, r7, r4
	eor lr, r7, r3
	str r0, [r8, #4]
	ldr r0, [r8, #0]
	eor lr, lr, r0
	str r1, [r8, #8]
	eor r1, r11, r4
	eor r4, r6, r4
	str r4, [r8, #12]
	eor r4, r7, r2
	str r4, [r8, #16]
	eor r4, r7, r12
	eor r4, r4, r0
	eor r7, r7, r11
	str r7, [r8, #20]
	eor r7, r5, r12
	eor r2, r6, r2
	eor r3, r3, r7
	str r3, [r8, #24]
	eor r3, r5, r11
	eor r3, r3, r0
	eor r11, r12, r11
	eor r11, r11, r0
	eor r12, r12, r3
	str r12, [r8, #28]
	eor r12, r5, r4
	str r3, [r8, #32]
	and r3, r1, r11
	str r1, [r8, #36]
	eor r1, r6, r12
	str r11, [r8, #40]
	eor r11, r10, r4
	eor r5, r5, lr
	eor r10, r10, r7
	and r7, r2, r5
	str r5, [r8, #44]
	ldr r5, [r8, #8]
	str r3, [r8, #48]
	eor r3, r5, r1
	eor r12, r5, r12
	eor r12, r12, r0
	orr r0, r3, r12
	str r3, [r8, #52]
	ldr r3, [r8, #32]
	str r12, [r8, #56]
	eor r12, r3, r2
	str r7, [r8, #60]
	eor r7, r5, r2
	eor r6, r6, r11
	orr r11, r12, r4
	str r12, [r8, #64]
	and r12, r5, r10
	str r10, [r8, #68]
	ldr r10, [r8, #24]
	str r2, [r8, #72]
	orr r2, r3, r10
	eor lr, r5, lr
	ldr r10, [r8, #12]
	eor r5, r3, r10
	ldr r3, [r8, #20]
	str r5, [r8, #76]
	orr r5, r1, r3
	orr r3, r6, lr
	eor r3, r3, r0
	eor r2, r2, r0
	ldr r0, [r8, #60]
	eor r0, r0, r12
	str r1, [r8, #60]
	ldr r1, [r8, #4]
	eor r10, r1, r10
	eor r1, r1, r4
	str r4, [r8, #4]
	ldr r4, [r8, #48]
	eor r5, r5, r4
	eor r0, r0, r5
	eor r11, r11, r4
	ldr r4, [r8, #28]
	eor r0, r0, r4
	and r4, r7, r1
	eor r2, r2, r5
	eor r3, r3, r11
	ldr r5, [r8, #76]
	eor r3, r3, r5
	ldr r5, [r8, #16]
	eor r2, r2, r5
	eor r4, r4, r12
	ldr r12, [r8, #8]
	eor r10, r12, r10
	eor r4, r4, r11
	and r11, r2, r0
	eor r4, r4, r10
	eor r2, r2, r3
	eor r10, r0, r4
	eor r5, r3, r11
	eor r11, r4, r11
	and r5, r5, r10
	eor r5, r5, r4
	and r10, r2, r11
	eor r12, r11, r5
	and r4, r4, r12
	eor r10, r10, r3
	eor r0, r0, r5
	eor r11, r11, r4
	ldr r3, [r8, #0]
	eor r6, r6, r3
	and r6, r5, r6
	and r11, r10, r11
	eor r2, r2, r11
	eor r11, r5, r3
	orr r11, r11, lr
	eor r4, r4, r0
	eor r4, r4, r3
	eor r0, r10, r5
	eor r5, r5, r4
	eor lr, r10, r2
	ldr r12, [r8, #56]
	orr r12, r5, r12
	and r1, r10, r1
	str r11, [r8, #56]
	ldr r11, [r8, #52]
	orr r5, r5, r11
	ldr r11, [r8, #32]
	orr r11, r4, r11
	str r6, [r8, #32]
	ldr r6, [r8, #24]
	orr r6, r4, r6
	ldr r3, [r8, #40]
	and r3, r0, r3
	and r10, r10, r7
	eor r7, r12, r6
	eor r3, r3, r11
	str r7, [r8, #40]
	ldr r7, [r8, #72]
	and r7, r2, r7
	eor r4, r2, r4
	str r11, [r8, #72]
	eor r11, r7, r3
	str r3, [r8, #24]
	ldr r3, [r8, #64]
	orr r3, r4, r3
	eor r10, r10, r11
	eor r12, r12, r1
	ldr r1, [r8, #44]
	and r2, r2, r1
	ldr r1, [r8, #4]
	orr r1, r4, r1
	ldr r11, [r8, #36]
	and r11, r0, r11
	eor r0, r0, r4
	ldr r4, [r8, #8]
	and r4, lr, r4
	eor r4, r4, r11
	eor r5, r5, r11
	eor r6, r6, r1
	eor r1, r2, r12
	ldr r11, [r8, #0]
	eor r1, r1, r11
	eor r3, r3, r5
	ldr r11, [r8, #60]
	orr r11, r0, r11
	str r2, [r8, #60]
	ldr r2, [r8, #20]
	orr r0, r0, r2
	eor r2, r11, r6
	eor r5, r5, r2
	eor r7, r7, r11
	ldr r11, [r8, #68]
	and lr, lr, r11
	ldr r11, [r8, #32]
	eor r2, r11, r1
	eor r12, lr, r12
	eor r11, r0, r10
	eor r6, r6, r2
	eor r7, r7, r4
	eor r12, r5, r12
	ldr r4, [r8, #24]
	eor r4, r4, r1
	eor r4, r5, r4
	eor r1, r10, r6
	ldr r6, [r8, #56]
	eor r6, r6, r11
	ldr r10, [r8, #72]
	eor r10, r10, r12
	eor r11, r11, r3
	eor r6, r2, r6
	ldr r2, [r8, #40]
	eor r5, r11, r2
	eor lr, lr, r11
	ldr r11, [r8, #32]
	eor r3, r11, r3
	ldr r11, [r8, #60]
	eor r2, r11, lr
	eor r0, r0, r10
	ror r12, r6, #8
	eor r10, r12, r12, ror #8
	eor r10, r10, r12, ror #16
	eor r10, r10, r0
	eor r10, r10, r0, ror #24
	ldr r11, [r8, #160]
	eor r10, r10, r11
	str r10, [r8, #160]
	ror r12, r7, #8
	eor r10, r12, r12, ror #8
	eor r10, r10, r12, ror #16
	eor r10, r10, r1
	eor r10, r10, r1, ror #24
	ldr r11, [r8, #164]
	eor r10, r10, r11
	str r10, [r8, #164]
	eor r10, r0, r0, ror #8
	eor r10, r10, r0, ror #16
	eor r10, r10, r2
	eor r10, r10, r2, ror #24
	ldr r11, [r8, #168]
	eor r10, r10, r11
	str r10, [r8, #168]
	eor r10, r1, r1, ror #8
	eor r10, r10, r1, ror #16
	eor r10, r10, r3
	eor r10, r10, r3, ror #24
	ldr r11, [r8, #172]
	eor r10, r10, r11
	str r10, [r8, #172]
	eor r10, r2, r2, ror #8
	eor r10, r10, r2, ror #16
	eor r10, r10, r4
	eor r10, r10, r4, ror #24
	ldr r11, [r8, #176]
	eor r10, r10, r11
	str r10, [r8, #176]
	eor r10, r3, r3, ror #8
	eor r10, r10, r3, ror #16
	eor r10, r10, r5
	eor r10, r10, r5, ror #24
	ldr r11, [r8, #180]
	eor r10, r10, r11
	str r10, [r8, #180]
	eor r10, r4, r4, ror #8
	eor r10, r10, r4, ror #16
	eor r10, r10, r6
	eor r10, r10, r6, ror #24
	ldr r11, [r8, #184]
	eor r10, r10, r11
	str r10, [r8, #184]
	eor r10, r5, r5, ror #8
	eor r10, r10, r5, ror #16
	eor r10, r10, r7
	eor r10, r10, r7, ror #24
	ldr r11, [r8, #188]
	eor r10, r10, r11
	str r10, [r8, #188]
	ldr r0, [r8, #224]
	ldr r10, [r8, #128]
	eor r0, r0, r10
	ldr r10, [r8, #160]
	eor r0, r0, r10
	ldr r10, [r9, #64]
	eor r0, r0, r10
	ldr r1, [r8, #228]
	ldr r10, [r8, #132]
	eor r1, r1, r10
	ldr r10, [r8, #164]
	eor r1, r1, r10
	ldr r10, [r9, #68]
	eor r1, r1, r10
	ldr r2, [r8, #232]
	ldr r10, [r8, #136]
	eor r2, r2, r10
	ldr r10, [r8, #168]
	eor r2, r2, r10
	ldr r10, [r9, #72]
	eor r2, r2, r10
	ldr r3, [r8, #236]
	ldr r10, [r8, #140]
	eor r3, r3, r10
	ldr r10, [r8, #172]
	eor r3, r3, r10
	ldr r10, [r9, #76]
	eor r3, r3, r10
	ldr r4, [r8, #240]
	ldr r10, [r8, #144]
	eor r4, r4, r10
	ldr r10, [r8, #176]
	eor r4, r4, r10
	ldr r10, [r9, #80]
	eor r4, r4, r10
	ldr r5, [r8, #244]
	ldr r10, [r8, #148]
	eor r5, r5, r10
	ldr r10, [r8, #180]
	eor r5, r5, r10
	ldr r10, [r9, #84]
	eor r5, r5, r10
	ldr r6, [r8, #248]
	ldr r10, [r8, #152]
	eor r6, r6, r10
	ldr r10, [r8, #184]
	eor r6, r6, r10
	ldr r10, [r9, #88]
	eor r6, r6, r10
	ldr r7, [r8, #252]
	ldr r10, [r8, #156]
	eor r7, r7, r10
	ldr r10, [r8, #188]
	eor r7, r7, r10
	ldr r10, [r9, #92]
	eor r7, r7, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r3, r0
	eor r11, r1, r10
	eor r12, r4, r2
	eor r4, r7, r4
	eor lr, r7, r3
	str r0, [r8, #4]
	ldr r0, [r8, #0]
	eor lr, lr, r0
	str r1, [r8, #8]
	eor r1, r11, r4
	eor r4, r6, r4
	str r4, [r8, #12]
	eor r4, r7, r2
	str r4, [r8, #16]
	eor r4, r7, r12
	eor r4, r4, r0
	eor r7, r7, r11
	str r7, [r8, #20]
	eor r7, r5, r12
	eor r2, r6, r2
	eor r3, r3, r7
	str r3, [r8, #24]
	eor r3, r5, r11
	eor r3, r3, r0
	eor r11, r12, r11
	eor r11, r11, r0
	eor r12, r12, r3
	str r12, [r8, #28]
	eor r12, r5, r4
	str r3, [r8, #32]
	and r3, r1, r11
	str r1, [r8, #36]
	eor r1, r6, r12
	str r11, [r8, #40]
	eor r11, r10, r4
	eor r5, r5, lr
	eor r10, r10, r7
	and r7, r2, r5
	str r5, [r8, #44]
	ldr r5, [r8, #8]
	str r3, [r8, #48]
	eor r3, r5, r1
	eor r12, r5, r12
	eor r12, r12, r0
	orr r0, r3, r12
	str r3, [r8, #52]
	ldr r3, [r8, #32]
	str r12, [r8, #56]
	eor r12, r3, r2
	str r7, [r8, #60]
	eor r7, r5, r2
	eor r6, r6, r11
	orr r11, r12, r4
	str r12, [r8, #64]
	and r12, r5, r10
	str r10, [r8, #68]
	ldr r10, [r8, #24]
	str r2, [r8, #72]
	orr r2, r3, r10
	eor lr, r5, lr
	ldr r10, [r8, #12]
	eor r5, r3, r10
	ldr r3, [r8, #20]
	str r5, [r8, #76]
	orr r5, r1, r3
	orr r3, r6, lr
	eor r3, r3, r0
	eor r2, r2, r0
	ldr r0, [r8, #60]
	eor r0, r0, r12
	str r1, [r8, #60]
	ldr r1, [r8, #4]
	eor r10, r1, r10
	eor r1, r1, r4
	str r4, [r8, #4]
	ldr r4, [r8, #48]
	eor r5, r5, r4
	eor r0, r0, r5
	eor r11, r11, r4
	ldr r4, [r8, #28]
	eor r0, r0, r4
	and r4, r7, r1
	eor r2, r2, r5
	eor r3, r3, r11
	ldr r5, [r8, #76]
	eor r3, r3, r5
	ldr r5, [r8, #16]
	eor r2, r2, r5
	eor r4, r4, r12
	ldr r12, [r8, #8]
	eor r10, r12, r10
	eor r4, r4, r11
	and r11, r2, r0
	eor r4, r4, r10
	eor r2, r2, r3
	eor r10, r0, r4
	eor r5, r3, r11
	eor r11, r4, r11
	and r5, r5, r10
	eor r5, r5, r4
	and r10, r2, r11
	eor r12, r11, r5
	and r4, r4, r12
	eor r10, r10, r3
	eor r0, r0, r5
	eor r11, r11, r4
	ldr r3, [r8, #0]
	eor r6, r6, r3
	and r6, r5, r6
	and r11, r10, r11
	eor r2, r2, r11
	eor r11, r5, r3
	orr r11, r11, lr
	eor r4, r4, r0
	eor r4, r4, r3
	eor r0, r10, r5
	eor r5, r5, r4
	eor lr, r10, r2
	ldr r12, [r8, #56]
	orr r12, r5, r12
	and r1, r10, r1
	str r11, [r8, #56]
	ldr r11, [r8, #52]
	orr r5, r5, r11
	ldr r11, [r8, #32]
	orr r11, r4, r11
	str r6, [r8, #32]
	ldr r6, [r8, #24]
	orr r6, r4, r6
	ldr r3, [r8, #40]
	and r3, r0, r3
	and r10, r10, r7
	eor r7, r12, r6
	eor r3, r3, r11
	str r7, [r8, #40]
	ldr r7, [r8, #72]
	and r7, r2, r7
	eor r4, r2, r4
	str r11, [r8, #72]
	eor r11, r7, r3
	str r3, [r8, #24]
	ldr r3, [r8, #64]
	orr r3, r4, r3
	eor r10, r10, r11
	eor r12, r12, r1
	ldr r1, [r8, #44]
	and r2, r2, r1
	ldr r1, [r8, #4]
	orr r1, r4, r1
	ldr r11, [r8, #36]
	and r11, r0, r11
	eor r0, r0, r4
	ldr r4, [r8, #8]
	and r4, lr, r4
	eor r4, r4, r11
	eor r5, r5, r11
	eor r6, r6, r1
	eor r1, r2, r12
	ldr r11, [r8, #0]
	eor r1, r1, r11
	eor r3, r3, r5
	ldr r11, [r8, #60]
	orr r11, r0, r11
	str r2, [r8, #60]
	ldr r2, [r8, #20]
	orr r0, r0, r2
	eor r2, r11, r6
	eor r5, r5, r2
	eor r7, r7, r11
	ldr r11, [r8, #68]
	and lr, lr, r11
	ldr r11, [r8, #32]
	eor r2, r11, r1
	eor r12, lr, r12
	eor r11, r0, r10
	eor r6, r6, r2
	eor r7, r7, r4
	eor r12, r5, r12
	ldr r4, [r8, #24]
	eor r4, r4, r1
	eor r4, r5, r4
	eor r1, r10, r6
	ldr r6, [r8, #56]
	eor r6, r6, r11
	ldr r10, [r8, #72]
	eor r10, r10, r12
	eor r11, r11, r3
	eor r6, r2, r6
	ldr r2, [r8, #40]
	eor r5, r11, r2
	eor lr, lr, r11
	ldr r11, [r8, #32]
	eor r3, r11, r3
	ldr r11, [r8, #60]
	eor r2, r11, lr
	eor r0, r0, r10
	ror r12, r6, #8
	eor r10, r12, r12, ror #8
	eor r10, r10, r12, ror #16
	eor r10, r10, r0
	eor r10, r10, r0, ror #24
	ldr r11, [r8, #192]
	eor r10, r10, r11
	str r10, [r8, #192]
	ror r12, r7, #8
	eor r10, r12, r12, ror #8
	eor r10, r10, r12, ror #16
	eor r10, r10, r1
	eor r10, r10, r1, ror #24
	ldr r11, [r8, #196]
	eor r10, r10, r11
	str r10, [r8, #196]
	eor r10, r0, r0, ror #8
	eor r10, r10, r0, ror #16
	eor r10, r10, r2
	eor r10, r10, r2, ror #24
	ldr r11, [r8, #200]
	eor r10, r10, r11
	str r10, [r8, #200]
	eor r10, r1, r1, ror #8
	eor r10, r10, r1, ror #16
	eor r10, r10, r3
	eor r10, r10, r3, ror #24
	ldr r11, [r8, #204]
	eor r10, r10, r11
	str r10, [r8, #204]
	eor r10, r2, r2, ror #8
	eor r10, r10, r2, ror #16
	eor r10, r10, r4
	eor r10, r10, r4, ror #24
	ldr r11, [r8, #208]
	eor r10, r10, r11
	str r10, [r8, #208]
	eor r10, r3, r3, ror #8
	eor r10, r10, r3, ror #16
	eor r10, r10, r5
	eor r10, r10, r5, ror #24
	ldr r11, [r8, #212]
	eor r10, r10, r11
	str r10, [r8, #212]
	eor r10, r4, r4, ror #8
	eor r10, r10, r4, ror #16
	eor r10, r10, r6
	eor r10, r10, r6, ror #24
	ldr r11, [r8, #216]
	eor r10, r10, r11
	str r10, [r8, #216]
	eor r10, r5, r5, ror #8
	eor r10, r10, r5, ror #16
	eor r10, r10, r7
	eor r10, r10, r7, ror #24
	ldr r11, [r8, #220]
	eor r10, r10, r11
	str r10, [r8, #220]
	ldr r0, [r8, #128]
	ldr r10, [r8, #160]
	eor r0, r0, r10
	ldr r10, [r8, #192]
	eor r0, r0, r10
	ldr r10, [r9, #96]
	eor r0, r0, r10
	ldr r1, [r8, #132]
	ldr r10, [r8, #164]
	eor r1, r1, r10
	ldr r10, [r8, #196]
	eor r1, r1, r10
	ldr r10, [r9, #100]
	eor r1, r1, r10
	ldr r2, [r8, #136]
	ldr r10, [r8, #168]
	eor r2, r2, r10
	ldr r10, [r8, #200]
	eor r2, r2, r10
	ldr r10, [r9, #104]
	eor r2, r2, r10
	ldr r3, [r8, #140]
	ldr r10, [r8, #172]
	eor r3, r3, r10
	ldr r10, [r8, #204]
	eor r3, r3, r10
	ldr r10, [r9, #108]
	eor r3, r3, r10
	ldr r4, [r8, #144]
	ldr r10, [r8, #176]
	eor r4, r4, r10
	ldr r10, [r8, #208]
	eor r4, r4, r10
	ldr r10, [r9, #112]
	eor r4, r4, r10
	ldr r5, [r8, #148]
	ldr r10, [r8, #180]
	eor r5, r5, r10
	ldr r10, [r8, #212]
	eor r5, r5, r10
	ldr r10, [r9, #116]
	eor r5, r5, r10
	ldr r6, [r8, #152]
	ldr r10, [r8, #184]
	eor r6, r6, r10
	ldr r10, [r8, #216]
	eor r6, r6, r10
	ldr r10, [r9, #120]
	eor r6, r6, r10
	ldr r7, [r8, #156]
	ldr r10, [r8, #188]
	eor r7, r7, r10
	ldr r10, [r8, #220]
	eor r7, r7, r10
	ldr r10, [r9, #124]
	eor r7, r7, r10
	mov r10, #0
	sub r10, r10, #1
	str r10, [r8, #0]
	eor r10, r3, r0
	eor r11, r1, r10
	eor r12, r4, r2
	eor r4, r7, r4
	eor lr, r7, r3
	str r0, [r8, #4]
	ldr r0, [r8, #0]
	eor lr, lr, r0
	str r1, [r8, #8]
	eor r1, r11, r4
	eor r4, r6, r4
	str r4, [r8, #12]
	eor r4, r7, r2
	str r4, [r8, #16]
	eor r4, r7, r12
	eor r4, r4, r0
	eor r7, r7, r11
	str r7, [r8, #20]
	eor r7, r5, r12
	eor r2, r6, r2
	eor r3, r3, r7
	str r3, [r8, #24]
	eor r3, r5, r11
	eor r3, r3, r0
	eor r11, r12, r11
	eor r11, r11, r0
	eor r12, r12, r3
	str r12, [r8, #28]
	eor r12, r5, r4
	str r3, [r8, #32]
	and r3, r1, r11
	str r1, [r8, #36]
	eor r1, r6, r12
	str r11, [r8, #40]
	eor r11, r10, r4
	eor r5, r5, lr
	eor r10, r10, r7
	and r7, r2, r5
	str r5, [r8, #44]
	ldr r5, [r8, #8]
	str r3, [r8, #48]
	eor r3, r5, r1
	eor r12, r5, r12
	eor r12, r12, r0
	orr r0, r3, r12
	str r3, [r8, #52]
	ldr r3, [r8, #32]
	str r12, [r8, #56]
	eor r12, r3, r2
	str r7, [r8, #60]
	eor r7, r5, r2
	eor r6, r6, r11
	orr r11, r12, r4
	str r12, [r8, #64]
	and r12, r5, r10
	str r10, [r8, #68]
	ldr r10, [r8, #24]
	str r2, [r8, #72]
	orr r2, r3, r10
	eor lr, r5, lr
	ldr r10, [r8, #12]
	eor r5, r3, r10
	ldr r3, [r8, #20]
	str r5, [r8, #76]
	orr r5, r1, r3
	orr r3, r6, lr
	eor r3, r3, r0
	eor r2, r2, r0
	ldr r0, [r8, #60]
	eor r0, r0, r12
	str r1, [r8, #60]
	ldr r1, [r8, #4]
	eor r10, r1, r10
	eor r1, r1, r4
	str r4, [r8, #4]
	ldr r4, [r8, #48]
	eor r5, r5, r4
	eor r0, r0, r5
	eor r11, r11, r4
	ldr r4, [r8, #28]
	eor r0, r0, r4
	and r4, r7, r1
	eor r2, r2, r5
	eor r3, r3, r11
	ldr r5, [r8, #76]
	eor r3, r3, r5
	ldr r5, [r8, #16]
	eor r2, r2, r5
	eor r4, r4, r12
	ldr r12, [r8, #8]
	eor r10, r12, r10
	eor r4, r4, r11
	and r11, r2, r0
	eor r4, r4, r10
	eor r2, r2, r3
	eor r10, r0, r4
	eor r5, r3, r11
	eor r11, r4, r11
	and r5, r5, r10
	eor r5, r5, r4
	and r10, r2, r11
	eor r12, r11, r5
	and r4, r4, r12
	eor r10, r10, r3
	eor r0, r0, r5
	eor r11, r11, r4
	ldr r3, [r8, #0]
	eor r6, r6, r3
	and r6, r5, r6
	and r11, r10, r11
	eor r2, r2, r11
	eor r11, r5, r3
	orr r11, r11, lr
	eor r4, r4, r0
	eor r4, r4, r3
	eor r0, r10, r5
	eor r5, r5, r4
	eor lr, r10, r2
	ldr r12, [r8, #56]
	orr r12, r5, r12
	and r1, r10, r1
	str r11, [r8, #56]
	ldr r11, [r8, #52]
	orr r5, r5, r11
	ldr r11, [r8, #32]
	orr r11, r4, r11
	str r6, [r8, #32]
	ldr r6, [r8, #24]
	orr r6, r4, r6
	ldr r3, [r8, #40]
	and r3, r0, r3
	and r10, r10, r7
	eor r7, r12, r6
	eor r3, r3, r11
	str r7, [r8, #40]
	ldr r7, [r8, #72]
	and r7, r2, r7
	eor r4, r2, r4
	str r11, [r8, #72]
	eor r11, r7, r3
	str r3, [r8, #24]
	ldr r3, [r8, #64]
	orr r3, r4, r3
	eor r10, r10, r11
	eor r12, r12, r1
	ldr r1, [r8, #44]
	and r2, r2, r1
	ldr r1, [r8, #4]
	orr r1, r4, r1
	ldr r11, [r8, #36]
	and r11, r0, r11
	eor r0, r0, r4
	ldr r4, [r8, #8]
	and r4, lr, r4
	eor r4, r4, r11
	eor r5, r5, r11
	eor r6, r6, r1
	eor r1, r2, r12
	ldr r11, [r8, #0]
	eor r1, r1, r11
	eor r3, r3, r5
	ldr r11, [r8, #60]
	orr r11, r0, r11
	str r2, [r8, #60]
	ldr r2, [r8, #20]
	orr r0, r0, r2
	eor r2, r11, r6
	eor r5, r5, r2
	eor r7, r7, r11
	ldr r11, [r8, #68]
	and lr, lr, r11
	ldr r11, [r8, #32]
	eor r2, r11, r1
	eor r12, lr, r12
	eor r11, r0, r10
	eor r6, r6, r2
	eor r7, r7, r4
	eor r12, r5, r12
	ldr r4, [r8, #24]
	eor r4, r4, r1
	eor r4, r5, r4
	eor r1, r10, r6
	ldr r6, [r8, #56]
	eor r6, r6, r11
	ldr r10, [r8, #72]
	eor r10, r10, r12
	eor r11, r11, r3
	eor r6, r2, r6
	ldr r2, [r8, #40]
	eor r5, r11, r2
	eor lr, lr, r11
	ldr r11, [r8, #32]
	eor r3, r11, r3
	ldr r11, [r8, #60]
	eor r2, r11, lr
	eor r0, r0, r10
	ror r12, r6, #8
	eor r10, r12, r12, ror #8
	eor r10, r10, r12, ror #16
	eor r10, r10, r0
	eor r10, r10, r0, ror #24
	ldr r11, [r8, #224]
	eor r10, r10, r11
	str r10, [r8, #224]
	ror r12, r7, #8
	eor r10, r12, r12, ror #8
	eor r10, r10, r12, ror #16
	eor r10, r10, r1
	eor r10, r10, r1, ror #24
	ldr r11, [r8, #228]
	eor r10, r10, r11
	str r10, [r8, #228]
	eor r10, r0, r0, ror #8
	eor r10, r10, r0, ror #16
	eor r10, r10, r2
	eor r10, r10, r2, ror #24
	ldr r11, [r8, #232]
	eor r10, r10, r11
	str r10, [r8, #232]
	eor r10, r1, r1, ror #8
	eor r10, r10, r1, ror #16
	eor r10, r10, r3
	eor r10, r10, r3, ror #24
	ldr r11, [r8, #236]
	eor r10, r10, r11
	str r10, [r8, #236]
	eor r10, r2, r2, ror #8
	eor r10, r10, r2, ror #16
	eor r10, r10, r4
	eor r10, r10, r4, ror #24
	ldr r11, [r8, #240]
	eor r10, r10, r11
	str r10, [r8, #240]
	eor r10, r3, r3, ror #8
	eor r10, r10, r3, ror #16
	eor r10, r10, r5
	eor r10, r10, r5, ror #24
	ldr r11, [r8, #244]
	eor r10, r10, r11
	str r10, [r8, #244]
	eor r10, r4, r4, ror #8
	eor r10, r10, r4, ror #16
	eor r10, r10, r6
	eor r10, r10, r6, ror #24
	ldr r11, [r8, #248]
	eor r10, r10, r11
	str r10, [r8, #248]
	eor r10, r5, r5, ror #8
	eor r10, r10, r5, ror #16
	eor r10, r10, r7
	eor r10, r10, r7, ror #24
	ldr r11, [r8, #252]
	eor r10, r10, r11
	str r10, [r8, #252]
	add r9, r9, #128
	sub r10, r9, r8
	cmp r10, #1408
	bne 210b
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
	str r0, [r8, #256]
	str r1, [r8, #272]
	str r2, [r8, #288]
	str r3, [r8, #304]
	str r4, [r8, #320]
	str r5, [r8, #336]
	str r6, [r8, #352]
	str r7, [r8, #368]
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
	str r0, [r8, #260]
	str r1, [r8, #276]
	str r2, [r8, #292]
	str r3, [r8, #308]
	str r4, [r8, #324]
	str r5, [r8, #340]
	str r6, [r8, #356]
	str r7, [r8, #372]
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
	str r0, [r8, #264]
	str r1, [r8, #280]
	str r2, [r8, #296]
	str r3, [r8, #312]
	str r4, [r8, #328]
	str r5, [r8, #344]
	str r6, [r8, #360]
	str r7, [r8, #376]
	ldr r0, [r8, #128]
	ldr r1, [r8, #132]
	ldr r2, [r8, #136]
	ldr r3, [r8, #140]
	ldr r4, [r8, #144]
	ldr r5, [r8, #148]
	ldr r6, [r8, #152]
	ldr r7, [r8, #156]
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
	str r0, [r8, #268]
	str r1, [r8, #284]
	str r2, [r8, #300]
	str r3, [r8, #316]
	str r4, [r8, #332]
	str r5, [r8, #348]
	str r6, [r8, #364]
	str r7, [r8, #380]
	ldr r1, [r8, #1444]
	ldr r2, [r8, #1448]
	lsr r10, r2, #3
	cmp r10, #0
	bne 211f
	mov r3, r2
	b 212f
211:
	mov r3, #8
212:
	add r0, r8, #256
	mov r12, r1
213:
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
	bne 213b
	lsr r10, r2, #3
	cmp r10, #0
	bne 214f
	mov r3, r2
	b 215f
214:
	mov r3, #8
215:
	add r1, r1, #128
	subs r2, r2, r3
	bne 26b
	b 25f
24:
25:
	mov r12, r8
	ldr r4, [r12, #1408]
	ldr r5, [r12, #1412]
	ldr r6, [r12, #1416]
	ldr r7, [r12, #1420]
	ldr r8, [r12, #1424]
	ldr r9, [r12, #1428]
	ldr r10, [r12, #1432]
	ldr r11, [r12, #1436]
	ldr lr, [r12, #1440]
	add r12, sp, #8
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
	str r2, [r12, #64]
	str r2, [r12, #68]
	str r2, [r12, #72]
	str r2, [r12, #76]
	str r2, [r12, #80]
	str r2, [r12, #84]
	str r2, [r12, #88]
	str r2, [r12, #92]
	str r2, [r12, #96]
	str r2, [r12, #100]
	str r2, [r12, #104]
	str r2, [r12, #108]
	str r2, [r12, #112]
	str r2, [r12, #116]
	str r2, [r12, #120]
	str r2, [r12, #124]
	str r2, [r12, #128]
	str r2, [r12, #132]
	str r2, [r12, #136]
	str r2, [r12, #140]
	str r2, [r12, #144]
	str r2, [r12, #148]
	str r2, [r12, #152]
	str r2, [r12, #156]
	str r2, [r12, #160]
	str r2, [r12, #164]
	str r2, [r12, #168]
	str r2, [r12, #172]
	str r2, [r12, #176]
	str r2, [r12, #180]
	str r2, [r12, #184]
	str r2, [r12, #188]
	str r2, [r12, #192]
	str r2, [r12, #196]
	str r2, [r12, #200]
	str r2, [r12, #204]
	str r2, [r12, #208]
	str r2, [r12, #212]
	str r2, [r12, #216]
	str r2, [r12, #220]
	str r2, [r12, #224]
	str r2, [r12, #228]
	str r2, [r12, #232]
	str r2, [r12, #236]
	str r2, [r12, #240]
	str r2, [r12, #244]
	str r2, [r12, #248]
	str r2, [r12, #252]
	str r2, [r12, #256]
	str r2, [r12, #260]
	str r2, [r12, #264]
	str r2, [r12, #268]
	str r2, [r12, #272]
	str r2, [r12, #276]
	str r2, [r12, #280]
	str r2, [r12, #284]
	str r2, [r12, #288]
	str r2, [r12, #292]
	str r2, [r12, #296]
	str r2, [r12, #300]
	str r2, [r12, #304]
	str r2, [r12, #308]
	str r2, [r12, #312]
	str r2, [r12, #316]
	str r2, [r12, #320]
	str r2, [r12, #324]
	str r2, [r12, #328]
	str r2, [r12, #332]
	str r2, [r12, #336]
	str r2, [r12, #340]
	str r2, [r12, #344]
	str r2, [r12, #348]
	str r2, [r12, #352]
	str r2, [r12, #356]
	str r2, [r12, #360]
	str r2, [r12, #364]
	str r2, [r12, #368]
	str r2, [r12, #372]
	str r2, [r12, #376]
	str r2, [r12, #380]
	str r2, [r12, #384]
	str r2, [r12, #388]
	str r2, [r12, #392]
	str r2, [r12, #396]
	str r2, [r12, #400]
	str r2, [r12, #404]
	str r2, [r12, #408]
	str r2, [r12, #412]
	str r2, [r12, #416]
	str r2, [r12, #420]
	str r2, [r12, #424]
	str r2, [r12, #428]
	str r2, [r12, #432]
	str r2, [r12, #436]
	str r2, [r12, #440]
	str r2, [r12, #444]
	str r2, [r12, #448]
	str r2, [r12, #452]
	str r2, [r12, #456]
	str r2, [r12, #460]
	str r2, [r12, #464]
	str r2, [r12, #468]
	str r2, [r12, #472]
	str r2, [r12, #476]
	str r2, [r12, #480]
	str r2, [r12, #484]
	str r2, [r12, #488]
	str r2, [r12, #492]
	str r2, [r12, #496]
	str r2, [r12, #500]
	str r2, [r12, #504]
	str r2, [r12, #508]
	str r2, [r12, #512]
	str r2, [r12, #516]
	str r2, [r12, #520]
	str r2, [r12, #524]
	str r2, [r12, #528]
	str r2, [r12, #532]
	str r2, [r12, #536]
	str r2, [r12, #540]
	str r2, [r12, #544]
	str r2, [r12, #548]
	str r2, [r12, #552]
	str r2, [r12, #556]
	str r2, [r12, #560]
	str r2, [r12, #564]
	str r2, [r12, #568]
	str r2, [r12, #572]
	str r2, [r12, #576]
	str r2, [r12, #580]
	str r2, [r12, #584]
	str r2, [r12, #588]
	str r2, [r12, #592]
	str r2, [r12, #596]
	str r2, [r12, #600]
	str r2, [r12, #604]
	str r2, [r12, #608]
	str r2, [r12, #612]
	str r2, [r12, #616]
	str r2, [r12, #620]
	str r2, [r12, #624]
	str r2, [r12, #628]
	str r2, [r12, #632]
	str r2, [r12, #636]
	str r2, [r12, #640]
	str r2, [r12, #644]
	str r2, [r12, #648]
	str r2, [r12, #652]
	str r2, [r12, #656]
	str r2, [r12, #660]
	str r2, [r12, #664]
	str r2, [r12, #668]
	str r2, [r12, #672]
	str r2, [r12, #676]
	str r2, [r12, #680]
	str r2, [r12, #684]
	str r2, [r12, #688]
	str r2, [r12, #692]
	str r2, [r12, #696]
	str r2, [r12, #700]
	str r2, [r12, #704]
	str r2, [r12, #708]
	str r2, [r12, #712]
	str r2, [r12, #716]
	str r2, [r12, #720]
	str r2, [r12, #724]
	str r2, [r12, #728]
	str r2, [r12, #732]
	str r2, [r12, #736]
	str r2, [r12, #740]
	str r2, [r12, #744]
	str r2, [r12, #748]
	str r2, [r12, #752]
	str r2, [r12, #756]
	str r2, [r12, #760]
	str r2, [r12, #764]
	str r2, [r12, #768]
	str r2, [r12, #772]
	str r2, [r12, #776]
	str r2, [r12, #780]
	str r2, [r12, #784]
	str r2, [r12, #788]
	str r2, [r12, #792]
	str r2, [r12, #796]
	str r2, [r12, #800]
	str r2, [r12, #804]
	str r2, [r12, #808]
	str r2, [r12, #812]
	str r2, [r12, #816]
	str r2, [r12, #820]
	str r2, [r12, #824]
	str r2, [r12, #828]
	str r2, [r12, #832]
	str r2, [r12, #836]
	str r2, [r12, #840]
	str r2, [r12, #844]
	str r2, [r12, #848]
	str r2, [r12, #852]
	str r2, [r12, #856]
	str r2, [r12, #860]
	str r2, [r12, #864]
	str r2, [r12, #868]
	str r2, [r12, #872]
	str r2, [r12, #876]
	str r2, [r12, #880]
	str r2, [r12, #884]
	str r2, [r12, #888]
	str r2, [r12, #892]
	str r2, [r12, #896]
	str r2, [r12, #900]
	str r2, [r12, #904]
	str r2, [r12, #908]
	str r2, [r12, #912]
	str r2, [r12, #916]
	str r2, [r12, #920]
	str r2, [r12, #924]
	str r2, [r12, #928]
	str r2, [r12, #932]
	str r2, [r12, #936]
	str r2, [r12, #940]
	str r2, [r12, #944]
	str r2, [r12, #948]
	str r2, [r12, #952]
	str r2, [r12, #956]
	str r2, [r12, #960]
	str r2, [r12, #964]
	str r2, [r12, #968]
	str r2, [r12, #972]
	str r2, [r12, #976]
	str r2, [r12, #980]
	str r2, [r12, #984]
	str r2, [r12, #988]
	str r2, [r12, #992]
	str r2, [r12, #996]
	str r2, [r12, #1000]
	str r2, [r12, #1004]
	str r2, [r12, #1008]
	str r2, [r12, #1012]
	str r2, [r12, #1016]
	str r2, [r12, #1020]
	str r2, [r12, #1024]
	str r2, [r12, #1028]
	str r2, [r12, #1032]
	str r2, [r12, #1036]
	str r2, [r12, #1040]
	str r2, [r12, #1044]
	str r2, [r12, #1048]
	str r2, [r12, #1052]
	str r2, [r12, #1056]
	str r2, [r12, #1060]
	str r2, [r12, #1064]
	str r2, [r12, #1068]
	str r2, [r12, #1072]
	str r2, [r12, #1076]
	str r2, [r12, #1080]
	str r2, [r12, #1084]
	str r2, [r12, #1088]
	str r2, [r12, #1092]
	str r2, [r12, #1096]
	str r2, [r12, #1100]
	str r2, [r12, #1104]
	str r2, [r12, #1108]
	str r2, [r12, #1112]
	str r2, [r12, #1116]
	str r2, [r12, #1120]
	str r2, [r12, #1124]
	str r2, [r12, #1128]
	str r2, [r12, #1132]
	str r2, [r12, #1136]
	str r2, [r12, #1140]
	str r2, [r12, #1144]
	str r2, [r12, #1148]
	str r2, [r12, #1152]
	str r2, [r12, #1156]
	str r2, [r12, #1160]
	str r2, [r12, #1164]
	str r2, [r12, #1168]
	str r2, [r12, #1172]
	str r2, [r12, #1176]
	str r2, [r12, #1180]
	str r2, [r12, #1184]
	str r2, [r12, #1188]
	str r2, [r12, #1192]
	str r2, [r12, #1196]
	str r2, [r12, #1200]
	str r2, [r12, #1204]
	str r2, [r12, #1208]
	str r2, [r12, #1212]
	str r2, [r12, #1216]
	str r2, [r12, #1220]
	str r2, [r12, #1224]
	str r2, [r12, #1228]
	str r2, [r12, #1232]
	str r2, [r12, #1236]
	str r2, [r12, #1240]
	str r2, [r12, #1244]
	str r2, [r12, #1248]
	str r2, [r12, #1252]
	str r2, [r12, #1256]
	str r2, [r12, #1260]
	str r2, [r12, #1264]
	str r2, [r12, #1268]
	str r2, [r12, #1272]
	str r2, [r12, #1276]
	str r2, [r12, #1280]
	str r2, [r12, #1284]
	str r2, [r12, #1288]
	str r2, [r12, #1292]
	str r2, [r12, #1296]
	str r2, [r12, #1300]
	str r2, [r12, #1304]
	str r2, [r12, #1308]
	str r2, [r12, #1312]
	str r2, [r12, #1316]
	str r2, [r12, #1320]
	str r2, [r12, #1324]
	str r2, [r12, #1328]
	str r2, [r12, #1332]
	str r2, [r12, #1336]
	str r2, [r12, #1340]
	str r2, [r12, #1344]
	str r2, [r12, #1348]
	str r2, [r12, #1352]
	str r2, [r12, #1356]
	str r2, [r12, #1360]
	str r2, [r12, #1364]
	str r2, [r12, #1368]
	str r2, [r12, #1372]
	str r2, [r12, #1376]
	str r2, [r12, #1380]
	str r2, [r12, #1384]
	str r2, [r12, #1388]
	str r2, [r12, #1392]
	str r2, [r12, #1396]
	str r2, [r12, #1400]
	str r2, [r12, #1404]
	str r2, [r12, #1408]
	str r2, [r12, #1412]
	str r2, [r12, #1416]
	str r2, [r12, #1420]
	str r2, [r12, #1424]
	str r2, [r12, #1428]
	str r2, [r12, #1432]
	str r2, [r12, #1436]
	str r2, [r12, #1440]
	str r2, [r12, #1444]
	str r2, [r12, #1448]
	str r2, [r12, #1452]
	add sp, sp, #1472
	bx lr
