// The functions of `src/rc2.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_init:
	sub sp, sp, #592
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #592]
	str lr, [r12, #0]
	ldr lr, [sp, #596]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	sub r12, r1, #1
	lsr r12, r12, #7
	cmp r12, #0
	bne 20f
	sub r12, r2, #1
	lsr r12, r12, #10
	cmp r12, #0
	bne 22f
	ldr r12, [sp, #0]
	cmp r12, #8
	bne 24f
	b 25f
24:
	mov r0, #3
25:
	b 23f
22:
	mov r0, #2
23:
	b 21f
20:
	mov r0, #1
21:
	bne 26f
	ldr r12, [sp, #8]
	str lr, [r12, #512]
	ldr lr, [r3, #0]
	ldr r3, [r3, #4]
	ldr r12, [sp, #4]
	str lr, [r12, #128]
	str r3, [r12, #132]
	mov r3, r12
	ldr r12, [sp, #8]
	push {r12, lr}
	bl {vg_rc2_expand_key}
	ldr r12, [sp], #8
	ldr r12, [sp, #8]
	ldr lr, [r12, #512]
	mov r0, #0
	b 27f
26:
27:
	add r12, sp, #16
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
	add sp, sp, #592
	bx lr

vg_rc2_cbc_encrypt_update:
	sub sp, sp, #592
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #592]
	str lr, [r12, #0]
	ldr lr, [sp, #596]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	ldr r12, [sp, #4]
	cmp r12, #0
	beq 20f
	ldr r12, [sp, #8]
	str lr, [r12, #512]
	ldr lr, [sp, #0]
	cmp r1, #0
	beq 22f
24:
	ldrb r12, [r0, #136]
	strb r12, [lr, #0]
	add r0, r0, #1
	add lr, lr, #1
	subs r1, r1, #1
	bne 24b
	b 23f
22:
23:
	ldr r12, [sp, #0]
	sub r12, lr, r12
	sub r0, r0, r12
	ldr r1, [sp, #4]
	sub r1, r1, r12
	sub r3, r3, r1
	cmp r1, #0
	beq 25f
27:
	ldrb r12, [r2, #0]
	strb r12, [lr, #0]
	add r2, r2, #1
	add lr, lr, #1
	subs r1, r1, #1
	bne 27b
	b 26f
25:
26:
	mov lr, r0
	cmp r3, #0
	beq 28f
210:
	ldrb r12, [r2, #0]
	strb r12, [lr, #136]
	add r2, r2, #1
	add lr, lr, #1
	subs r3, r3, #1
	bne 210b
	b 29f
28:
29:
	add r1, r0, #128
	ldr r2, [sp, #0]
	ldr r3, [sp, #4]
	lsr r3, r3, #3
	ldr r12, [sp, #8]
	push {r12, lr}
	bl {vg_rc2_cbc_encrypt}
	ldr r12, [sp], #8
	ldr r12, [sp, #8]
	ldr lr, [r12, #512]
	b 21f
20:
	add r1, r0, r1
	cmp r3, #0
	beq 211f
213:
	ldrb r12, [r2, #0]
	strb r12, [r1, #136]
	add r2, r2, #1
	add r1, r1, #1
	subs r3, r3, #1
	bne 213b
	b 212f
211:
212:
21:
	add r12, sp, #16
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
	add sp, sp, #592
	bx lr

vg_rc2_cbc_decrypt_update:
	sub sp, sp, #592
	add r12, sp, #0
	str lr, [r12, #12]
	ldr lr, [sp, #592]
	str lr, [r12, #0]
	ldr lr, [sp, #596]
	str lr, [r12, #4]
	add lr, sp, #16
	str lr, [r12, #8]
	ldr lr, [sp, #12]
	ldr r12, [sp, #4]
	cmp r12, #0
	beq 20f
	ldr r12, [sp, #8]
	str lr, [r12, #512]
	ldr lr, [sp, #0]
	cmp r1, #0
	beq 22f
24:
	ldrb r12, [r0, #136]
	strb r12, [lr, #0]
	add r0, r0, #1
	add lr, lr, #1
	subs r1, r1, #1
	bne 24b
	b 23f
22:
23:
	ldr r12, [sp, #0]
	sub r12, lr, r12
	sub r0, r0, r12
	ldr r1, [sp, #4]
	sub r1, r1, r12
	sub r3, r3, r1
	cmp r1, #0
	beq 25f
27:
	ldrb r12, [r2, #0]
	strb r12, [lr, #0]
	add r2, r2, #1
	add lr, lr, #1
	subs r1, r1, #1
	bne 27b
	b 26f
25:
26:
	mov lr, r0
	cmp r3, #0
	beq 28f
210:
	ldrb r12, [r2, #0]
	strb r12, [lr, #136]
	add r2, r2, #1
	add lr, lr, #1
	subs r3, r3, #1
	bne 210b
	b 29f
28:
29:
	add r1, r0, #128
	ldr r2, [sp, #0]
	ldr r3, [sp, #4]
	lsr r3, r3, #3
	ldr r12, [sp, #8]
	push {r12, lr}
	bl {vg_rc2_cbc_decrypt}
	ldr r12, [sp], #8
	ldr r12, [sp, #8]
	ldr lr, [r12, #512]
	b 21f
20:
	add r1, r0, r1
	cmp r3, #0
	beq 211f
213:
	ldrb r12, [r2, #0]
	strb r12, [r1, #136]
	add r2, r2, #1
	add r1, r1, #1
	subs r3, r3, #1
	bne 213b
	b 212f
211:
212:
21:
	add r12, sp, #16
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
	add sp, sp, #592
	bx lr

vg_rc2_cbc_encrypt:
	ldr r12, [sp, #0]
	str r4, [r12, #264]
	str r5, [r12, #268]
	str r6, [r12, #272]
	str r7, [r12, #276]
	str lr, [r12, #280]
	mov r4, r1
	mov r5, r3
	mov r1, r2
	mov r2, r12
	cmp r5, #0
	beq 20f
22:
	ldr r12, [r1, #0]
	ldr r3, [r1, #4]
	ldr r6, [r4, #0]
	ldr r7, [r4, #4]
	eor r12, r12, r6
	eor r3, r3, r7
	str r12, [r1, #0]
	str r3, [r1, #4]
	bl {vg_rc2_encrypt_block}
	ldr r12, [r1, #0]
	ldr r3, [r1, #4]
	str r12, [r4, #0]
	str r3, [r4, #4]
	add r1, r1, #8
	sub r5, r5, #1
	cmp r5, #0
	bne 22b
	b 21f
20:
21:
	ldr r4, [r2, #264]
	ldr r5, [r2, #268]
	ldr r6, [r2, #272]
	ldr r7, [r2, #276]
	ldr lr, [r2, #280]
	bx lr

vg_rc2_cbc_decrypt:
	ldr r12, [sp, #0]
	str r4, [r12, #264]
	str r5, [r12, #268]
	str r6, [r12, #272]
	str r7, [r12, #276]
	str lr, [r12, #280]
	mov r4, r1
	mov r5, r3
	mov r1, r2
	mov r2, r12
	cmp r5, #0
	beq 20f
22:
	ldr r12, [r1, #0]
	ldr r3, [r1, #4]
	str r12, [r2, #256]
	str r3, [r2, #260]
	bl {vg_rc2_decrypt_block}
	ldr r12, [r1, #0]
	ldr r3, [r1, #4]
	ldr r6, [r4, #0]
	ldr r7, [r4, #4]
	eor r12, r12, r6
	eor r3, r3, r7
	str r12, [r1, #0]
	str r3, [r1, #4]
	ldr r12, [r2, #256]
	ldr r3, [r2, #260]
	str r12, [r4, #0]
	str r3, [r4, #4]
	add r1, r1, #8
	sub r5, r5, #1
	cmp r5, #0
	bne 22b
	b 21f
20:
21:
	ldr r4, [r2, #264]
	ldr r5, [r2, #268]
	ldr r6, [r2, #272]
	ldr r7, [r2, #276]
	ldr lr, [r2, #280]
	bx lr

vg_rc2_expand_key:
	ldr r12, [sp, #0]
	str r8, [r12, #0]
	str r4, [r12, #4]
	str r5, [r12, #8]
	str r6, [r12, #12]
	str r7, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	mov r8, r12
	mov r4, r0
	mov r5, r1
	mov r6, r3
	mov r7, r2
	movw r0, #0
20:
	add lr, r4, r0
	ldrb r12, [lr, #0]
	add lr, r6, r0
	strb r12, [lr, #0]
	add r0, r0, #1
	cmp r0, r5
	bne 20b
	cmp r0, #128
	bne 21f
	b 22f
21:
23:
	add lr, r6, r0
	sub lr, lr, #1
	ldrb r12, [lr, #0]
	sub r9, r0, r5
	add lr, r6, r9
	ldrb r3, [lr, #0]
	add r12, r12, r3
	lsl r12, r12, #24
	lsr r12, r12, #24
	movw r3, #0
	movw lr, #:lower16:({VG_RC2_PITABLE}
	movt lr, #:upper16:({VG_RC2_PITABLE}
2:
	add lr, pc
3:
	mov r9, #0
24:
	ldr r10, [lr, #0]
	eor r11, r12, r9
	sub r11, r11, #4
	lsr r11, r11, #8
	orr r11, r11, r11, lsl #8
	and r10, r10, r11
	orr r3, r3, r10
	add lr, lr, #4
	cmp r9, #252
	add r9, r9, #4
	bne 24b
	and lr, r12, #3
	sub r10, lr, #1
	lsr r10, r10, #8
	and r12, r10, r3
	eor r10, lr, #1
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #8
	orr r12, r12, r10
	eor r10, lr, #2
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #16
	orr r12, r12, r10
	eor r10, lr, #3
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #24
	orr r12, r12, r10
	and r12, r12, #255
	add lr, r6, r0
	strb r12, [lr, #0]
	add r0, r0, #1
	cmp r0, #128
	bne 23b
22:
	add r1, r7, #7
	lsr r1, r1, #3
	movw r0, #128
	sub r0, r0, r1
	mov r9, r7
	lsl r9, r9, #29
	lsr r9, r9, #29
	movw r2, #255
	cmp r9, #1
	beq 25f
	b 26f
25:
	movw r2, #1
26:
	cmp r9, #2
	beq 27f
	b 28f
27:
	movw r2, #3
28:
	cmp r9, #3
	beq 29f
	b 210f
29:
	movw r2, #7
210:
	cmp r9, #4
	beq 211f
	b 212f
211:
	movw r2, #15
212:
	cmp r9, #5
	beq 213f
	b 214f
213:
	movw r2, #31
214:
	cmp r9, #6
	beq 215f
	b 216f
215:
	movw r2, #63
216:
	cmp r9, #7
	beq 217f
	b 218f
217:
	movw r2, #127
218:
	add lr, r6, r0
	ldrb r12, [lr, #0]
	and r12, r12, r2
	lsl r12, r12, #24
	lsr r12, r12, #24
	movw r3, #0
	movw lr, #:lower16:({VG_RC2_PITABLE}
	movt lr, #:upper16:({VG_RC2_PITABLE}
2:
	add lr, pc
3:
	mov r9, #0
219:
	ldr r10, [lr, #0]
	eor r11, r12, r9
	sub r11, r11, #4
	lsr r11, r11, #8
	orr r11, r11, r11, lsl #8
	and r10, r10, r11
	orr r3, r3, r10
	add lr, lr, #4
	cmp r9, #252
	add r9, r9, #4
	bne 219b
	and lr, r12, #3
	sub r10, lr, #1
	lsr r10, r10, #8
	and r12, r10, r3
	eor r10, lr, #1
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #8
	orr r12, r12, r10
	eor r10, lr, #2
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #16
	orr r12, r12, r10
	eor r10, lr, #3
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #24
	orr r12, r12, r10
	and r12, r12, #255
	add lr, r6, r0
	strb r12, [lr, #0]
	cmp r0, #0
	bne 220f
	b 221f
220:
222:
	sub r0, r0, #1
	add lr, r6, r0
	add lr, lr, #1
	ldrb r12, [lr, #0]
	add r9, r0, r1
	add lr, r6, r9
	ldrb r3, [lr, #0]
	eor r12, r12, r3
	lsl r12, r12, #24
	lsr r12, r12, #24
	movw r3, #0
	movw lr, #:lower16:({VG_RC2_PITABLE}
	movt lr, #:upper16:({VG_RC2_PITABLE}
2:
	add lr, pc
3:
	mov r9, #0
223:
	ldr r10, [lr, #0]
	eor r11, r12, r9
	sub r11, r11, #4
	lsr r11, r11, #8
	orr r11, r11, r11, lsl #8
	and r10, r10, r11
	orr r3, r3, r10
	add lr, lr, #4
	cmp r9, #252
	add r9, r9, #4
	bne 223b
	and lr, r12, #3
	sub r10, lr, #1
	lsr r10, r10, #8
	and r12, r10, r3
	eor r10, lr, #1
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #8
	orr r12, r12, r10
	eor r10, lr, #2
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #16
	orr r12, r12, r10
	eor r10, lr, #3
	sub r10, r10, #1
	lsr r10, r10, #8
	and r10, r10, r3, lsr #24
	orr r12, r12, r10
	and r12, r12, #255
	add lr, r6, r0
	strb r12, [lr, #0]
	cmp r0, #0
	bne 222b
221:
	mov r12, r8
	ldr r8, [r12, #0]
	ldr r4, [r12, #4]
	ldr r5, [r12, #8]
	ldr r6, [r12, #12]
	ldr r7, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	bx lr

vg_rc2_encrypt_block:
	str r4, [r2, #0]
	str r5, [r2, #4]
	str r6, [r2, #8]
	str r7, [r2, #12]
	str r8, [r2, #16]
	str r9, [r2, #20]
	str r10, [r2, #24]
	str r11, [r2, #28]
	str lr, [r2, #32]
	ldrb r4, [r1, #0]
	ldrb r12, [r1, #1]
	orr r4, r4, r12, lsl #8
	ldrb r5, [r1, #2]
	ldrb r12, [r1, #3]
	orr r5, r5, r12, lsl #8
	ldrb r6, [r1, #4]
	ldrb r12, [r1, #5]
	orr r6, r6, r12, lsl #8
	ldrb r7, [r1, #6]
	ldrb r12, [r1, #7]
	orr r7, r7, r12, lsl #8
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #0]
	ldrb r9, [r0, #1]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #2]
	ldrb r9, [r0, #3]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #4]
	ldrb r9, [r0, #5]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #6]
	ldrb r9, [r0, #7]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #8]
	ldrb r9, [r0, #9]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #10]
	ldrb r9, [r0, #11]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #12]
	ldrb r9, [r0, #13]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #14]
	ldrb r9, [r0, #15]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #16]
	ldrb r9, [r0, #17]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #18]
	ldrb r9, [r0, #19]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #20]
	ldrb r9, [r0, #21]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #22]
	ldrb r9, [r0, #23]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #24]
	ldrb r9, [r0, #25]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #26]
	ldrb r9, [r0, #27]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #28]
	ldrb r9, [r0, #29]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #30]
	ldrb r9, [r0, #31]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #32]
	ldrb r9, [r0, #33]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #34]
	ldrb r9, [r0, #35]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #36]
	ldrb r9, [r0, #37]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #38]
	ldrb r9, [r0, #39]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
20:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 20b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
21:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 21b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
22:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 22b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
23:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 23b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #40]
	ldrb r9, [r0, #41]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #42]
	ldrb r9, [r0, #43]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #44]
	ldrb r9, [r0, #45]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #46]
	ldrb r9, [r0, #47]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #48]
	ldrb r9, [r0, #49]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #50]
	ldrb r9, [r0, #51]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #52]
	ldrb r9, [r0, #53]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #54]
	ldrb r9, [r0, #55]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #56]
	ldrb r9, [r0, #57]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #58]
	ldrb r9, [r0, #59]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #60]
	ldrb r9, [r0, #61]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #62]
	ldrb r9, [r0, #63]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #64]
	ldrb r9, [r0, #65]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #66]
	ldrb r9, [r0, #67]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #68]
	ldrb r9, [r0, #69]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #70]
	ldrb r9, [r0, #71]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #72]
	ldrb r9, [r0, #73]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #74]
	ldrb r9, [r0, #75]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #76]
	ldrb r9, [r0, #77]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #78]
	ldrb r9, [r0, #79]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #80]
	ldrb r9, [r0, #81]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #82]
	ldrb r9, [r0, #83]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #84]
	ldrb r9, [r0, #85]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #86]
	ldrb r9, [r0, #87]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
24:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 24b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
25:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 25b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
26:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 26b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
27:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 27b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	add r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #88]
	ldrb r9, [r0, #89]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #90]
	ldrb r9, [r0, #91]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #92]
	ldrb r9, [r0, #93]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #94]
	ldrb r9, [r0, #95]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #96]
	ldrb r9, [r0, #97]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #98]
	ldrb r9, [r0, #99]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #100]
	ldrb r9, [r0, #101]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #102]
	ldrb r9, [r0, #103]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #104]
	ldrb r9, [r0, #105]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #106]
	ldrb r9, [r0, #107]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #108]
	ldrb r9, [r0, #109]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #110]
	ldrb r9, [r0, #111]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #112]
	ldrb r9, [r0, #113]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #114]
	ldrb r9, [r0, #115]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #116]
	ldrb r9, [r0, #117]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #118]
	ldrb r9, [r0, #119]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #120]
	ldrb r9, [r0, #121]
	ror r9, r9, #24
	orr r8, r8, r9
	add r4, r4, r8
	add r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r4
	lsr r12, r12, #15
	ror r4, r4, #31
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #122]
	ldrb r9, [r0, #123]
	ror r9, r9, #24
	orr r8, r8, r9
	add r5, r5, r8
	add r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r5
	lsr r12, r12, #14
	ror r5, r5, #30
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #124]
	ldrb r9, [r0, #125]
	ror r9, r9, #24
	orr r8, r8, r9
	add r6, r6, r8
	add r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r6
	lsr r12, r12, #13
	ror r6, r6, #29
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #126]
	ldrb r9, [r0, #127]
	ror r9, r9, #24
	orr r8, r8, r9
	add r7, r7, r8
	add r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r7
	lsr r12, r12, #11
	ror r7, r7, #27
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	strb r4, [r1, #0]
	lsr r12, r4, #8
	strb r12, [r1, #1]
	strb r5, [r1, #2]
	lsr r12, r5, #8
	strb r12, [r1, #3]
	strb r6, [r1, #4]
	lsr r12, r6, #8
	strb r12, [r1, #5]
	strb r7, [r1, #6]
	lsr r12, r7, #8
	strb r12, [r1, #7]
	ldr r4, [r2, #0]
	ldr r5, [r2, #4]
	ldr r6, [r2, #8]
	ldr r7, [r2, #12]
	ldr r8, [r2, #16]
	ldr r9, [r2, #20]
	ldr r10, [r2, #24]
	ldr r11, [r2, #28]
	ldr lr, [r2, #32]
	bx lr

vg_rc2_decrypt_block:
	str r4, [r2, #0]
	str r5, [r2, #4]
	str r6, [r2, #8]
	str r7, [r2, #12]
	str r8, [r2, #16]
	str r9, [r2, #20]
	str r10, [r2, #24]
	str r11, [r2, #28]
	str lr, [r2, #32]
	ldrb r4, [r1, #0]
	ldrb r12, [r1, #1]
	orr r4, r4, r12, lsl #8
	ldrb r5, [r1, #2]
	ldrb r12, [r1, #3]
	orr r5, r5, r12, lsl #8
	ldrb r6, [r1, #4]
	ldrb r12, [r1, #5]
	orr r6, r6, r12, lsl #8
	ldrb r7, [r1, #6]
	ldrb r12, [r1, #7]
	orr r7, r7, r12, lsl #8
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #126]
	ldrb r9, [r0, #127]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #124]
	ldrb r9, [r0, #125]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #122]
	ldrb r9, [r0, #123]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #120]
	ldrb r9, [r0, #121]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #118]
	ldrb r9, [r0, #119]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #116]
	ldrb r9, [r0, #117]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #114]
	ldrb r9, [r0, #115]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #112]
	ldrb r9, [r0, #113]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #110]
	ldrb r9, [r0, #111]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #108]
	ldrb r9, [r0, #109]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #106]
	ldrb r9, [r0, #107]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #104]
	ldrb r9, [r0, #105]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #102]
	ldrb r9, [r0, #103]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #100]
	ldrb r9, [r0, #101]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #98]
	ldrb r9, [r0, #99]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #96]
	ldrb r9, [r0, #97]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #94]
	ldrb r9, [r0, #95]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #92]
	ldrb r9, [r0, #93]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #90]
	ldrb r9, [r0, #91]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #88]
	ldrb r9, [r0, #89]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r6
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
20:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 20b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	sub r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r5
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
21:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 21b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	sub r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r4
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
22:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 22b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	sub r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r7
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
23:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 23b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	sub r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #86]
	ldrb r9, [r0, #87]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #84]
	ldrb r9, [r0, #85]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #82]
	ldrb r9, [r0, #83]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #80]
	ldrb r9, [r0, #81]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #78]
	ldrb r9, [r0, #79]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #76]
	ldrb r9, [r0, #77]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #74]
	ldrb r9, [r0, #75]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #72]
	ldrb r9, [r0, #73]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #70]
	ldrb r9, [r0, #71]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #68]
	ldrb r9, [r0, #69]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #66]
	ldrb r9, [r0, #67]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #64]
	ldrb r9, [r0, #65]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #62]
	ldrb r9, [r0, #63]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #60]
	ldrb r9, [r0, #61]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #58]
	ldrb r9, [r0, #59]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #56]
	ldrb r9, [r0, #57]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #54]
	ldrb r9, [r0, #55]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #52]
	ldrb r9, [r0, #53]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #50]
	ldrb r9, [r0, #51]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #48]
	ldrb r9, [r0, #49]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #46]
	ldrb r9, [r0, #47]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #44]
	ldrb r9, [r0, #45]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #42]
	ldrb r9, [r0, #43]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #40]
	ldrb r9, [r0, #41]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r6
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
24:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 24b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	sub r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r5
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
25:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 25b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	sub r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r4
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
26:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 26b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	sub r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r7
	and r12, r12, #63
	add r12, r12, #8
	movw r3, #0
	movw r11, #0
	movw r9, #64
	add lr, r0, #112
27:
	ldr r8, [lr, #0]
	eor r10, r12, r9
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #4]
	mul r8, r8, r10
	orr r11, r11, r8
	ldr r8, [lr, #8]
	eor r10, r12, r9
	eor r10, r10, #4
	sub r10, r10, #4
	lsr r10, r10, #31
	mul r8, r8, r10
	orr r3, r3, r8
	ldr r8, [lr, #12]
	mul r8, r8, r10
	orr r11, r11, r8
	sub lr, lr, #16
	subs r9, r9, #8
	bne 27b
	eor r11, r11, r3
	lsr r10, r12, #1
	and r10, r10, #1
	mul r11, r11, r10
	eor r3, r3, r11
	eor r11, r3, r3, lsr #16
	and r10, r12, #1
	mul r11, r11, r10
	eor r3, r3, r11
	lsl r12, r3, #16
	lsr r12, r12, #16
	sub r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #38]
	ldrb r9, [r0, #39]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #36]
	ldrb r9, [r0, #37]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #34]
	ldrb r9, [r0, #35]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #32]
	ldrb r9, [r0, #33]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #30]
	ldrb r9, [r0, #31]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #28]
	ldrb r9, [r0, #29]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #26]
	ldrb r9, [r0, #27]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #24]
	ldrb r9, [r0, #25]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #22]
	ldrb r9, [r0, #23]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #20]
	ldrb r9, [r0, #21]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #18]
	ldrb r9, [r0, #19]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #16]
	ldrb r9, [r0, #17]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #14]
	ldrb r9, [r0, #15]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #12]
	ldrb r9, [r0, #13]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #10]
	ldrb r9, [r0, #11]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #8]
	ldrb r9, [r0, #9]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	mov r12, r7
	lsr r12, r12, #5
	ror r7, r7, #21
	orr r7, r7, r12
	lsl r7, r7, #16
	lsr r7, r7, #16
	and r10, r6, r5
	movw r11, #0
	sub r11, r11, r6
	sub r11, r11, #1
	and r11, r11, r4
	add r10, r10, r11
	ldrb r8, [r0, #6]
	ldrb r9, [r0, #7]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r7, r7, r8
	sub r7, r7, r10
	lsl r7, r7, #16
	lsr r7, r7, #16
	mov r12, r6
	lsr r12, r12, #3
	ror r6, r6, #19
	orr r6, r6, r12
	lsl r6, r6, #16
	lsr r6, r6, #16
	and r10, r5, r4
	movw r11, #0
	sub r11, r11, r5
	sub r11, r11, #1
	and r11, r11, r7
	add r10, r10, r11
	ldrb r8, [r0, #4]
	ldrb r9, [r0, #5]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r6, r6, r8
	sub r6, r6, r10
	lsl r6, r6, #16
	lsr r6, r6, #16
	mov r12, r5
	lsr r12, r12, #2
	ror r5, r5, #18
	orr r5, r5, r12
	lsl r5, r5, #16
	lsr r5, r5, #16
	and r10, r4, r7
	movw r11, #0
	sub r11, r11, r4
	sub r11, r11, #1
	and r11, r11, r6
	add r10, r10, r11
	ldrb r8, [r0, #2]
	ldrb r9, [r0, #3]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r5, r5, r8
	sub r5, r5, r10
	lsl r5, r5, #16
	lsr r5, r5, #16
	mov r12, r4
	lsr r12, r12, #1
	ror r4, r4, #17
	orr r4, r4, r12
	lsl r4, r4, #16
	lsr r4, r4, #16
	and r10, r7, r6
	movw r11, #0
	sub r11, r11, r7
	sub r11, r11, #1
	and r11, r11, r5
	add r10, r10, r11
	ldrb r8, [r0, #0]
	ldrb r9, [r0, #1]
	ror r9, r9, #24
	orr r8, r8, r9
	sub r4, r4, r8
	sub r4, r4, r10
	lsl r4, r4, #16
	lsr r4, r4, #16
	strb r4, [r1, #0]
	lsr r12, r4, #8
	strb r12, [r1, #1]
	strb r5, [r1, #2]
	lsr r12, r5, #8
	strb r12, [r1, #3]
	strb r6, [r1, #4]
	lsr r12, r6, #8
	strb r12, [r1, #5]
	strb r7, [r1, #6]
	lsr r12, r7, #8
	strb r12, [r1, #7]
	ldr r4, [r2, #0]
	ldr r5, [r2, #4]
	ldr r6, [r2, #8]
	ldr r7, [r2, #12]
	ldr r8, [r2, #16]
	ldr r9, [r2, #20]
	ldr r10, [r2, #24]
	ldr r11, [r2, #28]
	ldr lr, [r2, #32]
	bx lr
