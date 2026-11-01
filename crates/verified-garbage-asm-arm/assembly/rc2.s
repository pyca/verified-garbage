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
