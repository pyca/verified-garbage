// The functions of `src/internal/vg_seed_ecb_decrypt_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_ecb_decrypt_core:
	sub sp, sp, #752
	add r3, sp, #0
	str r4, [r3, #704]
	str r5, [r3, #708]
	str r6, [r3, #712]
	str r7, [r3, #716]
	str r8, [r3, #720]
	str r9, [r3, #724]
	str r10, [r3, #728]
	str r11, [r3, #732]
	str lr, [r3, #736]
	mov r8, r3
	ldr r10, [r0, #120]
	str r10, [r8, #576]
	ldr r10, [r0, #124]
	str r10, [r8, #580]
	ldr r10, [r0, #112]
	str r10, [r8, #584]
	ldr r10, [r0, #116]
	str r10, [r8, #588]
	ldr r10, [r0, #104]
	str r10, [r8, #592]
	ldr r10, [r0, #108]
	str r10, [r8, #596]
	ldr r10, [r0, #96]
	str r10, [r8, #600]
	ldr r10, [r0, #100]
	str r10, [r8, #604]
	ldr r10, [r0, #88]
	str r10, [r8, #608]
	ldr r10, [r0, #92]
	str r10, [r8, #612]
	ldr r10, [r0, #80]
	str r10, [r8, #616]
	ldr r10, [r0, #84]
	str r10, [r8, #620]
	ldr r10, [r0, #72]
	str r10, [r8, #624]
	ldr r10, [r0, #76]
	str r10, [r8, #628]
	ldr r10, [r0, #64]
	str r10, [r8, #632]
	ldr r10, [r0, #68]
	str r10, [r8, #636]
	ldr r10, [r0, #56]
	str r10, [r8, #640]
	ldr r10, [r0, #60]
	str r10, [r8, #644]
	ldr r10, [r0, #48]
	str r10, [r8, #648]
	ldr r10, [r0, #52]
	str r10, [r8, #652]
	ldr r10, [r0, #40]
	str r10, [r8, #656]
	ldr r10, [r0, #44]
	str r10, [r8, #660]
	ldr r10, [r0, #32]
	str r10, [r8, #664]
	ldr r10, [r0, #36]
	str r10, [r8, #668]
	ldr r10, [r0, #24]
	str r10, [r8, #672]
	ldr r10, [r0, #28]
	str r10, [r8, #676]
	ldr r10, [r0, #16]
	str r10, [r8, #680]
	ldr r10, [r0, #20]
	str r10, [r8, #684]
	ldr r10, [r0, #8]
	str r10, [r8, #688]
	ldr r10, [r0, #12]
	str r10, [r8, #692]
	ldr r10, [r0, #0]
	str r10, [r8, #696]
	ldr r10, [r0, #4]
	str r10, [r8, #700]
	cmp r2, #0
	beq 20f
22:
	lsr r10, r2, #3
	cmp r10, #0
	bne 23f
	mov r3, r2
	b 24f
23:
	mov r3, #8
24:
	mov r0, r1
	add r12, r8, #448
25:
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
	bne 25b
	str r1, [r8, #740]
	str r2, [r8, #744]
	ldr r10, [r8, #448]
	rev r10, r10
	str r10, [r8, #320]
	ldr r10, [r8, #452]
	rev r10, r10
	str r10, [r8, #352]
	ldr r10, [r8, #456]
	rev r10, r10
	str r10, [r8, #384]
	ldr r10, [r8, #460]
	rev r10, r10
	str r10, [r8, #416]
	ldr r10, [r8, #464]
	rev r10, r10
	str r10, [r8, #324]
	ldr r10, [r8, #468]
	rev r10, r10
	str r10, [r8, #356]
	ldr r10, [r8, #472]
	rev r10, r10
	str r10, [r8, #388]
	ldr r10, [r8, #476]
	rev r10, r10
	str r10, [r8, #420]
	ldr r10, [r8, #480]
	rev r10, r10
	str r10, [r8, #328]
	ldr r10, [r8, #484]
	rev r10, r10
	str r10, [r8, #360]
	ldr r10, [r8, #488]
	rev r10, r10
	str r10, [r8, #392]
	ldr r10, [r8, #492]
	rev r10, r10
	str r10, [r8, #424]
	ldr r10, [r8, #496]
	rev r10, r10
	str r10, [r8, #332]
	ldr r10, [r8, #500]
	rev r10, r10
	str r10, [r8, #364]
	ldr r10, [r8, #504]
	rev r10, r10
	str r10, [r8, #396]
	ldr r10, [r8, #508]
	rev r10, r10
	str r10, [r8, #428]
	ldr r10, [r8, #512]
	rev r10, r10
	str r10, [r8, #336]
	ldr r10, [r8, #516]
	rev r10, r10
	str r10, [r8, #368]
	ldr r10, [r8, #520]
	rev r10, r10
	str r10, [r8, #400]
	ldr r10, [r8, #524]
	rev r10, r10
	str r10, [r8, #432]
	ldr r10, [r8, #528]
	rev r10, r10
	str r10, [r8, #340]
	ldr r10, [r8, #532]
	rev r10, r10
	str r10, [r8, #372]
	ldr r10, [r8, #536]
	rev r10, r10
	str r10, [r8, #404]
	ldr r10, [r8, #540]
	rev r10, r10
	str r10, [r8, #436]
	ldr r10, [r8, #544]
	rev r10, r10
	str r10, [r8, #344]
	ldr r10, [r8, #548]
	rev r10, r10
	str r10, [r8, #376]
	ldr r10, [r8, #552]
	rev r10, r10
	str r10, [r8, #408]
	ldr r10, [r8, #556]
	rev r10, r10
	str r10, [r8, #440]
	ldr r10, [r8, #560]
	rev r10, r10
	str r10, [r8, #348]
	ldr r10, [r8, #564]
	rev r10, r10
	str r10, [r8, #380]
	ldr r10, [r8, #568]
	rev r10, r10
	str r10, [r8, #412]
	ldr r10, [r8, #572]
	rev r10, r10
	str r10, [r8, #444]
	add r9, r8, #576
26:
	ldr r12, [r9, #0]
	ldr lr, [r9, #4]
	ldr r10, [r8, #384]
	eor r10, r10, r12
	str r10, [r8, #224]
	ldr r11, [r8, #416]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #160]
	ldr r10, [r8, #388]
	eor r10, r10, r12
	str r10, [r8, #228]
	ldr r11, [r8, #420]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #164]
	ldr r10, [r8, #392]
	eor r10, r10, r12
	str r10, [r8, #232]
	ldr r11, [r8, #424]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #168]
	ldr r10, [r8, #396]
	eor r10, r10, r12
	str r10, [r8, #236]
	ldr r11, [r8, #428]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #172]
	ldr r10, [r8, #400]
	eor r10, r10, r12
	str r10, [r8, #240]
	ldr r11, [r8, #432]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #176]
	ldr r10, [r8, #404]
	eor r10, r10, r12
	str r10, [r8, #244]
	ldr r11, [r8, #436]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #180]
	ldr r10, [r8, #408]
	eor r10, r10, r12
	str r10, [r8, #248]
	ldr r11, [r8, #440]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #184]
	ldr r10, [r8, #412]
	eor r10, r10, r12
	str r10, [r8, #252]
	ldr r11, [r8, #444]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	str r10, [r8, #256]
	ldr r11, [r8, #224]
	add r10, r10, r11
	str r10, [r8, #160]
	ldr r10, [r8, #164]
	str r10, [r8, #260]
	ldr r11, [r8, #228]
	add r10, r10, r11
	str r10, [r8, #164]
	ldr r10, [r8, #168]
	str r10, [r8, #264]
	ldr r11, [r8, #232]
	add r10, r10, r11
	str r10, [r8, #168]
	ldr r10, [r8, #172]
	str r10, [r8, #268]
	ldr r11, [r8, #236]
	add r10, r10, r11
	str r10, [r8, #172]
	ldr r10, [r8, #176]
	str r10, [r8, #272]
	ldr r11, [r8, #240]
	add r10, r10, r11
	str r10, [r8, #176]
	ldr r10, [r8, #180]
	str r10, [r8, #276]
	ldr r11, [r8, #244]
	add r10, r10, r11
	str r10, [r8, #180]
	ldr r10, [r8, #184]
	str r10, [r8, #280]
	ldr r11, [r8, #248]
	add r10, r10, r11
	str r10, [r8, #184]
	ldr r10, [r8, #188]
	str r10, [r8, #284]
	ldr r11, [r8, #252]
	add r10, r10, r11
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	str r10, [r8, #288]
	ldr r11, [r8, #256]
	add r10, r10, r11
	str r10, [r8, #160]
	ldr r10, [r8, #164]
	str r10, [r8, #292]
	ldr r11, [r8, #260]
	add r10, r10, r11
	str r10, [r8, #164]
	ldr r10, [r8, #168]
	str r10, [r8, #296]
	ldr r11, [r8, #264]
	add r10, r10, r11
	str r10, [r8, #168]
	ldr r10, [r8, #172]
	str r10, [r8, #300]
	ldr r11, [r8, #268]
	add r10, r10, r11
	str r10, [r8, #172]
	ldr r10, [r8, #176]
	str r10, [r8, #304]
	ldr r11, [r8, #272]
	add r10, r10, r11
	str r10, [r8, #176]
	ldr r10, [r8, #180]
	str r10, [r8, #308]
	ldr r11, [r8, #276]
	add r10, r10, r11
	str r10, [r8, #180]
	ldr r10, [r8, #184]
	str r10, [r8, #312]
	ldr r11, [r8, #280]
	add r10, r10, r11
	str r10, [r8, #184]
	ldr r10, [r8, #188]
	str r10, [r8, #316]
	ldr r11, [r8, #284]
	add r10, r10, r11
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	ldr r11, [r8, #352]
	eor r11, r11, r10
	str r11, [r8, #352]
	ldr r11, [r8, #288]
	add r10, r10, r11
	ldr r11, [r8, #320]
	eor r10, r10, r11
	str r10, [r8, #320]
	ldr r10, [r8, #164]
	ldr r11, [r8, #356]
	eor r11, r11, r10
	str r11, [r8, #356]
	ldr r11, [r8, #292]
	add r10, r10, r11
	ldr r11, [r8, #324]
	eor r10, r10, r11
	str r10, [r8, #324]
	ldr r10, [r8, #168]
	ldr r11, [r8, #360]
	eor r11, r11, r10
	str r11, [r8, #360]
	ldr r11, [r8, #296]
	add r10, r10, r11
	ldr r11, [r8, #328]
	eor r10, r10, r11
	str r10, [r8, #328]
	ldr r10, [r8, #172]
	ldr r11, [r8, #364]
	eor r11, r11, r10
	str r11, [r8, #364]
	ldr r11, [r8, #300]
	add r10, r10, r11
	ldr r11, [r8, #332]
	eor r10, r10, r11
	str r10, [r8, #332]
	ldr r10, [r8, #176]
	ldr r11, [r8, #368]
	eor r11, r11, r10
	str r11, [r8, #368]
	ldr r11, [r8, #304]
	add r10, r10, r11
	ldr r11, [r8, #336]
	eor r10, r10, r11
	str r10, [r8, #336]
	ldr r10, [r8, #180]
	ldr r11, [r8, #372]
	eor r11, r11, r10
	str r11, [r8, #372]
	ldr r11, [r8, #308]
	add r10, r10, r11
	ldr r11, [r8, #340]
	eor r10, r10, r11
	str r10, [r8, #340]
	ldr r10, [r8, #184]
	ldr r11, [r8, #376]
	eor r11, r11, r10
	str r11, [r8, #376]
	ldr r11, [r8, #312]
	add r10, r10, r11
	ldr r11, [r8, #344]
	eor r10, r10, r11
	str r10, [r8, #344]
	ldr r10, [r8, #188]
	ldr r11, [r8, #380]
	eor r11, r11, r10
	str r11, [r8, #380]
	ldr r11, [r8, #316]
	add r10, r10, r11
	ldr r11, [r8, #348]
	eor r10, r10, r11
	str r10, [r8, #348]
	add r9, r9, #8
	ldr r12, [r9, #0]
	ldr lr, [r9, #4]
	ldr r10, [r8, #320]
	eor r10, r10, r12
	str r10, [r8, #224]
	ldr r11, [r8, #352]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #160]
	ldr r10, [r8, #324]
	eor r10, r10, r12
	str r10, [r8, #228]
	ldr r11, [r8, #356]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #164]
	ldr r10, [r8, #328]
	eor r10, r10, r12
	str r10, [r8, #232]
	ldr r11, [r8, #360]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #168]
	ldr r10, [r8, #332]
	eor r10, r10, r12
	str r10, [r8, #236]
	ldr r11, [r8, #364]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #172]
	ldr r10, [r8, #336]
	eor r10, r10, r12
	str r10, [r8, #240]
	ldr r11, [r8, #368]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #176]
	ldr r10, [r8, #340]
	eor r10, r10, r12
	str r10, [r8, #244]
	ldr r11, [r8, #372]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #180]
	ldr r10, [r8, #344]
	eor r10, r10, r12
	str r10, [r8, #248]
	ldr r11, [r8, #376]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #184]
	ldr r10, [r8, #348]
	eor r10, r10, r12
	str r10, [r8, #252]
	ldr r11, [r8, #380]
	eor r10, r10, r11
	eor r10, r10, lr
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	str r10, [r8, #256]
	ldr r11, [r8, #224]
	add r10, r10, r11
	str r10, [r8, #160]
	ldr r10, [r8, #164]
	str r10, [r8, #260]
	ldr r11, [r8, #228]
	add r10, r10, r11
	str r10, [r8, #164]
	ldr r10, [r8, #168]
	str r10, [r8, #264]
	ldr r11, [r8, #232]
	add r10, r10, r11
	str r10, [r8, #168]
	ldr r10, [r8, #172]
	str r10, [r8, #268]
	ldr r11, [r8, #236]
	add r10, r10, r11
	str r10, [r8, #172]
	ldr r10, [r8, #176]
	str r10, [r8, #272]
	ldr r11, [r8, #240]
	add r10, r10, r11
	str r10, [r8, #176]
	ldr r10, [r8, #180]
	str r10, [r8, #276]
	ldr r11, [r8, #244]
	add r10, r10, r11
	str r10, [r8, #180]
	ldr r10, [r8, #184]
	str r10, [r8, #280]
	ldr r11, [r8, #248]
	add r10, r10, r11
	str r10, [r8, #184]
	ldr r10, [r8, #188]
	str r10, [r8, #284]
	ldr r11, [r8, #252]
	add r10, r10, r11
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	str r10, [r8, #288]
	ldr r11, [r8, #256]
	add r10, r10, r11
	str r10, [r8, #160]
	ldr r10, [r8, #164]
	str r10, [r8, #292]
	ldr r11, [r8, #260]
	add r10, r10, r11
	str r10, [r8, #164]
	ldr r10, [r8, #168]
	str r10, [r8, #296]
	ldr r11, [r8, #264]
	add r10, r10, r11
	str r10, [r8, #168]
	ldr r10, [r8, #172]
	str r10, [r8, #300]
	ldr r11, [r8, #268]
	add r10, r10, r11
	str r10, [r8, #172]
	ldr r10, [r8, #176]
	str r10, [r8, #304]
	ldr r11, [r8, #272]
	add r10, r10, r11
	str r10, [r8, #176]
	ldr r10, [r8, #180]
	str r10, [r8, #308]
	ldr r11, [r8, #276]
	add r10, r10, r11
	str r10, [r8, #180]
	ldr r10, [r8, #184]
	str r10, [r8, #312]
	ldr r11, [r8, #280]
	add r10, r10, r11
	str r10, [r8, #184]
	ldr r10, [r8, #188]
	str r10, [r8, #316]
	ldr r11, [r8, #284]
	add r10, r10, r11
	str r10, [r8, #188]
	bl {vg_seed_g8}
	ldr r10, [r8, #160]
	ldr r11, [r8, #416]
	eor r11, r11, r10
	str r11, [r8, #416]
	ldr r11, [r8, #288]
	add r10, r10, r11
	ldr r11, [r8, #384]
	eor r10, r10, r11
	str r10, [r8, #384]
	ldr r10, [r8, #164]
	ldr r11, [r8, #420]
	eor r11, r11, r10
	str r11, [r8, #420]
	ldr r11, [r8, #292]
	add r10, r10, r11
	ldr r11, [r8, #388]
	eor r10, r10, r11
	str r10, [r8, #388]
	ldr r10, [r8, #168]
	ldr r11, [r8, #424]
	eor r11, r11, r10
	str r11, [r8, #424]
	ldr r11, [r8, #296]
	add r10, r10, r11
	ldr r11, [r8, #392]
	eor r10, r10, r11
	str r10, [r8, #392]
	ldr r10, [r8, #172]
	ldr r11, [r8, #428]
	eor r11, r11, r10
	str r11, [r8, #428]
	ldr r11, [r8, #300]
	add r10, r10, r11
	ldr r11, [r8, #396]
	eor r10, r10, r11
	str r10, [r8, #396]
	ldr r10, [r8, #176]
	ldr r11, [r8, #432]
	eor r11, r11, r10
	str r11, [r8, #432]
	ldr r11, [r8, #304]
	add r10, r10, r11
	ldr r11, [r8, #400]
	eor r10, r10, r11
	str r10, [r8, #400]
	ldr r10, [r8, #180]
	ldr r11, [r8, #436]
	eor r11, r11, r10
	str r11, [r8, #436]
	ldr r11, [r8, #308]
	add r10, r10, r11
	ldr r11, [r8, #404]
	eor r10, r10, r11
	str r10, [r8, #404]
	ldr r10, [r8, #184]
	ldr r11, [r8, #440]
	eor r11, r11, r10
	str r11, [r8, #440]
	ldr r11, [r8, #312]
	add r10, r10, r11
	ldr r11, [r8, #408]
	eor r10, r10, r11
	str r10, [r8, #408]
	ldr r10, [r8, #188]
	ldr r11, [r8, #444]
	eor r11, r11, r10
	str r11, [r8, #444]
	ldr r11, [r8, #316]
	add r10, r10, r11
	ldr r11, [r8, #412]
	eor r10, r10, r11
	str r10, [r8, #412]
	add r9, r9, #8
	sub r10, r9, r8
	cmp r10, #704
	bne 26b
	ldr r10, [r8, #384]
	rev r10, r10
	str r10, [r8, #448]
	ldr r10, [r8, #416]
	rev r10, r10
	str r10, [r8, #452]
	ldr r10, [r8, #320]
	rev r10, r10
	str r10, [r8, #456]
	ldr r10, [r8, #352]
	rev r10, r10
	str r10, [r8, #460]
	ldr r10, [r8, #388]
	rev r10, r10
	str r10, [r8, #464]
	ldr r10, [r8, #420]
	rev r10, r10
	str r10, [r8, #468]
	ldr r10, [r8, #324]
	rev r10, r10
	str r10, [r8, #472]
	ldr r10, [r8, #356]
	rev r10, r10
	str r10, [r8, #476]
	ldr r10, [r8, #392]
	rev r10, r10
	str r10, [r8, #480]
	ldr r10, [r8, #424]
	rev r10, r10
	str r10, [r8, #484]
	ldr r10, [r8, #328]
	rev r10, r10
	str r10, [r8, #488]
	ldr r10, [r8, #360]
	rev r10, r10
	str r10, [r8, #492]
	ldr r10, [r8, #396]
	rev r10, r10
	str r10, [r8, #496]
	ldr r10, [r8, #428]
	rev r10, r10
	str r10, [r8, #500]
	ldr r10, [r8, #332]
	rev r10, r10
	str r10, [r8, #504]
	ldr r10, [r8, #364]
	rev r10, r10
	str r10, [r8, #508]
	ldr r10, [r8, #400]
	rev r10, r10
	str r10, [r8, #512]
	ldr r10, [r8, #432]
	rev r10, r10
	str r10, [r8, #516]
	ldr r10, [r8, #336]
	rev r10, r10
	str r10, [r8, #520]
	ldr r10, [r8, #368]
	rev r10, r10
	str r10, [r8, #524]
	ldr r10, [r8, #404]
	rev r10, r10
	str r10, [r8, #528]
	ldr r10, [r8, #436]
	rev r10, r10
	str r10, [r8, #532]
	ldr r10, [r8, #340]
	rev r10, r10
	str r10, [r8, #536]
	ldr r10, [r8, #372]
	rev r10, r10
	str r10, [r8, #540]
	ldr r10, [r8, #408]
	rev r10, r10
	str r10, [r8, #544]
	ldr r10, [r8, #440]
	rev r10, r10
	str r10, [r8, #548]
	ldr r10, [r8, #344]
	rev r10, r10
	str r10, [r8, #552]
	ldr r10, [r8, #376]
	rev r10, r10
	str r10, [r8, #556]
	ldr r10, [r8, #412]
	rev r10, r10
	str r10, [r8, #560]
	ldr r10, [r8, #444]
	rev r10, r10
	str r10, [r8, #564]
	ldr r10, [r8, #348]
	rev r10, r10
	str r10, [r8, #568]
	ldr r10, [r8, #380]
	rev r10, r10
	str r10, [r8, #572]
	ldr r1, [r8, #740]
	ldr r2, [r8, #744]
	lsr r10, r2, #3
	cmp r10, #0
	bne 27f
	mov r3, r2
	b 28f
27:
	mov r3, #8
28:
	add r0, r8, #448
	mov r12, r1
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
	lsr r10, r2, #3
	cmp r10, #0
	bne 210f
	mov r3, r2
	b 211f
210:
	mov r3, #8
211:
	add r1, r1, #128
	subs r2, r2, r3
	bne 22b
	b 21f
20:
21:
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
	bx lr
