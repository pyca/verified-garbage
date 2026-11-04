// The functions of `src/ecdsa_p192.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p192_verify:
	mov r12, r3
	str r4, [r12, #0]
	str r5, [r12, #4]
	str r6, [r12, #8]
	str r7, [r12, #12]
	str r8, [r12, #16]
	str r9, [r12, #20]
	str r10, [r12, #24]
	str r11, [r12, #28]
	str lr, [r12, #32]
	mov lr, r0
	ldr r4, [r2, #20]
	rev r4, r4
	str r4, [r12, #808]
	ldr r4, [r2, #16]
	rev r4, r4
	str r4, [r12, #812]
	ldr r4, [r2, #12]
	rev r4, r4
	str r4, [r12, #816]
	ldr r4, [r2, #8]
	rev r4, r4
	str r4, [r12, #820]
	ldr r4, [r2, #4]
	rev r4, r4
	str r4, [r12, #824]
	ldr r4, [r2, #0]
	rev r4, r4
	str r4, [r12, #828]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #832]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #836]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #840]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #844]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #848]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #852]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #876]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #64]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #68]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #72]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #76]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #80]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #84]
	movw r4, #10289
	movt r4, #46290
	str r4, [r12, #88]
	movw r4, #51633
	movt r4, #5227
	str r4, [r12, #92]
	movw r4, #63542
	movt r4, #39390
	str r4, [r12, #96]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #100]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #104]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #108]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #136]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #140]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #144]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #148]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #152]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #156]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #160]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #164]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #168]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #172]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #176]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #180]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #184]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #188]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #192]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #196]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #200]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #204]
	movw r4, #65532
	movt r4, #65535
	str r4, [r12, #208]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #212]
	movw r4, #65531
	movt r4, #65535
	str r4, [r12, #216]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #220]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #224]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #228]
	movw r4, #45001
	movt r4, #62633
	str r4, [r12, #232]
	movw r4, #44051
	movt r4, #10381
	str r4, [r12, #236]
	movw r4, #16552
	movt r4, #19222
	str r4, [r12, #240]
	movw r4, #26902
	movt r4, #22405
	str r4, [r12, #244]
	movw r4, #5012
	movt r4, #1858
	str r4, [r12, #248]
	movw r4, #52304
	movt r4, #23386
	str r4, [r12, #252]
	movw r4, #41224
	movt r4, #13103
	str r4, [r12, #256]
	movw r4, #45836
	movt r4, #3468
	str r4, [r12, #260]
	movw r4, #10505
	movt r4, #30417
	str r4, [r12, #264]
	movw r4, #54263
	movt r4, #35403
	str r4, [r12, #268]
	movw r4, #6391
	movt r4, #62418
	str r4, [r12, #272]
	movw r4, #51449
	movt r4, #38220
	str r4, [r12, #276]
	movw r4, #8841
	movt r4, #7746
	str r4, [r12, #280]
	movw r4, #41783
	movt r4, #31506
	str r4, [r12, #284]
	movw r4, #61534
	movt r4, #35174
	str r4, [r12, #288]
	movw r4, #46372
	movt r4, #56866
	str r4, [r12, #292]
	movw r4, #43085
	movt r4, #27373
	str r4, [r12, #296]
	movw r4, #15747
	movt r4, #27177
	str r4, [r12, #300]
	movw r4, #22881
	movt r4, #57011
	str r4, [r12, #304]
	movw r4, #47820
	movt r4, #52838
	str r4, [r12, #308]
	movw r4, #27630
	movt r4, #47930
	str r4, [r12, #312]
	movw r4, #59995
	movt r4, #18070
	str r4, [r12, #316]
	movw r4, #33186
	movt r4, #59909
	str r4, [r12, #320]
	movw r4, #22135
	movt r4, #10430
	str r4, [r12, #324]
	movw r4, #55247
	movt r4, #19245
	str r4, [r12, #328]
	movw r4, #13902
	movt r4, #60308
	str r4, [r12, #332]
	movw r4, #1993
	movt r4, #26145
	str r4, [r12, #336]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #340]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #344]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #348]
	movw r4, #65533
	movt r4, #65535
	str r4, [r12, #352]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #356]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #360]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #364]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #368]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #372]
	movw r4, #10287
	movt r4, #46290
	str r4, [r12, #376]
	movw r4, #51633
	movt r4, #5227
	str r4, [r12, #380]
	movw r4, #63542
	movt r4, #39390
	str r4, [r12, #384]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #388]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #392]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #396]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #400]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #404]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #408]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #412]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #416]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #420]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #424]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #428]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #432]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #436]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #440]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #444]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #448]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #452]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #456]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #460]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #464]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #468]
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1120]
	mov r11, #24
20:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #808]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #0]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #1]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #2]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #3]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #4]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #5]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #6]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #7]
	cmp r11, #0
	bne 20b
	mov r11, #24
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #352]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #192]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #193]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #194]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #195]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #196]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #197]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #198]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #199]
	cmp r11, #0
	bne 21b
	mov r11, #24
22:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #376]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #384]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #385]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #386]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #387]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #388]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #389]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #390]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #391]
	cmp r11, #0
	bne 22b
	add r6, r2, #24
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #784]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #788]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #792]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #796]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #800]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #804]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1000]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1004]
	movw r4, #2
	movt r4, #0
	str r4, [r12, #1008]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1012]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1016]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1020]
	movw r4, #15000
	movt r4, #42723
	str r4, [r12, #1024]
	movw r4, #58374
	movt r4, #25305
	str r4, [r12, #1028]
	movw r4, #27362
	movt r4, #6407
	str r4, [r12, #1032]
	movw r4, #52658
	movt r4, #29313
	str r4, [r12, #1036]
	movw r4, #45361
	movt r4, #22464
	str r4, [r12, #1040]
	movw r4, #61125
	movt r4, #29640
	str r4, [r12, #1044]
	add r6, r0, #1
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #856]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #860]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #864]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #868]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #872]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #876]
	add r6, r6, #24
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #928]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #932]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #936]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #940]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #944]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #948]
	ldrb r4, [r0, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #856]
	ldr r8, [r12, #64]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #860]
	ldr r8, [r12, #68]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #864]
	ldr r8, [r12, #72]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #868]
	ldr r8, [r12, #76]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #872]
	ldr r8, [r12, #80]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #876]
	ldr r8, [r12, #84]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	sub r5, r3, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #928]
	ldr r8, [r12, #64]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #932]
	ldr r8, [r12, #68]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #936]
	ldr r8, [r12, #72]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #940]
	ldr r8, [r12, #76]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #944]
	ldr r8, [r12, #80]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #948]
	ldr r8, [r12, #84]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	sub r5, r3, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	mov r10, lr
	mov r0, r12
	movw r1, #880
	movw r2, #856
	movw r3, #1000
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #928
	movw r3, #1000
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #952
	movw r2, #904
	movw r3, #904
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #880
	movw r3, #880
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #1048
	movw r3, #880
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #208
	movw r3, #880
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #976
	movw r2, #1072
	movw r3, #1048
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #976
	movw r3, #1024
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #952
	movw r3, #1072
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #1048]
	ldr r4, [r12, #1052]
	orr r5, r5, r4
	ldr r4, [r12, #1056]
	orr r5, r5, r4
	ldr r4, [r12, #1060]
	orr r5, r5, r4
	ldr r4, [r12, #1064]
	orr r5, r5, r4
	ldr r4, [r12, #1068]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r4, #0
	sub r5, r4, r5
	sub r5, r5, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r10, [r12, #1120]
	ldr r4, [r12, #256]
	ldr r5, [r12, #880]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #976]
	ldr r4, [r12, #260]
	ldr r5, [r12, #884]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #980]
	ldr r4, [r12, #264]
	ldr r5, [r12, #888]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #984]
	ldr r4, [r12, #268]
	ldr r5, [r12, #892]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #988]
	ldr r4, [r12, #272]
	ldr r5, [r12, #896]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #992]
	ldr r4, [r12, #276]
	ldr r5, [r12, #900]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #996]
	ldr r4, [r12, #280]
	ldr r5, [r12, #904]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1096]
	ldr r4, [r12, #284]
	ldr r5, [r12, #908]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1100]
	ldr r4, [r12, #288]
	ldr r5, [r12, #912]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1104]
	ldr r4, [r12, #292]
	ldr r5, [r12, #916]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1108]
	ldr r4, [r12, #296]
	ldr r5, [r12, #920]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1112]
	ldr r4, [r12, #300]
	ldr r5, [r12, #924]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1116]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #808]
	ldr r8, [r12, #88]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #812]
	ldr r8, [r12, #92]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #816]
	ldr r8, [r12, #96]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #820]
	ldr r8, [r12, #100]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #824]
	ldr r8, [r12, #104]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #828]
	ldr r8, [r12, #108]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	sub r5, r3, #1
	mov r9, r5
	ldr r5, [r12, #808]
	ldr r4, [r12, #812]
	orr r5, r5, r4
	ldr r4, [r12, #816]
	orr r5, r5, r4
	ldr r4, [r12, #820]
	orr r5, r5, r4
	ldr r4, [r12, #824]
	orr r5, r5, r4
	ldr r4, [r12, #828]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #784]
	ldr r8, [r12, #88]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #788]
	ldr r8, [r12, #92]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #792]
	ldr r8, [r12, #96]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #796]
	ldr r8, [r12, #100]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #800]
	ldr r8, [r12, #104]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	ldr r7, [r12, #804]
	ldr r8, [r12, #108]
	and r4, r7, r6
	and r5, r8, r6
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	lsr r4, r7, #16
	lsr r5, r8, #16
	add r4, r4, r6
	sub r4, r4, r5
	add r4, r4, r3
	lsr r3, r4, #16
	sub r5, r3, #1
	mov r9, r5
	ldr r5, [r12, #784]
	ldr r4, [r12, #788]
	orr r5, r5, r4
	ldr r4, [r12, #792]
	orr r5, r5, r4
	ldr r4, [r12, #796]
	orr r5, r5, r4
	ldr r4, [r12, #800]
	orr r5, r5, r4
	ldr r4, [r12, #804]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	mov r10, lr
	mov r0, r12
	movw r1, #952
	movw r2, #784
	movw r3, #304
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	ldr r4, [r12, #328]
	str r4, [r12, #760]
	ldr r4, [r12, #332]
	str r4, [r12, #764]
	ldr r4, [r12, #336]
	str r4, [r12, #768]
	ldr r4, [r12, #340]
	str r4, [r12, #772]
	ldr r4, [r12, #344]
	str r4, [r12, #776]
	ldr r4, [r12, #348]
	str r4, [r12, #780]
	mov r11, #192
23:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #760
	movw r2, #760
	movw r3, #760
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #760
	movw r3, #952
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #384]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #760]
	ldr r5, [r12, #784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #760]
	ldr r4, [r12, #764]
	ldr r5, [r12, #788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #764]
	ldr r4, [r12, #768]
	ldr r5, [r12, #792]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #768]
	ldr r4, [r12, #772]
	ldr r5, [r12, #796]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #772]
	ldr r4, [r12, #776]
	ldr r5, [r12, #800]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #776]
	ldr r4, [r12, #780]
	ldr r5, [r12, #804]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #780]
	cmp r11, #0
	bne 23b
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #832
	movw r3, #304
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1000
	movw r2, #808
	movw r3, #304
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1048
	movw r2, #1024
	movw r3, #760
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1072
	movw r2, #1000
	movw r3, #760
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #880
	movw r2, #1048
	movw r3, #160
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #1072
	movw r3, #160
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	mov r11, #24
24:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #880]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #0]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #1]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #2]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #3]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #4]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #5]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #6]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #7]
	cmp r11, #0
	bne 24b
	ldr r4, [r12, #256]
	str r4, [r12, #3576]
	ldr r4, [r12, #260]
	str r4, [r12, #3580]
	ldr r4, [r12, #264]
	str r4, [r12, #3584]
	ldr r4, [r12, #268]
	str r4, [r12, #3588]
	ldr r4, [r12, #272]
	str r4, [r12, #3592]
	ldr r4, [r12, #276]
	str r4, [r12, #3596]
	ldr r4, [r12, #280]
	str r4, [r12, #3600]
	ldr r4, [r12, #284]
	str r4, [r12, #3604]
	ldr r4, [r12, #288]
	str r4, [r12, #3608]
	ldr r4, [r12, #292]
	str r4, [r12, #3612]
	ldr r4, [r12, #296]
	str r4, [r12, #3616]
	ldr r4, [r12, #300]
	str r4, [r12, #3620]
	ldr r4, [r12, #184]
	str r4, [r12, #3624]
	ldr r4, [r12, #188]
	str r4, [r12, #3628]
	ldr r4, [r12, #192]
	str r4, [r12, #3632]
	ldr r4, [r12, #196]
	str r4, [r12, #3636]
	ldr r4, [r12, #200]
	str r4, [r12, #3640]
	ldr r4, [r12, #204]
	str r4, [r12, #3644]
	ldr r4, [r12, #208]
	str r4, [r12, #3648]
	ldr r4, [r12, #212]
	str r4, [r12, #3652]
	ldr r4, [r12, #216]
	str r4, [r12, #3656]
	ldr r4, [r12, #220]
	str r4, [r12, #3660]
	ldr r4, [r12, #224]
	str r4, [r12, #3664]
	ldr r4, [r12, #228]
	str r4, [r12, #3668]
	ldr r4, [r12, #232]
	str r4, [r12, #3672]
	ldr r4, [r12, #236]
	str r4, [r12, #3676]
	ldr r4, [r12, #240]
	str r4, [r12, #3680]
	ldr r4, [r12, #244]
	str r4, [r12, #3684]
	ldr r4, [r12, #248]
	str r4, [r12, #3688]
	ldr r4, [r12, #252]
	str r4, [r12, #3692]
	mov r11, #192
25:
	sub r11, r11, #1
	ldr r4, [r12, #400]
	str r4, [r12, #3504]
	ldr r4, [r12, #404]
	str r4, [r12, #3508]
	ldr r4, [r12, #408]
	str r4, [r12, #3512]
	ldr r4, [r12, #412]
	str r4, [r12, #3516]
	ldr r4, [r12, #416]
	str r4, [r12, #3520]
	ldr r4, [r12, #420]
	str r4, [r12, #3524]
	ldr r4, [r12, #424]
	str r4, [r12, #3528]
	ldr r4, [r12, #428]
	str r4, [r12, #3532]
	ldr r4, [r12, #432]
	str r4, [r12, #3536]
	ldr r4, [r12, #436]
	str r4, [r12, #3540]
	ldr r4, [r12, #440]
	str r4, [r12, #3544]
	ldr r4, [r12, #444]
	str r4, [r12, #3548]
	ldr r4, [r12, #448]
	str r4, [r12, #3552]
	ldr r4, [r12, #452]
	str r4, [r12, #3556]
	ldr r4, [r12, #456]
	str r4, [r12, #3560]
	ldr r4, [r12, #460]
	str r4, [r12, #3564]
	ldr r4, [r12, #464]
	str r4, [r12, #3568]
	ldr r4, [r12, #468]
	str r4, [r12, #3572]
	mov r10, lr
	mov r0, r12
	bl {vg_p192_point_double}
	mov lr, r10
	ldr r4, [r12, #3432]
	str r4, [r12, #3504]
	ldr r4, [r12, #3436]
	str r4, [r12, #3508]
	ldr r4, [r12, #3440]
	str r4, [r12, #3512]
	ldr r4, [r12, #3444]
	str r4, [r12, #3516]
	ldr r4, [r12, #3448]
	str r4, [r12, #3520]
	ldr r4, [r12, #3452]
	str r4, [r12, #3524]
	ldr r4, [r12, #3456]
	str r4, [r12, #3528]
	ldr r4, [r12, #3460]
	str r4, [r12, #3532]
	ldr r4, [r12, #3464]
	str r4, [r12, #3536]
	ldr r4, [r12, #3468]
	str r4, [r12, #3540]
	ldr r4, [r12, #3472]
	str r4, [r12, #3544]
	ldr r4, [r12, #3476]
	str r4, [r12, #3548]
	ldr r4, [r12, #3480]
	str r4, [r12, #3552]
	ldr r4, [r12, #3484]
	str r4, [r12, #3556]
	ldr r4, [r12, #3488]
	str r4, [r12, #3560]
	ldr r4, [r12, #3492]
	str r4, [r12, #3564]
	ldr r4, [r12, #3496]
	str r4, [r12, #3568]
	ldr r4, [r12, #3500]
	str r4, [r12, #3572]
	mov r10, lr
	mov r0, r12
	bl {vg_p192_point_add}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #0]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #3504]
	ldr r5, [r12, #3432]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #400]
	ldr r4, [r12, #3508]
	ldr r5, [r12, #3436]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #404]
	ldr r4, [r12, #3512]
	ldr r5, [r12, #3440]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #408]
	ldr r4, [r12, #3516]
	ldr r5, [r12, #3444]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #412]
	ldr r4, [r12, #3520]
	ldr r5, [r12, #3448]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #416]
	ldr r4, [r12, #3524]
	ldr r5, [r12, #3452]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #420]
	ldr r4, [r12, #3528]
	ldr r5, [r12, #3456]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #424]
	ldr r4, [r12, #3532]
	ldr r5, [r12, #3460]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #428]
	ldr r4, [r12, #3536]
	ldr r5, [r12, #3464]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #432]
	ldr r4, [r12, #3540]
	ldr r5, [r12, #3468]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #436]
	ldr r4, [r12, #3544]
	ldr r5, [r12, #3472]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #440]
	ldr r4, [r12, #3548]
	ldr r5, [r12, #3476]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #444]
	ldr r4, [r12, #3552]
	ldr r5, [r12, #3480]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #448]
	ldr r4, [r12, #3556]
	ldr r5, [r12, #3484]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #452]
	ldr r4, [r12, #3560]
	ldr r5, [r12, #3488]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #456]
	ldr r4, [r12, #3564]
	ldr r5, [r12, #3492]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #460]
	ldr r4, [r12, #3568]
	ldr r5, [r12, #3496]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #464]
	ldr r4, [r12, #3572]
	ldr r5, [r12, #3500]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #468]
	cmp r11, #0
	bne 25b
	ldr r4, [r12, #400]
	str r4, [r12, #1048]
	ldr r4, [r12, #404]
	str r4, [r12, #1052]
	ldr r4, [r12, #408]
	str r4, [r12, #1056]
	ldr r4, [r12, #412]
	str r4, [r12, #1060]
	ldr r4, [r12, #416]
	str r4, [r12, #1064]
	ldr r4, [r12, #420]
	str r4, [r12, #1068]
	ldr r4, [r12, #424]
	str r4, [r12, #1072]
	ldr r4, [r12, #428]
	str r4, [r12, #1076]
	ldr r4, [r12, #432]
	str r4, [r12, #1080]
	ldr r4, [r12, #436]
	str r4, [r12, #1084]
	ldr r4, [r12, #440]
	str r4, [r12, #1088]
	ldr r4, [r12, #444]
	str r4, [r12, #1092]
	ldr r4, [r12, #448]
	str r4, [r12, #952]
	ldr r4, [r12, #452]
	str r4, [r12, #956]
	ldr r4, [r12, #456]
	str r4, [r12, #960]
	ldr r4, [r12, #460]
	str r4, [r12, #964]
	ldr r4, [r12, #464]
	str r4, [r12, #968]
	ldr r4, [r12, #468]
	str r4, [r12, #972]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #400]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #404]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #408]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #412]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #416]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #420]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #424]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #428]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #432]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #436]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #440]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #444]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #448]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #452]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #456]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #460]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #464]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #468]
	mov r11, #24
26:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #904]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #0]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #1]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #2]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #3]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #4]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #5]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #6]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #7]
	cmp r11, #0
	bne 26b
	ldr r4, [r12, #976]
	str r4, [r12, #3576]
	ldr r4, [r12, #980]
	str r4, [r12, #3580]
	ldr r4, [r12, #984]
	str r4, [r12, #3584]
	ldr r4, [r12, #988]
	str r4, [r12, #3588]
	ldr r4, [r12, #992]
	str r4, [r12, #3592]
	ldr r4, [r12, #996]
	str r4, [r12, #3596]
	ldr r4, [r12, #1096]
	str r4, [r12, #3600]
	ldr r4, [r12, #1100]
	str r4, [r12, #3604]
	ldr r4, [r12, #1104]
	str r4, [r12, #3608]
	ldr r4, [r12, #1108]
	str r4, [r12, #3612]
	ldr r4, [r12, #1112]
	str r4, [r12, #3616]
	ldr r4, [r12, #1116]
	str r4, [r12, #3620]
	ldr r4, [r12, #184]
	str r4, [r12, #3624]
	ldr r4, [r12, #188]
	str r4, [r12, #3628]
	ldr r4, [r12, #192]
	str r4, [r12, #3632]
	ldr r4, [r12, #196]
	str r4, [r12, #3636]
	ldr r4, [r12, #200]
	str r4, [r12, #3640]
	ldr r4, [r12, #204]
	str r4, [r12, #3644]
	ldr r4, [r12, #208]
	str r4, [r12, #3648]
	ldr r4, [r12, #212]
	str r4, [r12, #3652]
	ldr r4, [r12, #216]
	str r4, [r12, #3656]
	ldr r4, [r12, #220]
	str r4, [r12, #3660]
	ldr r4, [r12, #224]
	str r4, [r12, #3664]
	ldr r4, [r12, #228]
	str r4, [r12, #3668]
	ldr r4, [r12, #232]
	str r4, [r12, #3672]
	ldr r4, [r12, #236]
	str r4, [r12, #3676]
	ldr r4, [r12, #240]
	str r4, [r12, #3680]
	ldr r4, [r12, #244]
	str r4, [r12, #3684]
	ldr r4, [r12, #248]
	str r4, [r12, #3688]
	ldr r4, [r12, #252]
	str r4, [r12, #3692]
	mov r11, #192
27:
	sub r11, r11, #1
	ldr r4, [r12, #400]
	str r4, [r12, #3504]
	ldr r4, [r12, #404]
	str r4, [r12, #3508]
	ldr r4, [r12, #408]
	str r4, [r12, #3512]
	ldr r4, [r12, #412]
	str r4, [r12, #3516]
	ldr r4, [r12, #416]
	str r4, [r12, #3520]
	ldr r4, [r12, #420]
	str r4, [r12, #3524]
	ldr r4, [r12, #424]
	str r4, [r12, #3528]
	ldr r4, [r12, #428]
	str r4, [r12, #3532]
	ldr r4, [r12, #432]
	str r4, [r12, #3536]
	ldr r4, [r12, #436]
	str r4, [r12, #3540]
	ldr r4, [r12, #440]
	str r4, [r12, #3544]
	ldr r4, [r12, #444]
	str r4, [r12, #3548]
	ldr r4, [r12, #448]
	str r4, [r12, #3552]
	ldr r4, [r12, #452]
	str r4, [r12, #3556]
	ldr r4, [r12, #456]
	str r4, [r12, #3560]
	ldr r4, [r12, #460]
	str r4, [r12, #3564]
	ldr r4, [r12, #464]
	str r4, [r12, #3568]
	ldr r4, [r12, #468]
	str r4, [r12, #3572]
	mov r10, lr
	mov r0, r12
	bl {vg_p192_point_double}
	mov lr, r10
	ldr r4, [r12, #3432]
	str r4, [r12, #3504]
	ldr r4, [r12, #3436]
	str r4, [r12, #3508]
	ldr r4, [r12, #3440]
	str r4, [r12, #3512]
	ldr r4, [r12, #3444]
	str r4, [r12, #3516]
	ldr r4, [r12, #3448]
	str r4, [r12, #3520]
	ldr r4, [r12, #3452]
	str r4, [r12, #3524]
	ldr r4, [r12, #3456]
	str r4, [r12, #3528]
	ldr r4, [r12, #3460]
	str r4, [r12, #3532]
	ldr r4, [r12, #3464]
	str r4, [r12, #3536]
	ldr r4, [r12, #3468]
	str r4, [r12, #3540]
	ldr r4, [r12, #3472]
	str r4, [r12, #3544]
	ldr r4, [r12, #3476]
	str r4, [r12, #3548]
	ldr r4, [r12, #3480]
	str r4, [r12, #3552]
	ldr r4, [r12, #3484]
	str r4, [r12, #3556]
	ldr r4, [r12, #3488]
	str r4, [r12, #3560]
	ldr r4, [r12, #3492]
	str r4, [r12, #3564]
	ldr r4, [r12, #3496]
	str r4, [r12, #3568]
	ldr r4, [r12, #3500]
	str r4, [r12, #3572]
	mov r10, lr
	mov r0, r12
	bl {vg_p192_point_add}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #0]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #3504]
	ldr r5, [r12, #3432]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #400]
	ldr r4, [r12, #3508]
	ldr r5, [r12, #3436]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #404]
	ldr r4, [r12, #3512]
	ldr r5, [r12, #3440]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #408]
	ldr r4, [r12, #3516]
	ldr r5, [r12, #3444]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #412]
	ldr r4, [r12, #3520]
	ldr r5, [r12, #3448]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #416]
	ldr r4, [r12, #3524]
	ldr r5, [r12, #3452]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #420]
	ldr r4, [r12, #3528]
	ldr r5, [r12, #3456]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #424]
	ldr r4, [r12, #3532]
	ldr r5, [r12, #3460]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #428]
	ldr r4, [r12, #3536]
	ldr r5, [r12, #3464]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #432]
	ldr r4, [r12, #3540]
	ldr r5, [r12, #3468]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #436]
	ldr r4, [r12, #3544]
	ldr r5, [r12, #3472]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #440]
	ldr r4, [r12, #3548]
	ldr r5, [r12, #3476]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #444]
	ldr r4, [r12, #3552]
	ldr r5, [r12, #3480]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #448]
	ldr r4, [r12, #3556]
	ldr r5, [r12, #3484]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #452]
	ldr r4, [r12, #3560]
	ldr r5, [r12, #3488]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #456]
	ldr r4, [r12, #3564]
	ldr r5, [r12, #3492]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #460]
	ldr r4, [r12, #3568]
	ldr r5, [r12, #3496]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #464]
	ldr r4, [r12, #3572]
	ldr r5, [r12, #3500]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #468]
	cmp r11, #0
	bne 27b
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #1048
	movw r3, #400
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #1072
	movw r3, #424
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #952
	movw r3, #448
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #1048
	movw r3, #1072
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #400
	movw r3, #424
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #712
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #616
	movw r3, #640
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #688
	movw r2, #688
	movw r3, #712
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #1048
	movw r3, #952
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #400
	movw r3, #448
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #712
	movw r3, #736
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #616
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #712
	movw r3, #736
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #1072
	movw r3, #952
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #424
	movw r3, #448
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #736
	movw r3, #472
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #640
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #736
	movw r2, #736
	movw r3, #472
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #208
	movw r3, #712
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #232
	movw r3, #664
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #472
	movw r3, #520
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #640
	movw r3, #520
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #640
	movw r3, #520
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #472
	movw r3, #520
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #616
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #208
	movw r3, #664
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #232
	movw r3, #712
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #616
	movw r3, #664
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #664
	movw r2, #208
	movw r3, #664
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #712
	movw r2, #712
	movw r3, #664
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #640
	movw r3, #712
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #496
	movw r2, #496
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #736
	movw r3, #712
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #688
	movw r3, #472
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #472
	movw r2, #472
	movw r3, #616
	bl {vg_p192_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #616
	movw r2, #688
	movw r3, #640
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #736
	movw r3, #520
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #520
	movw r2, #520
	movw r3, #616
	bl {vg_p192_add_mod_p}
	mov lr, r10
	ldr r4, [r12, #472]
	str r4, [r12, #400]
	ldr r4, [r12, #476]
	str r4, [r12, #404]
	ldr r4, [r12, #480]
	str r4, [r12, #408]
	ldr r4, [r12, #484]
	str r4, [r12, #412]
	ldr r4, [r12, #488]
	str r4, [r12, #416]
	ldr r4, [r12, #492]
	str r4, [r12, #420]
	ldr r4, [r12, #496]
	str r4, [r12, #424]
	ldr r4, [r12, #500]
	str r4, [r12, #428]
	ldr r4, [r12, #504]
	str r4, [r12, #432]
	ldr r4, [r12, #508]
	str r4, [r12, #436]
	ldr r4, [r12, #512]
	str r4, [r12, #440]
	ldr r4, [r12, #516]
	str r4, [r12, #444]
	ldr r4, [r12, #520]
	str r4, [r12, #448]
	ldr r4, [r12, #524]
	str r4, [r12, #452]
	ldr r4, [r12, #528]
	str r4, [r12, #456]
	ldr r4, [r12, #532]
	str r4, [r12, #460]
	ldr r4, [r12, #536]
	str r4, [r12, #464]
	ldr r4, [r12, #540]
	str r4, [r12, #468]
	ldr r4, [r12, #184]
	str r4, [r12, #760]
	ldr r4, [r12, #188]
	str r4, [r12, #764]
	ldr r4, [r12, #192]
	str r4, [r12, #768]
	ldr r4, [r12, #196]
	str r4, [r12, #772]
	ldr r4, [r12, #200]
	str r4, [r12, #776]
	ldr r4, [r12, #204]
	str r4, [r12, #780]
	mov r11, #192
28:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #760
	movw r2, #760
	movw r3, #760
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #784
	movw r2, #760
	movw r3, #448
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #192]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #760]
	ldr r5, [r12, #784]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #760]
	ldr r4, [r12, #764]
	ldr r5, [r12, #788]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #764]
	ldr r4, [r12, #768]
	ldr r5, [r12, #792]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #768]
	ldr r4, [r12, #772]
	ldr r5, [r12, #796]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #772]
	ldr r4, [r12, #776]
	ldr r5, [r12, #800]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #776]
	ldr r4, [r12, #780]
	ldr r5, [r12, #804]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #780]
	cmp r11, #0
	bne 28b
	mov r10, lr
	mov r0, r12
	movw r1, #880
	movw r2, #400
	movw r3, #760
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #904
	movw r2, #880
	movw r3, #160
	bl {vg_p192_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #976
	movw r2, #904
	movw r3, #304
	bl {vg_p192_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #976
	movw r3, #1000
	bl {vg_p192_sub_mod_n}
	mov lr, r10
	ldr r5, [r12, #448]
	ldr r4, [r12, #452]
	orr r5, r5, r4
	ldr r4, [r12, #456]
	orr r5, r5, r4
	ldr r4, [r12, #460]
	orr r5, r5, r4
	ldr r4, [r12, #464]
	orr r5, r5, r4
	ldr r4, [r12, #468]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r5, [r12, #1024]
	ldr r4, [r12, #1028]
	orr r5, r5, r4
	ldr r4, [r12, #1032]
	orr r5, r5, r4
	ldr r4, [r12, #1036]
	orr r5, r5, r4
	ldr r4, [r12, #1040]
	orr r5, r5, r4
	ldr r4, [r12, #1044]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r4, #0
	sub r5, r4, r5
	sub r5, r5, #1
	ldr r4, [r12, #1120]
	and r4, r4, r5
	str r4, [r12, #1120]
	ldr r10, [r12, #1120]
	and r0, r10, #1
	ldr r4, [r12, #0]
	ldr r5, [r12, #4]
	ldr r6, [r12, #8]
	ldr r7, [r12, #12]
	ldr r8, [r12, #16]
	ldr r9, [r12, #20]
	ldr r10, [r12, #24]
	ldr r11, [r12, #28]
	ldr lr, [r12, #32]
	bx lr

vg_ecdsa_p192_sign:
	ldr r12, [sp, #4]
	ldr r12, [r12, #12]
	cmp r12, #0
	beq 20f
	cmp r12, #1
	beq 22f
	cmp r12, #2
	beq 24f
	cmp r12, #3
	beq 26f
	cmp r12, #4
	beq 28f
	cmp r12, #5
	beq 210f
	cmp r12, #6
	beq 212f
	sub sp, sp, #216
	add r12, sp, #0
	str r4, [r12, #180]
	str r5, [r12, #184]
	str r6, [r12, #188]
	str r7, [r12, #192]
	str r9, [r12, #196]
	str r10, [r12, #200]
	str r11, [r12, #204]
	str lr, [r12, #208]
	str r8, [r12, #212]
	ldr r4, [r12, #220]
	str r0, [r12, #176]
	mov r5, r1
	mov r6, r2
	ldr r11, [r12, #216]
	mov r8, r12
	movw r10, #65535
	mov r7, #1
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #10289
	movt r1, #46290
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #20]
	ldr r0, [r6, #16]
	rev r0, r0
	str r0, [r8, #144]
	movw r1, #51633
	movt r1, #5227
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #16]
	ldr r0, [r6, #12]
	rev r0, r0
	str r0, [r8, #140]
	movw r1, #63542
	movt r1, #39390
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #12]
	ldr r0, [r6, #8]
	rev r0, r0
	str r0, [r8, #136]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #8]
	ldr r0, [r6, #4]
	rev r0, r0
	str r0, [r8, #132]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #4]
	ldr r0, [r6, #0]
	rev r0, r0
	str r0, [r8, #128]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #0]
	mov r12, #0
	sub r7, r12, r7
	ldr r0, [r8, #148]
	ldr r1, [r8, #20]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #148]
	ldr r0, [r8, #144]
	ldr r1, [r8, #16]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #144]
	ldr r0, [r8, #140]
	ldr r1, [r8, #12]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #140]
	ldr r0, [r8, #136]
	ldr r1, [r8, #8]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #136]
	ldr r0, [r8, #132]
	ldr r1, [r8, #4]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #132]
	ldr r0, [r8, #128]
	ldr r1, [r8, #0]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #128]
	movw r0, #257
	movt r0, #257
	mov r1, #0
	str r0, [r8, #64]
	str r1, [r8, #0]
	str r0, [r8, #68]
	str r1, [r8, #4]
	str r0, [r8, #72]
	str r1, [r8, #8]
	str r0, [r8, #76]
	str r1, [r8, #12]
	str r0, [r8, #80]
	str r1, [r8, #16]
	str r0, [r8, #84]
	str r1, [r8, #20]
	str r0, [r8, #88]
	str r1, [r8, #24]
	str r0, [r8, #92]
	str r1, [r8, #28]
	str r0, [r8, #96]
	str r1, [r8, #32]
	str r0, [r8, #100]
	str r1, [r8, #36]
	str r0, [r8, #104]
	str r1, [r8, #40]
	str r0, [r8, #108]
	str r1, [r8, #44]
	str r0, [r8, #112]
	str r1, [r8, #48]
	str r0, [r8, #116]
	str r1, [r8, #52]
	str r0, [r8, #120]
	str r1, [r8, #56]
	str r0, [r8, #124]
	str r1, [r8, #60]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	mov r0, #0
	strb r0, [r11, #2288]
	ldr r0, [r5, #0]
	str r0, [r11, #2289]
	ldr r0, [r5, #4]
	str r0, [r11, #2293]
	ldr r0, [r5, #8]
	str r0, [r11, #2297]
	ldr r0, [r5, #12]
	str r0, [r11, #2301]
	ldr r0, [r5, #16]
	str r0, [r11, #2305]
	ldr r0, [r5, #20]
	str r0, [r11, #2309]
	ldr r0, [r8, #128]
	str r0, [r11, #2313]
	ldr r0, [r8, #132]
	str r0, [r11, #2317]
	ldr r0, [r8, #136]
	str r0, [r11, #2321]
	ldr r0, [r8, #140]
	str r0, [r11, #2325]
	ldr r0, [r8, #144]
	str r0, [r11, #2329]
	ldr r0, [r8, #148]
	str r0, [r11, #2333]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #81
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #209
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	mov r0, #1
	strb r0, [r11, #2288]
	ldr r0, [r5, #0]
	str r0, [r11, #2289]
	ldr r0, [r5, #4]
	str r0, [r11, #2293]
	ldr r0, [r5, #8]
	str r0, [r11, #2297]
	ldr r0, [r5, #12]
	str r0, [r11, #2301]
	ldr r0, [r5, #16]
	str r0, [r11, #2305]
	ldr r0, [r5, #20]
	str r0, [r11, #2309]
	ldr r0, [r8, #128]
	str r0, [r11, #2313]
	ldr r0, [r8, #132]
	str r0, [r11, #2317]
	ldr r0, [r8, #136]
	str r0, [r11, #2321]
	ldr r0, [r8, #140]
	str r0, [r11, #2325]
	ldr r0, [r8, #144]
	str r0, [r11, #2329]
	ldr r0, [r8, #148]
	str r0, [r11, #2333]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #81
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #209
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	movw r9, #8
214:
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r8, #176]
	mov r1, r5
	mov r2, r6
	add r3, r8, #64
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_p192_sign_k}
	ldr r12, [sp], #8
	sub r9, r9, #1
	subs r10, r0, #1
	mov r10, #0
	adc r10, r10, #0
	sub r10, r10, #1
	and r7, r10, r9
	cmp r7, #0
	bne 215f
	mov r7, #0
	cmp r7, #0
	b 216f
215:
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	mov r0, #0
	strb r0, [r11, #2288]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #33
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #161
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #160
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	mov r7, #1
	cmp r7, #0
216:
	bne 214b
	mov r12, r8
	mov r1, #0
	str r1, [r12, #0]
	str r1, [r12, #4]
	str r1, [r12, #8]
	str r1, [r12, #12]
	str r1, [r12, #16]
	str r1, [r12, #20]
	str r1, [r12, #24]
	str r1, [r12, #28]
	str r1, [r12, #32]
	str r1, [r12, #36]
	str r1, [r12, #40]
	str r1, [r12, #44]
	str r1, [r12, #48]
	str r1, [r12, #52]
	str r1, [r12, #56]
	str r1, [r12, #60]
	str r1, [r12, #64]
	str r1, [r12, #68]
	str r1, [r12, #72]
	str r1, [r12, #76]
	str r1, [r12, #80]
	str r1, [r12, #84]
	str r1, [r12, #88]
	str r1, [r12, #92]
	str r1, [r12, #96]
	str r1, [r12, #100]
	str r1, [r12, #104]
	str r1, [r12, #108]
	str r1, [r12, #112]
	str r1, [r12, #116]
	str r1, [r12, #120]
	str r1, [r12, #124]
	str r1, [r12, #128]
	str r1, [r12, #132]
	str r1, [r12, #136]
	str r1, [r12, #140]
	str r1, [r12, #144]
	str r1, [r12, #148]
	str r1, [r12, #152]
	str r1, [r12, #156]
	str r1, [r12, #160]
	str r1, [r12, #164]
	str r1, [r12, #168]
	str r1, [r12, #172]
	ldr r4, [r12, #180]
	ldr r5, [r12, #184]
	ldr r6, [r12, #188]
	ldr r7, [r12, #192]
	ldr r9, [r12, #196]
	ldr r10, [r12, #200]
	ldr r11, [r12, #204]
	ldr lr, [r12, #208]
	ldr r8, [r12, #212]
	add sp, sp, #216
	b 213f
212:
	sub sp, sp, #216
	add r12, sp, #0
	str r4, [r12, #180]
	str r5, [r12, #184]
	str r6, [r12, #188]
	str r7, [r12, #192]
	str r9, [r12, #196]
	str r10, [r12, #200]
	str r11, [r12, #204]
	str lr, [r12, #208]
	str r8, [r12, #212]
	ldr r4, [r12, #220]
	str r0, [r12, #176]
	mov r5, r1
	mov r6, r2
	ldr r11, [r12, #216]
	mov r8, r12
	movw r10, #65535
	mov r7, #1
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #10289
	movt r1, #46290
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #20]
	ldr r0, [r6, #16]
	rev r0, r0
	str r0, [r8, #144]
	movw r1, #51633
	movt r1, #5227
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #16]
	ldr r0, [r6, #12]
	rev r0, r0
	str r0, [r8, #140]
	movw r1, #63542
	movt r1, #39390
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #12]
	ldr r0, [r6, #8]
	rev r0, r0
	str r0, [r8, #136]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #8]
	ldr r0, [r6, #4]
	rev r0, r0
	str r0, [r8, #132]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #4]
	ldr r0, [r6, #0]
	rev r0, r0
	str r0, [r8, #128]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #0]
	mov r12, #0
	sub r7, r12, r7
	ldr r0, [r8, #148]
	ldr r1, [r8, #20]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #148]
	ldr r0, [r8, #144]
	ldr r1, [r8, #16]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #144]
	ldr r0, [r8, #140]
	ldr r1, [r8, #12]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #140]
	ldr r0, [r8, #136]
	ldr r1, [r8, #8]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #136]
	ldr r0, [r8, #132]
	ldr r1, [r8, #4]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #132]
	ldr r0, [r8, #128]
	ldr r1, [r8, #0]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #128]
	movw r0, #257
	movt r0, #257
	mov r1, #0
	str r0, [r8, #64]
	str r1, [r8, #0]
	str r0, [r8, #68]
	str r1, [r8, #4]
	str r0, [r8, #72]
	str r1, [r8, #8]
	str r0, [r8, #76]
	str r1, [r8, #12]
	str r0, [r8, #80]
	str r1, [r8, #16]
	str r0, [r8, #84]
	str r1, [r8, #20]
	str r0, [r8, #88]
	str r1, [r8, #24]
	str r0, [r8, #92]
	str r1, [r8, #28]
	str r0, [r8, #96]
	str r1, [r8, #32]
	str r0, [r8, #100]
	str r1, [r8, #36]
	str r0, [r8, #104]
	str r1, [r8, #40]
	str r0, [r8, #108]
	str r1, [r8, #44]
	str r0, [r8, #112]
	str r1, [r8, #48]
	str r0, [r8, #116]
	str r1, [r8, #52]
	str r0, [r8, #120]
	str r1, [r8, #56]
	str r0, [r8, #124]
	str r1, [r8, #60]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	mov r0, #0
	strb r0, [r11, #2284]
	ldr r0, [r5, #0]
	str r0, [r11, #2285]
	ldr r0, [r5, #4]
	str r0, [r11, #2289]
	ldr r0, [r5, #8]
	str r0, [r11, #2293]
	ldr r0, [r5, #12]
	str r0, [r11, #2297]
	ldr r0, [r5, #16]
	str r0, [r11, #2301]
	ldr r0, [r5, #20]
	str r0, [r11, #2305]
	ldr r0, [r8, #128]
	str r0, [r11, #2309]
	ldr r0, [r8, #132]
	str r0, [r11, #2313]
	ldr r0, [r8, #136]
	str r0, [r11, #2317]
	ldr r0, [r8, #140]
	str r0, [r11, #2321]
	ldr r0, [r8, #144]
	str r0, [r11, #2325]
	ldr r0, [r8, #148]
	str r0, [r11, #2329]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #77
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #205
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	mov r0, #1
	strb r0, [r11, #2284]
	ldr r0, [r5, #0]
	str r0, [r11, #2285]
	ldr r0, [r5, #4]
	str r0, [r11, #2289]
	ldr r0, [r5, #8]
	str r0, [r11, #2293]
	ldr r0, [r5, #12]
	str r0, [r11, #2297]
	ldr r0, [r5, #16]
	str r0, [r11, #2301]
	ldr r0, [r5, #20]
	str r0, [r11, #2305]
	ldr r0, [r8, #128]
	str r0, [r11, #2309]
	ldr r0, [r8, #132]
	str r0, [r11, #2313]
	ldr r0, [r8, #136]
	str r0, [r11, #2317]
	ldr r0, [r8, #140]
	str r0, [r11, #2321]
	ldr r0, [r8, #144]
	str r0, [r11, #2325]
	ldr r0, [r8, #148]
	str r0, [r11, #2329]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #77
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #205
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	movw r9, #8
217:
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r8, #176]
	mov r1, r5
	mov r2, r6
	add r3, r8, #64
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_p192_sign_k}
	ldr r12, [sp], #8
	sub r9, r9, #1
	subs r10, r0, #1
	mov r10, #0
	adc r10, r10, #0
	sub r10, r10, #1
	and r7, r10, r9
	cmp r7, #0
	bne 218f
	mov r7, #0
	cmp r7, #0
	b 219f
218:
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	mov r0, #0
	strb r0, [r11, #2284]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #29
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #157
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #156
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	mov r7, #1
	cmp r7, #0
219:
	bne 217b
	mov r12, r8
	mov r1, #0
	str r1, [r12, #0]
	str r1, [r12, #4]
	str r1, [r12, #8]
	str r1, [r12, #12]
	str r1, [r12, #16]
	str r1, [r12, #20]
	str r1, [r12, #24]
	str r1, [r12, #28]
	str r1, [r12, #32]
	str r1, [r12, #36]
	str r1, [r12, #40]
	str r1, [r12, #44]
	str r1, [r12, #48]
	str r1, [r12, #52]
	str r1, [r12, #56]
	str r1, [r12, #60]
	str r1, [r12, #64]
	str r1, [r12, #68]
	str r1, [r12, #72]
	str r1, [r12, #76]
	str r1, [r12, #80]
	str r1, [r12, #84]
	str r1, [r12, #88]
	str r1, [r12, #92]
	str r1, [r12, #96]
	str r1, [r12, #100]
	str r1, [r12, #104]
	str r1, [r12, #108]
	str r1, [r12, #112]
	str r1, [r12, #116]
	str r1, [r12, #120]
	str r1, [r12, #124]
	str r1, [r12, #128]
	str r1, [r12, #132]
	str r1, [r12, #136]
	str r1, [r12, #140]
	str r1, [r12, #144]
	str r1, [r12, #148]
	str r1, [r12, #152]
	str r1, [r12, #156]
	str r1, [r12, #160]
	str r1, [r12, #164]
	str r1, [r12, #168]
	str r1, [r12, #172]
	ldr r4, [r12, #180]
	ldr r5, [r12, #184]
	ldr r6, [r12, #188]
	ldr r7, [r12, #192]
	ldr r9, [r12, #196]
	ldr r10, [r12, #200]
	ldr r11, [r12, #204]
	ldr lr, [r12, #208]
	ldr r8, [r12, #212]
	add sp, sp, #216
213:
	b 211f
210:
	sub sp, sp, #216
	add r12, sp, #0
	str r4, [r12, #180]
	str r5, [r12, #184]
	str r6, [r12, #188]
	str r7, [r12, #192]
	str r9, [r12, #196]
	str r10, [r12, #200]
	str r11, [r12, #204]
	str lr, [r12, #208]
	str r8, [r12, #212]
	ldr r4, [r12, #220]
	str r0, [r12, #176]
	mov r5, r1
	mov r6, r2
	ldr r11, [r12, #216]
	mov r8, r12
	movw r10, #65535
	mov r7, #1
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #10289
	movt r1, #46290
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #20]
	ldr r0, [r6, #16]
	rev r0, r0
	str r0, [r8, #144]
	movw r1, #51633
	movt r1, #5227
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #16]
	ldr r0, [r6, #12]
	rev r0, r0
	str r0, [r8, #140]
	movw r1, #63542
	movt r1, #39390
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #12]
	ldr r0, [r6, #8]
	rev r0, r0
	str r0, [r8, #136]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #8]
	ldr r0, [r6, #4]
	rev r0, r0
	str r0, [r8, #132]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #4]
	ldr r0, [r6, #0]
	rev r0, r0
	str r0, [r8, #128]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #0]
	mov r12, #0
	sub r7, r12, r7
	ldr r0, [r8, #148]
	ldr r1, [r8, #20]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #148]
	ldr r0, [r8, #144]
	ldr r1, [r8, #16]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #144]
	ldr r0, [r8, #140]
	ldr r1, [r8, #12]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #140]
	ldr r0, [r8, #136]
	ldr r1, [r8, #8]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #136]
	ldr r0, [r8, #132]
	ldr r1, [r8, #4]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #132]
	ldr r0, [r8, #128]
	ldr r1, [r8, #0]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #128]
	movw r0, #257
	movt r0, #257
	mov r1, #0
	str r0, [r8, #64]
	str r1, [r8, #0]
	str r0, [r8, #68]
	str r1, [r8, #4]
	str r0, [r8, #72]
	str r1, [r8, #8]
	str r0, [r8, #76]
	str r1, [r8, #12]
	str r0, [r8, #80]
	str r1, [r8, #16]
	str r0, [r8, #84]
	str r1, [r8, #20]
	str r0, [r8, #88]
	str r1, [r8, #24]
	str r0, [r8, #92]
	str r1, [r8, #28]
	str r0, [r8, #96]
	str r1, [r8, #32]
	str r0, [r8, #100]
	str r1, [r8, #36]
	str r0, [r8, #104]
	str r1, [r8, #40]
	str r0, [r8, #108]
	str r1, [r8, #44]
	str r0, [r8, #112]
	str r1, [r8, #48]
	str r0, [r8, #116]
	str r1, [r8, #52]
	str r0, [r8, #120]
	str r1, [r8, #56]
	str r0, [r8, #124]
	str r1, [r8, #60]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	ldr r0, [r8, #96]
	str r0, [r11, #2288]
	ldr r0, [r8, #100]
	str r0, [r11, #2292]
	ldr r0, [r8, #104]
	str r0, [r11, #2296]
	ldr r0, [r8, #108]
	str r0, [r11, #2300]
	ldr r0, [r8, #112]
	str r0, [r11, #2304]
	ldr r0, [r8, #116]
	str r0, [r11, #2308]
	ldr r0, [r8, #120]
	str r0, [r11, #2312]
	ldr r0, [r8, #124]
	str r0, [r11, #2316]
	mov r0, #0
	strb r0, [r11, #2320]
	ldr r0, [r5, #0]
	str r0, [r11, #2321]
	ldr r0, [r5, #4]
	str r0, [r11, #2325]
	ldr r0, [r5, #8]
	str r0, [r11, #2329]
	ldr r0, [r5, #12]
	str r0, [r11, #2333]
	ldr r0, [r5, #16]
	str r0, [r11, #2337]
	ldr r0, [r5, #20]
	str r0, [r11, #2341]
	ldr r0, [r8, #128]
	str r0, [r11, #2345]
	ldr r0, [r8, #132]
	str r0, [r11, #2349]
	ldr r0, [r8, #136]
	str r0, [r11, #2353]
	ldr r0, [r8, #140]
	str r0, [r11, #2357]
	ldr r0, [r8, #144]
	str r0, [r11, #2361]
	ldr r0, [r8, #148]
	str r0, [r11, #2365]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #113
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #241
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	ldr r0, [r11, #1952]
	str r0, [r8, #32]
	ldr r0, [r11, #1956]
	str r0, [r8, #36]
	ldr r0, [r11, #1960]
	str r0, [r8, #40]
	ldr r0, [r11, #1964]
	str r0, [r8, #44]
	ldr r0, [r11, #1968]
	str r0, [r8, #48]
	ldr r0, [r11, #1972]
	str r0, [r8, #52]
	ldr r0, [r11, #1976]
	str r0, [r8, #56]
	ldr r0, [r11, #1980]
	str r0, [r8, #60]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r11, #1952]
	str r0, [r8, #96]
	ldr r0, [r11, #1956]
	str r0, [r8, #100]
	ldr r0, [r11, #1960]
	str r0, [r8, #104]
	ldr r0, [r11, #1964]
	str r0, [r8, #108]
	ldr r0, [r11, #1968]
	str r0, [r8, #112]
	ldr r0, [r11, #1972]
	str r0, [r8, #116]
	ldr r0, [r11, #1976]
	str r0, [r8, #120]
	ldr r0, [r11, #1980]
	str r0, [r8, #124]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	ldr r0, [r8, #96]
	str r0, [r11, #2288]
	ldr r0, [r8, #100]
	str r0, [r11, #2292]
	ldr r0, [r8, #104]
	str r0, [r11, #2296]
	ldr r0, [r8, #108]
	str r0, [r11, #2300]
	ldr r0, [r8, #112]
	str r0, [r11, #2304]
	ldr r0, [r8, #116]
	str r0, [r11, #2308]
	ldr r0, [r8, #120]
	str r0, [r11, #2312]
	ldr r0, [r8, #124]
	str r0, [r11, #2316]
	mov r0, #1
	strb r0, [r11, #2320]
	ldr r0, [r5, #0]
	str r0, [r11, #2321]
	ldr r0, [r5, #4]
	str r0, [r11, #2325]
	ldr r0, [r5, #8]
	str r0, [r11, #2329]
	ldr r0, [r5, #12]
	str r0, [r11, #2333]
	ldr r0, [r5, #16]
	str r0, [r11, #2337]
	ldr r0, [r5, #20]
	str r0, [r11, #2341]
	ldr r0, [r8, #128]
	str r0, [r11, #2345]
	ldr r0, [r8, #132]
	str r0, [r11, #2349]
	ldr r0, [r8, #136]
	str r0, [r11, #2353]
	ldr r0, [r8, #140]
	str r0, [r11, #2357]
	ldr r0, [r8, #144]
	str r0, [r11, #2361]
	ldr r0, [r8, #148]
	str r0, [r11, #2365]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #113
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #241
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	ldr r0, [r11, #1952]
	str r0, [r8, #32]
	ldr r0, [r11, #1956]
	str r0, [r8, #36]
	ldr r0, [r11, #1960]
	str r0, [r8, #40]
	ldr r0, [r11, #1964]
	str r0, [r8, #44]
	ldr r0, [r11, #1968]
	str r0, [r8, #48]
	ldr r0, [r11, #1972]
	str r0, [r8, #52]
	ldr r0, [r11, #1976]
	str r0, [r8, #56]
	ldr r0, [r11, #1980]
	str r0, [r8, #60]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r11, #1952]
	str r0, [r8, #96]
	ldr r0, [r11, #1956]
	str r0, [r8, #100]
	ldr r0, [r11, #1960]
	str r0, [r8, #104]
	ldr r0, [r11, #1964]
	str r0, [r8, #108]
	ldr r0, [r11, #1968]
	str r0, [r8, #112]
	ldr r0, [r11, #1972]
	str r0, [r8, #116]
	ldr r0, [r11, #1976]
	str r0, [r8, #120]
	ldr r0, [r11, #1980]
	str r0, [r8, #124]
	movw r9, #8
220:
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r11, #1952]
	str r0, [r8, #96]
	ldr r0, [r11, #1956]
	str r0, [r8, #100]
	ldr r0, [r11, #1960]
	str r0, [r8, #104]
	ldr r0, [r11, #1964]
	str r0, [r8, #108]
	ldr r0, [r11, #1968]
	str r0, [r8, #112]
	ldr r0, [r11, #1972]
	str r0, [r8, #116]
	ldr r0, [r11, #1976]
	str r0, [r8, #120]
	ldr r0, [r11, #1980]
	str r0, [r8, #124]
	ldr r0, [r8, #176]
	mov r1, r5
	mov r2, r6
	add r3, r8, #64
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_p192_sign_k}
	ldr r12, [sp], #8
	sub r9, r9, #1
	subs r10, r0, #1
	mov r10, #0
	adc r10, r10, #0
	sub r10, r10, #1
	and r7, r10, r9
	cmp r7, #0
	bne 221f
	mov r7, #0
	cmp r7, #0
	b 222f
221:
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	ldr r0, [r8, #96]
	str r0, [r11, #2288]
	ldr r0, [r8, #100]
	str r0, [r11, #2292]
	ldr r0, [r8, #104]
	str r0, [r11, #2296]
	ldr r0, [r8, #108]
	str r0, [r11, #2300]
	ldr r0, [r8, #112]
	str r0, [r11, #2304]
	ldr r0, [r8, #116]
	str r0, [r11, #2308]
	ldr r0, [r8, #120]
	str r0, [r11, #2312]
	ldr r0, [r8, #124]
	str r0, [r11, #2316]
	mov r0, #0
	strb r0, [r11, #2320]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #65
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #193
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	ldr r0, [r11, #1952]
	str r0, [r8, #32]
	ldr r0, [r11, #1956]
	str r0, [r8, #36]
	ldr r0, [r11, #1960]
	str r0, [r8, #40]
	ldr r0, [r11, #1964]
	str r0, [r8, #44]
	ldr r0, [r11, #1968]
	str r0, [r8, #48]
	ldr r0, [r11, #1972]
	str r0, [r8, #52]
	ldr r0, [r11, #1976]
	str r0, [r8, #56]
	ldr r0, [r11, #1980]
	str r0, [r8, #60]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	ldr r0, [r8, #48]
	eor r0, r0, r1
	str r0, [r11, #1840]
	ldr r0, [r8, #52]
	eor r0, r0, r1
	str r0, [r11, #1844]
	ldr r0, [r8, #56]
	eor r0, r0, r1
	str r0, [r11, #1848]
	ldr r0, [r8, #60]
	eor r0, r0, r1
	str r0, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #192
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r11, #1952]
	str r0, [r8, #96]
	ldr r0, [r11, #1956]
	str r0, [r8, #100]
	ldr r0, [r11, #1960]
	str r0, [r8, #104]
	ldr r0, [r11, #1964]
	str r0, [r8, #108]
	ldr r0, [r11, #1968]
	str r0, [r8, #112]
	ldr r0, [r11, #1972]
	str r0, [r8, #116]
	ldr r0, [r11, #1976]
	str r0, [r8, #120]
	ldr r0, [r11, #1980]
	str r0, [r8, #124]
	mov r7, #1
	cmp r7, #0
222:
	bne 220b
	mov r12, r8
	mov r1, #0
	str r1, [r12, #0]
	str r1, [r12, #4]
	str r1, [r12, #8]
	str r1, [r12, #12]
	str r1, [r12, #16]
	str r1, [r12, #20]
	str r1, [r12, #24]
	str r1, [r12, #28]
	str r1, [r12, #32]
	str r1, [r12, #36]
	str r1, [r12, #40]
	str r1, [r12, #44]
	str r1, [r12, #48]
	str r1, [r12, #52]
	str r1, [r12, #56]
	str r1, [r12, #60]
	str r1, [r12, #64]
	str r1, [r12, #68]
	str r1, [r12, #72]
	str r1, [r12, #76]
	str r1, [r12, #80]
	str r1, [r12, #84]
	str r1, [r12, #88]
	str r1, [r12, #92]
	str r1, [r12, #96]
	str r1, [r12, #100]
	str r1, [r12, #104]
	str r1, [r12, #108]
	str r1, [r12, #112]
	str r1, [r12, #116]
	str r1, [r12, #120]
	str r1, [r12, #124]
	str r1, [r12, #128]
	str r1, [r12, #132]
	str r1, [r12, #136]
	str r1, [r12, #140]
	str r1, [r12, #144]
	str r1, [r12, #148]
	str r1, [r12, #152]
	str r1, [r12, #156]
	str r1, [r12, #160]
	str r1, [r12, #164]
	str r1, [r12, #168]
	str r1, [r12, #172]
	ldr r4, [r12, #180]
	ldr r5, [r12, #184]
	ldr r6, [r12, #188]
	ldr r7, [r12, #192]
	ldr r9, [r12, #196]
	ldr r10, [r12, #200]
	ldr r11, [r12, #204]
	ldr lr, [r12, #208]
	ldr r8, [r12, #212]
	add sp, sp, #216
211:
	b 29f
28:
	sub sp, sp, #216
	add r12, sp, #0
	str r4, [r12, #180]
	str r5, [r12, #184]
	str r6, [r12, #188]
	str r7, [r12, #192]
	str r9, [r12, #196]
	str r10, [r12, #200]
	str r11, [r12, #204]
	str lr, [r12, #208]
	str r8, [r12, #212]
	ldr r4, [r12, #220]
	str r0, [r12, #176]
	mov r5, r1
	mov r6, r2
	ldr r11, [r12, #216]
	mov r8, r12
	movw r10, #65535
	mov r7, #1
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #10289
	movt r1, #46290
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #20]
	ldr r0, [r6, #16]
	rev r0, r0
	str r0, [r8, #144]
	movw r1, #51633
	movt r1, #5227
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #16]
	ldr r0, [r6, #12]
	rev r0, r0
	str r0, [r8, #140]
	movw r1, #63542
	movt r1, #39390
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #12]
	ldr r0, [r6, #8]
	rev r0, r0
	str r0, [r8, #136]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #8]
	ldr r0, [r6, #4]
	rev r0, r0
	str r0, [r8, #132]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #4]
	ldr r0, [r6, #0]
	rev r0, r0
	str r0, [r8, #128]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #0]
	mov r12, #0
	sub r7, r12, r7
	ldr r0, [r8, #148]
	ldr r1, [r8, #20]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #148]
	ldr r0, [r8, #144]
	ldr r1, [r8, #16]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #144]
	ldr r0, [r8, #140]
	ldr r1, [r8, #12]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #140]
	ldr r0, [r8, #136]
	ldr r1, [r8, #8]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #136]
	ldr r0, [r8, #132]
	ldr r1, [r8, #4]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #132]
	ldr r0, [r8, #128]
	ldr r1, [r8, #0]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #128]
	movw r0, #257
	movt r0, #257
	mov r1, #0
	str r0, [r8, #64]
	str r1, [r8, #0]
	str r0, [r8, #68]
	str r1, [r8, #4]
	str r0, [r8, #72]
	str r1, [r8, #8]
	str r0, [r8, #76]
	str r1, [r8, #12]
	str r0, [r8, #80]
	str r1, [r8, #16]
	str r0, [r8, #84]
	str r1, [r8, #20]
	str r0, [r8, #88]
	str r1, [r8, #24]
	str r0, [r8, #92]
	str r1, [r8, #28]
	str r0, [r8, #96]
	str r1, [r8, #32]
	str r0, [r8, #100]
	str r1, [r8, #36]
	str r0, [r8, #104]
	str r1, [r8, #40]
	str r0, [r8, #108]
	str r1, [r8, #44]
	str r0, [r8, #112]
	str r1, [r8, #48]
	str r0, [r8, #116]
	str r1, [r8, #52]
	str r0, [r8, #120]
	str r1, [r8, #56]
	str r0, [r8, #124]
	str r1, [r8, #60]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	ldr r0, [r8, #96]
	str r0, [r11, #2288]
	ldr r0, [r8, #100]
	str r0, [r11, #2292]
	ldr r0, [r8, #104]
	str r0, [r11, #2296]
	ldr r0, [r8, #108]
	str r0, [r11, #2300]
	mov r0, #0
	strb r0, [r11, #2304]
	ldr r0, [r5, #0]
	str r0, [r11, #2305]
	ldr r0, [r5, #4]
	str r0, [r11, #2309]
	ldr r0, [r5, #8]
	str r0, [r11, #2313]
	ldr r0, [r5, #12]
	str r0, [r11, #2317]
	ldr r0, [r5, #16]
	str r0, [r11, #2321]
	ldr r0, [r5, #20]
	str r0, [r11, #2325]
	ldr r0, [r8, #128]
	str r0, [r11, #2329]
	ldr r0, [r8, #132]
	str r0, [r11, #2333]
	ldr r0, [r8, #136]
	str r0, [r11, #2337]
	ldr r0, [r8, #140]
	str r0, [r11, #2341]
	ldr r0, [r8, #144]
	str r0, [r11, #2345]
	ldr r0, [r8, #148]
	str r0, [r11, #2349]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #97
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #225
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	ldr r0, [r11, #1952]
	str r0, [r8, #32]
	ldr r0, [r11, #1956]
	str r0, [r8, #36]
	ldr r0, [r11, #1960]
	str r0, [r8, #40]
	ldr r0, [r11, #1964]
	str r0, [r8, #44]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r11, #1952]
	str r0, [r8, #96]
	ldr r0, [r11, #1956]
	str r0, [r8, #100]
	ldr r0, [r11, #1960]
	str r0, [r8, #104]
	ldr r0, [r11, #1964]
	str r0, [r8, #108]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	ldr r0, [r8, #96]
	str r0, [r11, #2288]
	ldr r0, [r8, #100]
	str r0, [r11, #2292]
	ldr r0, [r8, #104]
	str r0, [r11, #2296]
	ldr r0, [r8, #108]
	str r0, [r11, #2300]
	mov r0, #1
	strb r0, [r11, #2304]
	ldr r0, [r5, #0]
	str r0, [r11, #2305]
	ldr r0, [r5, #4]
	str r0, [r11, #2309]
	ldr r0, [r5, #8]
	str r0, [r11, #2313]
	ldr r0, [r5, #12]
	str r0, [r11, #2317]
	ldr r0, [r5, #16]
	str r0, [r11, #2321]
	ldr r0, [r5, #20]
	str r0, [r11, #2325]
	ldr r0, [r8, #128]
	str r0, [r11, #2329]
	ldr r0, [r8, #132]
	str r0, [r11, #2333]
	ldr r0, [r8, #136]
	str r0, [r11, #2337]
	ldr r0, [r8, #140]
	str r0, [r11, #2341]
	ldr r0, [r8, #144]
	str r0, [r11, #2345]
	ldr r0, [r8, #148]
	str r0, [r11, #2349]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #97
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #225
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	ldr r0, [r11, #1952]
	str r0, [r8, #32]
	ldr r0, [r11, #1956]
	str r0, [r8, #36]
	ldr r0, [r11, #1960]
	str r0, [r8, #40]
	ldr r0, [r11, #1964]
	str r0, [r8, #44]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r11, #1952]
	str r0, [r8, #96]
	ldr r0, [r11, #1956]
	str r0, [r8, #100]
	ldr r0, [r11, #1960]
	str r0, [r8, #104]
	ldr r0, [r11, #1964]
	str r0, [r8, #108]
	movw r9, #8
223:
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r11, #1952]
	str r0, [r8, #96]
	ldr r0, [r11, #1956]
	str r0, [r8, #100]
	ldr r0, [r11, #1960]
	str r0, [r8, #104]
	ldr r0, [r11, #1964]
	str r0, [r8, #108]
	ldr r0, [r8, #176]
	mov r1, r5
	mov r2, r6
	add r3, r8, #64
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_p192_sign_k}
	ldr r12, [sp], #8
	sub r9, r9, #1
	subs r10, r0, #1
	mov r10, #0
	adc r10, r10, #0
	sub r10, r10, #1
	and r7, r10, r9
	cmp r7, #0
	bne 224f
	mov r7, #0
	cmp r7, #0
	b 225f
224:
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	ldr r0, [r8, #96]
	str r0, [r11, #2288]
	ldr r0, [r8, #100]
	str r0, [r11, #2292]
	ldr r0, [r8, #104]
	str r0, [r11, #2296]
	ldr r0, [r8, #108]
	str r0, [r11, #2300]
	mov r0, #0
	strb r0, [r11, #2304]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #49
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #177
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	ldr r0, [r11, #1952]
	str r0, [r8, #32]
	ldr r0, [r11, #1956]
	str r0, [r8, #36]
	ldr r0, [r11, #1960]
	str r0, [r8, #40]
	ldr r0, [r11, #1964]
	str r0, [r8, #44]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	ldr r0, [r8, #32]
	eor r0, r0, r1
	str r0, [r11, #1824]
	ldr r0, [r8, #36]
	eor r0, r0, r1
	str r0, [r11, #1828]
	ldr r0, [r8, #40]
	eor r0, r0, r1
	str r0, [r11, #1832]
	ldr r0, [r8, #44]
	eor r0, r0, r1
	str r0, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	str r1, [r11, #1856]
	str r1, [r11, #1860]
	str r1, [r11, #1864]
	str r1, [r11, #1868]
	str r1, [r11, #1872]
	str r1, [r11, #1876]
	str r1, [r11, #1880]
	str r1, [r11, #1884]
	str r1, [r11, #1888]
	str r1, [r11, #1892]
	str r1, [r11, #1896]
	str r1, [r11, #1900]
	str r1, [r11, #1904]
	str r1, [r11, #1908]
	str r1, [r11, #1912]
	str r1, [r11, #1916]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #128
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #128
	mov r3, #0
	movw r7, #48
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #176
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r11, #1952]
	str r0, [r8, #96]
	ldr r0, [r11, #1956]
	str r0, [r8, #100]
	ldr r0, [r11, #1960]
	str r0, [r8, #104]
	ldr r0, [r11, #1964]
	str r0, [r8, #108]
	mov r7, #1
	cmp r7, #0
225:
	bne 223b
	mov r12, r8
	mov r1, #0
	str r1, [r12, #0]
	str r1, [r12, #4]
	str r1, [r12, #8]
	str r1, [r12, #12]
	str r1, [r12, #16]
	str r1, [r12, #20]
	str r1, [r12, #24]
	str r1, [r12, #28]
	str r1, [r12, #32]
	str r1, [r12, #36]
	str r1, [r12, #40]
	str r1, [r12, #44]
	str r1, [r12, #48]
	str r1, [r12, #52]
	str r1, [r12, #56]
	str r1, [r12, #60]
	str r1, [r12, #64]
	str r1, [r12, #68]
	str r1, [r12, #72]
	str r1, [r12, #76]
	str r1, [r12, #80]
	str r1, [r12, #84]
	str r1, [r12, #88]
	str r1, [r12, #92]
	str r1, [r12, #96]
	str r1, [r12, #100]
	str r1, [r12, #104]
	str r1, [r12, #108]
	str r1, [r12, #112]
	str r1, [r12, #116]
	str r1, [r12, #120]
	str r1, [r12, #124]
	str r1, [r12, #128]
	str r1, [r12, #132]
	str r1, [r12, #136]
	str r1, [r12, #140]
	str r1, [r12, #144]
	str r1, [r12, #148]
	str r1, [r12, #152]
	str r1, [r12, #156]
	str r1, [r12, #160]
	str r1, [r12, #164]
	str r1, [r12, #168]
	str r1, [r12, #172]
	ldr r4, [r12, #180]
	ldr r5, [r12, #184]
	ldr r6, [r12, #188]
	ldr r7, [r12, #192]
	ldr r9, [r12, #196]
	ldr r10, [r12, #200]
	ldr r11, [r12, #204]
	ldr lr, [r12, #208]
	ldr r8, [r12, #212]
	add sp, sp, #216
29:
	b 27f
26:
	sub sp, sp, #216
	add r12, sp, #0
	str r4, [r12, #180]
	str r5, [r12, #184]
	str r6, [r12, #188]
	str r7, [r12, #192]
	str r9, [r12, #196]
	str r10, [r12, #200]
	str r11, [r12, #204]
	str lr, [r12, #208]
	str r8, [r12, #212]
	ldr r4, [r12, #220]
	str r0, [r12, #176]
	mov r5, r1
	mov r6, r2
	ldr r11, [r12, #216]
	mov r8, r12
	movw r10, #65535
	mov r7, #1
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #10289
	movt r1, #46290
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #20]
	ldr r0, [r6, #16]
	rev r0, r0
	str r0, [r8, #144]
	movw r1, #51633
	movt r1, #5227
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #16]
	ldr r0, [r6, #12]
	rev r0, r0
	str r0, [r8, #140]
	movw r1, #63542
	movt r1, #39390
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #12]
	ldr r0, [r6, #8]
	rev r0, r0
	str r0, [r8, #136]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #8]
	ldr r0, [r6, #4]
	rev r0, r0
	str r0, [r8, #132]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #4]
	ldr r0, [r6, #0]
	rev r0, r0
	str r0, [r8, #128]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #0]
	mov r12, #0
	sub r7, r12, r7
	ldr r0, [r8, #148]
	ldr r1, [r8, #20]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #148]
	ldr r0, [r8, #144]
	ldr r1, [r8, #16]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #144]
	ldr r0, [r8, #140]
	ldr r1, [r8, #12]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #140]
	ldr r0, [r8, #136]
	ldr r1, [r8, #8]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #136]
	ldr r0, [r8, #132]
	ldr r1, [r8, #4]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #132]
	ldr r0, [r8, #128]
	ldr r1, [r8, #0]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #128]
	movw r0, #257
	movt r0, #257
	mov r1, #0
	str r0, [r8, #64]
	str r1, [r8, #0]
	str r0, [r8, #68]
	str r1, [r8, #4]
	str r0, [r8, #72]
	str r1, [r8, #8]
	str r0, [r8, #76]
	str r1, [r8, #12]
	str r0, [r8, #80]
	str r1, [r8, #16]
	str r0, [r8, #84]
	str r1, [r8, #20]
	str r0, [r8, #88]
	str r1, [r8, #24]
	str r0, [r8, #92]
	str r1, [r8, #28]
	str r0, [r8, #96]
	str r1, [r8, #32]
	str r0, [r8, #100]
	str r1, [r8, #36]
	str r0, [r8, #104]
	str r1, [r8, #40]
	str r0, [r8, #108]
	str r1, [r8, #44]
	str r0, [r8, #112]
	str r1, [r8, #48]
	str r0, [r8, #116]
	str r1, [r8, #52]
	str r0, [r8, #120]
	str r1, [r8, #56]
	str r0, [r8, #124]
	str r1, [r8, #60]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	mov r0, #0
	strb r0, [r11, #2288]
	ldr r0, [r5, #0]
	str r0, [r11, #2289]
	ldr r0, [r5, #4]
	str r0, [r11, #2293]
	ldr r0, [r5, #8]
	str r0, [r11, #2297]
	ldr r0, [r5, #12]
	str r0, [r11, #2301]
	ldr r0, [r5, #16]
	str r0, [r11, #2305]
	ldr r0, [r5, #20]
	str r0, [r11, #2309]
	ldr r0, [r8, #128]
	str r0, [r11, #2313]
	ldr r0, [r8, #132]
	str r0, [r11, #2317]
	ldr r0, [r8, #136]
	str r0, [r11, #2321]
	ldr r0, [r8, #140]
	str r0, [r11, #2325]
	ldr r0, [r8, #144]
	str r0, [r11, #2329]
	ldr r0, [r8, #148]
	str r0, [r11, #2333]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #81
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #145
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	mov r0, #1
	strb r0, [r11, #2288]
	ldr r0, [r5, #0]
	str r0, [r11, #2289]
	ldr r0, [r5, #4]
	str r0, [r11, #2293]
	ldr r0, [r5, #8]
	str r0, [r11, #2297]
	ldr r0, [r5, #12]
	str r0, [r11, #2301]
	ldr r0, [r5, #16]
	str r0, [r11, #2305]
	ldr r0, [r5, #20]
	str r0, [r11, #2309]
	ldr r0, [r8, #128]
	str r0, [r11, #2313]
	ldr r0, [r8, #132]
	str r0, [r11, #2317]
	ldr r0, [r8, #136]
	str r0, [r11, #2321]
	ldr r0, [r8, #140]
	str r0, [r11, #2325]
	ldr r0, [r8, #144]
	str r0, [r11, #2329]
	ldr r0, [r8, #148]
	str r0, [r11, #2333]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #81
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #145
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	movw r9, #8
226:
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	ldr r0, [r8, #176]
	mov r1, r5
	mov r2, r6
	add r3, r8, #64
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_p192_sign_k}
	ldr r12, [sp], #8
	sub r9, r9, #1
	subs r10, r0, #1
	mov r10, #0
	adc r10, r10, #0
	sub r10, r10, #1
	and r7, r10, r9
	cmp r7, #0
	bne 227f
	mov r7, #0
	cmp r7, #0
	b 228f
227:
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	ldr r0, [r8, #92]
	str r0, [r11, #2284]
	mov r0, #0
	strb r0, [r11, #2288]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #33
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #97
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	ldr r0, [r11, #1948]
	str r0, [r8, #28]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	ldr r0, [r8, #28]
	eor r0, r0, r1
	str r0, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #32
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #96
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r11, #1948]
	str r0, [r8, #92]
	mov r7, #1
	cmp r7, #0
228:
	bne 226b
	mov r12, r8
	mov r1, #0
	str r1, [r12, #0]
	str r1, [r12, #4]
	str r1, [r12, #8]
	str r1, [r12, #12]
	str r1, [r12, #16]
	str r1, [r12, #20]
	str r1, [r12, #24]
	str r1, [r12, #28]
	str r1, [r12, #32]
	str r1, [r12, #36]
	str r1, [r12, #40]
	str r1, [r12, #44]
	str r1, [r12, #48]
	str r1, [r12, #52]
	str r1, [r12, #56]
	str r1, [r12, #60]
	str r1, [r12, #64]
	str r1, [r12, #68]
	str r1, [r12, #72]
	str r1, [r12, #76]
	str r1, [r12, #80]
	str r1, [r12, #84]
	str r1, [r12, #88]
	str r1, [r12, #92]
	str r1, [r12, #96]
	str r1, [r12, #100]
	str r1, [r12, #104]
	str r1, [r12, #108]
	str r1, [r12, #112]
	str r1, [r12, #116]
	str r1, [r12, #120]
	str r1, [r12, #124]
	str r1, [r12, #128]
	str r1, [r12, #132]
	str r1, [r12, #136]
	str r1, [r12, #140]
	str r1, [r12, #144]
	str r1, [r12, #148]
	str r1, [r12, #152]
	str r1, [r12, #156]
	str r1, [r12, #160]
	str r1, [r12, #164]
	str r1, [r12, #168]
	str r1, [r12, #172]
	ldr r4, [r12, #180]
	ldr r5, [r12, #184]
	ldr r6, [r12, #188]
	ldr r7, [r12, #192]
	ldr r9, [r12, #196]
	ldr r10, [r12, #200]
	ldr r11, [r12, #204]
	ldr lr, [r12, #208]
	ldr r8, [r12, #212]
	add sp, sp, #216
27:
	b 25f
24:
	sub sp, sp, #216
	add r12, sp, #0
	str r4, [r12, #180]
	str r5, [r12, #184]
	str r6, [r12, #188]
	str r7, [r12, #192]
	str r9, [r12, #196]
	str r10, [r12, #200]
	str r11, [r12, #204]
	str lr, [r12, #208]
	str r8, [r12, #212]
	ldr r4, [r12, #220]
	str r0, [r12, #176]
	mov r5, r1
	mov r6, r2
	ldr r11, [r12, #216]
	mov r8, r12
	movw r10, #65535
	mov r7, #1
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #10289
	movt r1, #46290
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #20]
	ldr r0, [r6, #16]
	rev r0, r0
	str r0, [r8, #144]
	movw r1, #51633
	movt r1, #5227
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #16]
	ldr r0, [r6, #12]
	rev r0, r0
	str r0, [r8, #140]
	movw r1, #63542
	movt r1, #39390
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #12]
	ldr r0, [r6, #8]
	rev r0, r0
	str r0, [r8, #136]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #8]
	ldr r0, [r6, #4]
	rev r0, r0
	str r0, [r8, #132]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #4]
	ldr r0, [r6, #0]
	rev r0, r0
	str r0, [r8, #128]
	movw r1, #65535
	movt r1, #65535
	and r2, r0, r10
	and r3, r1, r10
	add r2, r2, r10
	sub r2, r2, r3
	add r2, r2, r7
	lsr r7, r2, #16
	and r2, r2, r10
	lsr r3, r0, #16
	lsr r12, r1, #16
	add r3, r3, r10
	sub r3, r3, r12
	add r3, r3, r7
	lsr r7, r3, #16
	lsl r3, r3, #16
	orr r2, r2, r3
	str r2, [r8, #0]
	mov r12, #0
	sub r7, r12, r7
	ldr r0, [r8, #148]
	ldr r1, [r8, #20]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #148]
	ldr r0, [r8, #144]
	ldr r1, [r8, #16]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #144]
	ldr r0, [r8, #140]
	ldr r1, [r8, #12]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #140]
	ldr r0, [r8, #136]
	ldr r1, [r8, #8]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #136]
	ldr r0, [r8, #132]
	ldr r1, [r8, #4]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #132]
	ldr r0, [r8, #128]
	ldr r1, [r8, #0]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #128]
	movw r0, #257
	movt r0, #257
	mov r1, #0
	str r0, [r8, #64]
	str r1, [r8, #0]
	str r0, [r8, #68]
	str r1, [r8, #4]
	str r0, [r8, #72]
	str r1, [r8, #8]
	str r0, [r8, #76]
	str r1, [r8, #12]
	str r0, [r8, #80]
	str r1, [r8, #16]
	str r0, [r8, #84]
	str r1, [r8, #20]
	str r0, [r8, #88]
	str r1, [r8, #24]
	str r0, [r8, #92]
	str r1, [r8, #28]
	str r0, [r8, #96]
	str r1, [r8, #32]
	str r0, [r8, #100]
	str r1, [r8, #36]
	str r0, [r8, #104]
	str r1, [r8, #40]
	str r0, [r8, #108]
	str r1, [r8, #44]
	str r0, [r8, #112]
	str r1, [r8, #48]
	str r0, [r8, #116]
	str r1, [r8, #52]
	str r0, [r8, #120]
	str r1, [r8, #56]
	str r0, [r8, #124]
	str r1, [r8, #60]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	mov r0, #0
	strb r0, [r11, #2284]
	ldr r0, [r5, #0]
	str r0, [r11, #2285]
	ldr r0, [r5, #4]
	str r0, [r11, #2289]
	ldr r0, [r5, #8]
	str r0, [r11, #2293]
	ldr r0, [r5, #12]
	str r0, [r11, #2297]
	ldr r0, [r5, #16]
	str r0, [r11, #2301]
	ldr r0, [r5, #20]
	str r0, [r11, #2305]
	ldr r0, [r8, #128]
	str r0, [r11, #2309]
	ldr r0, [r8, #132]
	str r0, [r11, #2313]
	ldr r0, [r8, #136]
	str r0, [r11, #2317]
	ldr r0, [r8, #140]
	str r0, [r11, #2321]
	ldr r0, [r8, #144]
	str r0, [r11, #2325]
	ldr r0, [r8, #148]
	str r0, [r11, #2329]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #77
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #141
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	mov r0, #1
	strb r0, [r11, #2284]
	ldr r0, [r5, #0]
	str r0, [r11, #2285]
	ldr r0, [r5, #4]
	str r0, [r11, #2289]
	ldr r0, [r5, #8]
	str r0, [r11, #2293]
	ldr r0, [r5, #12]
	str r0, [r11, #2297]
	ldr r0, [r5, #16]
	str r0, [r11, #2301]
	ldr r0, [r5, #20]
	str r0, [r11, #2305]
	ldr r0, [r8, #128]
	str r0, [r11, #2309]
	ldr r0, [r8, #132]
	str r0, [r11, #2313]
	ldr r0, [r8, #136]
	str r0, [r11, #2317]
	ldr r0, [r8, #140]
	str r0, [r11, #2321]
	ldr r0, [r8, #144]
	str r0, [r11, #2325]
	ldr r0, [r8, #148]
	str r0, [r11, #2329]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #77
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #141
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	movw r9, #8
229:
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	ldr r0, [r8, #176]
	mov r1, r5
	mov r2, r6
	add r3, r8, #64
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_p192_sign_k}
	ldr r12, [sp], #8
	sub r9, r9, #1
	subs r10, r0, #1
	mov r10, #0
	adc r10, r10, #0
	sub r10, r10, #1
	and r7, r10, r9
	cmp r7, #0
	bne 230f
	mov r7, #0
	cmp r7, #0
	b 231f
230:
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	ldr r0, [r8, #84]
	str r0, [r11, #2276]
	ldr r0, [r8, #88]
	str r0, [r11, #2280]
	mov r0, #0
	strb r0, [r11, #2284]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #29
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #93
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	ldr r0, [r11, #1940]
	str r0, [r8, #20]
	ldr r0, [r11, #1944]
	str r0, [r8, #24]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	ldr r0, [r8, #20]
	eor r0, r0, r1
	str r0, [r11, #1812]
	ldr r0, [r8, #24]
	eor r0, r0, r1
	str r0, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #28
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #92
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r11, #1940]
	str r0, [r8, #84]
	ldr r0, [r11, #1944]
	str r0, [r8, #88]
	mov r7, #1
	cmp r7, #0
231:
	bne 229b
	mov r12, r8
	mov r1, #0
	str r1, [r12, #0]
	str r1, [r12, #4]
	str r1, [r12, #8]
	str r1, [r12, #12]
	str r1, [r12, #16]
	str r1, [r12, #20]
	str r1, [r12, #24]
	str r1, [r12, #28]
	str r1, [r12, #32]
	str r1, [r12, #36]
	str r1, [r12, #40]
	str r1, [r12, #44]
	str r1, [r12, #48]
	str r1, [r12, #52]
	str r1, [r12, #56]
	str r1, [r12, #60]
	str r1, [r12, #64]
	str r1, [r12, #68]
	str r1, [r12, #72]
	str r1, [r12, #76]
	str r1, [r12, #80]
	str r1, [r12, #84]
	str r1, [r12, #88]
	str r1, [r12, #92]
	str r1, [r12, #96]
	str r1, [r12, #100]
	str r1, [r12, #104]
	str r1, [r12, #108]
	str r1, [r12, #112]
	str r1, [r12, #116]
	str r1, [r12, #120]
	str r1, [r12, #124]
	str r1, [r12, #128]
	str r1, [r12, #132]
	str r1, [r12, #136]
	str r1, [r12, #140]
	str r1, [r12, #144]
	str r1, [r12, #148]
	str r1, [r12, #152]
	str r1, [r12, #156]
	str r1, [r12, #160]
	str r1, [r12, #164]
	str r1, [r12, #168]
	str r1, [r12, #172]
	ldr r4, [r12, #180]
	ldr r5, [r12, #184]
	ldr r6, [r12, #188]
	ldr r7, [r12, #192]
	ldr r9, [r12, #196]
	ldr r10, [r12, #200]
	ldr r11, [r12, #204]
	ldr lr, [r12, #208]
	ldr r8, [r12, #212]
	add sp, sp, #216
25:
	b 23f
22:
	sub sp, sp, #488
	add r12, sp, #0
	str r4, [r12, #180]
	str r5, [r12, #184]
	str r6, [r12, #188]
	str r7, [r12, #192]
	str r9, [r12, #196]
	str r10, [r12, #200]
	str r11, [r12, #204]
	str lr, [r12, #208]
	str r8, [r12, #212]
	ldr r4, [r12, #492]
	str r0, [r12, #176]
	mov r5, r1
	mov r6, r2
	ldr r11, [r12, #488]
	mov r8, r12
	mov r0, #0
	str r0, [r8, #216]
	str r0, [r8, #220]
	str r0, [r8, #224]
	str r0, [r8, #228]
	str r0, [r8, #232]
	str r0, [r8, #236]
	str r0, [r8, #240]
	str r0, [r8, #244]
	str r0, [r8, #248]
	str r0, [r8, #252]
	str r0, [r8, #256]
	str r0, [r8, #260]
	str r0, [r8, #264]
	str r0, [r8, #268]
	str r0, [r8, #272]
	str r0, [r8, #276]
	str r0, [r8, #280]
	str r0, [r8, #284]
	ldr r0, [r6, #0]
	str r0, [r8, #220]
	ldr r0, [r6, #4]
	str r0, [r8, #224]
	ldr r0, [r6, #8]
	str r0, [r8, #228]
	ldr r0, [r6, #12]
	str r0, [r8, #232]
	ldr r0, [r6, #16]
	str r0, [r8, #236]
	movw r0, #257
	movt r0, #257
	mov r1, #0
	str r0, [r8, #64]
	str r1, [r8, #0]
	str r0, [r8, #68]
	str r1, [r8, #4]
	str r0, [r8, #72]
	str r1, [r8, #8]
	str r0, [r8, #76]
	str r1, [r8, #12]
	str r0, [r8, #80]
	str r1, [r8, #16]
	str r0, [r8, #84]
	str r1, [r8, #20]
	str r0, [r8, #88]
	str r1, [r8, #24]
	str r0, [r8, #92]
	str r1, [r8, #28]
	str r0, [r8, #96]
	str r1, [r8, #32]
	str r0, [r8, #100]
	str r1, [r8, #36]
	str r0, [r8, #104]
	str r1, [r8, #40]
	str r0, [r8, #108]
	str r1, [r8, #44]
	str r0, [r8, #112]
	str r1, [r8, #48]
	str r0, [r8, #116]
	str r1, [r8, #52]
	str r0, [r8, #120]
	str r1, [r8, #56]
	str r0, [r8, #124]
	str r1, [r8, #60]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	mov r0, #0
	strb r0, [r11, #2276]
	ldr r0, [r5, #0]
	str r0, [r11, #2277]
	ldr r0, [r5, #4]
	str r0, [r11, #2281]
	ldr r0, [r5, #8]
	str r0, [r11, #2285]
	ldr r0, [r5, #12]
	str r0, [r11, #2289]
	ldr r0, [r5, #16]
	str r0, [r11, #2293]
	ldr r0, [r5, #20]
	str r0, [r11, #2297]
	ldr r0, [r8, #216]
	str r0, [r11, #2301]
	ldr r0, [r8, #220]
	str r0, [r11, #2305]
	ldr r0, [r8, #224]
	str r0, [r11, #2309]
	ldr r0, [r8, #228]
	str r0, [r11, #2313]
	ldr r0, [r8, #232]
	str r0, [r11, #2317]
	ldr r0, [r8, #236]
	str r0, [r11, #2321]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #69
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #133
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	mov r0, #1
	strb r0, [r11, #2276]
	ldr r0, [r5, #0]
	str r0, [r11, #2277]
	ldr r0, [r5, #4]
	str r0, [r11, #2281]
	ldr r0, [r5, #8]
	str r0, [r11, #2285]
	ldr r0, [r5, #12]
	str r0, [r11, #2289]
	ldr r0, [r5, #16]
	str r0, [r11, #2293]
	ldr r0, [r5, #20]
	str r0, [r11, #2297]
	ldr r0, [r8, #216]
	str r0, [r11, #2301]
	ldr r0, [r8, #220]
	str r0, [r11, #2305]
	ldr r0, [r8, #224]
	str r0, [r11, #2309]
	ldr r0, [r8, #228]
	str r0, [r11, #2313]
	ldr r0, [r8, #232]
	str r0, [r11, #2317]
	ldr r0, [r8, #236]
	str r0, [r11, #2321]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #69
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #133
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	movw r9, #8
232:
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r8, #64]
	str r0, [r8, #360]
	ldr r0, [r8, #68]
	str r0, [r8, #364]
	ldr r0, [r8, #72]
	str r0, [r8, #368]
	ldr r0, [r8, #76]
	str r0, [r8, #372]
	ldr r0, [r8, #80]
	str r0, [r8, #376]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	ldr r0, [r8, #64]
	str r0, [r8, #380]
	ldr r0, [r8, #68]
	str r0, [r8, #384]
	ldr r0, [r8, #72]
	str r0, [r8, #388]
	ldr r0, [r8, #76]
	str r0, [r8, #392]
	ldr r0, [r8, #80]
	str r0, [r8, #396]
	ldr r0, [r8, #176]
	mov r1, r5
	add r2, r8, #216
	add r3, r8, #360
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_p192_sign_k}
	ldr r12, [sp], #8
	sub r9, r9, #1
	subs r10, r0, #1
	mov r10, #0
	adc r10, r10, #0
	sub r10, r10, #1
	and r7, r10, r9
	cmp r7, #0
	bne 233f
	mov r7, #0
	cmp r7, #0
	b 234f
233:
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	ldr r0, [r8, #80]
	str r0, [r11, #2272]
	mov r0, #0
	strb r0, [r11, #2276]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #21
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #85
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	ldr r0, [r11, #1936]
	str r0, [r8, #16]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	ldr r0, [r8, #16]
	eor r0, r0, r1
	str r0, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #20
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #84
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r11, #1936]
	str r0, [r8, #80]
	mov r7, #1
	cmp r7, #0
234:
	bne 232b
	mov r12, r8
	mov r1, #0
	str r1, [r12, #0]
	str r1, [r12, #4]
	str r1, [r12, #8]
	str r1, [r12, #12]
	str r1, [r12, #16]
	str r1, [r12, #20]
	str r1, [r12, #24]
	str r1, [r12, #28]
	str r1, [r12, #32]
	str r1, [r12, #36]
	str r1, [r12, #40]
	str r1, [r12, #44]
	str r1, [r12, #48]
	str r1, [r12, #52]
	str r1, [r12, #56]
	str r1, [r12, #60]
	str r1, [r12, #64]
	str r1, [r12, #68]
	str r1, [r12, #72]
	str r1, [r12, #76]
	str r1, [r12, #80]
	str r1, [r12, #84]
	str r1, [r12, #88]
	str r1, [r12, #92]
	str r1, [r12, #96]
	str r1, [r12, #100]
	str r1, [r12, #104]
	str r1, [r12, #108]
	str r1, [r12, #112]
	str r1, [r12, #116]
	str r1, [r12, #120]
	str r1, [r12, #124]
	str r1, [r12, #128]
	str r1, [r12, #132]
	str r1, [r12, #136]
	str r1, [r12, #140]
	str r1, [r12, #144]
	str r1, [r12, #148]
	str r1, [r12, #152]
	str r1, [r12, #156]
	str r1, [r12, #160]
	str r1, [r12, #164]
	str r1, [r12, #168]
	str r1, [r12, #172]
	str r1, [r12, #216]
	str r1, [r12, #220]
	str r1, [r12, #224]
	str r1, [r12, #228]
	str r1, [r12, #232]
	str r1, [r12, #236]
	str r1, [r12, #240]
	str r1, [r12, #244]
	str r1, [r12, #248]
	str r1, [r12, #252]
	str r1, [r12, #256]
	str r1, [r12, #260]
	str r1, [r12, #264]
	str r1, [r12, #268]
	str r1, [r12, #272]
	str r1, [r12, #276]
	str r1, [r12, #280]
	str r1, [r12, #284]
	str r1, [r12, #288]
	str r1, [r12, #292]
	str r1, [r12, #296]
	str r1, [r12, #300]
	str r1, [r12, #304]
	str r1, [r12, #308]
	str r1, [r12, #312]
	str r1, [r12, #316]
	str r1, [r12, #320]
	str r1, [r12, #324]
	str r1, [r12, #328]
	str r1, [r12, #332]
	str r1, [r12, #336]
	str r1, [r12, #340]
	str r1, [r12, #344]
	str r1, [r12, #348]
	str r1, [r12, #352]
	str r1, [r12, #356]
	str r1, [r12, #360]
	str r1, [r12, #364]
	str r1, [r12, #368]
	str r1, [r12, #372]
	str r1, [r12, #376]
	str r1, [r12, #380]
	str r1, [r12, #384]
	str r1, [r12, #388]
	str r1, [r12, #392]
	str r1, [r12, #396]
	str r1, [r12, #400]
	str r1, [r12, #404]
	str r1, [r12, #408]
	str r1, [r12, #412]
	str r1, [r12, #416]
	str r1, [r12, #420]
	str r1, [r12, #424]
	str r1, [r12, #428]
	str r1, [r12, #432]
	str r1, [r12, #436]
	str r1, [r12, #440]
	str r1, [r12, #444]
	str r1, [r12, #448]
	str r1, [r12, #452]
	str r1, [r12, #456]
	str r1, [r12, #460]
	str r1, [r12, #464]
	str r1, [r12, #468]
	str r1, [r12, #472]
	str r1, [r12, #476]
	str r1, [r12, #480]
	str r1, [r12, #484]
	ldr r4, [r12, #180]
	ldr r5, [r12, #184]
	ldr r6, [r12, #188]
	ldr r7, [r12, #192]
	ldr r9, [r12, #196]
	ldr r10, [r12, #200]
	ldr r11, [r12, #204]
	ldr lr, [r12, #208]
	ldr r8, [r12, #212]
	add sp, sp, #488
23:
	b 21f
20:
	sub sp, sp, #488
	add r12, sp, #0
	str r4, [r12, #180]
	str r5, [r12, #184]
	str r6, [r12, #188]
	str r7, [r12, #192]
	str r9, [r12, #196]
	str r10, [r12, #200]
	str r11, [r12, #204]
	str lr, [r12, #208]
	str r8, [r12, #212]
	ldr r4, [r12, #492]
	str r0, [r12, #176]
	mov r5, r1
	mov r6, r2
	ldr r11, [r12, #488]
	mov r8, r12
	mov r0, #0
	str r0, [r8, #216]
	str r0, [r8, #220]
	str r0, [r8, #224]
	str r0, [r8, #228]
	str r0, [r8, #232]
	str r0, [r8, #236]
	str r0, [r8, #240]
	str r0, [r8, #244]
	str r0, [r8, #248]
	str r0, [r8, #252]
	str r0, [r8, #256]
	str r0, [r8, #260]
	str r0, [r8, #264]
	str r0, [r8, #268]
	str r0, [r8, #272]
	str r0, [r8, #276]
	str r0, [r8, #280]
	str r0, [r8, #284]
	ldr r0, [r6, #0]
	str r0, [r8, #224]
	ldr r0, [r6, #4]
	str r0, [r8, #228]
	ldr r0, [r6, #8]
	str r0, [r8, #232]
	ldr r0, [r6, #12]
	str r0, [r8, #236]
	movw r0, #257
	movt r0, #257
	mov r1, #0
	str r0, [r8, #64]
	str r1, [r8, #0]
	str r0, [r8, #68]
	str r1, [r8, #4]
	str r0, [r8, #72]
	str r1, [r8, #8]
	str r0, [r8, #76]
	str r1, [r8, #12]
	str r0, [r8, #80]
	str r1, [r8, #16]
	str r0, [r8, #84]
	str r1, [r8, #20]
	str r0, [r8, #88]
	str r1, [r8, #24]
	str r0, [r8, #92]
	str r1, [r8, #28]
	str r0, [r8, #96]
	str r1, [r8, #32]
	str r0, [r8, #100]
	str r1, [r8, #36]
	str r0, [r8, #104]
	str r1, [r8, #40]
	str r0, [r8, #108]
	str r1, [r8, #44]
	str r0, [r8, #112]
	str r1, [r8, #48]
	str r0, [r8, #116]
	str r1, [r8, #52]
	str r0, [r8, #120]
	str r1, [r8, #56]
	str r0, [r8, #124]
	str r1, [r8, #60]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	mov r0, #0
	strb r0, [r11, #2272]
	ldr r0, [r5, #0]
	str r0, [r11, #2273]
	ldr r0, [r5, #4]
	str r0, [r11, #2277]
	ldr r0, [r5, #8]
	str r0, [r11, #2281]
	ldr r0, [r5, #12]
	str r0, [r11, #2285]
	ldr r0, [r5, #16]
	str r0, [r11, #2289]
	ldr r0, [r5, #20]
	str r0, [r11, #2293]
	ldr r0, [r8, #216]
	str r0, [r11, #2297]
	ldr r0, [r8, #220]
	str r0, [r11, #2301]
	ldr r0, [r8, #224]
	str r0, [r11, #2305]
	ldr r0, [r8, #228]
	str r0, [r11, #2309]
	ldr r0, [r8, #232]
	str r0, [r11, #2313]
	ldr r0, [r8, #236]
	str r0, [r11, #2317]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #65
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #129
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	mov r0, #1
	strb r0, [r11, #2272]
	ldr r0, [r5, #0]
	str r0, [r11, #2273]
	ldr r0, [r5, #4]
	str r0, [r11, #2277]
	ldr r0, [r5, #8]
	str r0, [r11, #2281]
	ldr r0, [r5, #12]
	str r0, [r11, #2285]
	ldr r0, [r5, #16]
	str r0, [r11, #2289]
	ldr r0, [r5, #20]
	str r0, [r11, #2293]
	ldr r0, [r8, #216]
	str r0, [r11, #2297]
	ldr r0, [r8, #220]
	str r0, [r11, #2301]
	ldr r0, [r8, #224]
	str r0, [r11, #2305]
	ldr r0, [r8, #228]
	str r0, [r11, #2309]
	ldr r0, [r8, #232]
	str r0, [r11, #2313]
	ldr r0, [r8, #236]
	str r0, [r11, #2317]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #65
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #129
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	movw r9, #8
235:
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r8, #64]
	str r0, [r8, #360]
	ldr r0, [r8, #68]
	str r0, [r8, #364]
	ldr r0, [r8, #72]
	str r0, [r8, #368]
	ldr r0, [r8, #76]
	str r0, [r8, #372]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	ldr r0, [r8, #64]
	str r0, [r8, #376]
	ldr r0, [r8, #68]
	str r0, [r8, #380]
	ldr r0, [r8, #72]
	str r0, [r8, #384]
	ldr r0, [r8, #76]
	str r0, [r8, #388]
	ldr r0, [r8, #176]
	mov r1, r5
	add r2, r8, #216
	add r3, r8, #360
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_p192_sign_k}
	ldr r12, [sp], #8
	sub r9, r9, #1
	subs r10, r0, #1
	mov r10, #0
	adc r10, r10, #0
	sub r10, r10, #1
	and r7, r10, r9
	cmp r7, #0
	bne 236f
	mov r7, #0
	cmp r7, #0
	b 237f
236:
	ldr r0, [r8, #64]
	str r0, [r11, #2256]
	ldr r0, [r8, #68]
	str r0, [r11, #2260]
	ldr r0, [r8, #72]
	str r0, [r11, #2264]
	ldr r0, [r8, #76]
	str r0, [r11, #2268]
	mov r0, #0
	strb r0, [r11, #2272]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r12, #2256
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #17
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #81
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #0]
	ldr r0, [r11, #1924]
	str r0, [r8, #4]
	ldr r0, [r11, #1928]
	str r0, [r8, #8]
	ldr r0, [r11, #1932]
	str r0, [r8, #12]
	movw r12, #0
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r12, #192
	add r0, r11, r12
	ldr r12, [r4, #0]
	blx r12
	movw r1, #13878
	movt r1, #13878
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #0
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r1, #23644
	movt r1, #23644
	ldr r0, [r8, #0]
	eor r0, r0, r1
	str r0, [r11, #1792]
	ldr r0, [r8, #4]
	eor r0, r0, r1
	str r0, [r11, #1796]
	ldr r0, [r8, #8]
	eor r0, r0, r1
	str r0, [r11, #1800]
	ldr r0, [r8, #12]
	eor r0, r0, r1
	str r0, [r11, #1804]
	str r1, [r11, #1808]
	str r1, [r11, #1812]
	str r1, [r11, #1816]
	str r1, [r11, #1820]
	str r1, [r11, #1824]
	str r1, [r11, #1828]
	str r1, [r11, #1832]
	str r1, [r11, #1836]
	str r1, [r11, #1840]
	str r1, [r11, #1844]
	str r1, [r11, #1848]
	str r1, [r11, #1852]
	movw r12, #192
	add r0, r11, r12
	movw r12, #1792
	add r1, r11, r12
	movw r2, #0
	mov r3, #0
	movw r7, #64
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	add r1, r8, #64
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	movw r12, #192
	add r0, r11, r12
	movw r12, #1920
	add r1, r11, r12
	movw r2, #64
	mov r3, #0
	movw r7, #16
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #192
	add r0, r11, r12
	movw r2, #80
	mov r3, #0
	movw r12, #1920
	add r1, r11, r12
	movw r12, #384
	add r12, r11, r12
	ldr r7, [r4, #8]
	push {r1, r12}
	blx r7
	ldr r1, [sp], #8
	ldr r0, [r11, #1920]
	str r0, [r8, #64]
	ldr r0, [r11, #1924]
	str r0, [r8, #68]
	ldr r0, [r11, #1928]
	str r0, [r8, #72]
	ldr r0, [r11, #1932]
	str r0, [r8, #76]
	mov r7, #1
	cmp r7, #0
237:
	bne 235b
	mov r12, r8
	mov r1, #0
	str r1, [r12, #0]
	str r1, [r12, #4]
	str r1, [r12, #8]
	str r1, [r12, #12]
	str r1, [r12, #16]
	str r1, [r12, #20]
	str r1, [r12, #24]
	str r1, [r12, #28]
	str r1, [r12, #32]
	str r1, [r12, #36]
	str r1, [r12, #40]
	str r1, [r12, #44]
	str r1, [r12, #48]
	str r1, [r12, #52]
	str r1, [r12, #56]
	str r1, [r12, #60]
	str r1, [r12, #64]
	str r1, [r12, #68]
	str r1, [r12, #72]
	str r1, [r12, #76]
	str r1, [r12, #80]
	str r1, [r12, #84]
	str r1, [r12, #88]
	str r1, [r12, #92]
	str r1, [r12, #96]
	str r1, [r12, #100]
	str r1, [r12, #104]
	str r1, [r12, #108]
	str r1, [r12, #112]
	str r1, [r12, #116]
	str r1, [r12, #120]
	str r1, [r12, #124]
	str r1, [r12, #128]
	str r1, [r12, #132]
	str r1, [r12, #136]
	str r1, [r12, #140]
	str r1, [r12, #144]
	str r1, [r12, #148]
	str r1, [r12, #152]
	str r1, [r12, #156]
	str r1, [r12, #160]
	str r1, [r12, #164]
	str r1, [r12, #168]
	str r1, [r12, #172]
	str r1, [r12, #216]
	str r1, [r12, #220]
	str r1, [r12, #224]
	str r1, [r12, #228]
	str r1, [r12, #232]
	str r1, [r12, #236]
	str r1, [r12, #240]
	str r1, [r12, #244]
	str r1, [r12, #248]
	str r1, [r12, #252]
	str r1, [r12, #256]
	str r1, [r12, #260]
	str r1, [r12, #264]
	str r1, [r12, #268]
	str r1, [r12, #272]
	str r1, [r12, #276]
	str r1, [r12, #280]
	str r1, [r12, #284]
	str r1, [r12, #288]
	str r1, [r12, #292]
	str r1, [r12, #296]
	str r1, [r12, #300]
	str r1, [r12, #304]
	str r1, [r12, #308]
	str r1, [r12, #312]
	str r1, [r12, #316]
	str r1, [r12, #320]
	str r1, [r12, #324]
	str r1, [r12, #328]
	str r1, [r12, #332]
	str r1, [r12, #336]
	str r1, [r12, #340]
	str r1, [r12, #344]
	str r1, [r12, #348]
	str r1, [r12, #352]
	str r1, [r12, #356]
	str r1, [r12, #360]
	str r1, [r12, #364]
	str r1, [r12, #368]
	str r1, [r12, #372]
	str r1, [r12, #376]
	str r1, [r12, #380]
	str r1, [r12, #384]
	str r1, [r12, #388]
	str r1, [r12, #392]
	str r1, [r12, #396]
	str r1, [r12, #400]
	str r1, [r12, #404]
	str r1, [r12, #408]
	str r1, [r12, #412]
	str r1, [r12, #416]
	str r1, [r12, #420]
	str r1, [r12, #424]
	str r1, [r12, #428]
	str r1, [r12, #432]
	str r1, [r12, #436]
	str r1, [r12, #440]
	str r1, [r12, #444]
	str r1, [r12, #448]
	str r1, [r12, #452]
	str r1, [r12, #456]
	str r1, [r12, #460]
	str r1, [r12, #464]
	str r1, [r12, #468]
	str r1, [r12, #472]
	str r1, [r12, #476]
	str r1, [r12, #480]
	str r1, [r12, #484]
	ldr r4, [r12, #180]
	ldr r5, [r12, #184]
	ldr r6, [r12, #188]
	ldr r7, [r12, #192]
	ldr r9, [r12, #196]
	ldr r10, [r12, #200]
	ldr r11, [r12, #204]
	ldr lr, [r12, #208]
	ldr r8, [r12, #212]
	add sp, sp, #488
21:
	bx lr
