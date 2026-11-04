// The functions of `src/ecdsa_secp256k1.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_secp256k1_verify:
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
	ldr r4, [r2, #28]
	rev r4, r4
	str r4, [r12, #1056]
	ldr r4, [r2, #24]
	rev r4, r4
	str r4, [r12, #1060]
	ldr r4, [r2, #20]
	rev r4, r4
	str r4, [r12, #1064]
	ldr r4, [r2, #16]
	rev r4, r4
	str r4, [r12, #1068]
	ldr r4, [r2, #12]
	rev r4, r4
	str r4, [r12, #1072]
	ldr r4, [r2, #8]
	rev r4, r4
	str r4, [r12, #1076]
	ldr r4, [r2, #4]
	rev r4, r4
	str r4, [r12, #1080]
	ldr r4, [r2, #0]
	rev r4, r4
	str r4, [r12, #1084]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1088]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1092]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1096]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1100]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1104]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1108]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1112]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1116]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1144]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1148]
	movw r4, #64559
	movt r4, #65535
	str r4, [r12, #64]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #68]
	movw r4, #65535
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
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #88]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #92]
	movw r4, #16705
	movt r4, #53302
	str r4, [r12, #96]
	movw r4, #24204
	movt r4, #49106
	str r4, [r12, #100]
	movw r4, #41019
	movt r4, #44872
	str r4, [r12, #104]
	movw r4, #56550
	movt r4, #47790
	str r4, [r12, #108]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #112]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #116]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #120]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #124]
	movw r4, #0
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
	movw r4, #0
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
	movw r4, #0
	movt r4, #0
	str r4, [r12, #208]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #212]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #216]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #220]
	movw r4, #977
	movt r4, #0
	str r4, [r12, #224]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #228]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #232]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #236]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #240]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #244]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #248]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #252]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #256]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #260]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #264]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #268]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #272]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #276]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #280]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #284]
	movw r4, #20517
	movt r4, #0
	str r4, [r12, #288]
	movw r4, #21
	movt r4, #0
	str r4, [r12, #292]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #296]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #300]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #304]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #308]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #312]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #316]
	movw r4, #8343
	movt r4, #18558
	str r4, [r12, #320]
	movw r4, #11866
	movt r4, #55094
	str r4, [r12, #324]
	movw r4, #26331
	movt r4, #10684
	str r4, [r12, #328]
	movw r4, #10579
	movt r4, #8990
	str r4, [r12, #332]
	movw r4, #4764
	movt r4, #13309
	str r4, [r12, #336]
	movw r4, #18624
	movt r4, #38815
	str r4, [r12, #340]
	movw r4, #40776
	movt r4, #59656
	str r4, [r12, #344]
	movw r4, #58947
	movt r4, #39297
	str r4, [r12, #348]
	movw r4, #44002
	movt r4, #54235
	str r4, [r12, #352]
	movw r4, #42706
	movt r4, #45406
	str r4, [r12, #356]
	movw r4, #50765
	movt r4, #7965
	str r4, [r12, #360]
	movw r4, #23901
	movt r4, #36348
	str r4, [r12, #364]
	movw r4, #49462
	movt r4, #44057
	str r4, [r12, #368]
	movw r4, #46490
	movt r4, #28854
	str r4, [r12, #372]
	movw r4, #33494
	movt r4, #54437
	str r4, [r12, #376]
	movw r4, #34079
	movt r4, #53055
	str r4, [r12, #380]
	movw r4, #53568
	movt r4, #26583
	str r4, [r12, #384]
	movw r4, #61972
	movt r4, #35180
	str r4, [r12, #388]
	movw r4, #63608
	movt r4, #3708
	str r4, [r12, #392]
	movw r4, #38594
	movt r4, #29716
	str r4, [r12, #396]
	movw r4, #1990
	movt r4, #23501
	str r4, [r12, #400]
	movw r4, #62948
	movt r4, #59031
	str r4, [r12, #404]
	movw r4, #39877
	movt r4, #33222
	str r4, [r12, #408]
	movw r4, #7381
	movt r4, #40295
	str r4, [r12, #412]
	movw r4, #48831
	movt r4, #12233
	str r4, [r12, #416]
	movw r4, #41331
	movt r4, #16429
	str r4, [r12, #420]
	movw r4, #24516
	movt r4, #20663
	str r4, [r12, #424]
	movw r4, #8985
	movt r4, #17745
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
	movw r4, #64557
	movt r4, #65535
	str r4, [r12, #448]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #452]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #456]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #460]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #464]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #468]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #472]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #476]
	movw r4, #16703
	movt r4, #53302
	str r4, [r12, #480]
	movw r4, #24204
	movt r4, #49106
	str r4, [r12, #484]
	movw r4, #41019
	movt r4, #44872
	str r4, [r12, #488]
	movw r4, #56550
	movt r4, #47790
	str r4, [r12, #492]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #496]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #500]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #504]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #508]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #512]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #516]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #520]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #524]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #528]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #532]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #536]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #540]
	movw r4, #977
	movt r4, #0
	str r4, [r12, #544]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #548]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #552]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #556]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #560]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #564]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #568]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #572]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #576]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #580]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #584]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #588]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #592]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #596]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #600]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #604]
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1472]
	mov r11, #32
20:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1056]
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
	mov r11, #32
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #448]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #256]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #257]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #258]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #259]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #260]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #261]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #262]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #263]
	cmp r11, #0
	bne 21b
	mov r11, #32
22:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #480]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #512]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #513]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #514]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #515]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #516]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #517]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #518]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #519]
	cmp r11, #0
	bne 22b
	add r6, r2, #32
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1024]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1028]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1032]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1036]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1040]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1044]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1048]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1052]
	movw r4, #37025
	movt r4, #14
	str r4, [r12, #1312]
	movw r4, #1954
	movt r4, #0
	str r4, [r12, #1316]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1320]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1324]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1328]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1332]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1336]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1340]
	movw r4, #6839
	movt r4, #0
	str r4, [r12, #1344]
	movw r4, #7
	movt r4, #0
	str r4, [r12, #1348]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1352]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1356]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1360]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1364]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1368]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1372]
	add r6, r0, #1
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1144]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1148]
	add r6, r6, #32
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1216]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1220]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1224]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1228]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1232]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1236]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1240]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1244]
	ldrb r4, [r0, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1120]
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
	ldr r7, [r12, #1124]
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
	ldr r7, [r12, #1128]
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
	ldr r7, [r12, #1132]
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
	ldr r7, [r12, #1136]
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
	ldr r7, [r12, #1140]
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
	ldr r7, [r12, #1144]
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
	ldr r7, [r12, #1148]
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
	sub r5, r3, #1
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1216]
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
	ldr r7, [r12, #1220]
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
	ldr r7, [r12, #1224]
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
	ldr r7, [r12, #1228]
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
	ldr r7, [r12, #1232]
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
	ldr r7, [r12, #1236]
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
	ldr r7, [r12, #1240]
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
	ldr r7, [r12, #1244]
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
	sub r5, r3, #1
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1120
	movw r3, #1312
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1216
	movw r3, #1312
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #1184
	movw r3, #1184
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1152
	movw r3, #1152
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1376
	movw r3, #1152
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #256
	movw r3, #1152
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1408
	movw r3, #1376
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1280
	movw r3, #1344
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1248
	movw r3, #1408
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #1376]
	ldr r4, [r12, #1380]
	orr r5, r5, r4
	ldr r4, [r12, #1384]
	orr r5, r5, r4
	ldr r4, [r12, #1388]
	orr r5, r5, r4
	ldr r4, [r12, #1392]
	orr r5, r5, r4
	ldr r4, [r12, #1396]
	orr r5, r5, r4
	ldr r4, [r12, #1400]
	orr r5, r5, r4
	ldr r4, [r12, #1404]
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
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	ldr r10, [r12, #1472]
	ldr r4, [r12, #320]
	ldr r5, [r12, #1152]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1280]
	ldr r4, [r12, #324]
	ldr r5, [r12, #1156]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1284]
	ldr r4, [r12, #328]
	ldr r5, [r12, #1160]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1288]
	ldr r4, [r12, #332]
	ldr r5, [r12, #1164]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1292]
	ldr r4, [r12, #336]
	ldr r5, [r12, #1168]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1296]
	ldr r4, [r12, #340]
	ldr r5, [r12, #1172]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1300]
	ldr r4, [r12, #344]
	ldr r5, [r12, #1176]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1304]
	ldr r4, [r12, #348]
	ldr r5, [r12, #1180]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1308]
	ldr r4, [r12, #352]
	ldr r5, [r12, #1184]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1440]
	ldr r4, [r12, #356]
	ldr r5, [r12, #1188]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1444]
	ldr r4, [r12, #360]
	ldr r5, [r12, #1192]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1448]
	ldr r4, [r12, #364]
	ldr r5, [r12, #1196]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1452]
	ldr r4, [r12, #368]
	ldr r5, [r12, #1200]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1456]
	ldr r4, [r12, #372]
	ldr r5, [r12, #1204]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1460]
	ldr r4, [r12, #376]
	ldr r5, [r12, #1208]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1464]
	ldr r4, [r12, #380]
	ldr r5, [r12, #1212]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1468]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1056]
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
	ldr r7, [r12, #1060]
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
	ldr r7, [r12, #1064]
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
	ldr r7, [r12, #1068]
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
	ldr r7, [r12, #1072]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #1076]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #1080]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #1084]
	ldr r8, [r12, #124]
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
	ldr r5, [r12, #1056]
	ldr r4, [r12, #1060]
	orr r5, r5, r4
	ldr r4, [r12, #1064]
	orr r5, r5, r4
	ldr r4, [r12, #1068]
	orr r5, r5, r4
	ldr r4, [r12, #1072]
	orr r5, r5, r4
	ldr r4, [r12, #1076]
	orr r5, r5, r4
	ldr r4, [r12, #1080]
	orr r5, r5, r4
	ldr r4, [r12, #1084]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1024]
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
	ldr r7, [r12, #1028]
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
	ldr r7, [r12, #1032]
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
	ldr r7, [r12, #1036]
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
	ldr r7, [r12, #1040]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #1044]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #1048]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #1052]
	ldr r8, [r12, #124]
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
	ldr r4, [r12, #1048]
	orr r5, r5, r4
	ldr r4, [r12, #1052]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #1024
	movw r3, #384
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	ldr r4, [r12, #416]
	str r4, [r12, #992]
	ldr r4, [r12, #420]
	str r4, [r12, #996]
	ldr r4, [r12, #424]
	str r4, [r12, #1000]
	ldr r4, [r12, #428]
	str r4, [r12, #1004]
	ldr r4, [r12, #432]
	str r4, [r12, #1008]
	ldr r4, [r12, #436]
	str r4, [r12, #1012]
	ldr r4, [r12, #440]
	str r4, [r12, #1016]
	ldr r4, [r12, #444]
	str r4, [r12, #1020]
	mov r11, #256
23:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #992
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #992
	movw r3, #1248
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #512]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #992]
	ldr r5, [r12, #1024]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #992]
	ldr r4, [r12, #996]
	ldr r5, [r12, #1028]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #996]
	ldr r4, [r12, #1000]
	ldr r5, [r12, #1032]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1000]
	ldr r4, [r12, #1004]
	ldr r5, [r12, #1036]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1004]
	ldr r4, [r12, #1008]
	ldr r5, [r12, #1040]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1008]
	ldr r4, [r12, #1012]
	ldr r5, [r12, #1044]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1012]
	ldr r4, [r12, #1016]
	ldr r5, [r12, #1048]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1016]
	ldr r4, [r12, #1020]
	ldr r5, [r12, #1052]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1020]
	cmp r11, #0
	bne 23b
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1088
	movw r3, #384
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1312
	movw r2, #1056
	movw r3, #384
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1344
	movw r3, #992
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1312
	movw r3, #992
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1376
	movw r3, #192
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1408
	movw r3, #192
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	mov r11, #32
24:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1152]
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
	ldr r4, [r12, #320]
	str r4, [r12, #3424]
	ldr r4, [r12, #324]
	str r4, [r12, #3428]
	ldr r4, [r12, #328]
	str r4, [r12, #3432]
	ldr r4, [r12, #332]
	str r4, [r12, #3436]
	ldr r4, [r12, #336]
	str r4, [r12, #3440]
	ldr r4, [r12, #340]
	str r4, [r12, #3444]
	ldr r4, [r12, #344]
	str r4, [r12, #3448]
	ldr r4, [r12, #348]
	str r4, [r12, #3452]
	ldr r4, [r12, #352]
	str r4, [r12, #3456]
	ldr r4, [r12, #356]
	str r4, [r12, #3460]
	ldr r4, [r12, #360]
	str r4, [r12, #3464]
	ldr r4, [r12, #364]
	str r4, [r12, #3468]
	ldr r4, [r12, #368]
	str r4, [r12, #3472]
	ldr r4, [r12, #372]
	str r4, [r12, #3476]
	ldr r4, [r12, #376]
	str r4, [r12, #3480]
	ldr r4, [r12, #380]
	str r4, [r12, #3484]
	ldr r4, [r12, #224]
	str r4, [r12, #3488]
	ldr r4, [r12, #228]
	str r4, [r12, #3492]
	ldr r4, [r12, #232]
	str r4, [r12, #3496]
	ldr r4, [r12, #236]
	str r4, [r12, #3500]
	ldr r4, [r12, #240]
	str r4, [r12, #3504]
	ldr r4, [r12, #244]
	str r4, [r12, #3508]
	ldr r4, [r12, #248]
	str r4, [r12, #3512]
	ldr r4, [r12, #252]
	str r4, [r12, #3516]
	ldr r4, [r12, #256]
	str r4, [r12, #3520]
	ldr r4, [r12, #260]
	str r4, [r12, #3524]
	ldr r4, [r12, #264]
	str r4, [r12, #3528]
	ldr r4, [r12, #268]
	str r4, [r12, #3532]
	ldr r4, [r12, #272]
	str r4, [r12, #3536]
	ldr r4, [r12, #276]
	str r4, [r12, #3540]
	ldr r4, [r12, #280]
	str r4, [r12, #3544]
	ldr r4, [r12, #284]
	str r4, [r12, #3548]
	ldr r4, [r12, #288]
	str r4, [r12, #3552]
	ldr r4, [r12, #292]
	str r4, [r12, #3556]
	ldr r4, [r12, #296]
	str r4, [r12, #3560]
	ldr r4, [r12, #300]
	str r4, [r12, #3564]
	ldr r4, [r12, #304]
	str r4, [r12, #3568]
	ldr r4, [r12, #308]
	str r4, [r12, #3572]
	ldr r4, [r12, #312]
	str r4, [r12, #3576]
	ldr r4, [r12, #316]
	str r4, [r12, #3580]
	movw r4, #5734
	movt r4, #38525
	str r4, [r12, #512]
	movw r4, #3436
	movt r4, #53333
	str r4, [r12, #516]
	movw r4, #47640
	movt r4, #26332
	str r4, [r12, #520]
	movw r4, #11912
	movt r4, #9768
	str r4, [r12, #524]
	movw r4, #38101
	movt r4, #2766
	str r4, [r12, #528]
	movw r4, #11127
	movt r4, #32460
	str r4, [r12, #532]
	movw r4, #5946
	movt r4, #52428
	str r4, [r12, #536]
	movw r4, #28620
	movt r4, #19212
	str r4, [r12, #540]
	movw r4, #24148
	movt r4, #57402
	str r4, [r12, #544]
	movw r4, #2389
	movt r4, #29882
	str r4, [r12, #548]
	movw r4, #61597
	movt r4, #23280
	str r4, [r12, #552]
	movw r4, #21314
	movt r4, #4282
	str r4, [r12, #556]
	movw r4, #29745
	movt r4, #20676
	str r4, [r12, #560]
	movw r4, #19972
	movt r4, #33667
	str r4, [r12, #564]
	movw r4, #48404
	movt r4, #28437
	str r4, [r12, #568]
	movw r4, #18023
	movt r4, #14446
	str r4, [r12, #572]
	movw r4, #977
	movt r4, #0
	str r4, [r12, #576]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #580]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #584]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #588]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #592]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #596]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #600]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #604]
	mov r11, #37
25:
	sub r11, r11, #1
	mov r4, #7
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	cmp r11, #36
	beq 26f
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #6]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #5]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #4]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #3]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
	b 27f
26:
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #3]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
27:
	sub r9, r9, #64
	lsr r4, r9, #31
	mov r5, #0
	sub r4, r5, r4
	eor r9, r9, r4
	sub r9, r9, r4
	movw r8, #:lower16:({VG_SECP256K1_COMB}
	movt r8, #:upper16:({VG_SECP256K1_COMB}
2:
	add r8, pc
3:
	mov r4, #4096
	mul r4, r4, r11
	add r8, r8, r4
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3424]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3428]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3432]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3436]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3440]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3444]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3448]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3452]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3456]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3460]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3464]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3468]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3472]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3476]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3480]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3484]
	mov r7, #1
28:
	eor r10, r9, r7
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #3424]
	ldr r5, [r8, #0]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3424]
	ldr r4, [r12, #3428]
	ldr r5, [r8, #4]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3428]
	ldr r4, [r12, #3432]
	ldr r5, [r8, #8]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3432]
	ldr r4, [r12, #3436]
	ldr r5, [r8, #12]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3436]
	ldr r4, [r12, #3440]
	ldr r5, [r8, #16]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3440]
	ldr r4, [r12, #3444]
	ldr r5, [r8, #20]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3444]
	ldr r4, [r12, #3448]
	ldr r5, [r8, #24]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3448]
	ldr r4, [r12, #3452]
	ldr r5, [r8, #28]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3452]
	ldr r4, [r12, #3456]
	ldr r5, [r8, #32]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3456]
	ldr r4, [r12, #3460]
	ldr r5, [r8, #36]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3460]
	ldr r4, [r12, #3464]
	ldr r5, [r8, #40]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3464]
	ldr r4, [r12, #3468]
	ldr r5, [r8, #44]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3468]
	ldr r4, [r12, #3472]
	ldr r5, [r8, #48]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3472]
	ldr r4, [r12, #3476]
	ldr r5, [r8, #52]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3476]
	ldr r4, [r12, #3480]
	ldr r5, [r8, #56]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3480]
	ldr r4, [r12, #3484]
	ldr r5, [r8, #60]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3484]
	add r8, r8, #64
	add r7, r7, #1
	cmp r7, #65
	bne 28b
	movw r4, #977
	movt r4, #0
	str r4, [r12, #3488]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #3492]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3496]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3500]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3504]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3508]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3512]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3516]
	eor r10, r9, #0
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #3456]
	ldr r5, [r12, #3488]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3456]
	ldr r4, [r12, #3460]
	ldr r5, [r12, #3492]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3460]
	ldr r4, [r12, #3464]
	ldr r5, [r12, #3496]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3464]
	ldr r4, [r12, #3468]
	ldr r5, [r12, #3500]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3468]
	ldr r4, [r12, #3472]
	ldr r5, [r12, #3504]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3472]
	ldr r4, [r12, #3476]
	ldr r5, [r12, #3508]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3476]
	ldr r4, [r12, #3480]
	ldr r5, [r12, #3512]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3480]
	ldr r4, [r12, #3484]
	ldr r5, [r12, #3516]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3484]
	ldr r4, [r12, #3488]
	ldr r5, [r12, #160]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3488]
	ldr r4, [r12, #3492]
	ldr r5, [r12, #164]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3492]
	ldr r4, [r12, #3496]
	ldr r5, [r12, #168]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3496]
	ldr r4, [r12, #3500]
	ldr r5, [r12, #172]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3500]
	ldr r4, [r12, #3504]
	ldr r5, [r12, #176]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3504]
	ldr r4, [r12, #3508]
	ldr r5, [r12, #180]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3508]
	ldr r4, [r12, #3512]
	ldr r5, [r12, #184]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3512]
	ldr r4, [r12, #3516]
	ldr r5, [r12, #188]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3516]
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #160
	movw r3, #3456
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	cmp r11, #36
	beq 29f
	mov r4, #7
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	ldrb r4, [r4, #6]
	sub r10, r4, #1
	b 210f
29:
	movw r10, #65535
	movt r10, #65535
210:
	ldr r4, [r12, #3456]
	ldr r5, [r12, #704]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3456]
	ldr r4, [r12, #3460]
	ldr r5, [r12, #708]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3460]
	ldr r4, [r12, #3464]
	ldr r5, [r12, #712]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3464]
	ldr r4, [r12, #3468]
	ldr r5, [r12, #716]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3468]
	ldr r4, [r12, #3472]
	ldr r5, [r12, #720]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3472]
	ldr r4, [r12, #3476]
	ldr r5, [r12, #724]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3476]
	ldr r4, [r12, #3480]
	ldr r5, [r12, #728]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3480]
	ldr r4, [r12, #3484]
	ldr r5, [r12, #732]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3484]
	ldr r4, [r12, #512]
	str r4, [r12, #3328]
	ldr r4, [r12, #516]
	str r4, [r12, #3332]
	ldr r4, [r12, #520]
	str r4, [r12, #3336]
	ldr r4, [r12, #524]
	str r4, [r12, #3340]
	ldr r4, [r12, #528]
	str r4, [r12, #3344]
	ldr r4, [r12, #532]
	str r4, [r12, #3348]
	ldr r4, [r12, #536]
	str r4, [r12, #3352]
	ldr r4, [r12, #540]
	str r4, [r12, #3356]
	ldr r4, [r12, #544]
	str r4, [r12, #3360]
	ldr r4, [r12, #548]
	str r4, [r12, #3364]
	ldr r4, [r12, #552]
	str r4, [r12, #3368]
	ldr r4, [r12, #556]
	str r4, [r12, #3372]
	ldr r4, [r12, #560]
	str r4, [r12, #3376]
	ldr r4, [r12, #564]
	str r4, [r12, #3380]
	ldr r4, [r12, #568]
	str r4, [r12, #3384]
	ldr r4, [r12, #572]
	str r4, [r12, #3388]
	ldr r4, [r12, #576]
	str r4, [r12, #3392]
	ldr r4, [r12, #580]
	str r4, [r12, #3396]
	ldr r4, [r12, #584]
	str r4, [r12, #3400]
	ldr r4, [r12, #588]
	str r4, [r12, #3404]
	ldr r4, [r12, #592]
	str r4, [r12, #3408]
	ldr r4, [r12, #596]
	str r4, [r12, #3412]
	ldr r4, [r12, #600]
	str r4, [r12, #3416]
	ldr r4, [r12, #604]
	str r4, [r12, #3420]
	mov r10, lr
	mov r0, r12
	bl {vg_secp256k1_point_add}
	mov lr, r10
	ldr r4, [r12, #3232]
	str r4, [r12, #512]
	ldr r4, [r12, #3236]
	str r4, [r12, #516]
	ldr r4, [r12, #3240]
	str r4, [r12, #520]
	ldr r4, [r12, #3244]
	str r4, [r12, #524]
	ldr r4, [r12, #3248]
	str r4, [r12, #528]
	ldr r4, [r12, #3252]
	str r4, [r12, #532]
	ldr r4, [r12, #3256]
	str r4, [r12, #536]
	ldr r4, [r12, #3260]
	str r4, [r12, #540]
	ldr r4, [r12, #3264]
	str r4, [r12, #544]
	ldr r4, [r12, #3268]
	str r4, [r12, #548]
	ldr r4, [r12, #3272]
	str r4, [r12, #552]
	ldr r4, [r12, #3276]
	str r4, [r12, #556]
	ldr r4, [r12, #3280]
	str r4, [r12, #560]
	ldr r4, [r12, #3284]
	str r4, [r12, #564]
	ldr r4, [r12, #3288]
	str r4, [r12, #568]
	ldr r4, [r12, #3292]
	str r4, [r12, #572]
	ldr r4, [r12, #3296]
	str r4, [r12, #576]
	ldr r4, [r12, #3300]
	str r4, [r12, #580]
	ldr r4, [r12, #3304]
	str r4, [r12, #584]
	ldr r4, [r12, #3308]
	str r4, [r12, #588]
	ldr r4, [r12, #3312]
	str r4, [r12, #592]
	ldr r4, [r12, #3316]
	str r4, [r12, #596]
	ldr r4, [r12, #3320]
	str r4, [r12, #600]
	ldr r4, [r12, #3324]
	str r4, [r12, #604]
	cmp r11, #0
	bne 25b
	ldr r4, [r12, #512]
	str r4, [r12, #1376]
	ldr r4, [r12, #516]
	str r4, [r12, #1380]
	ldr r4, [r12, #520]
	str r4, [r12, #1384]
	ldr r4, [r12, #524]
	str r4, [r12, #1388]
	ldr r4, [r12, #528]
	str r4, [r12, #1392]
	ldr r4, [r12, #532]
	str r4, [r12, #1396]
	ldr r4, [r12, #536]
	str r4, [r12, #1400]
	ldr r4, [r12, #540]
	str r4, [r12, #1404]
	ldr r4, [r12, #544]
	str r4, [r12, #1408]
	ldr r4, [r12, #548]
	str r4, [r12, #1412]
	ldr r4, [r12, #552]
	str r4, [r12, #1416]
	ldr r4, [r12, #556]
	str r4, [r12, #1420]
	ldr r4, [r12, #560]
	str r4, [r12, #1424]
	ldr r4, [r12, #564]
	str r4, [r12, #1428]
	ldr r4, [r12, #568]
	str r4, [r12, #1432]
	ldr r4, [r12, #572]
	str r4, [r12, #1436]
	ldr r4, [r12, #576]
	str r4, [r12, #1248]
	ldr r4, [r12, #580]
	str r4, [r12, #1252]
	ldr r4, [r12, #584]
	str r4, [r12, #1256]
	ldr r4, [r12, #588]
	str r4, [r12, #1260]
	ldr r4, [r12, #592]
	str r4, [r12, #1264]
	ldr r4, [r12, #596]
	str r4, [r12, #1268]
	ldr r4, [r12, #600]
	str r4, [r12, #1272]
	ldr r4, [r12, #604]
	str r4, [r12, #1276]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #512]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #516]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #520]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #524]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #528]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #532]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #536]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #540]
	movw r4, #977
	movt r4, #0
	str r4, [r12, #544]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #548]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #552]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #556]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #560]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #564]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #568]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #572]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #576]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #580]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #584]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #588]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #592]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #596]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #600]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #604]
	mov r11, #32
211:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1184]
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
	bne 211b
	ldr r4, [r12, #1280]
	str r4, [r12, #3424]
	ldr r4, [r12, #1284]
	str r4, [r12, #3428]
	ldr r4, [r12, #1288]
	str r4, [r12, #3432]
	ldr r4, [r12, #1292]
	str r4, [r12, #3436]
	ldr r4, [r12, #1296]
	str r4, [r12, #3440]
	ldr r4, [r12, #1300]
	str r4, [r12, #3444]
	ldr r4, [r12, #1304]
	str r4, [r12, #3448]
	ldr r4, [r12, #1308]
	str r4, [r12, #3452]
	ldr r4, [r12, #1440]
	str r4, [r12, #3456]
	ldr r4, [r12, #1444]
	str r4, [r12, #3460]
	ldr r4, [r12, #1448]
	str r4, [r12, #3464]
	ldr r4, [r12, #1452]
	str r4, [r12, #3468]
	ldr r4, [r12, #1456]
	str r4, [r12, #3472]
	ldr r4, [r12, #1460]
	str r4, [r12, #3476]
	ldr r4, [r12, #1464]
	str r4, [r12, #3480]
	ldr r4, [r12, #1468]
	str r4, [r12, #3484]
	ldr r4, [r12, #224]
	str r4, [r12, #3488]
	ldr r4, [r12, #228]
	str r4, [r12, #3492]
	ldr r4, [r12, #232]
	str r4, [r12, #3496]
	ldr r4, [r12, #236]
	str r4, [r12, #3500]
	ldr r4, [r12, #240]
	str r4, [r12, #3504]
	ldr r4, [r12, #244]
	str r4, [r12, #3508]
	ldr r4, [r12, #248]
	str r4, [r12, #3512]
	ldr r4, [r12, #252]
	str r4, [r12, #3516]
	ldr r4, [r12, #256]
	str r4, [r12, #3520]
	ldr r4, [r12, #260]
	str r4, [r12, #3524]
	ldr r4, [r12, #264]
	str r4, [r12, #3528]
	ldr r4, [r12, #268]
	str r4, [r12, #3532]
	ldr r4, [r12, #272]
	str r4, [r12, #3536]
	ldr r4, [r12, #276]
	str r4, [r12, #3540]
	ldr r4, [r12, #280]
	str r4, [r12, #3544]
	ldr r4, [r12, #284]
	str r4, [r12, #3548]
	ldr r4, [r12, #288]
	str r4, [r12, #3552]
	ldr r4, [r12, #292]
	str r4, [r12, #3556]
	ldr r4, [r12, #296]
	str r4, [r12, #3560]
	ldr r4, [r12, #300]
	str r4, [r12, #3564]
	ldr r4, [r12, #304]
	str r4, [r12, #3568]
	ldr r4, [r12, #308]
	str r4, [r12, #3572]
	ldr r4, [r12, #312]
	str r4, [r12, #3576]
	ldr r4, [r12, #316]
	str r4, [r12, #3580]
	mov r11, #256
212:
	sub r11, r11, #1
	ldr r4, [r12, #512]
	str r4, [r12, #3328]
	ldr r4, [r12, #516]
	str r4, [r12, #3332]
	ldr r4, [r12, #520]
	str r4, [r12, #3336]
	ldr r4, [r12, #524]
	str r4, [r12, #3340]
	ldr r4, [r12, #528]
	str r4, [r12, #3344]
	ldr r4, [r12, #532]
	str r4, [r12, #3348]
	ldr r4, [r12, #536]
	str r4, [r12, #3352]
	ldr r4, [r12, #540]
	str r4, [r12, #3356]
	ldr r4, [r12, #544]
	str r4, [r12, #3360]
	ldr r4, [r12, #548]
	str r4, [r12, #3364]
	ldr r4, [r12, #552]
	str r4, [r12, #3368]
	ldr r4, [r12, #556]
	str r4, [r12, #3372]
	ldr r4, [r12, #560]
	str r4, [r12, #3376]
	ldr r4, [r12, #564]
	str r4, [r12, #3380]
	ldr r4, [r12, #568]
	str r4, [r12, #3384]
	ldr r4, [r12, #572]
	str r4, [r12, #3388]
	ldr r4, [r12, #576]
	str r4, [r12, #3392]
	ldr r4, [r12, #580]
	str r4, [r12, #3396]
	ldr r4, [r12, #584]
	str r4, [r12, #3400]
	ldr r4, [r12, #588]
	str r4, [r12, #3404]
	ldr r4, [r12, #592]
	str r4, [r12, #3408]
	ldr r4, [r12, #596]
	str r4, [r12, #3412]
	ldr r4, [r12, #600]
	str r4, [r12, #3416]
	ldr r4, [r12, #604]
	str r4, [r12, #3420]
	mov r10, lr
	mov r0, r12
	bl {vg_secp256k1_point_a0_double}
	mov lr, r10
	ldr r4, [r12, #3232]
	str r4, [r12, #3328]
	ldr r4, [r12, #3236]
	str r4, [r12, #3332]
	ldr r4, [r12, #3240]
	str r4, [r12, #3336]
	ldr r4, [r12, #3244]
	str r4, [r12, #3340]
	ldr r4, [r12, #3248]
	str r4, [r12, #3344]
	ldr r4, [r12, #3252]
	str r4, [r12, #3348]
	ldr r4, [r12, #3256]
	str r4, [r12, #3352]
	ldr r4, [r12, #3260]
	str r4, [r12, #3356]
	ldr r4, [r12, #3264]
	str r4, [r12, #3360]
	ldr r4, [r12, #3268]
	str r4, [r12, #3364]
	ldr r4, [r12, #3272]
	str r4, [r12, #3368]
	ldr r4, [r12, #3276]
	str r4, [r12, #3372]
	ldr r4, [r12, #3280]
	str r4, [r12, #3376]
	ldr r4, [r12, #3284]
	str r4, [r12, #3380]
	ldr r4, [r12, #3288]
	str r4, [r12, #3384]
	ldr r4, [r12, #3292]
	str r4, [r12, #3388]
	ldr r4, [r12, #3296]
	str r4, [r12, #3392]
	ldr r4, [r12, #3300]
	str r4, [r12, #3396]
	ldr r4, [r12, #3304]
	str r4, [r12, #3400]
	ldr r4, [r12, #3308]
	str r4, [r12, #3404]
	ldr r4, [r12, #3312]
	str r4, [r12, #3408]
	ldr r4, [r12, #3316]
	str r4, [r12, #3412]
	ldr r4, [r12, #3320]
	str r4, [r12, #3416]
	ldr r4, [r12, #3324]
	str r4, [r12, #3420]
	mov r10, lr
	mov r0, r12
	bl {vg_secp256k1_point_a0_add_affine}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #0]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #3328]
	ldr r5, [r12, #3232]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #512]
	ldr r4, [r12, #3332]
	ldr r5, [r12, #3236]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #516]
	ldr r4, [r12, #3336]
	ldr r5, [r12, #3240]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #520]
	ldr r4, [r12, #3340]
	ldr r5, [r12, #3244]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #524]
	ldr r4, [r12, #3344]
	ldr r5, [r12, #3248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #528]
	ldr r4, [r12, #3348]
	ldr r5, [r12, #3252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #532]
	ldr r4, [r12, #3352]
	ldr r5, [r12, #3256]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #536]
	ldr r4, [r12, #3356]
	ldr r5, [r12, #3260]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #540]
	ldr r4, [r12, #3360]
	ldr r5, [r12, #3264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #544]
	ldr r4, [r12, #3364]
	ldr r5, [r12, #3268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #548]
	ldr r4, [r12, #3368]
	ldr r5, [r12, #3272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #552]
	ldr r4, [r12, #3372]
	ldr r5, [r12, #3276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #556]
	ldr r4, [r12, #3376]
	ldr r5, [r12, #3280]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #560]
	ldr r4, [r12, #3380]
	ldr r5, [r12, #3284]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #564]
	ldr r4, [r12, #3384]
	ldr r5, [r12, #3288]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #568]
	ldr r4, [r12, #3388]
	ldr r5, [r12, #3292]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #572]
	ldr r4, [r12, #3392]
	ldr r5, [r12, #3296]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #576]
	ldr r4, [r12, #3396]
	ldr r5, [r12, #3300]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #580]
	ldr r4, [r12, #3400]
	ldr r5, [r12, #3304]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #584]
	ldr r4, [r12, #3404]
	ldr r5, [r12, #3308]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #588]
	ldr r4, [r12, #3408]
	ldr r5, [r12, #3312]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #592]
	ldr r4, [r12, #3412]
	ldr r5, [r12, #3316]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #596]
	ldr r4, [r12, #3416]
	ldr r5, [r12, #3320]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #600]
	ldr r4, [r12, #3420]
	ldr r5, [r12, #3324]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #604]
	cmp r11, #0
	bne 212b
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #1376
	movw r3, #512
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #1408
	movw r3, #544
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #1248
	movw r3, #576
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #1376
	movw r3, #1408
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #512
	movw r3, #544
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #800
	movw r3, #832
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #928
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #1376
	movw r3, #1248
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #512
	movw r3, #576
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #960
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #800
	movw r3, #864
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #960
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #1408
	movw r3, #1248
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #544
	movw r3, #576
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #960
	movw r3, #608
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #832
	movw r3, #864
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #960
	movw r3, #608
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #256
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #288
	movw r3, #864
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #608
	movw r3, #672
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #832
	movw r3, #672
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #832
	movw r3, #672
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #608
	movw r3, #672
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #800
	movw r3, #800
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #800
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #256
	movw r3, #864
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #288
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #864
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #800
	movw r3, #864
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #256
	movw r3, #864
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #864
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #832
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #800
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #960
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #896
	movw r3, #608
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #608
	movw r3, #800
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #896
	movw r3, #832
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #960
	movw r3, #672
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #672
	movw r3, #800
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	ldr r4, [r12, #608]
	str r4, [r12, #512]
	ldr r4, [r12, #612]
	str r4, [r12, #516]
	ldr r4, [r12, #616]
	str r4, [r12, #520]
	ldr r4, [r12, #620]
	str r4, [r12, #524]
	ldr r4, [r12, #624]
	str r4, [r12, #528]
	ldr r4, [r12, #628]
	str r4, [r12, #532]
	ldr r4, [r12, #632]
	str r4, [r12, #536]
	ldr r4, [r12, #636]
	str r4, [r12, #540]
	ldr r4, [r12, #640]
	str r4, [r12, #544]
	ldr r4, [r12, #644]
	str r4, [r12, #548]
	ldr r4, [r12, #648]
	str r4, [r12, #552]
	ldr r4, [r12, #652]
	str r4, [r12, #556]
	ldr r4, [r12, #656]
	str r4, [r12, #560]
	ldr r4, [r12, #660]
	str r4, [r12, #564]
	ldr r4, [r12, #664]
	str r4, [r12, #568]
	ldr r4, [r12, #668]
	str r4, [r12, #572]
	ldr r4, [r12, #672]
	str r4, [r12, #576]
	ldr r4, [r12, #676]
	str r4, [r12, #580]
	ldr r4, [r12, #680]
	str r4, [r12, #584]
	ldr r4, [r12, #684]
	str r4, [r12, #588]
	ldr r4, [r12, #688]
	str r4, [r12, #592]
	ldr r4, [r12, #692]
	str r4, [r12, #596]
	ldr r4, [r12, #696]
	str r4, [r12, #600]
	ldr r4, [r12, #700]
	str r4, [r12, #604]
	ldr r4, [r12, #224]
	str r4, [r12, #992]
	ldr r4, [r12, #228]
	str r4, [r12, #996]
	ldr r4, [r12, #232]
	str r4, [r12, #1000]
	ldr r4, [r12, #236]
	str r4, [r12, #1004]
	ldr r4, [r12, #240]
	str r4, [r12, #1008]
	ldr r4, [r12, #244]
	str r4, [r12, #1012]
	ldr r4, [r12, #248]
	str r4, [r12, #1016]
	ldr r4, [r12, #252]
	str r4, [r12, #1020]
	mov r11, #256
213:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #992
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #992
	movw r3, #576
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #256]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #992]
	ldr r5, [r12, #1024]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #992]
	ldr r4, [r12, #996]
	ldr r5, [r12, #1028]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #996]
	ldr r4, [r12, #1000]
	ldr r5, [r12, #1032]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1000]
	ldr r4, [r12, #1004]
	ldr r5, [r12, #1036]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1004]
	ldr r4, [r12, #1008]
	ldr r5, [r12, #1040]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1008]
	ldr r4, [r12, #1012]
	ldr r5, [r12, #1044]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1012]
	ldr r4, [r12, #1016]
	ldr r5, [r12, #1048]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1016]
	ldr r4, [r12, #1020]
	ldr r5, [r12, #1052]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1020]
	cmp r11, #0
	bne 213b
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #512
	movw r3, #992
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1152
	movw r3, #192
	bl {vg_secp256k1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1184
	movw r3, #384
	bl {vg_secp256k1_mul_mod_n}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1280
	movw r3, #1312
	bl {vg_secp256k1_sub_mod_n}
	mov lr, r10
	ldr r5, [r12, #576]
	ldr r4, [r12, #580]
	orr r5, r5, r4
	ldr r4, [r12, #584]
	orr r5, r5, r4
	ldr r4, [r12, #588]
	orr r5, r5, r4
	ldr r4, [r12, #592]
	orr r5, r5, r4
	ldr r4, [r12, #596]
	orr r5, r5, r4
	ldr r4, [r12, #600]
	orr r5, r5, r4
	ldr r4, [r12, #604]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	ldr r5, [r12, #1344]
	ldr r4, [r12, #1348]
	orr r5, r5, r4
	ldr r4, [r12, #1352]
	orr r5, r5, r4
	ldr r4, [r12, #1356]
	orr r5, r5, r4
	ldr r4, [r12, #1360]
	orr r5, r5, r4
	ldr r4, [r12, #1364]
	orr r5, r5, r4
	ldr r4, [r12, #1368]
	orr r5, r5, r4
	ldr r4, [r12, #1372]
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
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	ldr r10, [r12, #1472]
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

vg_ecdsa_secp256k1_verify_umaal:
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
	ldr r4, [r2, #28]
	rev r4, r4
	str r4, [r12, #1056]
	ldr r4, [r2, #24]
	rev r4, r4
	str r4, [r12, #1060]
	ldr r4, [r2, #20]
	rev r4, r4
	str r4, [r12, #1064]
	ldr r4, [r2, #16]
	rev r4, r4
	str r4, [r12, #1068]
	ldr r4, [r2, #12]
	rev r4, r4
	str r4, [r12, #1072]
	ldr r4, [r2, #8]
	rev r4, r4
	str r4, [r12, #1076]
	ldr r4, [r2, #4]
	rev r4, r4
	str r4, [r12, #1080]
	ldr r4, [r2, #0]
	rev r4, r4
	str r4, [r12, #1084]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1088]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1092]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1096]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1100]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1104]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1108]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1112]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1116]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1144]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1148]
	movw r4, #64559
	movt r4, #65535
	str r4, [r12, #64]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #68]
	movw r4, #65535
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
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #88]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #92]
	movw r4, #16705
	movt r4, #53302
	str r4, [r12, #96]
	movw r4, #24204
	movt r4, #49106
	str r4, [r12, #100]
	movw r4, #41019
	movt r4, #44872
	str r4, [r12, #104]
	movw r4, #56550
	movt r4, #47790
	str r4, [r12, #108]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #112]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #116]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #120]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #124]
	movw r4, #0
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
	movw r4, #0
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
	movw r4, #0
	movt r4, #0
	str r4, [r12, #208]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #212]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #216]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #220]
	movw r4, #977
	movt r4, #0
	str r4, [r12, #224]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #228]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #232]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #236]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #240]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #244]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #248]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #252]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #256]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #260]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #264]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #268]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #272]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #276]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #280]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #284]
	movw r4, #20517
	movt r4, #0
	str r4, [r12, #288]
	movw r4, #21
	movt r4, #0
	str r4, [r12, #292]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #296]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #300]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #304]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #308]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #312]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #316]
	movw r4, #8343
	movt r4, #18558
	str r4, [r12, #320]
	movw r4, #11866
	movt r4, #55094
	str r4, [r12, #324]
	movw r4, #26331
	movt r4, #10684
	str r4, [r12, #328]
	movw r4, #10579
	movt r4, #8990
	str r4, [r12, #332]
	movw r4, #4764
	movt r4, #13309
	str r4, [r12, #336]
	movw r4, #18624
	movt r4, #38815
	str r4, [r12, #340]
	movw r4, #40776
	movt r4, #59656
	str r4, [r12, #344]
	movw r4, #58947
	movt r4, #39297
	str r4, [r12, #348]
	movw r4, #44002
	movt r4, #54235
	str r4, [r12, #352]
	movw r4, #42706
	movt r4, #45406
	str r4, [r12, #356]
	movw r4, #50765
	movt r4, #7965
	str r4, [r12, #360]
	movw r4, #23901
	movt r4, #36348
	str r4, [r12, #364]
	movw r4, #49462
	movt r4, #44057
	str r4, [r12, #368]
	movw r4, #46490
	movt r4, #28854
	str r4, [r12, #372]
	movw r4, #33494
	movt r4, #54437
	str r4, [r12, #376]
	movw r4, #34079
	movt r4, #53055
	str r4, [r12, #380]
	movw r4, #53568
	movt r4, #26583
	str r4, [r12, #384]
	movw r4, #61972
	movt r4, #35180
	str r4, [r12, #388]
	movw r4, #63608
	movt r4, #3708
	str r4, [r12, #392]
	movw r4, #38594
	movt r4, #29716
	str r4, [r12, #396]
	movw r4, #1990
	movt r4, #23501
	str r4, [r12, #400]
	movw r4, #62948
	movt r4, #59031
	str r4, [r12, #404]
	movw r4, #39877
	movt r4, #33222
	str r4, [r12, #408]
	movw r4, #7381
	movt r4, #40295
	str r4, [r12, #412]
	movw r4, #48831
	movt r4, #12233
	str r4, [r12, #416]
	movw r4, #41331
	movt r4, #16429
	str r4, [r12, #420]
	movw r4, #24516
	movt r4, #20663
	str r4, [r12, #424]
	movw r4, #8985
	movt r4, #17745
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
	movw r4, #64557
	movt r4, #65535
	str r4, [r12, #448]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #452]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #456]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #460]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #464]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #468]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #472]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #476]
	movw r4, #16703
	movt r4, #53302
	str r4, [r12, #480]
	movw r4, #24204
	movt r4, #49106
	str r4, [r12, #484]
	movw r4, #41019
	movt r4, #44872
	str r4, [r12, #488]
	movw r4, #56550
	movt r4, #47790
	str r4, [r12, #492]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #496]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #500]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #504]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #508]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #512]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #516]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #520]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #524]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #528]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #532]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #536]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #540]
	movw r4, #977
	movt r4, #0
	str r4, [r12, #544]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #548]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #552]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #556]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #560]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #564]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #568]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #572]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #576]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #580]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #584]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #588]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #592]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #596]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #600]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #604]
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1472]
	mov r11, #32
20:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1056]
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
	mov r11, #32
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #448]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #256]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #257]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #258]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #259]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #260]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #261]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #262]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #263]
	cmp r11, #0
	bne 21b
	mov r11, #32
22:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #480]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #512]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #513]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #514]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #515]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #516]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #517]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #518]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #519]
	cmp r11, #0
	bne 22b
	add r6, r2, #32
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1024]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1028]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1032]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1036]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1040]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1044]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1048]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1052]
	movw r4, #37025
	movt r4, #14
	str r4, [r12, #1312]
	movw r4, #1954
	movt r4, #0
	str r4, [r12, #1316]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1320]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1324]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1328]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1332]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1336]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1340]
	movw r4, #6839
	movt r4, #0
	str r4, [r12, #1344]
	movw r4, #7
	movt r4, #0
	str r4, [r12, #1348]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1352]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1356]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1360]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1364]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1368]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1372]
	add r6, r0, #1
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1144]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1148]
	add r6, r6, #32
	ldr r4, [r6, #28]
	rev r4, r4
	str r4, [r12, #1216]
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1220]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1224]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1228]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1232]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1236]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1240]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1244]
	ldrb r4, [r0, #0]
	eor r4, r4, #4
	sub r4, r4, #1
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1120]
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
	ldr r7, [r12, #1124]
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
	ldr r7, [r12, #1128]
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
	ldr r7, [r12, #1132]
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
	ldr r7, [r12, #1136]
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
	ldr r7, [r12, #1140]
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
	ldr r7, [r12, #1144]
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
	ldr r7, [r12, #1148]
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
	sub r5, r3, #1
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1216]
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
	ldr r7, [r12, #1220]
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
	ldr r7, [r12, #1224]
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
	ldr r7, [r12, #1228]
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
	ldr r7, [r12, #1232]
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
	ldr r7, [r12, #1236]
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
	ldr r7, [r12, #1240]
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
	ldr r7, [r12, #1244]
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
	sub r5, r3, #1
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1120
	movw r3, #1312
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1216
	movw r3, #1312
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #1184
	movw r3, #1184
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1152
	movw r3, #1152
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1376
	movw r3, #1152
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #256
	movw r3, #1152
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1408
	movw r3, #1376
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1280
	movw r3, #1344
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1248
	movw r3, #1408
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #1376]
	ldr r4, [r12, #1380]
	orr r5, r5, r4
	ldr r4, [r12, #1384]
	orr r5, r5, r4
	ldr r4, [r12, #1388]
	orr r5, r5, r4
	ldr r4, [r12, #1392]
	orr r5, r5, r4
	ldr r4, [r12, #1396]
	orr r5, r5, r4
	ldr r4, [r12, #1400]
	orr r5, r5, r4
	ldr r4, [r12, #1404]
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
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	ldr r10, [r12, #1472]
	ldr r4, [r12, #320]
	ldr r5, [r12, #1152]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1280]
	ldr r4, [r12, #324]
	ldr r5, [r12, #1156]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1284]
	ldr r4, [r12, #328]
	ldr r5, [r12, #1160]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1288]
	ldr r4, [r12, #332]
	ldr r5, [r12, #1164]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1292]
	ldr r4, [r12, #336]
	ldr r5, [r12, #1168]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1296]
	ldr r4, [r12, #340]
	ldr r5, [r12, #1172]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1300]
	ldr r4, [r12, #344]
	ldr r5, [r12, #1176]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1304]
	ldr r4, [r12, #348]
	ldr r5, [r12, #1180]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1308]
	ldr r4, [r12, #352]
	ldr r5, [r12, #1184]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1440]
	ldr r4, [r12, #356]
	ldr r5, [r12, #1188]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1444]
	ldr r4, [r12, #360]
	ldr r5, [r12, #1192]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1448]
	ldr r4, [r12, #364]
	ldr r5, [r12, #1196]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1452]
	ldr r4, [r12, #368]
	ldr r5, [r12, #1200]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1456]
	ldr r4, [r12, #372]
	ldr r5, [r12, #1204]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1460]
	ldr r4, [r12, #376]
	ldr r5, [r12, #1208]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1464]
	ldr r4, [r12, #380]
	ldr r5, [r12, #1212]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1468]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1056]
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
	ldr r7, [r12, #1060]
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
	ldr r7, [r12, #1064]
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
	ldr r7, [r12, #1068]
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
	ldr r7, [r12, #1072]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #1076]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #1080]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #1084]
	ldr r8, [r12, #124]
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
	ldr r5, [r12, #1056]
	ldr r4, [r12, #1060]
	orr r5, r5, r4
	ldr r4, [r12, #1064]
	orr r5, r5, r4
	ldr r4, [r12, #1068]
	orr r5, r5, r4
	ldr r4, [r12, #1072]
	orr r5, r5, r4
	ldr r4, [r12, #1076]
	orr r5, r5, r4
	ldr r4, [r12, #1080]
	orr r5, r5, r4
	ldr r4, [r12, #1084]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1024]
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
	ldr r7, [r12, #1028]
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
	ldr r7, [r12, #1032]
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
	ldr r7, [r12, #1036]
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
	ldr r7, [r12, #1040]
	ldr r8, [r12, #112]
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
	ldr r7, [r12, #1044]
	ldr r8, [r12, #116]
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
	ldr r7, [r12, #1048]
	ldr r8, [r12, #120]
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
	ldr r7, [r12, #1052]
	ldr r8, [r12, #124]
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
	ldr r4, [r12, #1048]
	orr r5, r5, r4
	ldr r4, [r12, #1052]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #1024
	movw r3, #384
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	ldr r4, [r12, #416]
	str r4, [r12, #992]
	ldr r4, [r12, #420]
	str r4, [r12, #996]
	ldr r4, [r12, #424]
	str r4, [r12, #1000]
	ldr r4, [r12, #428]
	str r4, [r12, #1004]
	ldr r4, [r12, #432]
	str r4, [r12, #1008]
	ldr r4, [r12, #436]
	str r4, [r12, #1012]
	ldr r4, [r12, #440]
	str r4, [r12, #1016]
	ldr r4, [r12, #444]
	str r4, [r12, #1020]
	mov r11, #256
23:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #992
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #992
	movw r3, #1248
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #512]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #992]
	ldr r5, [r12, #1024]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #992]
	ldr r4, [r12, #996]
	ldr r5, [r12, #1028]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #996]
	ldr r4, [r12, #1000]
	ldr r5, [r12, #1032]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1000]
	ldr r4, [r12, #1004]
	ldr r5, [r12, #1036]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1004]
	ldr r4, [r12, #1008]
	ldr r5, [r12, #1040]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1008]
	ldr r4, [r12, #1012]
	ldr r5, [r12, #1044]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1012]
	ldr r4, [r12, #1016]
	ldr r5, [r12, #1048]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1016]
	ldr r4, [r12, #1020]
	ldr r5, [r12, #1052]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1020]
	cmp r11, #0
	bne 23b
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1088
	movw r3, #384
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1312
	movw r2, #1056
	movw r3, #384
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1344
	movw r3, #992
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1312
	movw r3, #992
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1376
	movw r3, #192
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1408
	movw r3, #192
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	mov r11, #32
24:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1152]
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
	ldr r4, [r12, #320]
	str r4, [r12, #3424]
	ldr r4, [r12, #324]
	str r4, [r12, #3428]
	ldr r4, [r12, #328]
	str r4, [r12, #3432]
	ldr r4, [r12, #332]
	str r4, [r12, #3436]
	ldr r4, [r12, #336]
	str r4, [r12, #3440]
	ldr r4, [r12, #340]
	str r4, [r12, #3444]
	ldr r4, [r12, #344]
	str r4, [r12, #3448]
	ldr r4, [r12, #348]
	str r4, [r12, #3452]
	ldr r4, [r12, #352]
	str r4, [r12, #3456]
	ldr r4, [r12, #356]
	str r4, [r12, #3460]
	ldr r4, [r12, #360]
	str r4, [r12, #3464]
	ldr r4, [r12, #364]
	str r4, [r12, #3468]
	ldr r4, [r12, #368]
	str r4, [r12, #3472]
	ldr r4, [r12, #372]
	str r4, [r12, #3476]
	ldr r4, [r12, #376]
	str r4, [r12, #3480]
	ldr r4, [r12, #380]
	str r4, [r12, #3484]
	ldr r4, [r12, #224]
	str r4, [r12, #3488]
	ldr r4, [r12, #228]
	str r4, [r12, #3492]
	ldr r4, [r12, #232]
	str r4, [r12, #3496]
	ldr r4, [r12, #236]
	str r4, [r12, #3500]
	ldr r4, [r12, #240]
	str r4, [r12, #3504]
	ldr r4, [r12, #244]
	str r4, [r12, #3508]
	ldr r4, [r12, #248]
	str r4, [r12, #3512]
	ldr r4, [r12, #252]
	str r4, [r12, #3516]
	ldr r4, [r12, #256]
	str r4, [r12, #3520]
	ldr r4, [r12, #260]
	str r4, [r12, #3524]
	ldr r4, [r12, #264]
	str r4, [r12, #3528]
	ldr r4, [r12, #268]
	str r4, [r12, #3532]
	ldr r4, [r12, #272]
	str r4, [r12, #3536]
	ldr r4, [r12, #276]
	str r4, [r12, #3540]
	ldr r4, [r12, #280]
	str r4, [r12, #3544]
	ldr r4, [r12, #284]
	str r4, [r12, #3548]
	ldr r4, [r12, #288]
	str r4, [r12, #3552]
	ldr r4, [r12, #292]
	str r4, [r12, #3556]
	ldr r4, [r12, #296]
	str r4, [r12, #3560]
	ldr r4, [r12, #300]
	str r4, [r12, #3564]
	ldr r4, [r12, #304]
	str r4, [r12, #3568]
	ldr r4, [r12, #308]
	str r4, [r12, #3572]
	ldr r4, [r12, #312]
	str r4, [r12, #3576]
	ldr r4, [r12, #316]
	str r4, [r12, #3580]
	movw r4, #5734
	movt r4, #38525
	str r4, [r12, #512]
	movw r4, #3436
	movt r4, #53333
	str r4, [r12, #516]
	movw r4, #47640
	movt r4, #26332
	str r4, [r12, #520]
	movw r4, #11912
	movt r4, #9768
	str r4, [r12, #524]
	movw r4, #38101
	movt r4, #2766
	str r4, [r12, #528]
	movw r4, #11127
	movt r4, #32460
	str r4, [r12, #532]
	movw r4, #5946
	movt r4, #52428
	str r4, [r12, #536]
	movw r4, #28620
	movt r4, #19212
	str r4, [r12, #540]
	movw r4, #24148
	movt r4, #57402
	str r4, [r12, #544]
	movw r4, #2389
	movt r4, #29882
	str r4, [r12, #548]
	movw r4, #61597
	movt r4, #23280
	str r4, [r12, #552]
	movw r4, #21314
	movt r4, #4282
	str r4, [r12, #556]
	movw r4, #29745
	movt r4, #20676
	str r4, [r12, #560]
	movw r4, #19972
	movt r4, #33667
	str r4, [r12, #564]
	movw r4, #48404
	movt r4, #28437
	str r4, [r12, #568]
	movw r4, #18023
	movt r4, #14446
	str r4, [r12, #572]
	movw r4, #977
	movt r4, #0
	str r4, [r12, #576]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #580]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #584]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #588]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #592]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #596]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #600]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #604]
	mov r11, #37
25:
	sub r11, r11, #1
	mov r4, #7
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	cmp r11, #36
	beq 26f
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #6]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #5]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #4]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #3]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
	b 27f
26:
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #3]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
27:
	sub r9, r9, #64
	lsr r4, r9, #31
	mov r5, #0
	sub r4, r5, r4
	eor r9, r9, r4
	sub r9, r9, r4
	movw r8, #:lower16:({VG_SECP256K1_COMB}
	movt r8, #:upper16:({VG_SECP256K1_COMB}
2:
	add r8, pc
3:
	mov r4, #4096
	mul r4, r4, r11
	add r8, r8, r4
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3424]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3428]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3432]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3436]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3440]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3444]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3448]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3452]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3456]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3460]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3464]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3468]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3472]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3476]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3480]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3484]
	mov r7, #1
28:
	eor r10, r9, r7
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #3424]
	ldr r5, [r8, #0]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3424]
	ldr r4, [r12, #3428]
	ldr r5, [r8, #4]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3428]
	ldr r4, [r12, #3432]
	ldr r5, [r8, #8]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3432]
	ldr r4, [r12, #3436]
	ldr r5, [r8, #12]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3436]
	ldr r4, [r12, #3440]
	ldr r5, [r8, #16]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3440]
	ldr r4, [r12, #3444]
	ldr r5, [r8, #20]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3444]
	ldr r4, [r12, #3448]
	ldr r5, [r8, #24]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3448]
	ldr r4, [r12, #3452]
	ldr r5, [r8, #28]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3452]
	ldr r4, [r12, #3456]
	ldr r5, [r8, #32]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3456]
	ldr r4, [r12, #3460]
	ldr r5, [r8, #36]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3460]
	ldr r4, [r12, #3464]
	ldr r5, [r8, #40]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3464]
	ldr r4, [r12, #3468]
	ldr r5, [r8, #44]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3468]
	ldr r4, [r12, #3472]
	ldr r5, [r8, #48]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3472]
	ldr r4, [r12, #3476]
	ldr r5, [r8, #52]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3476]
	ldr r4, [r12, #3480]
	ldr r5, [r8, #56]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3480]
	ldr r4, [r12, #3484]
	ldr r5, [r8, #60]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3484]
	add r8, r8, #64
	add r7, r7, #1
	cmp r7, #65
	bne 28b
	movw r4, #977
	movt r4, #0
	str r4, [r12, #3488]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #3492]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3496]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3500]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3504]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3508]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3512]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #3516]
	eor r10, r9, #0
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #3456]
	ldr r5, [r12, #3488]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3456]
	ldr r4, [r12, #3460]
	ldr r5, [r12, #3492]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3460]
	ldr r4, [r12, #3464]
	ldr r5, [r12, #3496]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3464]
	ldr r4, [r12, #3468]
	ldr r5, [r12, #3500]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3468]
	ldr r4, [r12, #3472]
	ldr r5, [r12, #3504]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3472]
	ldr r4, [r12, #3476]
	ldr r5, [r12, #3508]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3476]
	ldr r4, [r12, #3480]
	ldr r5, [r12, #3512]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3480]
	ldr r4, [r12, #3484]
	ldr r5, [r12, #3516]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3484]
	ldr r4, [r12, #3488]
	ldr r5, [r12, #160]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3488]
	ldr r4, [r12, #3492]
	ldr r5, [r12, #164]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3492]
	ldr r4, [r12, #3496]
	ldr r5, [r12, #168]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3496]
	ldr r4, [r12, #3500]
	ldr r5, [r12, #172]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3500]
	ldr r4, [r12, #3504]
	ldr r5, [r12, #176]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3504]
	ldr r4, [r12, #3508]
	ldr r5, [r12, #180]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3508]
	ldr r4, [r12, #3512]
	ldr r5, [r12, #184]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3512]
	ldr r4, [r12, #3516]
	ldr r5, [r12, #188]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3516]
	mov r10, lr
	mov r0, r12
	movw r1, #704
	movw r2, #160
	movw r3, #3456
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	cmp r11, #36
	beq 29f
	mov r4, #7
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	ldrb r4, [r4, #6]
	sub r10, r4, #1
	b 210f
29:
	movw r10, #65535
	movt r10, #65535
210:
	ldr r4, [r12, #3456]
	ldr r5, [r12, #704]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3456]
	ldr r4, [r12, #3460]
	ldr r5, [r12, #708]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3460]
	ldr r4, [r12, #3464]
	ldr r5, [r12, #712]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3464]
	ldr r4, [r12, #3468]
	ldr r5, [r12, #716]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3468]
	ldr r4, [r12, #3472]
	ldr r5, [r12, #720]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3472]
	ldr r4, [r12, #3476]
	ldr r5, [r12, #724]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3476]
	ldr r4, [r12, #3480]
	ldr r5, [r12, #728]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3480]
	ldr r4, [r12, #3484]
	ldr r5, [r12, #732]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #3484]
	ldr r4, [r12, #512]
	str r4, [r12, #3328]
	ldr r4, [r12, #516]
	str r4, [r12, #3332]
	ldr r4, [r12, #520]
	str r4, [r12, #3336]
	ldr r4, [r12, #524]
	str r4, [r12, #3340]
	ldr r4, [r12, #528]
	str r4, [r12, #3344]
	ldr r4, [r12, #532]
	str r4, [r12, #3348]
	ldr r4, [r12, #536]
	str r4, [r12, #3352]
	ldr r4, [r12, #540]
	str r4, [r12, #3356]
	ldr r4, [r12, #544]
	str r4, [r12, #3360]
	ldr r4, [r12, #548]
	str r4, [r12, #3364]
	ldr r4, [r12, #552]
	str r4, [r12, #3368]
	ldr r4, [r12, #556]
	str r4, [r12, #3372]
	ldr r4, [r12, #560]
	str r4, [r12, #3376]
	ldr r4, [r12, #564]
	str r4, [r12, #3380]
	ldr r4, [r12, #568]
	str r4, [r12, #3384]
	ldr r4, [r12, #572]
	str r4, [r12, #3388]
	ldr r4, [r12, #576]
	str r4, [r12, #3392]
	ldr r4, [r12, #580]
	str r4, [r12, #3396]
	ldr r4, [r12, #584]
	str r4, [r12, #3400]
	ldr r4, [r12, #588]
	str r4, [r12, #3404]
	ldr r4, [r12, #592]
	str r4, [r12, #3408]
	ldr r4, [r12, #596]
	str r4, [r12, #3412]
	ldr r4, [r12, #600]
	str r4, [r12, #3416]
	ldr r4, [r12, #604]
	str r4, [r12, #3420]
	mov r10, lr
	mov r0, r12
	bl {vg_secp256k1_point_add_umaal}
	mov lr, r10
	ldr r4, [r12, #3232]
	str r4, [r12, #512]
	ldr r4, [r12, #3236]
	str r4, [r12, #516]
	ldr r4, [r12, #3240]
	str r4, [r12, #520]
	ldr r4, [r12, #3244]
	str r4, [r12, #524]
	ldr r4, [r12, #3248]
	str r4, [r12, #528]
	ldr r4, [r12, #3252]
	str r4, [r12, #532]
	ldr r4, [r12, #3256]
	str r4, [r12, #536]
	ldr r4, [r12, #3260]
	str r4, [r12, #540]
	ldr r4, [r12, #3264]
	str r4, [r12, #544]
	ldr r4, [r12, #3268]
	str r4, [r12, #548]
	ldr r4, [r12, #3272]
	str r4, [r12, #552]
	ldr r4, [r12, #3276]
	str r4, [r12, #556]
	ldr r4, [r12, #3280]
	str r4, [r12, #560]
	ldr r4, [r12, #3284]
	str r4, [r12, #564]
	ldr r4, [r12, #3288]
	str r4, [r12, #568]
	ldr r4, [r12, #3292]
	str r4, [r12, #572]
	ldr r4, [r12, #3296]
	str r4, [r12, #576]
	ldr r4, [r12, #3300]
	str r4, [r12, #580]
	ldr r4, [r12, #3304]
	str r4, [r12, #584]
	ldr r4, [r12, #3308]
	str r4, [r12, #588]
	ldr r4, [r12, #3312]
	str r4, [r12, #592]
	ldr r4, [r12, #3316]
	str r4, [r12, #596]
	ldr r4, [r12, #3320]
	str r4, [r12, #600]
	ldr r4, [r12, #3324]
	str r4, [r12, #604]
	cmp r11, #0
	bne 25b
	ldr r4, [r12, #512]
	str r4, [r12, #1376]
	ldr r4, [r12, #516]
	str r4, [r12, #1380]
	ldr r4, [r12, #520]
	str r4, [r12, #1384]
	ldr r4, [r12, #524]
	str r4, [r12, #1388]
	ldr r4, [r12, #528]
	str r4, [r12, #1392]
	ldr r4, [r12, #532]
	str r4, [r12, #1396]
	ldr r4, [r12, #536]
	str r4, [r12, #1400]
	ldr r4, [r12, #540]
	str r4, [r12, #1404]
	ldr r4, [r12, #544]
	str r4, [r12, #1408]
	ldr r4, [r12, #548]
	str r4, [r12, #1412]
	ldr r4, [r12, #552]
	str r4, [r12, #1416]
	ldr r4, [r12, #556]
	str r4, [r12, #1420]
	ldr r4, [r12, #560]
	str r4, [r12, #1424]
	ldr r4, [r12, #564]
	str r4, [r12, #1428]
	ldr r4, [r12, #568]
	str r4, [r12, #1432]
	ldr r4, [r12, #572]
	str r4, [r12, #1436]
	ldr r4, [r12, #576]
	str r4, [r12, #1248]
	ldr r4, [r12, #580]
	str r4, [r12, #1252]
	ldr r4, [r12, #584]
	str r4, [r12, #1256]
	ldr r4, [r12, #588]
	str r4, [r12, #1260]
	ldr r4, [r12, #592]
	str r4, [r12, #1264]
	ldr r4, [r12, #596]
	str r4, [r12, #1268]
	ldr r4, [r12, #600]
	str r4, [r12, #1272]
	ldr r4, [r12, #604]
	str r4, [r12, #1276]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #512]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #516]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #520]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #524]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #528]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #532]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #536]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #540]
	movw r4, #977
	movt r4, #0
	str r4, [r12, #544]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #548]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #552]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #556]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #560]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #564]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #568]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #572]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #576]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #580]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #584]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #588]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #592]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #596]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #600]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #604]
	mov r11, #32
211:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1184]
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
	bne 211b
	ldr r4, [r12, #1280]
	str r4, [r12, #3424]
	ldr r4, [r12, #1284]
	str r4, [r12, #3428]
	ldr r4, [r12, #1288]
	str r4, [r12, #3432]
	ldr r4, [r12, #1292]
	str r4, [r12, #3436]
	ldr r4, [r12, #1296]
	str r4, [r12, #3440]
	ldr r4, [r12, #1300]
	str r4, [r12, #3444]
	ldr r4, [r12, #1304]
	str r4, [r12, #3448]
	ldr r4, [r12, #1308]
	str r4, [r12, #3452]
	ldr r4, [r12, #1440]
	str r4, [r12, #3456]
	ldr r4, [r12, #1444]
	str r4, [r12, #3460]
	ldr r4, [r12, #1448]
	str r4, [r12, #3464]
	ldr r4, [r12, #1452]
	str r4, [r12, #3468]
	ldr r4, [r12, #1456]
	str r4, [r12, #3472]
	ldr r4, [r12, #1460]
	str r4, [r12, #3476]
	ldr r4, [r12, #1464]
	str r4, [r12, #3480]
	ldr r4, [r12, #1468]
	str r4, [r12, #3484]
	ldr r4, [r12, #224]
	str r4, [r12, #3488]
	ldr r4, [r12, #228]
	str r4, [r12, #3492]
	ldr r4, [r12, #232]
	str r4, [r12, #3496]
	ldr r4, [r12, #236]
	str r4, [r12, #3500]
	ldr r4, [r12, #240]
	str r4, [r12, #3504]
	ldr r4, [r12, #244]
	str r4, [r12, #3508]
	ldr r4, [r12, #248]
	str r4, [r12, #3512]
	ldr r4, [r12, #252]
	str r4, [r12, #3516]
	ldr r4, [r12, #256]
	str r4, [r12, #3520]
	ldr r4, [r12, #260]
	str r4, [r12, #3524]
	ldr r4, [r12, #264]
	str r4, [r12, #3528]
	ldr r4, [r12, #268]
	str r4, [r12, #3532]
	ldr r4, [r12, #272]
	str r4, [r12, #3536]
	ldr r4, [r12, #276]
	str r4, [r12, #3540]
	ldr r4, [r12, #280]
	str r4, [r12, #3544]
	ldr r4, [r12, #284]
	str r4, [r12, #3548]
	ldr r4, [r12, #288]
	str r4, [r12, #3552]
	ldr r4, [r12, #292]
	str r4, [r12, #3556]
	ldr r4, [r12, #296]
	str r4, [r12, #3560]
	ldr r4, [r12, #300]
	str r4, [r12, #3564]
	ldr r4, [r12, #304]
	str r4, [r12, #3568]
	ldr r4, [r12, #308]
	str r4, [r12, #3572]
	ldr r4, [r12, #312]
	str r4, [r12, #3576]
	ldr r4, [r12, #316]
	str r4, [r12, #3580]
	mov r11, #256
212:
	sub r11, r11, #1
	ldr r4, [r12, #512]
	str r4, [r12, #3328]
	ldr r4, [r12, #516]
	str r4, [r12, #3332]
	ldr r4, [r12, #520]
	str r4, [r12, #3336]
	ldr r4, [r12, #524]
	str r4, [r12, #3340]
	ldr r4, [r12, #528]
	str r4, [r12, #3344]
	ldr r4, [r12, #532]
	str r4, [r12, #3348]
	ldr r4, [r12, #536]
	str r4, [r12, #3352]
	ldr r4, [r12, #540]
	str r4, [r12, #3356]
	ldr r4, [r12, #544]
	str r4, [r12, #3360]
	ldr r4, [r12, #548]
	str r4, [r12, #3364]
	ldr r4, [r12, #552]
	str r4, [r12, #3368]
	ldr r4, [r12, #556]
	str r4, [r12, #3372]
	ldr r4, [r12, #560]
	str r4, [r12, #3376]
	ldr r4, [r12, #564]
	str r4, [r12, #3380]
	ldr r4, [r12, #568]
	str r4, [r12, #3384]
	ldr r4, [r12, #572]
	str r4, [r12, #3388]
	ldr r4, [r12, #576]
	str r4, [r12, #3392]
	ldr r4, [r12, #580]
	str r4, [r12, #3396]
	ldr r4, [r12, #584]
	str r4, [r12, #3400]
	ldr r4, [r12, #588]
	str r4, [r12, #3404]
	ldr r4, [r12, #592]
	str r4, [r12, #3408]
	ldr r4, [r12, #596]
	str r4, [r12, #3412]
	ldr r4, [r12, #600]
	str r4, [r12, #3416]
	ldr r4, [r12, #604]
	str r4, [r12, #3420]
	mov r10, lr
	mov r0, r12
	bl {vg_secp256k1_point_a0_double_umaal}
	mov lr, r10
	ldr r4, [r12, #3232]
	str r4, [r12, #3328]
	ldr r4, [r12, #3236]
	str r4, [r12, #3332]
	ldr r4, [r12, #3240]
	str r4, [r12, #3336]
	ldr r4, [r12, #3244]
	str r4, [r12, #3340]
	ldr r4, [r12, #3248]
	str r4, [r12, #3344]
	ldr r4, [r12, #3252]
	str r4, [r12, #3348]
	ldr r4, [r12, #3256]
	str r4, [r12, #3352]
	ldr r4, [r12, #3260]
	str r4, [r12, #3356]
	ldr r4, [r12, #3264]
	str r4, [r12, #3360]
	ldr r4, [r12, #3268]
	str r4, [r12, #3364]
	ldr r4, [r12, #3272]
	str r4, [r12, #3368]
	ldr r4, [r12, #3276]
	str r4, [r12, #3372]
	ldr r4, [r12, #3280]
	str r4, [r12, #3376]
	ldr r4, [r12, #3284]
	str r4, [r12, #3380]
	ldr r4, [r12, #3288]
	str r4, [r12, #3384]
	ldr r4, [r12, #3292]
	str r4, [r12, #3388]
	ldr r4, [r12, #3296]
	str r4, [r12, #3392]
	ldr r4, [r12, #3300]
	str r4, [r12, #3396]
	ldr r4, [r12, #3304]
	str r4, [r12, #3400]
	ldr r4, [r12, #3308]
	str r4, [r12, #3404]
	ldr r4, [r12, #3312]
	str r4, [r12, #3408]
	ldr r4, [r12, #3316]
	str r4, [r12, #3412]
	ldr r4, [r12, #3320]
	str r4, [r12, #3416]
	ldr r4, [r12, #3324]
	str r4, [r12, #3420]
	mov r10, lr
	mov r0, r12
	bl {vg_secp256k1_point_a0_add_affine_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #0]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #3328]
	ldr r5, [r12, #3232]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #512]
	ldr r4, [r12, #3332]
	ldr r5, [r12, #3236]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #516]
	ldr r4, [r12, #3336]
	ldr r5, [r12, #3240]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #520]
	ldr r4, [r12, #3340]
	ldr r5, [r12, #3244]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #524]
	ldr r4, [r12, #3344]
	ldr r5, [r12, #3248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #528]
	ldr r4, [r12, #3348]
	ldr r5, [r12, #3252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #532]
	ldr r4, [r12, #3352]
	ldr r5, [r12, #3256]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #536]
	ldr r4, [r12, #3356]
	ldr r5, [r12, #3260]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #540]
	ldr r4, [r12, #3360]
	ldr r5, [r12, #3264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #544]
	ldr r4, [r12, #3364]
	ldr r5, [r12, #3268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #548]
	ldr r4, [r12, #3368]
	ldr r5, [r12, #3272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #552]
	ldr r4, [r12, #3372]
	ldr r5, [r12, #3276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #556]
	ldr r4, [r12, #3376]
	ldr r5, [r12, #3280]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #560]
	ldr r4, [r12, #3380]
	ldr r5, [r12, #3284]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #564]
	ldr r4, [r12, #3384]
	ldr r5, [r12, #3288]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #568]
	ldr r4, [r12, #3388]
	ldr r5, [r12, #3292]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #572]
	ldr r4, [r12, #3392]
	ldr r5, [r12, #3296]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #576]
	ldr r4, [r12, #3396]
	ldr r5, [r12, #3300]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #580]
	ldr r4, [r12, #3400]
	ldr r5, [r12, #3304]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #584]
	ldr r4, [r12, #3404]
	ldr r5, [r12, #3308]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #588]
	ldr r4, [r12, #3408]
	ldr r5, [r12, #3312]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #592]
	ldr r4, [r12, #3412]
	ldr r5, [r12, #3316]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #596]
	ldr r4, [r12, #3416]
	ldr r5, [r12, #3320]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #600]
	ldr r4, [r12, #3420]
	ldr r5, [r12, #3324]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #604]
	cmp r11, #0
	bne 212b
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #1376
	movw r3, #512
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #1408
	movw r3, #544
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #1248
	movw r3, #576
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #1376
	movw r3, #1408
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #512
	movw r3, #544
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #800
	movw r3, #832
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #928
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #1376
	movw r3, #1248
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #512
	movw r3, #576
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #960
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #800
	movw r3, #864
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #960
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #1408
	movw r3, #1248
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #544
	movw r3, #576
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #960
	movw r3, #608
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #832
	movw r3, #864
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #960
	movw r3, #608
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #256
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #288
	movw r3, #864
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #608
	movw r3, #672
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #832
	movw r3, #672
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #832
	movw r3, #672
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #608
	movw r3, #672
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #800
	movw r3, #800
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #800
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #256
	movw r3, #864
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #288
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #864
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #800
	movw r3, #864
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #864
	movw r2, #256
	movw r3, #864
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #864
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #832
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #640
	movw r2, #640
	movw r3, #800
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #960
	movw r3, #928
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #896
	movw r3, #608
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #608
	movw r2, #608
	movw r3, #800
	bl {vg_secp256k1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #896
	movw r3, #832
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #960
	movw r3, #672
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #672
	movw r2, #672
	movw r3, #800
	bl {vg_secp256k1_add_mod_p}
	mov lr, r10
	ldr r4, [r12, #608]
	str r4, [r12, #512]
	ldr r4, [r12, #612]
	str r4, [r12, #516]
	ldr r4, [r12, #616]
	str r4, [r12, #520]
	ldr r4, [r12, #620]
	str r4, [r12, #524]
	ldr r4, [r12, #624]
	str r4, [r12, #528]
	ldr r4, [r12, #628]
	str r4, [r12, #532]
	ldr r4, [r12, #632]
	str r4, [r12, #536]
	ldr r4, [r12, #636]
	str r4, [r12, #540]
	ldr r4, [r12, #640]
	str r4, [r12, #544]
	ldr r4, [r12, #644]
	str r4, [r12, #548]
	ldr r4, [r12, #648]
	str r4, [r12, #552]
	ldr r4, [r12, #652]
	str r4, [r12, #556]
	ldr r4, [r12, #656]
	str r4, [r12, #560]
	ldr r4, [r12, #660]
	str r4, [r12, #564]
	ldr r4, [r12, #664]
	str r4, [r12, #568]
	ldr r4, [r12, #668]
	str r4, [r12, #572]
	ldr r4, [r12, #672]
	str r4, [r12, #576]
	ldr r4, [r12, #676]
	str r4, [r12, #580]
	ldr r4, [r12, #680]
	str r4, [r12, #584]
	ldr r4, [r12, #684]
	str r4, [r12, #588]
	ldr r4, [r12, #688]
	str r4, [r12, #592]
	ldr r4, [r12, #692]
	str r4, [r12, #596]
	ldr r4, [r12, #696]
	str r4, [r12, #600]
	ldr r4, [r12, #700]
	str r4, [r12, #604]
	ldr r4, [r12, #224]
	str r4, [r12, #992]
	ldr r4, [r12, #228]
	str r4, [r12, #996]
	ldr r4, [r12, #232]
	str r4, [r12, #1000]
	ldr r4, [r12, #236]
	str r4, [r12, #1004]
	ldr r4, [r12, #240]
	str r4, [r12, #1008]
	ldr r4, [r12, #244]
	str r4, [r12, #1012]
	ldr r4, [r12, #248]
	str r4, [r12, #1016]
	ldr r4, [r12, #252]
	str r4, [r12, #1020]
	mov r11, #256
213:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #992
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #992
	movw r3, #576
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #256]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #992]
	ldr r5, [r12, #1024]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #992]
	ldr r4, [r12, #996]
	ldr r5, [r12, #1028]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #996]
	ldr r4, [r12, #1000]
	ldr r5, [r12, #1032]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1000]
	ldr r4, [r12, #1004]
	ldr r5, [r12, #1036]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1004]
	ldr r4, [r12, #1008]
	ldr r5, [r12, #1040]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1008]
	ldr r4, [r12, #1012]
	ldr r5, [r12, #1044]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1012]
	ldr r4, [r12, #1016]
	ldr r5, [r12, #1048]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1016]
	ldr r4, [r12, #1020]
	ldr r5, [r12, #1052]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1020]
	cmp r11, #0
	bne 213b
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #512
	movw r3, #992
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1152
	movw r3, #192
	bl {vg_secp256k1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1184
	movw r3, #384
	bl {vg_secp256k1_mul_mod_n_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1280
	movw r3, #1312
	bl {vg_secp256k1_sub_mod_n}
	mov lr, r10
	ldr r5, [r12, #576]
	ldr r4, [r12, #580]
	orr r5, r5, r4
	ldr r4, [r12, #584]
	orr r5, r5, r4
	ldr r4, [r12, #588]
	orr r5, r5, r4
	ldr r4, [r12, #592]
	orr r5, r5, r4
	ldr r4, [r12, #596]
	orr r5, r5, r4
	ldr r4, [r12, #600]
	orr r5, r5, r4
	ldr r4, [r12, #604]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	ldr r5, [r12, #1344]
	ldr r4, [r12, #1348]
	orr r5, r5, r4
	ldr r4, [r12, #1352]
	orr r5, r5, r4
	ldr r4, [r12, #1356]
	orr r5, r5, r4
	ldr r4, [r12, #1360]
	orr r5, r5, r4
	ldr r4, [r12, #1364]
	orr r5, r5, r4
	ldr r4, [r12, #1368]
	orr r5, r5, r4
	ldr r4, [r12, #1372]
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
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	ldr r10, [r12, #1472]
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

vg_ecdsa_secp256k1_sign:
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
	ldr r0, [r6, #28]
	rev r0, r0
	str r0, [r8, #156]
	movw r1, #16705
	movt r1, #53302
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
	str r2, [r8, #28]
	ldr r0, [r6, #24]
	rev r0, r0
	str r0, [r8, #152]
	movw r1, #24204
	movt r1, #49106
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
	str r2, [r8, #24]
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #41019
	movt r1, #44872
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
	movw r1, #56550
	movt r1, #47790
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
	movw r1, #65534
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
	ldr r0, [r8, #156]
	ldr r1, [r8, #28]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #156]
	ldr r0, [r8, #152]
	ldr r1, [r8, #24]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #152]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2313]
	ldr r0, [r5, #28]
	str r0, [r11, #2317]
	ldr r0, [r8, #128]
	str r0, [r11, #2321]
	ldr r0, [r8, #132]
	str r0, [r11, #2325]
	ldr r0, [r8, #136]
	str r0, [r11, #2329]
	ldr r0, [r8, #140]
	str r0, [r11, #2333]
	ldr r0, [r8, #144]
	str r0, [r11, #2337]
	ldr r0, [r8, #148]
	str r0, [r11, #2341]
	ldr r0, [r8, #152]
	str r0, [r11, #2345]
	ldr r0, [r8, #156]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2313]
	ldr r0, [r5, #28]
	str r0, [r11, #2317]
	ldr r0, [r8, #128]
	str r0, [r11, #2321]
	ldr r0, [r8, #132]
	str r0, [r11, #2325]
	ldr r0, [r8, #136]
	str r0, [r11, #2329]
	ldr r0, [r8, #140]
	str r0, [r11, #2333]
	ldr r0, [r8, #144]
	str r0, [r11, #2337]
	ldr r0, [r8, #148]
	str r0, [r11, #2341]
	ldr r0, [r8, #152]
	str r0, [r11, #2345]
	ldr r0, [r8, #156]
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
	bl {vg_ecdsa_secp256k1_sign_k}
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
	ldr r0, [r6, #20]
	str r0, [r8, #240]
	ldr r0, [r6, #24]
	str r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2309]
	ldr r0, [r5, #28]
	str r0, [r11, #2313]
	ldr r0, [r8, #216]
	str r0, [r11, #2317]
	ldr r0, [r8, #220]
	str r0, [r11, #2321]
	ldr r0, [r8, #224]
	str r0, [r11, #2325]
	ldr r0, [r8, #228]
	str r0, [r11, #2329]
	ldr r0, [r8, #232]
	str r0, [r11, #2333]
	ldr r0, [r8, #236]
	str r0, [r11, #2337]
	ldr r0, [r8, #240]
	str r0, [r11, #2341]
	ldr r0, [r8, #244]
	str r0, [r11, #2345]
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
	movw r7, #93
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #221
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
	ldr r0, [r5, #24]
	str r0, [r11, #2309]
	ldr r0, [r5, #28]
	str r0, [r11, #2313]
	ldr r0, [r8, #216]
	str r0, [r11, #2317]
	ldr r0, [r8, #220]
	str r0, [r11, #2321]
	ldr r0, [r8, #224]
	str r0, [r11, #2325]
	ldr r0, [r8, #228]
	str r0, [r11, #2329]
	ldr r0, [r8, #232]
	str r0, [r11, #2333]
	ldr r0, [r8, #236]
	str r0, [r11, #2337]
	ldr r0, [r8, #240]
	str r0, [r11, #2341]
	ldr r0, [r8, #244]
	str r0, [r11, #2345]
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
	movw r7, #93
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #221
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
	ldr r0, [r8, #84]
	str r0, [r8, #380]
	ldr r0, [r8, #88]
	str r0, [r8, #384]
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
	str r0, [r8, #388]
	ldr r0, [r8, #68]
	str r0, [r8, #392]
	ldr r0, [r8, #72]
	str r0, [r8, #396]
	ldr r0, [r8, #76]
	str r0, [r8, #400]
	ldr r0, [r8, #80]
	str r0, [r8, #404]
	ldr r0, [r8, #84]
	str r0, [r8, #408]
	ldr r0, [r8, #88]
	str r0, [r8, #412]
	ldr r0, [r8, #176]
	mov r1, r5
	add r2, r8, #216
	add r3, r8, #360
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_secp256k1_sign_k}
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
	ldr r0, [r6, #28]
	rev r0, r0
	str r0, [r8, #156]
	movw r1, #16705
	movt r1, #53302
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
	str r2, [r8, #28]
	ldr r0, [r6, #24]
	rev r0, r0
	str r0, [r8, #152]
	movw r1, #24204
	movt r1, #49106
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
	str r2, [r8, #24]
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #41019
	movt r1, #44872
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
	movw r1, #56550
	movt r1, #47790
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
	movw r1, #65534
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
	ldr r0, [r8, #156]
	ldr r1, [r8, #28]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #156]
	ldr r0, [r8, #152]
	ldr r1, [r8, #24]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #152]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2345]
	ldr r0, [r5, #28]
	str r0, [r11, #2349]
	ldr r0, [r8, #128]
	str r0, [r11, #2353]
	ldr r0, [r8, #132]
	str r0, [r11, #2357]
	ldr r0, [r8, #136]
	str r0, [r11, #2361]
	ldr r0, [r8, #140]
	str r0, [r11, #2365]
	ldr r0, [r8, #144]
	str r0, [r11, #2369]
	ldr r0, [r8, #148]
	str r0, [r11, #2373]
	ldr r0, [r8, #152]
	str r0, [r11, #2377]
	ldr r0, [r8, #156]
	str r0, [r11, #2381]
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
	movw r7, #129
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #257
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
	ldr r0, [r5, #24]
	str r0, [r11, #2345]
	ldr r0, [r5, #28]
	str r0, [r11, #2349]
	ldr r0, [r8, #128]
	str r0, [r11, #2353]
	ldr r0, [r8, #132]
	str r0, [r11, #2357]
	ldr r0, [r8, #136]
	str r0, [r11, #2361]
	ldr r0, [r8, #140]
	str r0, [r11, #2365]
	ldr r0, [r8, #144]
	str r0, [r11, #2369]
	ldr r0, [r8, #148]
	str r0, [r11, #2373]
	ldr r0, [r8, #152]
	str r0, [r11, #2377]
	ldr r0, [r8, #156]
	str r0, [r11, #2381]
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
	movw r7, #129
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #257
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
	bl {vg_ecdsa_secp256k1_sign_k}
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
	ldr r0, [r6, #28]
	rev r0, r0
	str r0, [r8, #156]
	movw r1, #16705
	movt r1, #53302
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
	str r2, [r8, #28]
	ldr r0, [r6, #24]
	rev r0, r0
	str r0, [r8, #152]
	movw r1, #24204
	movt r1, #49106
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
	str r2, [r8, #24]
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #41019
	movt r1, #44872
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
	movw r1, #56550
	movt r1, #47790
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
	movw r1, #65534
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
	ldr r0, [r8, #156]
	ldr r1, [r8, #28]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #156]
	ldr r0, [r8, #152]
	ldr r1, [r8, #24]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #152]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2329]
	ldr r0, [r5, #28]
	str r0, [r11, #2333]
	ldr r0, [r8, #128]
	str r0, [r11, #2337]
	ldr r0, [r8, #132]
	str r0, [r11, #2341]
	ldr r0, [r8, #136]
	str r0, [r11, #2345]
	ldr r0, [r8, #140]
	str r0, [r11, #2349]
	ldr r0, [r8, #144]
	str r0, [r11, #2353]
	ldr r0, [r8, #148]
	str r0, [r11, #2357]
	ldr r0, [r8, #152]
	str r0, [r11, #2361]
	ldr r0, [r8, #156]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2329]
	ldr r0, [r5, #28]
	str r0, [r11, #2333]
	ldr r0, [r8, #128]
	str r0, [r11, #2337]
	ldr r0, [r8, #132]
	str r0, [r11, #2341]
	ldr r0, [r8, #136]
	str r0, [r11, #2345]
	ldr r0, [r8, #140]
	str r0, [r11, #2349]
	ldr r0, [r8, #144]
	str r0, [r11, #2353]
	ldr r0, [r8, #148]
	str r0, [r11, #2357]
	ldr r0, [r8, #152]
	str r0, [r11, #2361]
	ldr r0, [r8, #156]
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
	bl {vg_ecdsa_secp256k1_sign_k}
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
	ldr r0, [r6, #28]
	rev r0, r0
	str r0, [r8, #156]
	movw r1, #16705
	movt r1, #53302
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
	str r2, [r8, #28]
	ldr r0, [r6, #24]
	rev r0, r0
	str r0, [r8, #152]
	movw r1, #24204
	movt r1, #49106
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
	str r2, [r8, #24]
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #41019
	movt r1, #44872
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
	movw r1, #56550
	movt r1, #47790
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
	movw r1, #65534
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
	ldr r0, [r8, #156]
	ldr r1, [r8, #28]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #156]
	ldr r0, [r8, #152]
	ldr r1, [r8, #24]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #152]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2313]
	ldr r0, [r5, #28]
	str r0, [r11, #2317]
	ldr r0, [r8, #128]
	str r0, [r11, #2321]
	ldr r0, [r8, #132]
	str r0, [r11, #2325]
	ldr r0, [r8, #136]
	str r0, [r11, #2329]
	ldr r0, [r8, #140]
	str r0, [r11, #2333]
	ldr r0, [r8, #144]
	str r0, [r11, #2337]
	ldr r0, [r8, #148]
	str r0, [r11, #2341]
	ldr r0, [r8, #152]
	str r0, [r11, #2345]
	ldr r0, [r8, #156]
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
	movw r7, #97
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
	ldr r0, [r5, #24]
	str r0, [r11, #2313]
	ldr r0, [r5, #28]
	str r0, [r11, #2317]
	ldr r0, [r8, #128]
	str r0, [r11, #2321]
	ldr r0, [r8, #132]
	str r0, [r11, #2325]
	ldr r0, [r8, #136]
	str r0, [r11, #2329]
	ldr r0, [r8, #140]
	str r0, [r11, #2333]
	ldr r0, [r8, #144]
	str r0, [r11, #2337]
	ldr r0, [r8, #148]
	str r0, [r11, #2341]
	ldr r0, [r8, #152]
	str r0, [r11, #2345]
	ldr r0, [r8, #156]
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
	movw r7, #97
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
	bl {vg_ecdsa_secp256k1_sign_k}
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
	ldr r0, [r6, #20]
	str r0, [r8, #240]
	ldr r0, [r6, #24]
	str r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2309]
	ldr r0, [r5, #28]
	str r0, [r11, #2313]
	ldr r0, [r8, #216]
	str r0, [r11, #2317]
	ldr r0, [r8, #220]
	str r0, [r11, #2321]
	ldr r0, [r8, #224]
	str r0, [r11, #2325]
	ldr r0, [r8, #228]
	str r0, [r11, #2329]
	ldr r0, [r8, #232]
	str r0, [r11, #2333]
	ldr r0, [r8, #236]
	str r0, [r11, #2337]
	ldr r0, [r8, #240]
	str r0, [r11, #2341]
	ldr r0, [r8, #244]
	str r0, [r11, #2345]
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
	movw r7, #93
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
	ldr r0, [r5, #24]
	str r0, [r11, #2309]
	ldr r0, [r5, #28]
	str r0, [r11, #2313]
	ldr r0, [r8, #216]
	str r0, [r11, #2317]
	ldr r0, [r8, #220]
	str r0, [r11, #2321]
	ldr r0, [r8, #224]
	str r0, [r11, #2325]
	ldr r0, [r8, #228]
	str r0, [r11, #2329]
	ldr r0, [r8, #232]
	str r0, [r11, #2333]
	ldr r0, [r8, #236]
	str r0, [r11, #2337]
	ldr r0, [r8, #240]
	str r0, [r11, #2341]
	ldr r0, [r8, #244]
	str r0, [r11, #2345]
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
	movw r7, #93
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
	ldr r0, [r8, #84]
	str r0, [r8, #380]
	ldr r0, [r8, #88]
	str r0, [r8, #384]
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
	str r0, [r8, #388]
	ldr r0, [r8, #68]
	str r0, [r8, #392]
	ldr r0, [r8, #72]
	str r0, [r8, #396]
	ldr r0, [r8, #76]
	str r0, [r8, #400]
	ldr r0, [r8, #80]
	str r0, [r8, #404]
	ldr r0, [r8, #84]
	str r0, [r8, #408]
	ldr r0, [r8, #88]
	str r0, [r8, #412]
	ldr r0, [r8, #176]
	mov r1, r5
	add r2, r8, #216
	add r3, r8, #360
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_secp256k1_sign_k}
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
	str r0, [r8, #228]
	ldr r0, [r6, #4]
	str r0, [r8, #232]
	ldr r0, [r6, #8]
	str r0, [r8, #236]
	ldr r0, [r6, #12]
	str r0, [r8, #240]
	ldr r0, [r6, #16]
	str r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2301]
	ldr r0, [r5, #28]
	str r0, [r11, #2305]
	ldr r0, [r8, #216]
	str r0, [r11, #2309]
	ldr r0, [r8, #220]
	str r0, [r11, #2313]
	ldr r0, [r8, #224]
	str r0, [r11, #2317]
	ldr r0, [r8, #228]
	str r0, [r11, #2321]
	ldr r0, [r8, #232]
	str r0, [r11, #2325]
	ldr r0, [r8, #236]
	str r0, [r11, #2329]
	ldr r0, [r8, #240]
	str r0, [r11, #2333]
	ldr r0, [r8, #244]
	str r0, [r11, #2337]
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
	movw r7, #85
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #149
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
	ldr r0, [r5, #24]
	str r0, [r11, #2301]
	ldr r0, [r5, #28]
	str r0, [r11, #2305]
	ldr r0, [r8, #216]
	str r0, [r11, #2309]
	ldr r0, [r8, #220]
	str r0, [r11, #2313]
	ldr r0, [r8, #224]
	str r0, [r11, #2317]
	ldr r0, [r8, #228]
	str r0, [r11, #2321]
	ldr r0, [r8, #232]
	str r0, [r11, #2325]
	ldr r0, [r8, #236]
	str r0, [r11, #2329]
	ldr r0, [r8, #240]
	str r0, [r11, #2333]
	ldr r0, [r8, #244]
	str r0, [r11, #2337]
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
	movw r7, #85
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #149
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
	bl {vg_ecdsa_secp256k1_sign_k}
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
	str r0, [r8, #232]
	ldr r0, [r6, #4]
	str r0, [r8, #236]
	ldr r0, [r6, #8]
	str r0, [r8, #240]
	ldr r0, [r6, #12]
	str r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2297]
	ldr r0, [r5, #28]
	str r0, [r11, #2301]
	ldr r0, [r8, #216]
	str r0, [r11, #2305]
	ldr r0, [r8, #220]
	str r0, [r11, #2309]
	ldr r0, [r8, #224]
	str r0, [r11, #2313]
	ldr r0, [r8, #228]
	str r0, [r11, #2317]
	ldr r0, [r8, #232]
	str r0, [r11, #2321]
	ldr r0, [r8, #236]
	str r0, [r11, #2325]
	ldr r0, [r8, #240]
	str r0, [r11, #2329]
	ldr r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2297]
	ldr r0, [r5, #28]
	str r0, [r11, #2301]
	ldr r0, [r8, #216]
	str r0, [r11, #2305]
	ldr r0, [r8, #220]
	str r0, [r11, #2309]
	ldr r0, [r8, #224]
	str r0, [r11, #2313]
	ldr r0, [r8, #228]
	str r0, [r11, #2317]
	ldr r0, [r8, #232]
	str r0, [r11, #2321]
	ldr r0, [r8, #236]
	str r0, [r11, #2325]
	ldr r0, [r8, #240]
	str r0, [r11, #2329]
	ldr r0, [r8, #244]
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
	bl {vg_ecdsa_secp256k1_sign_k}
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

vg_ecdsa_secp256k1_sign_umaal:
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
	ldr r0, [r6, #28]
	rev r0, r0
	str r0, [r8, #156]
	movw r1, #16705
	movt r1, #53302
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
	str r2, [r8, #28]
	ldr r0, [r6, #24]
	rev r0, r0
	str r0, [r8, #152]
	movw r1, #24204
	movt r1, #49106
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
	str r2, [r8, #24]
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #41019
	movt r1, #44872
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
	movw r1, #56550
	movt r1, #47790
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
	movw r1, #65534
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
	ldr r0, [r8, #156]
	ldr r1, [r8, #28]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #156]
	ldr r0, [r8, #152]
	ldr r1, [r8, #24]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #152]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2313]
	ldr r0, [r5, #28]
	str r0, [r11, #2317]
	ldr r0, [r8, #128]
	str r0, [r11, #2321]
	ldr r0, [r8, #132]
	str r0, [r11, #2325]
	ldr r0, [r8, #136]
	str r0, [r11, #2329]
	ldr r0, [r8, #140]
	str r0, [r11, #2333]
	ldr r0, [r8, #144]
	str r0, [r11, #2337]
	ldr r0, [r8, #148]
	str r0, [r11, #2341]
	ldr r0, [r8, #152]
	str r0, [r11, #2345]
	ldr r0, [r8, #156]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2313]
	ldr r0, [r5, #28]
	str r0, [r11, #2317]
	ldr r0, [r8, #128]
	str r0, [r11, #2321]
	ldr r0, [r8, #132]
	str r0, [r11, #2325]
	ldr r0, [r8, #136]
	str r0, [r11, #2329]
	ldr r0, [r8, #140]
	str r0, [r11, #2333]
	ldr r0, [r8, #144]
	str r0, [r11, #2337]
	ldr r0, [r8, #148]
	str r0, [r11, #2341]
	ldr r0, [r8, #152]
	str r0, [r11, #2345]
	ldr r0, [r8, #156]
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
	bl {vg_ecdsa_secp256k1_sign_k_umaal}
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
	ldr r0, [r6, #20]
	str r0, [r8, #240]
	ldr r0, [r6, #24]
	str r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2309]
	ldr r0, [r5, #28]
	str r0, [r11, #2313]
	ldr r0, [r8, #216]
	str r0, [r11, #2317]
	ldr r0, [r8, #220]
	str r0, [r11, #2321]
	ldr r0, [r8, #224]
	str r0, [r11, #2325]
	ldr r0, [r8, #228]
	str r0, [r11, #2329]
	ldr r0, [r8, #232]
	str r0, [r11, #2333]
	ldr r0, [r8, #236]
	str r0, [r11, #2337]
	ldr r0, [r8, #240]
	str r0, [r11, #2341]
	ldr r0, [r8, #244]
	str r0, [r11, #2345]
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
	movw r7, #93
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #221
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
	ldr r0, [r5, #24]
	str r0, [r11, #2309]
	ldr r0, [r5, #28]
	str r0, [r11, #2313]
	ldr r0, [r8, #216]
	str r0, [r11, #2317]
	ldr r0, [r8, #220]
	str r0, [r11, #2321]
	ldr r0, [r8, #224]
	str r0, [r11, #2325]
	ldr r0, [r8, #228]
	str r0, [r11, #2329]
	ldr r0, [r8, #232]
	str r0, [r11, #2333]
	ldr r0, [r8, #236]
	str r0, [r11, #2337]
	ldr r0, [r8, #240]
	str r0, [r11, #2341]
	ldr r0, [r8, #244]
	str r0, [r11, #2345]
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
	movw r7, #93
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #221
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
	ldr r0, [r8, #84]
	str r0, [r8, #380]
	ldr r0, [r8, #88]
	str r0, [r8, #384]
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
	str r0, [r8, #388]
	ldr r0, [r8, #68]
	str r0, [r8, #392]
	ldr r0, [r8, #72]
	str r0, [r8, #396]
	ldr r0, [r8, #76]
	str r0, [r8, #400]
	ldr r0, [r8, #80]
	str r0, [r8, #404]
	ldr r0, [r8, #84]
	str r0, [r8, #408]
	ldr r0, [r8, #88]
	str r0, [r8, #412]
	ldr r0, [r8, #176]
	mov r1, r5
	add r2, r8, #216
	add r3, r8, #360
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_secp256k1_sign_k_umaal}
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
	ldr r0, [r6, #28]
	rev r0, r0
	str r0, [r8, #156]
	movw r1, #16705
	movt r1, #53302
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
	str r2, [r8, #28]
	ldr r0, [r6, #24]
	rev r0, r0
	str r0, [r8, #152]
	movw r1, #24204
	movt r1, #49106
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
	str r2, [r8, #24]
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #41019
	movt r1, #44872
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
	movw r1, #56550
	movt r1, #47790
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
	movw r1, #65534
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
	ldr r0, [r8, #156]
	ldr r1, [r8, #28]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #156]
	ldr r0, [r8, #152]
	ldr r1, [r8, #24]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #152]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2345]
	ldr r0, [r5, #28]
	str r0, [r11, #2349]
	ldr r0, [r8, #128]
	str r0, [r11, #2353]
	ldr r0, [r8, #132]
	str r0, [r11, #2357]
	ldr r0, [r8, #136]
	str r0, [r11, #2361]
	ldr r0, [r8, #140]
	str r0, [r11, #2365]
	ldr r0, [r8, #144]
	str r0, [r11, #2369]
	ldr r0, [r8, #148]
	str r0, [r11, #2373]
	ldr r0, [r8, #152]
	str r0, [r11, #2377]
	ldr r0, [r8, #156]
	str r0, [r11, #2381]
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
	movw r7, #129
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #257
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
	ldr r0, [r5, #24]
	str r0, [r11, #2345]
	ldr r0, [r5, #28]
	str r0, [r11, #2349]
	ldr r0, [r8, #128]
	str r0, [r11, #2353]
	ldr r0, [r8, #132]
	str r0, [r11, #2357]
	ldr r0, [r8, #136]
	str r0, [r11, #2361]
	ldr r0, [r8, #140]
	str r0, [r11, #2365]
	ldr r0, [r8, #144]
	str r0, [r11, #2369]
	ldr r0, [r8, #148]
	str r0, [r11, #2373]
	ldr r0, [r8, #152]
	str r0, [r11, #2377]
	ldr r0, [r8, #156]
	str r0, [r11, #2381]
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
	movw r7, #129
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #257
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
	bl {vg_ecdsa_secp256k1_sign_k_umaal}
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
	ldr r0, [r6, #28]
	rev r0, r0
	str r0, [r8, #156]
	movw r1, #16705
	movt r1, #53302
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
	str r2, [r8, #28]
	ldr r0, [r6, #24]
	rev r0, r0
	str r0, [r8, #152]
	movw r1, #24204
	movt r1, #49106
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
	str r2, [r8, #24]
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #41019
	movt r1, #44872
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
	movw r1, #56550
	movt r1, #47790
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
	movw r1, #65534
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
	ldr r0, [r8, #156]
	ldr r1, [r8, #28]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #156]
	ldr r0, [r8, #152]
	ldr r1, [r8, #24]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #152]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2329]
	ldr r0, [r5, #28]
	str r0, [r11, #2333]
	ldr r0, [r8, #128]
	str r0, [r11, #2337]
	ldr r0, [r8, #132]
	str r0, [r11, #2341]
	ldr r0, [r8, #136]
	str r0, [r11, #2345]
	ldr r0, [r8, #140]
	str r0, [r11, #2349]
	ldr r0, [r8, #144]
	str r0, [r11, #2353]
	ldr r0, [r8, #148]
	str r0, [r11, #2357]
	ldr r0, [r8, #152]
	str r0, [r11, #2361]
	ldr r0, [r8, #156]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2329]
	ldr r0, [r5, #28]
	str r0, [r11, #2333]
	ldr r0, [r8, #128]
	str r0, [r11, #2337]
	ldr r0, [r8, #132]
	str r0, [r11, #2341]
	ldr r0, [r8, #136]
	str r0, [r11, #2345]
	ldr r0, [r8, #140]
	str r0, [r11, #2349]
	ldr r0, [r8, #144]
	str r0, [r11, #2353]
	ldr r0, [r8, #148]
	str r0, [r11, #2357]
	ldr r0, [r8, #152]
	str r0, [r11, #2361]
	ldr r0, [r8, #156]
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
	bl {vg_ecdsa_secp256k1_sign_k_umaal}
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
	ldr r0, [r6, #28]
	rev r0, r0
	str r0, [r8, #156]
	movw r1, #16705
	movt r1, #53302
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
	str r2, [r8, #28]
	ldr r0, [r6, #24]
	rev r0, r0
	str r0, [r8, #152]
	movw r1, #24204
	movt r1, #49106
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
	str r2, [r8, #24]
	ldr r0, [r6, #20]
	rev r0, r0
	str r0, [r8, #148]
	movw r1, #41019
	movt r1, #44872
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
	movw r1, #56550
	movt r1, #47790
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
	movw r1, #65534
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
	ldr r0, [r8, #156]
	ldr r1, [r8, #28]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #156]
	ldr r0, [r8, #152]
	ldr r1, [r8, #24]
	eor r1, r1, r0
	and r1, r1, r7
	eor r0, r0, r1
	rev r0, r0
	str r0, [r8, #152]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2313]
	ldr r0, [r5, #28]
	str r0, [r11, #2317]
	ldr r0, [r8, #128]
	str r0, [r11, #2321]
	ldr r0, [r8, #132]
	str r0, [r11, #2325]
	ldr r0, [r8, #136]
	str r0, [r11, #2329]
	ldr r0, [r8, #140]
	str r0, [r11, #2333]
	ldr r0, [r8, #144]
	str r0, [r11, #2337]
	ldr r0, [r8, #148]
	str r0, [r11, #2341]
	ldr r0, [r8, #152]
	str r0, [r11, #2345]
	ldr r0, [r8, #156]
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
	movw r7, #97
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
	ldr r0, [r5, #24]
	str r0, [r11, #2313]
	ldr r0, [r5, #28]
	str r0, [r11, #2317]
	ldr r0, [r8, #128]
	str r0, [r11, #2321]
	ldr r0, [r8, #132]
	str r0, [r11, #2325]
	ldr r0, [r8, #136]
	str r0, [r11, #2329]
	ldr r0, [r8, #140]
	str r0, [r11, #2333]
	ldr r0, [r8, #144]
	str r0, [r11, #2337]
	ldr r0, [r8, #148]
	str r0, [r11, #2341]
	ldr r0, [r8, #152]
	str r0, [r11, #2345]
	ldr r0, [r8, #156]
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
	movw r7, #97
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
	bl {vg_ecdsa_secp256k1_sign_k_umaal}
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
	ldr r0, [r6, #20]
	str r0, [r8, #240]
	ldr r0, [r6, #24]
	str r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2309]
	ldr r0, [r5, #28]
	str r0, [r11, #2313]
	ldr r0, [r8, #216]
	str r0, [r11, #2317]
	ldr r0, [r8, #220]
	str r0, [r11, #2321]
	ldr r0, [r8, #224]
	str r0, [r11, #2325]
	ldr r0, [r8, #228]
	str r0, [r11, #2329]
	ldr r0, [r8, #232]
	str r0, [r11, #2333]
	ldr r0, [r8, #236]
	str r0, [r11, #2337]
	ldr r0, [r8, #240]
	str r0, [r11, #2341]
	ldr r0, [r8, #244]
	str r0, [r11, #2345]
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
	movw r7, #93
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
	ldr r0, [r5, #24]
	str r0, [r11, #2309]
	ldr r0, [r5, #28]
	str r0, [r11, #2313]
	ldr r0, [r8, #216]
	str r0, [r11, #2317]
	ldr r0, [r8, #220]
	str r0, [r11, #2321]
	ldr r0, [r8, #224]
	str r0, [r11, #2325]
	ldr r0, [r8, #228]
	str r0, [r11, #2329]
	ldr r0, [r8, #232]
	str r0, [r11, #2333]
	ldr r0, [r8, #236]
	str r0, [r11, #2337]
	ldr r0, [r8, #240]
	str r0, [r11, #2341]
	ldr r0, [r8, #244]
	str r0, [r11, #2345]
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
	movw r7, #93
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
	ldr r0, [r8, #84]
	str r0, [r8, #380]
	ldr r0, [r8, #88]
	str r0, [r8, #384]
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
	str r0, [r8, #388]
	ldr r0, [r8, #68]
	str r0, [r8, #392]
	ldr r0, [r8, #72]
	str r0, [r8, #396]
	ldr r0, [r8, #76]
	str r0, [r8, #400]
	ldr r0, [r8, #80]
	str r0, [r8, #404]
	ldr r0, [r8, #84]
	str r0, [r8, #408]
	ldr r0, [r8, #88]
	str r0, [r8, #412]
	ldr r0, [r8, #176]
	mov r1, r5
	add r2, r8, #216
	add r3, r8, #360
	mov r12, r11
	push {r12, lr}
	bl {vg_ecdsa_secp256k1_sign_k_umaal}
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
	str r0, [r8, #228]
	ldr r0, [r6, #4]
	str r0, [r8, #232]
	ldr r0, [r6, #8]
	str r0, [r8, #236]
	ldr r0, [r6, #12]
	str r0, [r8, #240]
	ldr r0, [r6, #16]
	str r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2301]
	ldr r0, [r5, #28]
	str r0, [r11, #2305]
	ldr r0, [r8, #216]
	str r0, [r11, #2309]
	ldr r0, [r8, #220]
	str r0, [r11, #2313]
	ldr r0, [r8, #224]
	str r0, [r11, #2317]
	ldr r0, [r8, #228]
	str r0, [r11, #2321]
	ldr r0, [r8, #232]
	str r0, [r11, #2325]
	ldr r0, [r8, #236]
	str r0, [r11, #2329]
	ldr r0, [r8, #240]
	str r0, [r11, #2333]
	ldr r0, [r8, #244]
	str r0, [r11, #2337]
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
	movw r7, #85
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #149
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
	ldr r0, [r5, #24]
	str r0, [r11, #2301]
	ldr r0, [r5, #28]
	str r0, [r11, #2305]
	ldr r0, [r8, #216]
	str r0, [r11, #2309]
	ldr r0, [r8, #220]
	str r0, [r11, #2313]
	ldr r0, [r8, #224]
	str r0, [r11, #2317]
	ldr r0, [r8, #228]
	str r0, [r11, #2321]
	ldr r0, [r8, #232]
	str r0, [r11, #2325]
	ldr r0, [r8, #236]
	str r0, [r11, #2329]
	ldr r0, [r8, #240]
	str r0, [r11, #2333]
	ldr r0, [r8, #244]
	str r0, [r11, #2337]
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
	movw r7, #85
	movw r12, #384
	add r10, r11, r12
	ldr r12, [r4, #4]
	push {r1, r7, r10, r12}
	blx r12
	ldr r1, [sp], #16
	movw r12, #0
	add r0, r11, r12
	movw r2, #149
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
	bl {vg_ecdsa_secp256k1_sign_k_umaal}
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
	str r0, [r8, #232]
	ldr r0, [r6, #4]
	str r0, [r8, #236]
	ldr r0, [r6, #8]
	str r0, [r8, #240]
	ldr r0, [r6, #12]
	str r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2297]
	ldr r0, [r5, #28]
	str r0, [r11, #2301]
	ldr r0, [r8, #216]
	str r0, [r11, #2305]
	ldr r0, [r8, #220]
	str r0, [r11, #2309]
	ldr r0, [r8, #224]
	str r0, [r11, #2313]
	ldr r0, [r8, #228]
	str r0, [r11, #2317]
	ldr r0, [r8, #232]
	str r0, [r11, #2321]
	ldr r0, [r8, #236]
	str r0, [r11, #2325]
	ldr r0, [r8, #240]
	str r0, [r11, #2329]
	ldr r0, [r8, #244]
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
	ldr r0, [r5, #24]
	str r0, [r11, #2297]
	ldr r0, [r5, #28]
	str r0, [r11, #2301]
	ldr r0, [r8, #216]
	str r0, [r11, #2305]
	ldr r0, [r8, #220]
	str r0, [r11, #2309]
	ldr r0, [r8, #224]
	str r0, [r11, #2313]
	ldr r0, [r8, #228]
	str r0, [r11, #2317]
	ldr r0, [r8, #232]
	str r0, [r11, #2321]
	ldr r0, [r8, #236]
	str r0, [r11, #2325]
	ldr r0, [r8, #240]
	str r0, [r11, #2329]
	ldr r0, [r8, #244]
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
	bl {vg_ecdsa_secp256k1_sign_k_umaal}
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
