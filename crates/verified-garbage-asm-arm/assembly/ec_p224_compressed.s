// The functions of `src/ec_p224_compressed.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p224_compress_public_key:
	mov r12, r2
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
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1056]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1060]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1064]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1068]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1072]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1076]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1080]
	mov r4, #0
	str r4, [r12, #1084]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1088]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1092]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1096]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1100]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1104]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1108]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1112]
	mov r4, #0
	str r4, [r12, #1116]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1144]
	mov r4, #0
	str r4, [r12, #1148]
	movw r10, #:lower16:({VG_P224_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P224_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r9, r12
	mov r11, #17
20:
	sub r11, r11, #1
	ldr r4, [r10, #0]
	ldr r5, [r10, #4]
	str r4, [r9, #64]
	str r5, [r9, #68]
	ldr r4, [r10, #8]
	ldr r5, [r10, #12]
	str r4, [r9, #72]
	str r5, [r9, #76]
	ldr r4, [r10, #16]
	ldr r5, [r10, #20]
	str r4, [r9, #80]
	str r5, [r9, #84]
	ldr r4, [r10, #24]
	ldr r5, [r10, #28]
	str r4, [r9, #88]
	str r5, [r9, #92]
	add r10, r10, #32
	add r9, r9, #32
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1472]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1312]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1316]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1320]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1324]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1328]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #1332]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1336]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1340]
	movw r4, #22989
	movt r4, #25536
	str r4, [r12, #1344]
	movw r4, #52726
	movt r4, #59240
	str r4, [r12, #1348]
	movw r4, #4880
	movt r4, #52464
	str r4, [r12, #1352]
	movw r4, #49907
	movt r4, #4218
	str r4, [r12, #1356]
	movw r4, #33105
	movt r4, #51282
	str r4, [r12, #1360]
	movw r4, #47768
	movt r4, #15822
	str r4, [r12, #1364]
	movw r4, #12179
	movt r4, #32704
	str r4, [r12, #1368]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1372]
	add r6, r1, #1
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1144]
	mov r4, #0
	str r4, [r12, #1148]
	add r6, r6, #28
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1216]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1220]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1224]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1228]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1232]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1236]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1240]
	mov r4, #0
	str r4, [r12, #1244]
	ldrb r4, [r1, #0]
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
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1216
	movw r3, #1312
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #1184
	movw r3, #1184
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1152
	movw r3, #1152
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1376
	movw r3, #1152
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #256
	movw r3, #1152
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1408
	movw r3, #1376
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1280
	movw r3, #1344
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1248
	movw r3, #1408
	bl {vg_p224_sub_mod_p}
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
	ldr r10, [r12, #1472]
	ldr r4, [r12, #1216]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1120]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1124]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1128]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1132]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1136]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1140]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1144]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
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
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_ec_p224_decompress_public_key:
	mov r12, r2
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
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1056]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1060]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1064]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1068]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1072]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1076]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1080]
	mov r4, #0
	str r4, [r12, #1084]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1088]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1092]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1096]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1100]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1104]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1108]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1112]
	mov r4, #0
	str r4, [r12, #1116]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1144]
	mov r4, #0
	str r4, [r12, #1148]
	movw r10, #:lower16:({VG_P224_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P224_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r9, r12
	mov r11, #17
20:
	sub r11, r11, #1
	ldr r4, [r10, #0]
	ldr r5, [r10, #4]
	str r4, [r9, #64]
	str r5, [r9, #68]
	ldr r4, [r10, #8]
	ldr r5, [r10, #12]
	str r4, [r9, #72]
	str r5, [r9, #76]
	ldr r4, [r10, #16]
	ldr r5, [r10, #20]
	str r4, [r9, #80]
	str r5, [r9, #84]
	ldr r4, [r10, #24]
	ldr r5, [r10, #28]
	str r4, [r9, #88]
	str r5, [r9, #92]
	add r10, r10, #32
	add r9, r9, #32
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1472]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1312]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1316]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1320]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1324]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1328]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #1332]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1336]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1340]
	movw r4, #22989
	movt r4, #25536
	str r4, [r12, #1344]
	movw r4, #52726
	movt r4, #59240
	str r4, [r12, #1348]
	movw r4, #4880
	movt r4, #52464
	str r4, [r12, #1352]
	movw r4, #49907
	movt r4, #4218
	str r4, [r12, #1356]
	movw r4, #33105
	movt r4, #51282
	str r4, [r12, #1360]
	movw r4, #47768
	movt r4, #15822
	str r4, [r12, #1364]
	movw r4, #12179
	movt r4, #32704
	str r4, [r12, #1368]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1372]
	add r6, r1, #1
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1144]
	mov r4, #0
	str r4, [r12, #1148]
	ldrb r4, [r1, #0]
	str r4, [r12, #1088]
	orr r4, r4, #1
	eor r4, r4, #3
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
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1120
	movw r3, #1312
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1152
	movw r3, #1152
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1376
	movw r3, #1152
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #256
	movw r3, #1152
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1408
	movw r3, #1376
	bl {vg_p224_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1280
	movw r3, #1344
	bl {vg_p224_add_mod_p}
	mov lr, r10
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
	movt r4, #32768
	str r4, [r12, #460]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #464]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #468]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #472]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #476]
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
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #992
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #992
	movw r3, #1408
	bl {vg_p224_mul_mod_p}
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
	bne 22b
	ldr r4, [r12, #992]
	str r4, [r12, #960]
	ldr r4, [r12, #996]
	str r4, [r12, #964]
	ldr r4, [r12, #1000]
	str r4, [r12, #968]
	ldr r4, [r12, #1004]
	str r4, [r12, #972]
	ldr r4, [r12, #1008]
	str r4, [r12, #976]
	ldr r4, [r12, #1012]
	str r4, [r12, #980]
	ldr r4, [r12, #1016]
	str r4, [r12, #984]
	ldr r4, [r12, #1020]
	str r4, [r12, #988]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #448]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #452]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #456]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #460]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #464]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #468]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #472]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #476]
	mov r11, #32
23:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #448]
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
	bne 23b
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
24:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #992
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #992
	movw r3, #1408
	bl {vg_p224_mul_mod_p}
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
	bne 24b
	ldr r4, [r12, #992]
	str r4, [r12, #800]
	ldr r4, [r12, #996]
	str r4, [r12, #804]
	ldr r4, [r12, #1000]
	str r4, [r12, #808]
	ldr r4, [r12, #1004]
	str r4, [r12, #812]
	ldr r4, [r12, #1008]
	str r4, [r12, #816]
	ldr r4, [r12, #1012]
	str r4, [r12, #820]
	ldr r4, [r12, #1016]
	str r4, [r12, #824]
	ldr r4, [r12, #1020]
	str r4, [r12, #828]
	ldr r4, [r12, #960]
	str r4, [r12, #992]
	ldr r4, [r12, #964]
	str r4, [r12, #996]
	ldr r4, [r12, #968]
	str r4, [r12, #1000]
	ldr r4, [r12, #972]
	str r4, [r12, #1004]
	ldr r4, [r12, #976]
	str r4, [r12, #1008]
	ldr r4, [r12, #980]
	str r4, [r12, #1012]
	ldr r4, [r12, #984]
	str r4, [r12, #1016]
	ldr r4, [r12, #988]
	str r4, [r12, #1020]
	movw r4, #31852
	movt r4, #24290
	str r4, [r12, #832]
	movw r4, #12728
	movt r4, #5953
	str r4, [r12, #836]
	movw r4, #8763
	movt r4, #34412
	str r4, [r12, #840]
	movw r4, #48733
	movt r4, #30825
	str r4, [r12, #844]
	movw r4, #24139
	movt r4, #56721
	str r4, [r12, #848]
	movw r4, #10992
	movt r4, #27966
	str r4, [r12, #852]
	movw r4, #7588
	movt r4, #41755
	str r4, [r12, #856]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #860]
	mov r4, #95
	str r4, [r12, #864]
25:
	ldr r4, [r12, #800]
	str r4, [r12, #896]
	ldr r4, [r12, #804]
	str r4, [r12, #900]
	ldr r4, [r12, #808]
	str r4, [r12, #904]
	ldr r4, [r12, #812]
	str r4, [r12, #908]
	ldr r4, [r12, #816]
	str r4, [r12, #912]
	ldr r4, [r12, #820]
	str r4, [r12, #916]
	ldr r4, [r12, #824]
	str r4, [r12, #920]
	ldr r4, [r12, #828]
	str r4, [r12, #924]
	ldr r11, [r12, #864]
	sub r11, r11, #1
	cmp r11, #0
	beq 26f
28:
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #896
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	sub r11, r11, #1
	cmp r11, #0
	bne 28b
	b 27f
26:
27:
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #896
	movw r3, #224
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #1248]
	ldr r4, [r12, #1252]
	orr r5, r5, r4
	ldr r4, [r12, #1256]
	orr r5, r5, r4
	ldr r4, [r12, #1260]
	orr r5, r5, r4
	ldr r4, [r12, #1264]
	orr r5, r5, r4
	ldr r4, [r12, #1268]
	orr r5, r5, r4
	ldr r4, [r12, #1272]
	orr r5, r5, r4
	ldr r4, [r12, #1276]
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
	mov r10, r5
	ldr r4, [r12, #832]
	ldr r5, [r12, #224]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #928]
	ldr r4, [r12, #836]
	ldr r5, [r12, #228]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #932]
	ldr r4, [r12, #840]
	ldr r5, [r12, #232]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #936]
	ldr r4, [r12, #844]
	ldr r5, [r12, #236]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #940]
	ldr r4, [r12, #848]
	ldr r5, [r12, #240]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #944]
	ldr r4, [r12, #852]
	ldr r5, [r12, #244]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #948]
	ldr r4, [r12, #856]
	ldr r5, [r12, #248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #952]
	ldr r4, [r12, #860]
	ldr r5, [r12, #252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #956]
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #928
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #928
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #800
	movw r3, #928
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	ldr r11, [r12, #864]
	sub r11, r11, #1
	str r11, [r12, #864]
	cmp r11, #0
	bne 25b
	mov r10, lr
	mov r0, r12
	movw r1, #1216
	movw r2, #992
	movw r3, #192
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #160
	movw r3, #1216
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	ldr r4, [r12, #1216]
	ldr r5, [r12, #1088]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #1216]
	ldr r5, [r12, #1248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1216]
	ldr r4, [r12, #1220]
	ldr r5, [r12, #1252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1220]
	ldr r4, [r12, #1224]
	ldr r5, [r12, #1256]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1224]
	ldr r4, [r12, #1228]
	ldr r5, [r12, #1260]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1228]
	ldr r4, [r12, #1232]
	ldr r5, [r12, #1264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1232]
	ldr r4, [r12, #1236]
	ldr r5, [r12, #1268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1236]
	ldr r4, [r12, #1240]
	ldr r5, [r12, #1272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1240]
	ldr r4, [r12, #1244]
	ldr r5, [r12, #1276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1244]
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1216
	movw r3, #1312
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1184
	movw r3, #1184
	bl {vg_p224_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1376
	movw r3, #1408
	bl {vg_p224_sub_mod_p}
	mov lr, r10
	ldr r5, [r12, #1280]
	ldr r4, [r12, #1284]
	orr r5, r5, r4
	ldr r4, [r12, #1288]
	orr r5, r5, r4
	ldr r4, [r12, #1292]
	orr r5, r5, r4
	ldr r4, [r12, #1296]
	orr r5, r5, r4
	ldr r4, [r12, #1300]
	orr r5, r5, r4
	ldr r4, [r12, #1304]
	orr r5, r5, r4
	ldr r4, [r12, #1308]
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
	ldr r4, [r12, #1216]
	ldr r5, [r12, #1088]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	ldr r10, [r12, #1472]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1120]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1124]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1128]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1132]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1136]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1140]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1144]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #1216]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #1220]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
	ldr r4, [r12, #1224]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1228]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #1232]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1236]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1240]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
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
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_ec_p224_compress_public_key_umaal:
	mov r12, r2
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
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1056]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1060]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1064]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1068]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1072]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1076]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1080]
	mov r4, #0
	str r4, [r12, #1084]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1088]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1092]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1096]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1100]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1104]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1108]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1112]
	mov r4, #0
	str r4, [r12, #1116]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1144]
	mov r4, #0
	str r4, [r12, #1148]
	movw r10, #:lower16:({VG_P224_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P224_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r9, r12
	mov r11, #17
20:
	sub r11, r11, #1
	ldr r4, [r10, #0]
	ldr r5, [r10, #4]
	str r4, [r9, #64]
	str r5, [r9, #68]
	ldr r4, [r10, #8]
	ldr r5, [r10, #12]
	str r4, [r9, #72]
	str r5, [r9, #76]
	ldr r4, [r10, #16]
	ldr r5, [r10, #20]
	str r4, [r9, #80]
	str r5, [r9, #84]
	ldr r4, [r10, #24]
	ldr r5, [r10, #28]
	str r4, [r9, #88]
	str r5, [r9, #92]
	add r10, r10, #32
	add r9, r9, #32
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1472]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1312]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1316]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1320]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1324]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1328]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #1332]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1336]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1340]
	movw r4, #22989
	movt r4, #25536
	str r4, [r12, #1344]
	movw r4, #52726
	movt r4, #59240
	str r4, [r12, #1348]
	movw r4, #4880
	movt r4, #52464
	str r4, [r12, #1352]
	movw r4, #49907
	movt r4, #4218
	str r4, [r12, #1356]
	movw r4, #33105
	movt r4, #51282
	str r4, [r12, #1360]
	movw r4, #47768
	movt r4, #15822
	str r4, [r12, #1364]
	movw r4, #12179
	movt r4, #32704
	str r4, [r12, #1368]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1372]
	add r6, r1, #1
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1144]
	mov r4, #0
	str r4, [r12, #1148]
	add r6, r6, #28
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1216]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1220]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1224]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1228]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1232]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1236]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1240]
	mov r4, #0
	str r4, [r12, #1244]
	ldrb r4, [r1, #0]
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
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1216
	movw r3, #1312
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #1184
	movw r3, #1184
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1152
	movw r3, #1152
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1376
	movw r3, #1152
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #256
	movw r3, #1152
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1408
	movw r3, #1376
	bl {vg_p224_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1280
	movw r3, #1344
	bl {vg_p224_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1248
	movw r3, #1408
	bl {vg_p224_sub_mod_p_umaal}
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
	ldr r10, [r12, #1472]
	ldr r4, [r12, #1216]
	and r4, r4, #1
	orr r4, r4, #2
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1120]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1124]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1128]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1132]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1136]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1140]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1144]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
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
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr

vg_ec_p224_decompress_public_key_umaal:
	mov r12, r2
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
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1056]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1060]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1064]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1068]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1072]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1076]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1080]
	mov r4, #0
	str r4, [r12, #1084]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1088]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1092]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1096]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1100]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1104]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1108]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1112]
	mov r4, #0
	str r4, [r12, #1116]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1144]
	mov r4, #0
	str r4, [r12, #1148]
	movw r10, #:lower16:({VG_P224_FRAME_CONSTS}
	movt r10, #:upper16:({VG_P224_FRAME_CONSTS}
2:
	add r10, pc
3:
	mov r9, r12
	mov r11, #17
20:
	sub r11, r11, #1
	ldr r4, [r10, #0]
	ldr r5, [r10, #4]
	str r4, [r9, #64]
	str r5, [r9, #68]
	ldr r4, [r10, #8]
	ldr r5, [r10, #12]
	str r4, [r9, #72]
	str r5, [r9, #76]
	ldr r4, [r10, #16]
	ldr r5, [r10, #20]
	str r4, [r9, #80]
	str r5, [r9, #84]
	ldr r4, [r10, #24]
	ldr r5, [r10, #28]
	str r4, [r9, #88]
	str r5, [r9, #92]
	add r10, r10, #32
	add r9, r9, #32
	cmp r11, #0
	bne 20b
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #1472]
	movw r4, #1
	movt r4, #0
	str r4, [r12, #1312]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1316]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1320]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1324]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1328]
	movw r4, #65534
	movt r4, #65535
	str r4, [r12, #1332]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #1336]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1340]
	movw r4, #22989
	movt r4, #25536
	str r4, [r12, #1344]
	movw r4, #52726
	movt r4, #59240
	str r4, [r12, #1348]
	movw r4, #4880
	movt r4, #52464
	str r4, [r12, #1352]
	movw r4, #49907
	movt r4, #4218
	str r4, [r12, #1356]
	movw r4, #33105
	movt r4, #51282
	str r4, [r12, #1360]
	movw r4, #47768
	movt r4, #15822
	str r4, [r12, #1364]
	movw r4, #12179
	movt r4, #32704
	str r4, [r12, #1368]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #1372]
	add r6, r1, #1
	ldr r4, [r6, #24]
	rev r4, r4
	str r4, [r12, #1120]
	ldr r4, [r6, #20]
	rev r4, r4
	str r4, [r12, #1124]
	ldr r4, [r6, #16]
	rev r4, r4
	str r4, [r12, #1128]
	ldr r4, [r6, #12]
	rev r4, r4
	str r4, [r12, #1132]
	ldr r4, [r6, #8]
	rev r4, r4
	str r4, [r12, #1136]
	ldr r4, [r6, #4]
	rev r4, r4
	str r4, [r12, #1140]
	ldr r4, [r6, #0]
	rev r4, r4
	str r4, [r12, #1144]
	mov r4, #0
	str r4, [r12, #1148]
	ldrb r4, [r1, #0]
	str r4, [r12, #1088]
	orr r4, r4, #1
	eor r4, r4, #3
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
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1120
	movw r3, #1312
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1152
	movw r3, #1152
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1376
	movw r3, #1152
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #256
	movw r3, #1152
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1408
	movw r3, #1376
	bl {vg_p224_add_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1280
	movw r3, #1344
	bl {vg_p224_add_mod_p_umaal}
	mov lr, r10
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
	movt r4, #32768
	str r4, [r12, #460]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #464]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #468]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #472]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #476]
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
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #992
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #992
	movw r3, #1408
	bl {vg_p224_mul_mod_p_umaal}
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
	bne 22b
	ldr r4, [r12, #992]
	str r4, [r12, #960]
	ldr r4, [r12, #996]
	str r4, [r12, #964]
	ldr r4, [r12, #1000]
	str r4, [r12, #968]
	ldr r4, [r12, #1004]
	str r4, [r12, #972]
	ldr r4, [r12, #1008]
	str r4, [r12, #976]
	ldr r4, [r12, #1012]
	str r4, [r12, #980]
	ldr r4, [r12, #1016]
	str r4, [r12, #984]
	ldr r4, [r12, #1020]
	str r4, [r12, #988]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #448]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #452]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #456]
	movw r4, #65535
	movt r4, #65535
	str r4, [r12, #460]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #464]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #468]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #472]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #476]
	mov r11, #32
23:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #448]
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
	bne 23b
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
24:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #992
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #992
	movw r3, #1408
	bl {vg_p224_mul_mod_p_umaal}
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
	bne 24b
	ldr r4, [r12, #992]
	str r4, [r12, #800]
	ldr r4, [r12, #996]
	str r4, [r12, #804]
	ldr r4, [r12, #1000]
	str r4, [r12, #808]
	ldr r4, [r12, #1004]
	str r4, [r12, #812]
	ldr r4, [r12, #1008]
	str r4, [r12, #816]
	ldr r4, [r12, #1012]
	str r4, [r12, #820]
	ldr r4, [r12, #1016]
	str r4, [r12, #824]
	ldr r4, [r12, #1020]
	str r4, [r12, #828]
	ldr r4, [r12, #960]
	str r4, [r12, #992]
	ldr r4, [r12, #964]
	str r4, [r12, #996]
	ldr r4, [r12, #968]
	str r4, [r12, #1000]
	ldr r4, [r12, #972]
	str r4, [r12, #1004]
	ldr r4, [r12, #976]
	str r4, [r12, #1008]
	ldr r4, [r12, #980]
	str r4, [r12, #1012]
	ldr r4, [r12, #984]
	str r4, [r12, #1016]
	ldr r4, [r12, #988]
	str r4, [r12, #1020]
	movw r4, #31852
	movt r4, #24290
	str r4, [r12, #832]
	movw r4, #12728
	movt r4, #5953
	str r4, [r12, #836]
	movw r4, #8763
	movt r4, #34412
	str r4, [r12, #840]
	movw r4, #48733
	movt r4, #30825
	str r4, [r12, #844]
	movw r4, #24139
	movt r4, #56721
	str r4, [r12, #848]
	movw r4, #10992
	movt r4, #27966
	str r4, [r12, #852]
	movw r4, #7588
	movt r4, #41755
	str r4, [r12, #856]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #860]
	mov r4, #95
	str r4, [r12, #864]
25:
	ldr r4, [r12, #800]
	str r4, [r12, #896]
	ldr r4, [r12, #804]
	str r4, [r12, #900]
	ldr r4, [r12, #808]
	str r4, [r12, #904]
	ldr r4, [r12, #812]
	str r4, [r12, #908]
	ldr r4, [r12, #816]
	str r4, [r12, #912]
	ldr r4, [r12, #820]
	str r4, [r12, #916]
	ldr r4, [r12, #824]
	str r4, [r12, #920]
	ldr r4, [r12, #828]
	str r4, [r12, #924]
	ldr r11, [r12, #864]
	sub r11, r11, #1
	cmp r11, #0
	beq 26f
28:
	mov r10, lr
	mov r0, r12
	movw r1, #896
	movw r2, #896
	movw r3, #896
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	sub r11, r11, #1
	cmp r11, #0
	bne 28b
	b 27f
26:
27:
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #896
	movw r3, #224
	bl {vg_p224_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #1248]
	ldr r4, [r12, #1252]
	orr r5, r5, r4
	ldr r4, [r12, #1256]
	orr r5, r5, r4
	ldr r4, [r12, #1260]
	orr r5, r5, r4
	ldr r4, [r12, #1264]
	orr r5, r5, r4
	ldr r4, [r12, #1268]
	orr r5, r5, r4
	ldr r4, [r12, #1272]
	orr r5, r5, r4
	ldr r4, [r12, #1276]
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
	mov r10, r5
	ldr r4, [r12, #832]
	ldr r5, [r12, #224]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #928]
	ldr r4, [r12, #836]
	ldr r5, [r12, #228]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #932]
	ldr r4, [r12, #840]
	ldr r5, [r12, #232]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #936]
	ldr r4, [r12, #844]
	ldr r5, [r12, #236]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #940]
	ldr r4, [r12, #848]
	ldr r5, [r12, #240]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #944]
	ldr r4, [r12, #852]
	ldr r5, [r12, #244]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #948]
	ldr r4, [r12, #856]
	ldr r5, [r12, #248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #952]
	ldr r4, [r12, #860]
	ldr r5, [r12, #252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #956]
	mov r10, lr
	mov r0, r12
	movw r1, #992
	movw r2, #992
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #928
	movw r2, #928
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #800
	movw r2, #800
	movw r3, #928
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #832
	movw r2, #832
	movw r3, #832
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	ldr r11, [r12, #864]
	sub r11, r11, #1
	str r11, [r12, #864]
	cmp r11, #0
	bne 25b
	mov r10, lr
	mov r0, r12
	movw r1, #1216
	movw r2, #992
	movw r3, #192
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1248
	movw r2, #160
	movw r3, #1216
	bl {vg_p224_sub_mod_p_umaal}
	mov lr, r10
	ldr r4, [r12, #1216]
	ldr r5, [r12, #1088]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	ldr r4, [r12, #1216]
	ldr r5, [r12, #1248]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1216]
	ldr r4, [r12, #1220]
	ldr r5, [r12, #1252]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1220]
	ldr r4, [r12, #1224]
	ldr r5, [r12, #1256]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1224]
	ldr r4, [r12, #1228]
	ldr r5, [r12, #1260]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1228]
	ldr r4, [r12, #1232]
	ldr r5, [r12, #1264]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1232]
	ldr r4, [r12, #1236]
	ldr r5, [r12, #1268]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1236]
	ldr r4, [r12, #1240]
	ldr r5, [r12, #1272]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1240]
	ldr r4, [r12, #1244]
	ldr r5, [r12, #1276]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1244]
	mov r10, lr
	mov r0, r12
	movw r1, #1184
	movw r2, #1216
	movw r3, #1312
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1376
	movw r2, #1184
	movw r3, #1184
	bl {vg_p224_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1376
	movw r3, #1408
	bl {vg_p224_sub_mod_p_umaal}
	mov lr, r10
	ldr r5, [r12, #1280]
	ldr r4, [r12, #1284]
	orr r5, r5, r4
	ldr r4, [r12, #1288]
	orr r5, r5, r4
	ldr r4, [r12, #1292]
	orr r5, r5, r4
	ldr r4, [r12, #1296]
	orr r5, r5, r4
	ldr r4, [r12, #1300]
	orr r5, r5, r4
	ldr r4, [r12, #1304]
	orr r5, r5, r4
	ldr r4, [r12, #1308]
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
	ldr r4, [r12, #1216]
	ldr r5, [r12, #1088]
	eor r5, r5, r4
	and r5, r5, #1
	mov r4, #0
	sub r10, r4, r5
	add r5, r10, #1
	mov r4, #0
	sub r5, r4, r5
	ldr r4, [r12, #1472]
	and r4, r4, r5
	str r4, [r12, #1472]
	ldr r10, [r12, #1472]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1120]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1124]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1128]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1132]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1136]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1140]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1144]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #1216]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #1220]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
	ldr r4, [r12, #1224]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1228]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #1232]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1236]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1240]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
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
	mov r1, #0
	mov r2, #0
	mov r3, #0
	mov r12, #0
	cmp r2, r2
	bx lr
