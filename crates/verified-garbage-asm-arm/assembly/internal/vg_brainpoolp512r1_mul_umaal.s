// The functions of `src/internal/vg_brainpoolp512r1_mul_umaal.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp512r1_mul_umaal:
	mov r12, r0
	str r4, [r12, #2944]
	str r5, [r12, #2948]
	str r6, [r12, #2952]
	str r7, [r12, #2956]
	str r8, [r12, #2960]
	str r9, [r12, #2964]
	str r11, [r12, #2972]
	str lr, [r12, #2976]
	mov lr, r10
	mov r11, #64
20:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #2048]
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
	movw r5, #5632
	add r5, r12, r5
	ldr r4, [r12, #256]
	str r4, [r5, #0]
	ldr r4, [r12, #260]
	str r4, [r5, #4]
	ldr r4, [r12, #264]
	str r4, [r5, #8]
	ldr r4, [r12, #268]
	str r4, [r5, #12]
	ldr r4, [r12, #272]
	str r4, [r5, #16]
	ldr r4, [r12, #276]
	str r4, [r5, #20]
	ldr r4, [r12, #280]
	str r4, [r5, #24]
	ldr r4, [r12, #284]
	str r4, [r5, #28]
	ldr r4, [r12, #288]
	str r4, [r5, #32]
	ldr r4, [r12, #292]
	str r4, [r5, #36]
	ldr r4, [r12, #296]
	str r4, [r5, #40]
	ldr r4, [r12, #300]
	str r4, [r5, #44]
	ldr r4, [r12, #304]
	str r4, [r5, #48]
	ldr r4, [r12, #308]
	str r4, [r5, #52]
	ldr r4, [r12, #312]
	str r4, [r5, #56]
	ldr r4, [r12, #316]
	str r4, [r5, #60]
	ldr r4, [r12, #384]
	str r4, [r5, #64]
	ldr r4, [r12, #388]
	str r4, [r5, #68]
	ldr r4, [r12, #392]
	str r4, [r5, #72]
	ldr r4, [r12, #396]
	str r4, [r5, #76]
	ldr r4, [r12, #400]
	str r4, [r5, #80]
	ldr r4, [r12, #404]
	str r4, [r5, #84]
	ldr r4, [r12, #408]
	str r4, [r5, #88]
	ldr r4, [r12, #412]
	str r4, [r5, #92]
	ldr r4, [r12, #416]
	str r4, [r5, #96]
	ldr r4, [r12, #420]
	str r4, [r5, #100]
	ldr r4, [r12, #424]
	str r4, [r5, #104]
	ldr r4, [r12, #428]
	str r4, [r5, #108]
	ldr r4, [r12, #432]
	str r4, [r5, #112]
	ldr r4, [r12, #436]
	str r4, [r5, #116]
	ldr r4, [r12, #440]
	str r4, [r5, #120]
	ldr r4, [r12, #444]
	str r4, [r5, #124]
	ldr r4, [r12, #256]
	str r4, [r5, #128]
	ldr r4, [r12, #260]
	str r4, [r5, #132]
	ldr r4, [r12, #264]
	str r4, [r5, #136]
	ldr r4, [r12, #268]
	str r4, [r5, #140]
	ldr r4, [r12, #272]
	str r4, [r5, #144]
	ldr r4, [r12, #276]
	str r4, [r5, #148]
	ldr r4, [r12, #280]
	str r4, [r5, #152]
	ldr r4, [r12, #284]
	str r4, [r5, #156]
	ldr r4, [r12, #288]
	str r4, [r5, #160]
	ldr r4, [r12, #292]
	str r4, [r5, #164]
	ldr r4, [r12, #296]
	str r4, [r5, #168]
	ldr r4, [r12, #300]
	str r4, [r5, #172]
	ldr r4, [r12, #304]
	str r4, [r5, #176]
	ldr r4, [r12, #308]
	str r4, [r5, #180]
	ldr r4, [r12, #312]
	str r4, [r5, #184]
	ldr r4, [r12, #316]
	str r4, [r5, #188]
	ldr r4, [r12, #960]
	str r4, [r5, #192]
	ldr r4, [r12, #964]
	str r4, [r5, #196]
	ldr r4, [r12, #968]
	str r4, [r5, #200]
	ldr r4, [r12, #972]
	str r4, [r5, #204]
	ldr r4, [r12, #976]
	str r4, [r5, #208]
	ldr r4, [r12, #980]
	str r4, [r5, #212]
	ldr r4, [r12, #984]
	str r4, [r5, #216]
	ldr r4, [r12, #988]
	str r4, [r5, #220]
	ldr r4, [r12, #992]
	str r4, [r5, #224]
	ldr r4, [r12, #996]
	str r4, [r5, #228]
	ldr r4, [r12, #1000]
	str r4, [r5, #232]
	ldr r4, [r12, #1004]
	str r4, [r5, #236]
	ldr r4, [r12, #1008]
	str r4, [r5, #240]
	ldr r4, [r12, #1012]
	str r4, [r5, #244]
	ldr r4, [r12, #1016]
	str r4, [r5, #248]
	ldr r4, [r12, #1020]
	str r4, [r5, #252]
	ldr r4, [r12, #1024]
	str r4, [r5, #256]
	ldr r4, [r12, #1028]
	str r4, [r5, #260]
	ldr r4, [r12, #1032]
	str r4, [r5, #264]
	ldr r4, [r12, #1036]
	str r4, [r5, #268]
	ldr r4, [r12, #1040]
	str r4, [r5, #272]
	ldr r4, [r12, #1044]
	str r4, [r5, #276]
	ldr r4, [r12, #1048]
	str r4, [r5, #280]
	ldr r4, [r12, #1052]
	str r4, [r5, #284]
	ldr r4, [r12, #1056]
	str r4, [r5, #288]
	ldr r4, [r12, #1060]
	str r4, [r5, #292]
	ldr r4, [r12, #1064]
	str r4, [r5, #296]
	ldr r4, [r12, #1068]
	str r4, [r5, #300]
	ldr r4, [r12, #1072]
	str r4, [r5, #304]
	ldr r4, [r12, #1076]
	str r4, [r5, #308]
	ldr r4, [r12, #1080]
	str r4, [r5, #312]
	ldr r4, [r12, #1084]
	str r4, [r5, #316]
	ldr r4, [r12, #384]
	str r4, [r5, #320]
	ldr r4, [r12, #388]
	str r4, [r5, #324]
	ldr r4, [r12, #392]
	str r4, [r5, #328]
	ldr r4, [r12, #396]
	str r4, [r5, #332]
	ldr r4, [r12, #400]
	str r4, [r5, #336]
	ldr r4, [r12, #404]
	str r4, [r5, #340]
	ldr r4, [r12, #408]
	str r4, [r5, #344]
	ldr r4, [r12, #412]
	str r4, [r5, #348]
	ldr r4, [r12, #416]
	str r4, [r5, #352]
	ldr r4, [r12, #420]
	str r4, [r5, #356]
	ldr r4, [r12, #424]
	str r4, [r5, #360]
	ldr r4, [r12, #428]
	str r4, [r5, #364]
	ldr r4, [r12, #432]
	str r4, [r5, #368]
	ldr r4, [r12, #436]
	str r4, [r5, #372]
	ldr r4, [r12, #440]
	str r4, [r5, #376]
	ldr r4, [r12, #444]
	str r4, [r5, #380]
	ldr r4, [r12, #960]
	str r4, [r12, #1152]
	ldr r4, [r12, #964]
	str r4, [r12, #1156]
	ldr r4, [r12, #968]
	str r4, [r12, #1160]
	ldr r4, [r12, #972]
	str r4, [r12, #1164]
	ldr r4, [r12, #976]
	str r4, [r12, #1168]
	ldr r4, [r12, #980]
	str r4, [r12, #1172]
	ldr r4, [r12, #984]
	str r4, [r12, #1176]
	ldr r4, [r12, #988]
	str r4, [r12, #1180]
	ldr r4, [r12, #992]
	str r4, [r12, #1184]
	ldr r4, [r12, #996]
	str r4, [r12, #1188]
	ldr r4, [r12, #1000]
	str r4, [r12, #1192]
	ldr r4, [r12, #1004]
	str r4, [r12, #1196]
	ldr r4, [r12, #1008]
	str r4, [r12, #1200]
	ldr r4, [r12, #1012]
	str r4, [r12, #1204]
	ldr r4, [r12, #1016]
	str r4, [r12, #1208]
	ldr r4, [r12, #1020]
	str r4, [r12, #1212]
	ldr r4, [r12, #1024]
	str r4, [r12, #1216]
	ldr r4, [r12, #1028]
	str r4, [r12, #1220]
	ldr r4, [r12, #1032]
	str r4, [r12, #1224]
	ldr r4, [r12, #1036]
	str r4, [r12, #1228]
	ldr r4, [r12, #1040]
	str r4, [r12, #1232]
	ldr r4, [r12, #1044]
	str r4, [r12, #1236]
	ldr r4, [r12, #1048]
	str r4, [r12, #1240]
	ldr r4, [r12, #1052]
	str r4, [r12, #1244]
	ldr r4, [r12, #1056]
	str r4, [r12, #1248]
	ldr r4, [r12, #1060]
	str r4, [r12, #1252]
	ldr r4, [r12, #1064]
	str r4, [r12, #1256]
	ldr r4, [r12, #1068]
	str r4, [r12, #1260]
	ldr r4, [r12, #1072]
	str r4, [r12, #1264]
	ldr r4, [r12, #1076]
	str r4, [r12, #1268]
	ldr r4, [r12, #1080]
	str r4, [r12, #1272]
	ldr r4, [r12, #1084]
	str r4, [r12, #1276]
	ldr r4, [r12, #384]
	str r4, [r12, #1280]
	ldr r4, [r12, #388]
	str r4, [r12, #1284]
	ldr r4, [r12, #392]
	str r4, [r12, #1288]
	ldr r4, [r12, #396]
	str r4, [r12, #1292]
	ldr r4, [r12, #400]
	str r4, [r12, #1296]
	ldr r4, [r12, #404]
	str r4, [r12, #1300]
	ldr r4, [r12, #408]
	str r4, [r12, #1304]
	ldr r4, [r12, #412]
	str r4, [r12, #1308]
	ldr r4, [r12, #416]
	str r4, [r12, #1312]
	ldr r4, [r12, #420]
	str r4, [r12, #1316]
	ldr r4, [r12, #424]
	str r4, [r12, #1320]
	ldr r4, [r12, #428]
	str r4, [r12, #1324]
	ldr r4, [r12, #432]
	str r4, [r12, #1328]
	ldr r4, [r12, #436]
	str r4, [r12, #1332]
	ldr r4, [r12, #440]
	str r4, [r12, #1336]
	ldr r4, [r12, #444]
	str r4, [r12, #1340]
	mov r11, #1
21:
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1152
	movw r3, #960
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1216
	movw r3, #1024
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1280
	movw r3, #384
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1152
	movw r3, #1216
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #960
	movw r3, #1024
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1536
	movw r3, #1600
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1792
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1152
	movw r3, #1280
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #960
	movw r3, #384
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1856
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1536
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1856
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1216
	movw r3, #1280
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1024
	movw r3, #384
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1856
	movw r3, #1344
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1600
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1856
	movw r3, #1344
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1472
	movw r2, #448
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #512
	movw r3, #1664
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1472
	movw r2, #1344
	movw r3, #1472
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1600
	movw r3, #1472
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1472
	movw r2, #1600
	movw r3, #1472
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1344
	movw r3, #1472
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1536
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1600
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #448
	movw r3, #1664
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #512
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1600
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1536
	movw r3, #1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #448
	movw r3, #1664
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1600
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1408
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1856
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1728
	movw r3, #1344
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1344
	movw r3, #1536
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1728
	movw r3, #1600
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1472
	movw r2, #1856
	movw r3, #1472
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1472
	movw r2, #1472
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r4, #192
	mul r4, r4, r11
	movw r5, #5824
	add r5, r12, r5
	add r5, r5, r4
	ldr r4, [r12, #1344]
	str r4, [r5, #0]
	ldr r4, [r12, #1348]
	str r4, [r5, #4]
	ldr r4, [r12, #1352]
	str r4, [r5, #8]
	ldr r4, [r12, #1356]
	str r4, [r5, #12]
	ldr r4, [r12, #1360]
	str r4, [r5, #16]
	ldr r4, [r12, #1364]
	str r4, [r5, #20]
	ldr r4, [r12, #1368]
	str r4, [r5, #24]
	ldr r4, [r12, #1372]
	str r4, [r5, #28]
	ldr r4, [r12, #1376]
	str r4, [r5, #32]
	ldr r4, [r12, #1380]
	str r4, [r5, #36]
	ldr r4, [r12, #1384]
	str r4, [r5, #40]
	ldr r4, [r12, #1388]
	str r4, [r5, #44]
	ldr r4, [r12, #1392]
	str r4, [r5, #48]
	ldr r4, [r12, #1396]
	str r4, [r5, #52]
	ldr r4, [r12, #1400]
	str r4, [r5, #56]
	ldr r4, [r12, #1404]
	str r4, [r5, #60]
	ldr r4, [r12, #1408]
	str r4, [r5, #64]
	ldr r4, [r12, #1412]
	str r4, [r5, #68]
	ldr r4, [r12, #1416]
	str r4, [r5, #72]
	ldr r4, [r12, #1420]
	str r4, [r5, #76]
	ldr r4, [r12, #1424]
	str r4, [r5, #80]
	ldr r4, [r12, #1428]
	str r4, [r5, #84]
	ldr r4, [r12, #1432]
	str r4, [r5, #88]
	ldr r4, [r12, #1436]
	str r4, [r5, #92]
	ldr r4, [r12, #1440]
	str r4, [r5, #96]
	ldr r4, [r12, #1444]
	str r4, [r5, #100]
	ldr r4, [r12, #1448]
	str r4, [r5, #104]
	ldr r4, [r12, #1452]
	str r4, [r5, #108]
	ldr r4, [r12, #1456]
	str r4, [r5, #112]
	ldr r4, [r12, #1460]
	str r4, [r5, #116]
	ldr r4, [r12, #1464]
	str r4, [r5, #120]
	ldr r4, [r12, #1468]
	str r4, [r5, #124]
	ldr r4, [r12, #1472]
	str r4, [r5, #128]
	ldr r4, [r12, #1476]
	str r4, [r5, #132]
	ldr r4, [r12, #1480]
	str r4, [r5, #136]
	ldr r4, [r12, #1484]
	str r4, [r5, #140]
	ldr r4, [r12, #1488]
	str r4, [r5, #144]
	ldr r4, [r12, #1492]
	str r4, [r5, #148]
	ldr r4, [r12, #1496]
	str r4, [r5, #152]
	ldr r4, [r12, #1500]
	str r4, [r5, #156]
	ldr r4, [r12, #1504]
	str r4, [r5, #160]
	ldr r4, [r12, #1508]
	str r4, [r5, #164]
	ldr r4, [r12, #1512]
	str r4, [r5, #168]
	ldr r4, [r12, #1516]
	str r4, [r5, #172]
	ldr r4, [r12, #1520]
	str r4, [r5, #176]
	ldr r4, [r12, #1524]
	str r4, [r5, #180]
	ldr r4, [r12, #1528]
	str r4, [r5, #184]
	ldr r4, [r12, #1532]
	str r4, [r5, #188]
	ldr r4, [r12, #1344]
	str r4, [r12, #1152]
	ldr r4, [r12, #1348]
	str r4, [r12, #1156]
	ldr r4, [r12, #1352]
	str r4, [r12, #1160]
	ldr r4, [r12, #1356]
	str r4, [r12, #1164]
	ldr r4, [r12, #1360]
	str r4, [r12, #1168]
	ldr r4, [r12, #1364]
	str r4, [r12, #1172]
	ldr r4, [r12, #1368]
	str r4, [r12, #1176]
	ldr r4, [r12, #1372]
	str r4, [r12, #1180]
	ldr r4, [r12, #1376]
	str r4, [r12, #1184]
	ldr r4, [r12, #1380]
	str r4, [r12, #1188]
	ldr r4, [r12, #1384]
	str r4, [r12, #1192]
	ldr r4, [r12, #1388]
	str r4, [r12, #1196]
	ldr r4, [r12, #1392]
	str r4, [r12, #1200]
	ldr r4, [r12, #1396]
	str r4, [r12, #1204]
	ldr r4, [r12, #1400]
	str r4, [r12, #1208]
	ldr r4, [r12, #1404]
	str r4, [r12, #1212]
	ldr r4, [r12, #1408]
	str r4, [r12, #1216]
	ldr r4, [r12, #1412]
	str r4, [r12, #1220]
	ldr r4, [r12, #1416]
	str r4, [r12, #1224]
	ldr r4, [r12, #1420]
	str r4, [r12, #1228]
	ldr r4, [r12, #1424]
	str r4, [r12, #1232]
	ldr r4, [r12, #1428]
	str r4, [r12, #1236]
	ldr r4, [r12, #1432]
	str r4, [r12, #1240]
	ldr r4, [r12, #1436]
	str r4, [r12, #1244]
	ldr r4, [r12, #1440]
	str r4, [r12, #1248]
	ldr r4, [r12, #1444]
	str r4, [r12, #1252]
	ldr r4, [r12, #1448]
	str r4, [r12, #1256]
	ldr r4, [r12, #1452]
	str r4, [r12, #1260]
	ldr r4, [r12, #1456]
	str r4, [r12, #1264]
	ldr r4, [r12, #1460]
	str r4, [r12, #1268]
	ldr r4, [r12, #1464]
	str r4, [r12, #1272]
	ldr r4, [r12, #1468]
	str r4, [r12, #1276]
	ldr r4, [r12, #1472]
	str r4, [r12, #1280]
	ldr r4, [r12, #1476]
	str r4, [r12, #1284]
	ldr r4, [r12, #1480]
	str r4, [r12, #1288]
	ldr r4, [r12, #1484]
	str r4, [r12, #1292]
	ldr r4, [r12, #1488]
	str r4, [r12, #1296]
	ldr r4, [r12, #1492]
	str r4, [r12, #1300]
	ldr r4, [r12, #1496]
	str r4, [r12, #1304]
	ldr r4, [r12, #1500]
	str r4, [r12, #1308]
	ldr r4, [r12, #1504]
	str r4, [r12, #1312]
	ldr r4, [r12, #1508]
	str r4, [r12, #1316]
	ldr r4, [r12, #1512]
	str r4, [r12, #1320]
	ldr r4, [r12, #1516]
	str r4, [r12, #1324]
	ldr r4, [r12, #1520]
	str r4, [r12, #1328]
	ldr r4, [r12, #1524]
	str r4, [r12, #1332]
	ldr r4, [r12, #1528]
	str r4, [r12, #1336]
	ldr r4, [r12, #1532]
	str r4, [r12, #1340]
	add r11, r11, #1
	cmp r11, #7
	bne 21b
	ldr r4, [r12, #256]
	str r4, [r12, #960]
	ldr r4, [r12, #260]
	str r4, [r12, #964]
	ldr r4, [r12, #264]
	str r4, [r12, #968]
	ldr r4, [r12, #268]
	str r4, [r12, #972]
	ldr r4, [r12, #272]
	str r4, [r12, #976]
	ldr r4, [r12, #276]
	str r4, [r12, #980]
	ldr r4, [r12, #280]
	str r4, [r12, #984]
	ldr r4, [r12, #284]
	str r4, [r12, #988]
	ldr r4, [r12, #288]
	str r4, [r12, #992]
	ldr r4, [r12, #292]
	str r4, [r12, #996]
	ldr r4, [r12, #296]
	str r4, [r12, #1000]
	ldr r4, [r12, #300]
	str r4, [r12, #1004]
	ldr r4, [r12, #304]
	str r4, [r12, #1008]
	ldr r4, [r12, #308]
	str r4, [r12, #1012]
	ldr r4, [r12, #312]
	str r4, [r12, #1016]
	ldr r4, [r12, #316]
	str r4, [r12, #1020]
	ldr r4, [r12, #384]
	str r4, [r12, #1024]
	ldr r4, [r12, #388]
	str r4, [r12, #1028]
	ldr r4, [r12, #392]
	str r4, [r12, #1032]
	ldr r4, [r12, #396]
	str r4, [r12, #1036]
	ldr r4, [r12, #400]
	str r4, [r12, #1040]
	ldr r4, [r12, #404]
	str r4, [r12, #1044]
	ldr r4, [r12, #408]
	str r4, [r12, #1048]
	ldr r4, [r12, #412]
	str r4, [r12, #1052]
	ldr r4, [r12, #416]
	str r4, [r12, #1056]
	ldr r4, [r12, #420]
	str r4, [r12, #1060]
	ldr r4, [r12, #424]
	str r4, [r12, #1064]
	ldr r4, [r12, #428]
	str r4, [r12, #1068]
	ldr r4, [r12, #432]
	str r4, [r12, #1072]
	ldr r4, [r12, #436]
	str r4, [r12, #1076]
	ldr r4, [r12, #440]
	str r4, [r12, #1080]
	ldr r4, [r12, #444]
	str r4, [r12, #1084]
	ldr r4, [r12, #256]
	str r4, [r12, #1088]
	ldr r4, [r12, #260]
	str r4, [r12, #1092]
	ldr r4, [r12, #264]
	str r4, [r12, #1096]
	ldr r4, [r12, #268]
	str r4, [r12, #1100]
	ldr r4, [r12, #272]
	str r4, [r12, #1104]
	ldr r4, [r12, #276]
	str r4, [r12, #1108]
	ldr r4, [r12, #280]
	str r4, [r12, #1112]
	ldr r4, [r12, #284]
	str r4, [r12, #1116]
	ldr r4, [r12, #288]
	str r4, [r12, #1120]
	ldr r4, [r12, #292]
	str r4, [r12, #1124]
	ldr r4, [r12, #296]
	str r4, [r12, #1128]
	ldr r4, [r12, #300]
	str r4, [r12, #1132]
	ldr r4, [r12, #304]
	str r4, [r12, #1136]
	ldr r4, [r12, #308]
	str r4, [r12, #1140]
	ldr r4, [r12, #312]
	str r4, [r12, #1144]
	ldr r4, [r12, #316]
	str r4, [r12, #1148]
	mov r11, #171
22:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #960
	movw r3, #1088
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1088
	movw r3, #1088
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1216
	movw r2, #1024
	movw r3, #1536
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1088
	movw r3, #256
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1152
	movw r3, #1152
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1216
	movw r3, #1216
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1600
	movw r3, #1600
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1152
	movw r3, #1600
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1728
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1536
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1728
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1280
	movw r3, #1280
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #448
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1536
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1856
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1856
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1472
	movw r2, #1216
	movw r3, #1280
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1472
	movw r2, #1472
	movw r3, #1472
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1792
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1344
	movw r3, #1728
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1344
	movw r3, #1728
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1728
	movw r3, #1344
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1792
	movw r3, #1408
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1664
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1664
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1664
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1408
	movw r3, #1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1344
	movw r3, #1344
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1408
	movw r3, #1408
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1600
	movw r3, #1600
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1344
	movw r3, #1600
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1728
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1536
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1728
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1472
	movw r3, #1472
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #448
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1536
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1856
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1856
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1408
	movw r3, #1472
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1280
	movw r3, #1280
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1792
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1152
	movw r3, #1728
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1152
	movw r3, #1728
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1216
	movw r2, #1728
	movw r3, #1152
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1216
	movw r2, #1792
	movw r3, #1216
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1664
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1664
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1664
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1216
	movw r2, #1216
	movw r3, #1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1152
	movw r3, #1152
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1216
	movw r3, #1216
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1600
	movw r3, #1600
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1152
	movw r3, #1600
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1728
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1536
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1728
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1280
	movw r3, #1280
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #448
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1536
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1856
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1856
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1472
	movw r2, #1216
	movw r3, #1280
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1472
	movw r2, #1472
	movw r3, #1472
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1792
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1344
	movw r3, #1728
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1344
	movw r2, #1344
	movw r3, #1728
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1728
	movw r3, #1344
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1792
	movw r3, #1408
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1664
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1664
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1664
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1408
	movw r2, #1408
	movw r3, #1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #960
	movw r2, #1344
	movw r3, #1472
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1472
	movw r3, #1472
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1088
	movw r2, #1536
	movw r3, #1472
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1024
	movw r2, #1408
	movw r3, #256
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	ldr r5, [r12, #1088]
	ldr r4, [r12, #1092]
	orr r5, r5, r4
	ldr r4, [r12, #1096]
	orr r5, r5, r4
	ldr r4, [r12, #1100]
	orr r5, r5, r4
	ldr r4, [r12, #1104]
	orr r5, r5, r4
	ldr r4, [r12, #1108]
	orr r5, r5, r4
	ldr r4, [r12, #1112]
	orr r5, r5, r4
	ldr r4, [r12, #1116]
	orr r5, r5, r4
	ldr r4, [r12, #1120]
	orr r5, r5, r4
	ldr r4, [r12, #1124]
	orr r5, r5, r4
	ldr r4, [r12, #1128]
	orr r5, r5, r4
	ldr r4, [r12, #1132]
	orr r5, r5, r4
	ldr r4, [r12, #1136]
	orr r5, r5, r4
	ldr r4, [r12, #1140]
	orr r5, r5, r4
	ldr r4, [r12, #1144]
	orr r5, r5, r4
	ldr r4, [r12, #1148]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	mov r10, r5
	ldr r4, [r12, #384]
	ldr r5, [r12, #1024]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1024]
	ldr r4, [r12, #388]
	ldr r5, [r12, #1028]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1028]
	ldr r4, [r12, #392]
	ldr r5, [r12, #1032]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1032]
	ldr r4, [r12, #396]
	ldr r5, [r12, #1036]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1036]
	ldr r4, [r12, #400]
	ldr r5, [r12, #1040]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1040]
	ldr r4, [r12, #404]
	ldr r5, [r12, #1044]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1044]
	ldr r4, [r12, #408]
	ldr r5, [r12, #1048]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1048]
	ldr r4, [r12, #412]
	ldr r5, [r12, #1052]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1052]
	ldr r4, [r12, #416]
	ldr r5, [r12, #1056]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1056]
	ldr r4, [r12, #420]
	ldr r5, [r12, #1060]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1060]
	ldr r4, [r12, #424]
	ldr r5, [r12, #1064]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1064]
	ldr r4, [r12, #428]
	ldr r5, [r12, #1068]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1068]
	ldr r4, [r12, #432]
	ldr r5, [r12, #1072]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1072]
	ldr r4, [r12, #436]
	ldr r5, [r12, #1076]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1076]
	ldr r4, [r12, #440]
	ldr r5, [r12, #1080]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1080]
	ldr r4, [r12, #444]
	ldr r5, [r12, #1084]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1084]
	mov r4, #3
	mul r4, r4, r11
	add r4, r12, r4
	add r4, r4, #4096
	cmp r11, #170
	beq 23f
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #2]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
	b 24f
23:
	mov r9, #0
	add r9, r9, r9
	ldrb r5, [r4, #1]
	add r9, r9, r5
	add r9, r9, r9
	ldrb r5, [r4, #0]
	add r9, r9, r5
24:
	movw r8, #5632
	add r8, r12, r8
	mov r7, #0
25:
	eor r10, r9, r7
	sub r10, r10, #1
	lsr r10, r10, #31
	mov r5, #0
	sub r10, r5, r10
	ldr r4, [r12, #1344]
	ldr r5, [r8, #0]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1344]
	ldr r4, [r12, #1348]
	ldr r5, [r8, #4]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1348]
	ldr r4, [r12, #1352]
	ldr r5, [r8, #8]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1352]
	ldr r4, [r12, #1356]
	ldr r5, [r8, #12]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1356]
	ldr r4, [r12, #1360]
	ldr r5, [r8, #16]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1360]
	ldr r4, [r12, #1364]
	ldr r5, [r8, #20]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1364]
	ldr r4, [r12, #1368]
	ldr r5, [r8, #24]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1368]
	ldr r4, [r12, #1372]
	ldr r5, [r8, #28]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1372]
	ldr r4, [r12, #1376]
	ldr r5, [r8, #32]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1376]
	ldr r4, [r12, #1380]
	ldr r5, [r8, #36]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1380]
	ldr r4, [r12, #1384]
	ldr r5, [r8, #40]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1384]
	ldr r4, [r12, #1388]
	ldr r5, [r8, #44]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1388]
	ldr r4, [r12, #1392]
	ldr r5, [r8, #48]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1392]
	ldr r4, [r12, #1396]
	ldr r5, [r8, #52]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1396]
	ldr r4, [r12, #1400]
	ldr r5, [r8, #56]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1400]
	ldr r4, [r12, #1404]
	ldr r5, [r8, #60]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1404]
	ldr r4, [r12, #1408]
	ldr r5, [r8, #64]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1408]
	ldr r4, [r12, #1412]
	ldr r5, [r8, #68]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1412]
	ldr r4, [r12, #1416]
	ldr r5, [r8, #72]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1416]
	ldr r4, [r12, #1420]
	ldr r5, [r8, #76]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1420]
	ldr r4, [r12, #1424]
	ldr r5, [r8, #80]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1424]
	ldr r4, [r12, #1428]
	ldr r5, [r8, #84]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1428]
	ldr r4, [r12, #1432]
	ldr r5, [r8, #88]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1432]
	ldr r4, [r12, #1436]
	ldr r5, [r8, #92]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1436]
	ldr r4, [r12, #1440]
	ldr r5, [r8, #96]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1440]
	ldr r4, [r12, #1444]
	ldr r5, [r8, #100]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1444]
	ldr r4, [r12, #1448]
	ldr r5, [r8, #104]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1448]
	ldr r4, [r12, #1452]
	ldr r5, [r8, #108]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1452]
	ldr r4, [r12, #1456]
	ldr r5, [r8, #112]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1456]
	ldr r4, [r12, #1460]
	ldr r5, [r8, #116]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1460]
	ldr r4, [r12, #1464]
	ldr r5, [r8, #120]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1464]
	ldr r4, [r12, #1468]
	ldr r5, [r8, #124]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1468]
	ldr r4, [r12, #1472]
	ldr r5, [r8, #128]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1472]
	ldr r4, [r12, #1476]
	ldr r5, [r8, #132]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1476]
	ldr r4, [r12, #1480]
	ldr r5, [r8, #136]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1480]
	ldr r4, [r12, #1484]
	ldr r5, [r8, #140]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1484]
	ldr r4, [r12, #1488]
	ldr r5, [r8, #144]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1488]
	ldr r4, [r12, #1492]
	ldr r5, [r8, #148]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1492]
	ldr r4, [r12, #1496]
	ldr r5, [r8, #152]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1496]
	ldr r4, [r12, #1500]
	ldr r5, [r8, #156]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1500]
	ldr r4, [r12, #1504]
	ldr r5, [r8, #160]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1504]
	ldr r4, [r12, #1508]
	ldr r5, [r8, #164]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1508]
	ldr r4, [r12, #1512]
	ldr r5, [r8, #168]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1512]
	ldr r4, [r12, #1516]
	ldr r5, [r8, #172]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1516]
	ldr r4, [r12, #1520]
	ldr r5, [r8, #176]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1520]
	ldr r4, [r12, #1524]
	ldr r5, [r8, #180]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1524]
	ldr r4, [r12, #1528]
	ldr r5, [r8, #184]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1528]
	ldr r4, [r12, #1532]
	ldr r5, [r8, #188]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1532]
	add r8, r8, #192
	add r7, r7, #1
	cmp r7, #8
	bne 25b
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #960
	movw r3, #1344
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1024
	movw r3, #1408
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1088
	movw r3, #1472
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #960
	movw r3, #1024
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1344
	movw r3, #1408
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1536
	movw r3, #1600
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1728
	movw r2, #1728
	movw r3, #1792
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #960
	movw r3, #1088
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1344
	movw r3, #1472
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1856
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1536
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1856
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1024
	movw r3, #1088
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1408
	movw r3, #1472
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1856
	movw r3, #1152
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1600
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1856
	movw r2, #1856
	movw r3, #1152
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #448
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #512
	movw r3, #1664
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1152
	movw r3, #1280
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1600
	movw r3, #1280
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1600
	movw r3, #1280
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1216
	movw r2, #1152
	movw r3, #1280
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1536
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1600
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #448
	movw r3, #1664
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #512
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1600
	movw r2, #1600
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #1536
	movw r3, #1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1664
	movw r2, #448
	movw r3, #1664
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1792
	movw r2, #1792
	movw r3, #1664
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1600
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1216
	movw r2, #1216
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1856
	movw r3, #1792
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1728
	movw r3, #1152
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1152
	movw r2, #1152
	movw r3, #1536
	bl {vg_brainpoolp512r1_sub_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1536
	movw r2, #1728
	movw r3, #1600
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1856
	movw r3, #1280
	bl {vg_brainpoolp512r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1280
	movw r2, #1280
	movw r3, #1536
	bl {vg_brainpoolp512r1_add_mod_p}
	mov lr, r10
	ldr r4, [r12, #1152]
	str r4, [r12, #960]
	ldr r4, [r12, #1156]
	str r4, [r12, #964]
	ldr r4, [r12, #1160]
	str r4, [r12, #968]
	ldr r4, [r12, #1164]
	str r4, [r12, #972]
	ldr r4, [r12, #1168]
	str r4, [r12, #976]
	ldr r4, [r12, #1172]
	str r4, [r12, #980]
	ldr r4, [r12, #1176]
	str r4, [r12, #984]
	ldr r4, [r12, #1180]
	str r4, [r12, #988]
	ldr r4, [r12, #1184]
	str r4, [r12, #992]
	ldr r4, [r12, #1188]
	str r4, [r12, #996]
	ldr r4, [r12, #1192]
	str r4, [r12, #1000]
	ldr r4, [r12, #1196]
	str r4, [r12, #1004]
	ldr r4, [r12, #1200]
	str r4, [r12, #1008]
	ldr r4, [r12, #1204]
	str r4, [r12, #1012]
	ldr r4, [r12, #1208]
	str r4, [r12, #1016]
	ldr r4, [r12, #1212]
	str r4, [r12, #1020]
	ldr r4, [r12, #1216]
	str r4, [r12, #1024]
	ldr r4, [r12, #1220]
	str r4, [r12, #1028]
	ldr r4, [r12, #1224]
	str r4, [r12, #1032]
	ldr r4, [r12, #1228]
	str r4, [r12, #1036]
	ldr r4, [r12, #1232]
	str r4, [r12, #1040]
	ldr r4, [r12, #1236]
	str r4, [r12, #1044]
	ldr r4, [r12, #1240]
	str r4, [r12, #1048]
	ldr r4, [r12, #1244]
	str r4, [r12, #1052]
	ldr r4, [r12, #1248]
	str r4, [r12, #1056]
	ldr r4, [r12, #1252]
	str r4, [r12, #1060]
	ldr r4, [r12, #1256]
	str r4, [r12, #1064]
	ldr r4, [r12, #1260]
	str r4, [r12, #1068]
	ldr r4, [r12, #1264]
	str r4, [r12, #1072]
	ldr r4, [r12, #1268]
	str r4, [r12, #1076]
	ldr r4, [r12, #1272]
	str r4, [r12, #1080]
	ldr r4, [r12, #1276]
	str r4, [r12, #1084]
	ldr r4, [r12, #1280]
	str r4, [r12, #1088]
	ldr r4, [r12, #1284]
	str r4, [r12, #1092]
	ldr r4, [r12, #1288]
	str r4, [r12, #1096]
	ldr r4, [r12, #1292]
	str r4, [r12, #1100]
	ldr r4, [r12, #1296]
	str r4, [r12, #1104]
	ldr r4, [r12, #1300]
	str r4, [r12, #1108]
	ldr r4, [r12, #1304]
	str r4, [r12, #1112]
	ldr r4, [r12, #1308]
	str r4, [r12, #1116]
	ldr r4, [r12, #1312]
	str r4, [r12, #1120]
	ldr r4, [r12, #1316]
	str r4, [r12, #1124]
	ldr r4, [r12, #1320]
	str r4, [r12, #1128]
	ldr r4, [r12, #1324]
	str r4, [r12, #1132]
	ldr r4, [r12, #1328]
	str r4, [r12, #1136]
	ldr r4, [r12, #1332]
	str r4, [r12, #1140]
	ldr r4, [r12, #1336]
	str r4, [r12, #1144]
	ldr r4, [r12, #1340]
	str r4, [r12, #1148]
	cmp r11, #0
	bne 22b
	mov r10, lr
	ldr r4, [r12, #2944]
	ldr r5, [r12, #2948]
	ldr r6, [r12, #2952]
	ldr r7, [r12, #2956]
	ldr r8, [r12, #2960]
	ldr r9, [r12, #2964]
	ldr r11, [r12, #2972]
	ldr lr, [r12, #2976]
	bx lr
