// The functions of `src/internal/vg_mlkem_inv_ntt.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_inv_ntt:
	str r4, [r1, #512]
	str r5, [r1, #516]
	str r6, [r1, #520]
	str r7, [r1, #524]
	str r8, [r1, #528]
	str r9, [r1, #532]
	str r10, [r1, #536]
	str r11, [r1, #540]
	movw r12, #1
	str r12, [r1, #0]
	movw r12, #1729
	str r12, [r1, #4]
	movw r12, #2580
	str r12, [r1, #8]
	movw r12, #3289
	str r12, [r1, #12]
	movw r12, #2642
	str r12, [r1, #16]
	movw r12, #630
	str r12, [r1, #20]
	movw r12, #1897
	str r12, [r1, #24]
	movw r12, #848
	str r12, [r1, #28]
	movw r12, #1062
	str r12, [r1, #32]
	movw r12, #1919
	str r12, [r1, #36]
	movw r12, #193
	str r12, [r1, #40]
	movw r12, #797
	str r12, [r1, #44]
	movw r12, #2786
	str r12, [r1, #48]
	movw r12, #3260
	str r12, [r1, #52]
	movw r12, #569
	str r12, [r1, #56]
	movw r12, #1746
	str r12, [r1, #60]
	movw r12, #296
	str r12, [r1, #64]
	movw r12, #2447
	str r12, [r1, #68]
	movw r12, #1339
	str r12, [r1, #72]
	movw r12, #1476
	str r12, [r1, #76]
	movw r12, #3046
	str r12, [r1, #80]
	movw r12, #56
	str r12, [r1, #84]
	movw r12, #2240
	str r12, [r1, #88]
	movw r12, #1333
	str r12, [r1, #92]
	movw r12, #1426
	str r12, [r1, #96]
	movw r12, #2094
	str r12, [r1, #100]
	movw r12, #535
	str r12, [r1, #104]
	movw r12, #2882
	str r12, [r1, #108]
	movw r12, #2393
	str r12, [r1, #112]
	movw r12, #2879
	str r12, [r1, #116]
	movw r12, #1974
	str r12, [r1, #120]
	movw r12, #821
	str r12, [r1, #124]
	movw r12, #289
	str r12, [r1, #128]
	movw r12, #331
	str r12, [r1, #132]
	movw r12, #3253
	str r12, [r1, #136]
	movw r12, #1756
	str r12, [r1, #140]
	movw r12, #1197
	str r12, [r1, #144]
	movw r12, #2304
	str r12, [r1, #148]
	movw r12, #2277
	str r12, [r1, #152]
	movw r12, #2055
	str r12, [r1, #156]
	movw r12, #650
	str r12, [r1, #160]
	movw r12, #1977
	str r12, [r1, #164]
	movw r12, #2513
	str r12, [r1, #168]
	movw r12, #632
	str r12, [r1, #172]
	movw r12, #2865
	str r12, [r1, #176]
	movw r12, #33
	str r12, [r1, #180]
	movw r12, #1320
	str r12, [r1, #184]
	movw r12, #1915
	str r12, [r1, #188]
	movw r12, #2319
	str r12, [r1, #192]
	movw r12, #1435
	str r12, [r1, #196]
	movw r12, #807
	str r12, [r1, #200]
	movw r12, #452
	str r12, [r1, #204]
	movw r12, #1438
	str r12, [r1, #208]
	movw r12, #2868
	str r12, [r1, #212]
	movw r12, #1534
	str r12, [r1, #216]
	movw r12, #2402
	str r12, [r1, #220]
	movw r12, #2647
	str r12, [r1, #224]
	movw r12, #2617
	str r12, [r1, #228]
	movw r12, #1481
	str r12, [r1, #232]
	movw r12, #648
	str r12, [r1, #236]
	movw r12, #2474
	str r12, [r1, #240]
	movw r12, #3110
	str r12, [r1, #244]
	movw r12, #1227
	str r12, [r1, #248]
	movw r12, #910
	str r12, [r1, #252]
	movw r12, #17
	str r12, [r1, #256]
	movw r12, #2761
	str r12, [r1, #260]
	movw r12, #583
	str r12, [r1, #264]
	movw r12, #2649
	str r12, [r1, #268]
	movw r12, #1637
	str r12, [r1, #272]
	movw r12, #723
	str r12, [r1, #276]
	movw r12, #2288
	str r12, [r1, #280]
	movw r12, #1100
	str r12, [r1, #284]
	movw r12, #1409
	str r12, [r1, #288]
	movw r12, #2662
	str r12, [r1, #292]
	movw r12, #3281
	str r12, [r1, #296]
	movw r12, #233
	str r12, [r1, #300]
	movw r12, #756
	str r12, [r1, #304]
	movw r12, #2156
	str r12, [r1, #308]
	movw r12, #3015
	str r12, [r1, #312]
	movw r12, #3050
	str r12, [r1, #316]
	movw r12, #1703
	str r12, [r1, #320]
	movw r12, #1651
	str r12, [r1, #324]
	movw r12, #2789
	str r12, [r1, #328]
	movw r12, #1789
	str r12, [r1, #332]
	movw r12, #1847
	str r12, [r1, #336]
	movw r12, #952
	str r12, [r1, #340]
	movw r12, #1461
	str r12, [r1, #344]
	movw r12, #2687
	str r12, [r1, #348]
	movw r12, #939
	str r12, [r1, #352]
	movw r12, #2308
	str r12, [r1, #356]
	movw r12, #2437
	str r12, [r1, #360]
	movw r12, #2388
	str r12, [r1, #364]
	movw r12, #733
	str r12, [r1, #368]
	movw r12, #2337
	str r12, [r1, #372]
	movw r12, #268
	str r12, [r1, #376]
	movw r12, #641
	str r12, [r1, #380]
	movw r12, #1584
	str r12, [r1, #384]
	movw r12, #2298
	str r12, [r1, #388]
	movw r12, #2037
	str r12, [r1, #392]
	movw r12, #3220
	str r12, [r1, #396]
	movw r12, #375
	str r12, [r1, #400]
	movw r12, #2549
	str r12, [r1, #404]
	movw r12, #2090
	str r12, [r1, #408]
	movw r12, #1645
	str r12, [r1, #412]
	movw r12, #1063
	str r12, [r1, #416]
	movw r12, #319
	str r12, [r1, #420]
	movw r12, #2773
	str r12, [r1, #424]
	movw r12, #757
	str r12, [r1, #428]
	movw r12, #2099
	str r12, [r1, #432]
	movw r12, #561
	str r12, [r1, #436]
	movw r12, #2466
	str r12, [r1, #440]
	movw r12, #2594
	str r12, [r1, #444]
	movw r12, #2804
	str r12, [r1, #448]
	movw r12, #1092
	str r12, [r1, #452]
	movw r12, #403
	str r12, [r1, #456]
	movw r12, #1026
	str r12, [r1, #460]
	movw r12, #1143
	str r12, [r1, #464]
	movw r12, #2150
	str r12, [r1, #468]
	movw r12, #2775
	str r12, [r1, #472]
	movw r12, #886
	str r12, [r1, #476]
	movw r12, #1722
	str r12, [r1, #480]
	movw r12, #1212
	str r12, [r1, #484]
	movw r12, #1874
	str r12, [r1, #488]
	movw r12, #1029
	str r12, [r1, #492]
	movw r12, #2110
	str r12, [r1, #496]
	movw r12, #2935
	str r12, [r1, #500]
	movw r12, #885
	str r12, [r1, #504]
	movw r12, #2154
	str r12, [r1, #508]
	movw r8, #30198
	movt r8, #2
	add r0, r0, #1024
	add r1, r1, #508
	mov r10, #8
20:
	sub r2, r0, #1024
21:
	ldr r7, [r1, #0]
	sub r1, r1, #4
	add r3, r2, r10
	lsr r11, r10, #2
22:
	ldr r4, [r2, #0]
	ldr r5, [r3, #0]
	add r6, r4, r5
	sub r6, r6, #3328
	sub r6, r6, #1
	lsr r12, r6, #31
	add r6, r6, r12
	add r6, r6, r12, lsl #8
	add r6, r6, r12, lsl #10
	add r6, r6, r12, lsl #11
	str r6, [r2, #0]
	sub r5, r5, r4
	lsr r12, r5, #31
	add r5, r5, r12
	add r5, r5, r12, lsl #8
	add r5, r5, r12, lsl #10
	add r5, r5, r12, lsl #11
	mul r5, r7, r5
	lsr r6, r5, #11
	mul r6, r6, r8
	lsr r6, r6, #18
	sub r5, r5, r6
	sub r5, r5, r6, lsl #8
	sub r5, r5, r6, lsl #10
	sub r5, r5, r6, lsl #11
	sub r5, r5, #3328
	sub r5, r5, #1
	lsr r6, r5, #31
	add r5, r5, r6
	add r5, r5, r6, lsl #8
	add r5, r5, r6, lsl #10
	add r5, r5, r6, lsl #11
	str r5, [r3, #0]
	add r2, r2, #4
	add r3, r3, #4
	subs r11, r11, #1
	bne 22b
	mov r2, r3
	cmp r2, r0
	bne 21b
	lsl r10, r10, #1
	cmp r10, #1024
	bne 20b
	movw r7, #3303
	sub r2, r0, #1024
	mov r11, #256
23:
	ldr r4, [r2, #0]
	mul r4, r4, r7
	lsr r6, r4, #11
	mul r6, r6, r8
	lsr r6, r6, #18
	sub r4, r4, r6
	sub r4, r4, r6, lsl #8
	sub r4, r4, r6, lsl #10
	sub r4, r4, r6, lsl #11
	sub r4, r4, #3328
	sub r4, r4, #1
	lsr r6, r4, #31
	add r4, r4, r6
	add r4, r4, r6, lsl #8
	add r4, r4, r6, lsl #10
	add r4, r4, r6, lsl #11
	str r4, [r2, #0]
	add r2, r2, #4
	subs r11, r11, #1
	bne 23b
	ldr r4, [r1, #512]
	ldr r5, [r1, #516]
	ldr r6, [r1, #520]
	ldr r7, [r1, #524]
	ldr r8, [r1, #528]
	ldr r9, [r1, #532]
	ldr r10, [r1, #536]
	ldr r11, [r1, #540]
	bx lr
