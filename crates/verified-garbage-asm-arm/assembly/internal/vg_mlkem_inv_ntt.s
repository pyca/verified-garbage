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
	movw r12, #19
	movt r12, #1
	str r12, [r1, #0]
	movw r12, #34037
	movt r12, #1729
	str r12, [r1, #4]
	movw r12, #50790
	movt r12, #2580
	str r12, [r1, #8]
	movw r12, #64748
	movt r12, #3289
	str r12, [r1, #12]
	movw r12, #52011
	movt r12, #2642
	str r12, [r1, #16]
	movw r12, #12402
	movt r12, #630
	str r12, [r1, #20]
	movw r12, #37345
	movt r12, #1897
	str r12, [r1, #24]
	movw r12, #16694
	movt r12, #848
	str r12, [r1, #28]
	movw r12, #20906
	movt r12, #1062
	str r12, [r1, #32]
	movw r12, #37778
	movt r12, #1919
	str r12, [r1, #36]
	movw r12, #3799
	movt r12, #193
	str r12, [r1, #40]
	movw r12, #15690
	movt r12, #797
	str r12, [r1, #44]
	movw r12, #54846
	movt r12, #2786
	str r12, [r1, #48]
	movw r12, #64177
	movt r12, #3260
	str r12, [r1, #52]
	movw r12, #11201
	movt r12, #569
	str r12, [r1, #56]
	movw r12, #34372
	movt r12, #1746
	str r12, [r1, #60]
	movw r12, #5827
	movt r12, #296
	str r12, [r1, #64]
	movw r12, #48172
	movt r12, #2447
	str r12, [r1, #68]
	movw r12, #26360
	movt r12, #1339
	str r12, [r1, #72]
	movw r12, #29057
	movt r12, #1476
	str r12, [r1, #76]
	movw r12, #59964
	movt r12, #3046
	str r12, [r1, #80]
	movw r12, #1102
	movt r12, #56
	str r12, [r1, #84]
	movw r12, #44097
	movt r12, #2240
	str r12, [r1, #88]
	movw r12, #26241
	movt r12, #1333
	str r12, [r1, #92]
	movw r12, #28072
	movt r12, #1426
	str r12, [r1, #96]
	movw r12, #41223
	movt r12, #2094
	str r12, [r1, #100]
	movw r12, #10532
	movt r12, #535
	str r12, [r1, #104]
	movw r12, #56736
	movt r12, #2882
	str r12, [r1, #108]
	movw r12, #47109
	movt r12, #2393
	str r12, [r1, #112]
	movw r12, #56677
	movt r12, #2879
	str r12, [r1, #116]
	movw r12, #38860
	movt r12, #1974
	str r12, [r1, #120]
	movw r12, #16162
	movt r12, #821
	str r12, [r1, #124]
	movw r12, #5689
	movt r12, #289
	str r12, [r1, #128]
	movw r12, #6516
	movt r12, #331
	str r12, [r1, #132]
	movw r12, #64039
	movt r12, #3253
	str r12, [r1, #136]
	movw r12, #34569
	movt r12, #1756
	str r12, [r1, #140]
	movw r12, #23564
	movt r12, #1197
	str r12, [r1, #144]
	movw r12, #45357
	movt r12, #2304
	str r12, [r1, #148]
	movw r12, #44825
	movt r12, #2277
	str r12, [r1, #152]
	movw r12, #40455
	movt r12, #2055
	str r12, [r1, #156]
	movw r12, #12796
	movt r12, #650
	str r12, [r1, #160]
	movw r12, #38919
	movt r12, #1977
	str r12, [r1, #164]
	movw r12, #49471
	movt r12, #2513
	str r12, [r1, #168]
	movw r12, #12441
	movt r12, #632
	str r12, [r1, #172]
	movw r12, #56401
	movt r12, #2865
	str r12, [r1, #176]
	movw r12, #649
	movt r12, #33
	str r12, [r1, #180]
	movw r12, #25986
	movt r12, #1320
	str r12, [r1, #184]
	movw r12, #37699
	movt r12, #1915
	str r12, [r1, #188]
	movw r12, #45652
	movt r12, #2319
	str r12, [r1, #192]
	movw r12, #28249
	movt r12, #1435
	str r12, [r1, #196]
	movw r12, #15886
	movt r12, #807
	str r12, [r1, #200]
	movw r12, #8898
	movt r12, #452
	str r12, [r1, #204]
	movw r12, #28309
	movt r12, #1438
	str r12, [r1, #208]
	movw r12, #56460
	movt r12, #2868
	str r12, [r1, #212]
	movw r12, #30198
	movt r12, #1534
	str r12, [r1, #216]
	movw r12, #47286
	movt r12, #2402
	str r12, [r1, #220]
	movw r12, #52109
	movt r12, #2647
	str r12, [r1, #224]
	movw r12, #51519
	movt r12, #2617
	str r12, [r1, #228]
	movw r12, #29155
	movt r12, #1481
	str r12, [r1, #232]
	movw r12, #12756
	movt r12, #648
	str r12, [r1, #236]
	movw r12, #48704
	movt r12, #2474
	str r12, [r1, #240]
	movw r12, #61224
	movt r12, #3110
	str r12, [r1, #244]
	movw r12, #24155
	movt r12, #1227
	str r12, [r1, #248]
	movw r12, #17914
	movt r12, #910
	str r12, [r1, #252]
	movw r12, #334
	movt r12, #17
	str r12, [r1, #256]
	movw r12, #54354
	movt r12, #2761
	str r12, [r1, #260]
	movw r12, #11477
	movt r12, #583
	str r12, [r1, #264]
	movw r12, #52149
	movt r12, #2649
	str r12, [r1, #268]
	movw r12, #32226
	movt r12, #1637
	str r12, [r1, #272]
	movw r12, #14233
	movt r12, #723
	str r12, [r1, #276]
	movw r12, #45042
	movt r12, #2288
	str r12, [r1, #280]
	movw r12, #21655
	movt r12, #1100
	str r12, [r1, #284]
	movw r12, #27738
	movt r12, #1409
	str r12, [r1, #288]
	movw r12, #52405
	movt r12, #2662
	str r12, [r1, #292]
	movw r12, #64591
	movt r12, #3281
	str r12, [r1, #296]
	movw r12, #4586
	movt r12, #233
	str r12, [r1, #300]
	movw r12, #14882
	movt r12, #756
	str r12, [r1, #304]
	movw r12, #42443
	movt r12, #2156
	str r12, [r1, #308]
	movw r12, #59354
	movt r12, #3015
	str r12, [r1, #312]
	movw r12, #60043
	movt r12, #3050
	str r12, [r1, #316]
	movw r12, #33525
	movt r12, #1703
	str r12, [r1, #320]
	movw r12, #32502
	movt r12, #1651
	str r12, [r1, #324]
	movw r12, #54905
	movt r12, #2789
	str r12, [r1, #328]
	movw r12, #35218
	movt r12, #1789
	str r12, [r1, #332]
	movw r12, #36360
	movt r12, #1847
	str r12, [r1, #336]
	movw r12, #18741
	movt r12, #952
	str r12, [r1, #340]
	movw r12, #28761
	movt r12, #1461
	str r12, [r1, #344]
	movw r12, #52897
	movt r12, #2687
	str r12, [r1, #348]
	movw r12, #18485
	movt r12, #939
	str r12, [r1, #352]
	movw r12, #45436
	movt r12, #2308
	str r12, [r1, #356]
	movw r12, #47975
	movt r12, #2437
	str r12, [r1, #360]
	movw r12, #47011
	movt r12, #2388
	str r12, [r1, #364]
	movw r12, #14430
	movt r12, #733
	str r12, [r1, #368]
	movw r12, #46007
	movt r12, #2337
	str r12, [r1, #372]
	movw r12, #5275
	movt r12, #268
	str r12, [r1, #376]
	movw r12, #12618
	movt r12, #641
	str r12, [r1, #380]
	movw r12, #31183
	movt r12, #1584
	str r12, [r1, #384]
	movw r12, #45239
	movt r12, #2298
	str r12, [r1, #388]
	movw r12, #40101
	movt r12, #2037
	str r12, [r1, #392]
	movw r12, #63390
	movt r12, #3220
	str r12, [r1, #396]
	movw r12, #7382
	movt r12, #375
	str r12, [r1, #400]
	movw r12, #50180
	movt r12, #2549
	str r12, [r1, #404]
	movw r12, #41144
	movt r12, #2090
	str r12, [r1, #408]
	movw r12, #32384
	movt r12, #1645
	str r12, [r1, #412]
	movw r12, #20926
	movt r12, #1063
	str r12, [r1, #416]
	movw r12, #6279
	movt r12, #319
	str r12, [r1, #420]
	movw r12, #54590
	movt r12, #2773
	str r12, [r1, #424]
	movw r12, #14902
	movt r12, #757
	str r12, [r1, #428]
	movw r12, #41321
	movt r12, #2099
	str r12, [r1, #432]
	movw r12, #11044
	movt r12, #561
	str r12, [r1, #436]
	movw r12, #48546
	movt r12, #2466
	str r12, [r1, #440]
	movw r12, #51066
	movt r12, #2594
	str r12, [r1, #444]
	movw r12, #55200
	movt r12, #2804
	str r12, [r1, #448]
	movw r12, #21497
	movt r12, #1092
	str r12, [r1, #452]
	movw r12, #7933
	movt r12, #403
	str r12, [r1, #456]
	movw r12, #20198
	movt r12, #1026
	str r12, [r1, #460]
	movw r12, #22501
	movt r12, #1143
	str r12, [r1, #464]
	movw r12, #42325
	movt r12, #2150
	str r12, [r1, #468]
	movw r12, #54629
	movt r12, #2775
	str r12, [r1, #472]
	movw r12, #17442
	movt r12, #886
	str r12, [r1, #476]
	movw r12, #33899
	movt r12, #1722
	str r12, [r1, #480]
	movw r12, #23859
	movt r12, #1212
	str r12, [r1, #484]
	movw r12, #36892
	movt r12, #1874
	str r12, [r1, #488]
	movw r12, #20257
	movt r12, #1029
	str r12, [r1, #492]
	movw r12, #41538
	movt r12, #2110
	str r12, [r1, #496]
	movw r12, #57779
	movt r12, #2935
	str r12, [r1, #500]
	movw r12, #17422
	movt r12, #885
	str r12, [r1, #504]
	movw r12, #42404
	movt r12, #2154
	str r12, [r1, #508]
	movw r8, #62207
	movt r8, #65535
	movw r12, #3329
	add r1, r1, #508
	mov r2, #64
20:
	ldr r9, [r1, #0]
	lsr r7, r9, #16
	sub r9, r9, r7, lsl #16
	sub r1, r1, #4
	ldr r4, [r0, #0]
	ldr r5, [r0, #8]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #0]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #8]
	ldr r4, [r0, #4]
	ldr r5, [r0, #12]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #4]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #12]
	add r0, r0, #16
	subs r2, r2, #1
	bne 20b
	sub r0, r0, #1024
	mov r2, #32
21:
	ldr r9, [r1, #0]
	lsr r7, r9, #16
	sub r9, r9, r7, lsl #16
	sub r1, r1, #4
	ldr r4, [r0, #0]
	ldr r5, [r0, #16]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #0]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #16]
	ldr r4, [r0, #4]
	ldr r5, [r0, #20]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #4]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #20]
	ldr r4, [r0, #8]
	ldr r5, [r0, #24]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #8]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #24]
	ldr r4, [r0, #12]
	ldr r5, [r0, #28]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #12]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #28]
	add r0, r0, #32
	subs r2, r2, #1
	bne 21b
	sub r0, r0, #1024
	mov r2, #16
22:
	ldr r9, [r1, #0]
	lsr r7, r9, #16
	sub r9, r9, r7, lsl #16
	sub r1, r1, #4
	mov r3, #2
23:
	ldr r4, [r0, #0]
	ldr r5, [r0, #32]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #0]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #32]
	ldr r4, [r0, #4]
	ldr r5, [r0, #36]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #4]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #36]
	ldr r4, [r0, #8]
	ldr r5, [r0, #40]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #8]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #40]
	ldr r4, [r0, #12]
	ldr r5, [r0, #44]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #12]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #44]
	add r0, r0, #16
	subs r3, r3, #1
	bne 23b
	add r0, r0, #32
	subs r2, r2, #1
	bne 22b
	sub r0, r0, #1024
	mov r2, #8
24:
	ldr r9, [r1, #0]
	lsr r7, r9, #16
	sub r9, r9, r7, lsl #16
	sub r1, r1, #4
	mov r3, #4
25:
	ldr r4, [r0, #0]
	ldr r5, [r0, #64]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #0]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #64]
	ldr r4, [r0, #4]
	ldr r5, [r0, #68]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #4]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #68]
	ldr r4, [r0, #8]
	ldr r5, [r0, #72]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #8]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #72]
	ldr r4, [r0, #12]
	ldr r5, [r0, #76]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #12]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #76]
	add r0, r0, #16
	subs r3, r3, #1
	bne 25b
	add r0, r0, #64
	subs r2, r2, #1
	bne 24b
	sub r0, r0, #1024
	mov r2, #4
26:
	ldr r9, [r1, #0]
	lsr r7, r9, #16
	sub r9, r9, r7, lsl #16
	sub r1, r1, #4
	mov r3, #8
27:
	ldr r4, [r0, #0]
	ldr r5, [r0, #128]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #0]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #128]
	ldr r4, [r0, #4]
	ldr r5, [r0, #132]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #4]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #132]
	ldr r4, [r0, #8]
	ldr r5, [r0, #136]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #8]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #136]
	ldr r4, [r0, #12]
	ldr r5, [r0, #140]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #12]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #140]
	add r0, r0, #16
	subs r3, r3, #1
	bne 27b
	add r0, r0, #128
	subs r2, r2, #1
	bne 26b
	sub r0, r0, #1024
	mov r2, #2
28:
	ldr r9, [r1, #0]
	lsr r7, r9, #16
	sub r9, r9, r7, lsl #16
	sub r1, r1, #4
	mov r3, #16
29:
	ldr r4, [r0, #0]
	ldr r5, [r0, #256]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #0]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #256]
	ldr r4, [r0, #4]
	ldr r5, [r0, #260]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #4]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #260]
	ldr r4, [r0, #8]
	ldr r5, [r0, #264]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #8]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #264]
	ldr r4, [r0, #12]
	ldr r5, [r0, #268]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	lsr r4, r6, #12
	mla r6, r4, r8, r6
	str r6, [r0, #12]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	str r5, [r0, #268]
	add r0, r0, #16
	subs r3, r3, #1
	bne 29b
	add r0, r0, #256
	subs r2, r2, #1
	bne 28b
	sub r0, r0, #1024
	movw r10, #3303
	movw r11, #65024
	movw r7, #1652
	movw r9, #32521
	mov r3, #32
210:
	ldr r4, [r0, #0]
	ldr r5, [r0, #512]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	mul r4, r6, r11
	lsr r4, r4, #16
	mul r6, r6, r10
	mla r6, r4, r8, r6
	sub r6, r6, r12
	lsr r4, r6, #31
	mla r6, r4, r12, r6
	str r6, [r0, #0]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	sub r5, r5, r12
	lsr r4, r5, #31
	mla r5, r4, r12, r5
	str r5, [r0, #512]
	ldr r4, [r0, #4]
	ldr r5, [r0, #516]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	mul r4, r6, r11
	lsr r4, r4, #16
	mul r6, r6, r10
	mla r6, r4, r8, r6
	sub r6, r6, r12
	lsr r4, r6, #31
	mla r6, r4, r12, r6
	str r6, [r0, #4]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	sub r5, r5, r12
	lsr r4, r5, #31
	mla r5, r4, r12, r5
	str r5, [r0, #516]
	ldr r4, [r0, #8]
	ldr r5, [r0, #520]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	mul r4, r6, r11
	lsr r4, r4, #16
	mul r6, r6, r10
	mla r6, r4, r8, r6
	sub r6, r6, r12
	lsr r4, r6, #31
	mla r6, r4, r12, r6
	str r6, [r0, #8]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	sub r5, r5, r12
	lsr r4, r5, #31
	mla r5, r4, r12, r5
	str r5, [r0, #520]
	ldr r4, [r0, #12]
	ldr r5, [r0, #524]
	add r6, r4, r5
	add r5, r5, r12, lsl #1
	sub r5, r5, r4
	mul r4, r6, r11
	lsr r4, r4, #16
	mul r6, r6, r10
	mla r6, r4, r8, r6
	sub r6, r6, r12
	lsr r4, r6, #31
	mla r6, r4, r12, r6
	str r6, [r0, #12]
	mul r4, r5, r9
	lsr r4, r4, #16
	mul r5, r5, r7
	mla r5, r4, r8, r5
	sub r5, r5, r12
	lsr r4, r5, #31
	mla r5, r4, r12, r5
	str r5, [r0, #524]
	add r0, r0, #16
	subs r3, r3, #1
	bne 210b
	ldr r4, [r1, #508]
	ldr r5, [r1, #512]
	ldr r6, [r1, #516]
	ldr r7, [r1, #520]
	ldr r8, [r1, #524]
	ldr r9, [r1, #528]
	ldr r10, [r1, #532]
	ldr r11, [r1, #536]
	bx lr
