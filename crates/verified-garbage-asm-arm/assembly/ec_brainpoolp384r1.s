// The functions of `src/ec_brainpoolp384r1.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp384r1_public_key:
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
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1552]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1556]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1560]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1564]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1568]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1572]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1576]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1580]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1584]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1588]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1592]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1596]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1600]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1604]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1608]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1612]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1616]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1620]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1624]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1628]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1632]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1636]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1640]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1644]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1648]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1652]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1656]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1660]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1664]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1668]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1672]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1676]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1680]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1684]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1688]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1692]
	movw r4, #60499
	movt r4, #12551
	str r4, [r12, #64]
	movw r4, #19
	movt r4, #34631
	str r4, [r12, #68]
	movw r4, #6769
	movt r4, #36893
	str r4, [r12, #72]
	movw r4, #42793
	movt r4, #44243
	str r4, [r12, #76]
	movw r4, #4387
	movt r4, #32695
	str r4, [r12, #80]
	movw r4, #55833
	movt r4, #4785
	str r4, [r12, #84]
	movw r4, #22196
	movt r4, #60756
	str r4, [r12, #88]
	movw r4, #28937
	movt r4, #5423
	str r4, [r12, #92]
	movw r4, #16863
	movt r4, #20710
	str r4, [r12, #96]
	movw r4, #28542
	movt r4, #3933
	str r4, [r12, #100]
	movw r4, #27944
	movt r4, #41784
	str r4, [r12, #104]
	movw r4, #7810
	movt r4, #36025
	str r4, [r12, #108]
	movw r4, #25957
	movt r4, #59652
	str r4, [r12, #112]
	movw r4, #12802
	movt r4, #15240
	str r4, [r12, #116]
	movw r4, #49936
	movt r4, #27519
	str r4, [r12, #120]
	movw r4, #46767
	movt r4, #53050
	str r4, [r12, #124]
	movw r4, #9639
	movt r4, #44036
	str r4, [r12, #128]
	movw r4, #28268
	movt r4, #7958
	str r4, [r12, #132]
	movw r4, #22195
	movt r4, #60756
	str r4, [r12, #136]
	movw r4, #28937
	movt r4, #5423
	str r4, [r12, #140]
	movw r4, #16863
	movt r4, #20710
	str r4, [r12, #144]
	movw r4, #28542
	movt r4, #3933
	str r4, [r12, #148]
	movw r4, #27944
	movt r4, #41784
	str r4, [r12, #152]
	movw r4, #7810
	movt r4, #36025
	str r4, [r12, #156]
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
	movw r4, #0
	movt r4, #0
	str r4, [r12, #224]
	movw r4, #0
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
	movw r4, #1
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
	movw r4, #0
	movt r4, #0
	str r4, [r12, #288]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #292]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #296]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #300]
	movw r4, #5037
	movt r4, #52984
	str r4, [r12, #304]
	movw r4, #65516
	movt r4, #30904
	str r4, [r12, #308]
	movw r4, #58766
	movt r4, #28642
	str r4, [r12, #312]
	movw r4, #22742
	movt r4, #21292
	str r4, [r12, #316]
	movw r4, #61148
	movt r4, #32840
	str r4, [r12, #320]
	movw r4, #9702
	movt r4, #60750
	str r4, [r12, #324]
	movw r4, #43339
	movt r4, #4779
	str r4, [r12, #328]
	movw r4, #36598
	movt r4, #60112
	str r4, [r12, #332]
	movw r4, #48672
	movt r4, #44825
	str r4, [r12, #336]
	movw r4, #36993
	movt r4, #61602
	str r4, [r12, #340]
	movw r4, #37591
	movt r4, #23751
	str r4, [r12, #344]
	movw r4, #57725
	movt r4, #29510
	str r4, [r12, #348]
	movw r4, #15513
	movt r4, #18028
	str r4, [r12, #352]
	movw r4, #47253
	movt r4, #56102
	str r4, [r12, #356]
	movw r4, #45179
	movt r4, #61783
	str r4, [r12, #360]
	movw r4, #62462
	movt r4, #30167
	str r4, [r12, #364]
	movw r4, #3508
	movt r4, #55281
	str r4, [r12, #368]
	movw r4, #29113
	movt r4, #37735
	str r4, [r12, #372]
	movw r4, #37748
	movt r4, #13650
	str r4, [r12, #376]
	movw r4, #59877
	movt r4, #59391
	str r4, [r12, #380]
	movw r4, #3168
	movt r4, #17072
	str r4, [r12, #384]
	movw r4, #36831
	movt r4, #16394
	str r4, [r12, #388]
	movw r4, #49361
	movt r4, #41704
	str r4, [r12, #392]
	movw r4, #32801
	movt r4, #31795
	str r4, [r12, #396]
	movw r4, #47092
	movt r4, #53586
	str r4, [r12, #400]
	movw r4, #63914
	movt r4, #54730
	str r4, [r12, #404]
	movw r4, #5431
	movt r4, #53489
	str r4, [r12, #408]
	movw r4, #16430
	movt r4, #62905
	str r4, [r12, #412]
	movw r4, #15210
	movt r4, #26029
	str r4, [r12, #416]
	movw r4, #10802
	movt r4, #22123
	str r4, [r12, #420]
	movw r4, #42454
	movt r4, #3603
	str r4, [r12, #424]
	movw r4, #14190
	movt r4, #12436
	str r4, [r12, #428]
	movw r4, #11832
	movt r4, #9345
	str r4, [r12, #432]
	movw r4, #37895
	movt r4, #29244
	str r4, [r12, #436]
	movw r4, #9942
	movt r4, #5531
	str r4, [r12, #440]
	movw r4, #20078
	movt r4, #17152
	str r4, [r12, #444]
	movw r4, #64449
	movt r4, #54328
	str r4, [r12, #448]
	movw r4, #57067
	movt r4, #41353
	str r4, [r12, #452]
	movw r4, #34495
	movt r4, #54696
	str r4, [r12, #456]
	movw r4, #33000
	movt r4, #26364
	str r4, [r12, #460]
	movw r4, #12067
	movt r4, #40224
	str r4, [r12, #464]
	movw r4, #30953
	movt r4, #38083
	str r4, [r12, #468]
	movw r4, #8548
	movt r4, #63836
	str r4, [r12, #472]
	movw r4, #9806
	movt r4, #1675
	str r4, [r12, #476]
	movw r4, #153
	movt r4, #47821
	str r4, [r12, #480]
	movw r4, #3535
	movt r4, #40157
	str r4, [r12, #484]
	movw r4, #16321
	movt r4, #35061
	str r4, [r12, #488]
	movw r4, #30003
	movt r4, #34048
	str r4, [r12, #492]
	movw r4, #16549
	movt r4, #3553
	str r4, [r12, #496]
	movw r4, #45873
	movt r4, #59192
	str r4, [r12, #500]
	movw r4, #28501
	movt r4, #51097
	str r4, [r12, #504]
	movw r4, #53830
	movt r4, #62944
	str r4, [r12, #508]
	movw r4, #14332
	movt r4, #36615
	str r4, [r12, #512]
	movw r4, #2467
	movt r4, #63619
	str r4, [r12, #516]
	movw r4, #37399
	movt r4, #54641
	str r4, [r12, #520]
	movw r4, #44244
	movt r4, #41344
	str r4, [r12, #524]
	movw r4, #56758
	movt r4, #20257
	str r4, [r12, #528]
	movw r4, #9574
	movt r4, #50710
	str r4, [r12, #532]
	movw r4, #26805
	movt r4, #17801
	str r4, [r12, #536]
	movw r4, #41058
	movt r4, #11508
	str r4, [r12, #540]
	movw r4, #7310
	movt r4, #56951
	str r4, [r12, #544]
	movw r4, #54178
	movt r4, #44110
	str r4, [r12, #548]
	movw r4, #27502
	movt r4, #12075
	str r4, [r12, #552]
	movw r4, #20000
	movt r4, #14118
	str r4, [r12, #556]
	movw r4, #26762
	movt r4, #38914
	str r4, [r12, #560]
	movw r4, #32315
	movt r4, #10898
	str r4, [r12, #564]
	movw r4, #18687
	movt r4, #21207
	str r4, [r12, #568]
	movw r4, #29899
	movt r4, #22346
	str r4, [r12, #572]
	movw r4, #24539
	movt r4, #25878
	str r4, [r12, #576]
	movw r4, #28105
	movt r4, #36744
	str r4, [r12, #580]
	movw r4, #38850
	movt r4, #24910
	str r4, [r12, #584]
	movw r4, #37914
	movt r4, #3304
	str r4, [r12, #588]
	movw r4, #39579
	movt r4, #5883
	str r4, [r12, #592]
	movw r4, #52733
	movt r4, #50295
	str r4, [r12, #596]
	movw r4, #15599
	movt r4, #38016
	str r4, [r12, #600]
	movw r4, #18768
	movt r4, #12485
	str r4, [r12, #604]
	movw r4, #55896
	movt r4, #21499
	str r4, [r12, #608]
	movw r4, #37267
	movt r4, #57577
	str r4, [r12, #612]
	movw r4, #43340
	movt r4, #4779
	str r4, [r12, #616]
	movw r4, #36598
	movt r4, #60112
	str r4, [r12, #620]
	movw r4, #48672
	movt r4, #44825
	str r4, [r12, #624]
	movw r4, #36993
	movt r4, #61602
	str r4, [r12, #628]
	movw r4, #37591
	movt r4, #23751
	str r4, [r12, #632]
	movw r4, #57725
	movt r4, #29510
	str r4, [r12, #636]
	movw r4, #60497
	movt r4, #12551
	str r4, [r12, #640]
	movw r4, #19
	movt r4, #34631
	str r4, [r12, #644]
	movw r4, #6769
	movt r4, #36893
	str r4, [r12, #648]
	movw r4, #42793
	movt r4, #44243
	str r4, [r12, #652]
	movw r4, #4387
	movt r4, #32695
	str r4, [r12, #656]
	movw r4, #55833
	movt r4, #4785
	str r4, [r12, #660]
	movw r4, #22196
	movt r4, #60756
	str r4, [r12, #664]
	movw r4, #28937
	movt r4, #5423
	str r4, [r12, #668]
	movw r4, #16863
	movt r4, #20710
	str r4, [r12, #672]
	movw r4, #28542
	movt r4, #3933
	str r4, [r12, #676]
	movw r4, #27944
	movt r4, #41784
	str r4, [r12, #680]
	movw r4, #7810
	movt r4, #36025
	str r4, [r12, #684]
	movw r4, #25955
	movt r4, #59652
	str r4, [r12, #688]
	movw r4, #12802
	movt r4, #15240
	str r4, [r12, #692]
	movw r4, #49936
	movt r4, #27519
	str r4, [r12, #696]
	movw r4, #46767
	movt r4, #53050
	str r4, [r12, #700]
	movw r4, #9639
	movt r4, #44036
	str r4, [r12, #704]
	movw r4, #28268
	movt r4, #7958
	str r4, [r12, #708]
	movw r4, #22195
	movt r4, #60756
	str r4, [r12, #712]
	movw r4, #28937
	movt r4, #5423
	str r4, [r12, #716]
	movw r4, #16863
	movt r4, #20710
	str r4, [r12, #720]
	movw r4, #28542
	movt r4, #3933
	str r4, [r12, #724]
	movw r4, #27944
	movt r4, #41784
	str r4, [r12, #728]
	movw r4, #7810
	movt r4, #36025
	str r4, [r12, #732]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #736]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #740]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #744]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #748]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #752]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #756]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #760]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #764]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #768]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #772]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #776]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #780]
	movw r4, #5037
	movt r4, #52984
	str r4, [r12, #784]
	movw r4, #65516
	movt r4, #30904
	str r4, [r12, #788]
	movw r4, #58766
	movt r4, #28642
	str r4, [r12, #792]
	movw r4, #22742
	movt r4, #21292
	str r4, [r12, #796]
	movw r4, #61148
	movt r4, #32840
	str r4, [r12, #800]
	movw r4, #9702
	movt r4, #60750
	str r4, [r12, #804]
	movw r4, #43339
	movt r4, #4779
	str r4, [r12, #808]
	movw r4, #36598
	movt r4, #60112
	str r4, [r12, #812]
	movw r4, #48672
	movt r4, #44825
	str r4, [r12, #816]
	movw r4, #36993
	movt r4, #61602
	str r4, [r12, #820]
	movw r4, #37591
	movt r4, #23751
	str r4, [r12, #824]
	movw r4, #57725
	movt r4, #29510
	str r4, [r12, #828]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #832]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #836]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #840]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #844]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #848]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #852]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #856]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #860]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #864]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #868]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #872]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #876]
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #2176]
	mov r11, #48
20:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1552]
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
	mov r11, #48
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #640]
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
	bne 21b
	mov r11, #48
22:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #688]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #768]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #769]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #770]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #771]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #772]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #773]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #774]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #775]
	cmp r11, #0
	bne 22b
	ldr r4, [r12, #448]
	str r4, [r12, #3120]
	ldr r4, [r12, #452]
	str r4, [r12, #3124]
	ldr r4, [r12, #456]
	str r4, [r12, #3128]
	ldr r4, [r12, #460]
	str r4, [r12, #3132]
	ldr r4, [r12, #464]
	str r4, [r12, #3136]
	ldr r4, [r12, #468]
	str r4, [r12, #3140]
	ldr r4, [r12, #472]
	str r4, [r12, #3144]
	ldr r4, [r12, #476]
	str r4, [r12, #3148]
	ldr r4, [r12, #480]
	str r4, [r12, #3152]
	ldr r4, [r12, #484]
	str r4, [r12, #3156]
	ldr r4, [r12, #488]
	str r4, [r12, #3160]
	ldr r4, [r12, #492]
	str r4, [r12, #3164]
	ldr r4, [r12, #496]
	str r4, [r12, #3168]
	ldr r4, [r12, #500]
	str r4, [r12, #3172]
	ldr r4, [r12, #504]
	str r4, [r12, #3176]
	ldr r4, [r12, #508]
	str r4, [r12, #3180]
	ldr r4, [r12, #512]
	str r4, [r12, #3184]
	ldr r4, [r12, #516]
	str r4, [r12, #3188]
	ldr r4, [r12, #520]
	str r4, [r12, #3192]
	ldr r4, [r12, #524]
	str r4, [r12, #3196]
	ldr r4, [r12, #528]
	str r4, [r12, #3200]
	ldr r4, [r12, #532]
	str r4, [r12, #3204]
	ldr r4, [r12, #536]
	str r4, [r12, #3208]
	ldr r4, [r12, #540]
	str r4, [r12, #3212]
	ldr r4, [r12, #304]
	str r4, [r12, #3216]
	ldr r4, [r12, #308]
	str r4, [r12, #3220]
	ldr r4, [r12, #312]
	str r4, [r12, #3224]
	ldr r4, [r12, #316]
	str r4, [r12, #3228]
	ldr r4, [r12, #320]
	str r4, [r12, #3232]
	ldr r4, [r12, #324]
	str r4, [r12, #3236]
	ldr r4, [r12, #328]
	str r4, [r12, #3240]
	ldr r4, [r12, #332]
	str r4, [r12, #3244]
	ldr r4, [r12, #336]
	str r4, [r12, #3248]
	ldr r4, [r12, #340]
	str r4, [r12, #3252]
	ldr r4, [r12, #344]
	str r4, [r12, #3256]
	ldr r4, [r12, #348]
	str r4, [r12, #3260]
	ldr r4, [r12, #352]
	str r4, [r12, #3264]
	ldr r4, [r12, #356]
	str r4, [r12, #3268]
	ldr r4, [r12, #360]
	str r4, [r12, #3272]
	ldr r4, [r12, #364]
	str r4, [r12, #3276]
	ldr r4, [r12, #368]
	str r4, [r12, #3280]
	ldr r4, [r12, #372]
	str r4, [r12, #3284]
	ldr r4, [r12, #376]
	str r4, [r12, #3288]
	ldr r4, [r12, #380]
	str r4, [r12, #3292]
	ldr r4, [r12, #384]
	str r4, [r12, #3296]
	ldr r4, [r12, #388]
	str r4, [r12, #3300]
	ldr r4, [r12, #392]
	str r4, [r12, #3304]
	ldr r4, [r12, #396]
	str r4, [r12, #3308]
	ldr r4, [r12, #400]
	str r4, [r12, #3312]
	ldr r4, [r12, #404]
	str r4, [r12, #3316]
	ldr r4, [r12, #408]
	str r4, [r12, #3320]
	ldr r4, [r12, #412]
	str r4, [r12, #3324]
	ldr r4, [r12, #416]
	str r4, [r12, #3328]
	ldr r4, [r12, #420]
	str r4, [r12, #3332]
	ldr r4, [r12, #424]
	str r4, [r12, #3336]
	ldr r4, [r12, #428]
	str r4, [r12, #3340]
	ldr r4, [r12, #432]
	str r4, [r12, #3344]
	ldr r4, [r12, #436]
	str r4, [r12, #3348]
	ldr r4, [r12, #440]
	str r4, [r12, #3352]
	ldr r4, [r12, #444]
	str r4, [r12, #3356]
	mov r11, #384
23:
	sub r11, r11, #1
	ldr r4, [r12, #736]
	str r4, [r12, #2976]
	ldr r4, [r12, #740]
	str r4, [r12, #2980]
	ldr r4, [r12, #744]
	str r4, [r12, #2984]
	ldr r4, [r12, #748]
	str r4, [r12, #2988]
	ldr r4, [r12, #752]
	str r4, [r12, #2992]
	ldr r4, [r12, #756]
	str r4, [r12, #2996]
	ldr r4, [r12, #760]
	str r4, [r12, #3000]
	ldr r4, [r12, #764]
	str r4, [r12, #3004]
	ldr r4, [r12, #768]
	str r4, [r12, #3008]
	ldr r4, [r12, #772]
	str r4, [r12, #3012]
	ldr r4, [r12, #776]
	str r4, [r12, #3016]
	ldr r4, [r12, #780]
	str r4, [r12, #3020]
	ldr r4, [r12, #784]
	str r4, [r12, #3024]
	ldr r4, [r12, #788]
	str r4, [r12, #3028]
	ldr r4, [r12, #792]
	str r4, [r12, #3032]
	ldr r4, [r12, #796]
	str r4, [r12, #3036]
	ldr r4, [r12, #800]
	str r4, [r12, #3040]
	ldr r4, [r12, #804]
	str r4, [r12, #3044]
	ldr r4, [r12, #808]
	str r4, [r12, #3048]
	ldr r4, [r12, #812]
	str r4, [r12, #3052]
	ldr r4, [r12, #816]
	str r4, [r12, #3056]
	ldr r4, [r12, #820]
	str r4, [r12, #3060]
	ldr r4, [r12, #824]
	str r4, [r12, #3064]
	ldr r4, [r12, #828]
	str r4, [r12, #3068]
	ldr r4, [r12, #832]
	str r4, [r12, #3072]
	ldr r4, [r12, #836]
	str r4, [r12, #3076]
	ldr r4, [r12, #840]
	str r4, [r12, #3080]
	ldr r4, [r12, #844]
	str r4, [r12, #3084]
	ldr r4, [r12, #848]
	str r4, [r12, #3088]
	ldr r4, [r12, #852]
	str r4, [r12, #3092]
	ldr r4, [r12, #856]
	str r4, [r12, #3096]
	ldr r4, [r12, #860]
	str r4, [r12, #3100]
	ldr r4, [r12, #864]
	str r4, [r12, #3104]
	ldr r4, [r12, #868]
	str r4, [r12, #3108]
	ldr r4, [r12, #872]
	str r4, [r12, #3112]
	ldr r4, [r12, #876]
	str r4, [r12, #3116]
	mov r10, lr
	mov r0, r12
	bl {vg_brainpoolp384r1_point_double}
	mov lr, r10
	ldr r4, [r12, #2832]
	str r4, [r12, #2976]
	ldr r4, [r12, #2836]
	str r4, [r12, #2980]
	ldr r4, [r12, #2840]
	str r4, [r12, #2984]
	ldr r4, [r12, #2844]
	str r4, [r12, #2988]
	ldr r4, [r12, #2848]
	str r4, [r12, #2992]
	ldr r4, [r12, #2852]
	str r4, [r12, #2996]
	ldr r4, [r12, #2856]
	str r4, [r12, #3000]
	ldr r4, [r12, #2860]
	str r4, [r12, #3004]
	ldr r4, [r12, #2864]
	str r4, [r12, #3008]
	ldr r4, [r12, #2868]
	str r4, [r12, #3012]
	ldr r4, [r12, #2872]
	str r4, [r12, #3016]
	ldr r4, [r12, #2876]
	str r4, [r12, #3020]
	ldr r4, [r12, #2880]
	str r4, [r12, #3024]
	ldr r4, [r12, #2884]
	str r4, [r12, #3028]
	ldr r4, [r12, #2888]
	str r4, [r12, #3032]
	ldr r4, [r12, #2892]
	str r4, [r12, #3036]
	ldr r4, [r12, #2896]
	str r4, [r12, #3040]
	ldr r4, [r12, #2900]
	str r4, [r12, #3044]
	ldr r4, [r12, #2904]
	str r4, [r12, #3048]
	ldr r4, [r12, #2908]
	str r4, [r12, #3052]
	ldr r4, [r12, #2912]
	str r4, [r12, #3056]
	ldr r4, [r12, #2916]
	str r4, [r12, #3060]
	ldr r4, [r12, #2920]
	str r4, [r12, #3064]
	ldr r4, [r12, #2924]
	str r4, [r12, #3068]
	ldr r4, [r12, #2928]
	str r4, [r12, #3072]
	ldr r4, [r12, #2932]
	str r4, [r12, #3076]
	ldr r4, [r12, #2936]
	str r4, [r12, #3080]
	ldr r4, [r12, #2940]
	str r4, [r12, #3084]
	ldr r4, [r12, #2944]
	str r4, [r12, #3088]
	ldr r4, [r12, #2948]
	str r4, [r12, #3092]
	ldr r4, [r12, #2952]
	str r4, [r12, #3096]
	ldr r4, [r12, #2956]
	str r4, [r12, #3100]
	ldr r4, [r12, #2960]
	str r4, [r12, #3104]
	ldr r4, [r12, #2964]
	str r4, [r12, #3108]
	ldr r4, [r12, #2968]
	str r4, [r12, #3112]
	ldr r4, [r12, #2972]
	str r4, [r12, #3116]
	mov r10, lr
	mov r0, r12
	bl {vg_brainpoolp384r1_point_add}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #0]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #2976]
	ldr r5, [r12, #2832]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #736]
	ldr r4, [r12, #2980]
	ldr r5, [r12, #2836]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #740]
	ldr r4, [r12, #2984]
	ldr r5, [r12, #2840]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #744]
	ldr r4, [r12, #2988]
	ldr r5, [r12, #2844]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #748]
	ldr r4, [r12, #2992]
	ldr r5, [r12, #2848]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #752]
	ldr r4, [r12, #2996]
	ldr r5, [r12, #2852]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #756]
	ldr r4, [r12, #3000]
	ldr r5, [r12, #2856]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #760]
	ldr r4, [r12, #3004]
	ldr r5, [r12, #2860]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #764]
	ldr r4, [r12, #3008]
	ldr r5, [r12, #2864]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #768]
	ldr r4, [r12, #3012]
	ldr r5, [r12, #2868]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #772]
	ldr r4, [r12, #3016]
	ldr r5, [r12, #2872]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #776]
	ldr r4, [r12, #3020]
	ldr r5, [r12, #2876]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #780]
	ldr r4, [r12, #3024]
	ldr r5, [r12, #2880]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #784]
	ldr r4, [r12, #3028]
	ldr r5, [r12, #2884]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #788]
	ldr r4, [r12, #3032]
	ldr r5, [r12, #2888]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #792]
	ldr r4, [r12, #3036]
	ldr r5, [r12, #2892]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #796]
	ldr r4, [r12, #3040]
	ldr r5, [r12, #2896]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #800]
	ldr r4, [r12, #3044]
	ldr r5, [r12, #2900]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #804]
	ldr r4, [r12, #3048]
	ldr r5, [r12, #2904]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #808]
	ldr r4, [r12, #3052]
	ldr r5, [r12, #2908]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #812]
	ldr r4, [r12, #3056]
	ldr r5, [r12, #2912]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #816]
	ldr r4, [r12, #3060]
	ldr r5, [r12, #2916]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #820]
	ldr r4, [r12, #3064]
	ldr r5, [r12, #2920]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #824]
	ldr r4, [r12, #3068]
	ldr r5, [r12, #2924]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #828]
	ldr r4, [r12, #3072]
	ldr r5, [r12, #2928]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #832]
	ldr r4, [r12, #3076]
	ldr r5, [r12, #2932]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #836]
	ldr r4, [r12, #3080]
	ldr r5, [r12, #2936]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #840]
	ldr r4, [r12, #3084]
	ldr r5, [r12, #2940]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #844]
	ldr r4, [r12, #3088]
	ldr r5, [r12, #2944]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #848]
	ldr r4, [r12, #3092]
	ldr r5, [r12, #2948]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #852]
	ldr r4, [r12, #3096]
	ldr r5, [r12, #2952]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #856]
	ldr r4, [r12, #3100]
	ldr r5, [r12, #2956]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #860]
	ldr r4, [r12, #3104]
	ldr r5, [r12, #2960]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #864]
	ldr r4, [r12, #3108]
	ldr r5, [r12, #2964]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #868]
	ldr r4, [r12, #3112]
	ldr r5, [r12, #2968]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #872]
	ldr r4, [r12, #3116]
	ldr r5, [r12, #2972]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #876]
	cmp r11, #0
	bne 23b
	ldr r4, [r12, #304]
	str r4, [r12, #1456]
	ldr r4, [r12, #308]
	str r4, [r12, #1460]
	ldr r4, [r12, #312]
	str r4, [r12, #1464]
	ldr r4, [r12, #316]
	str r4, [r12, #1468]
	ldr r4, [r12, #320]
	str r4, [r12, #1472]
	ldr r4, [r12, #324]
	str r4, [r12, #1476]
	ldr r4, [r12, #328]
	str r4, [r12, #1480]
	ldr r4, [r12, #332]
	str r4, [r12, #1484]
	ldr r4, [r12, #336]
	str r4, [r12, #1488]
	ldr r4, [r12, #340]
	str r4, [r12, #1492]
	ldr r4, [r12, #344]
	str r4, [r12, #1496]
	ldr r4, [r12, #348]
	str r4, [r12, #1500]
	mov r11, #384
24:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1456
	movw r2, #1456
	movw r3, #1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1504
	movw r2, #1456
	movw r3, #832
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #384]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #1456]
	ldr r5, [r12, #1504]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1456]
	ldr r4, [r12, #1460]
	ldr r5, [r12, #1508]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1460]
	ldr r4, [r12, #1464]
	ldr r5, [r12, #1512]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1464]
	ldr r4, [r12, #1468]
	ldr r5, [r12, #1516]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1468]
	ldr r4, [r12, #1472]
	ldr r5, [r12, #1520]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1472]
	ldr r4, [r12, #1476]
	ldr r5, [r12, #1524]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1476]
	ldr r4, [r12, #1480]
	ldr r5, [r12, #1528]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1480]
	ldr r4, [r12, #1484]
	ldr r5, [r12, #1532]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1484]
	ldr r4, [r12, #1488]
	ldr r5, [r12, #1536]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1488]
	ldr r4, [r12, #1492]
	ldr r5, [r12, #1540]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1492]
	ldr r4, [r12, #1496]
	ldr r5, [r12, #1544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1496]
	ldr r4, [r12, #1500]
	ldr r5, [r12, #1548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1500]
	cmp r11, #0
	bne 24b
	mov r10, lr
	mov r0, r12
	movw r1, #1696
	movw r2, #736
	movw r3, #1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1696
	movw r3, #256
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #784
	movw r3, #1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2128
	movw r2, #1888
	movw r3, #256
	bl {vg_brainpoolp384r1_mul_mod_p}
	mov lr, r10
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1600]
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
	ldr r7, [r12, #1604]
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
	ldr r7, [r12, #1608]
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
	ldr r7, [r12, #1612]
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
	ldr r7, [r12, #1616]
	ldr r8, [r12, #128]
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
	ldr r7, [r12, #1620]
	ldr r8, [r12, #132]
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
	ldr r7, [r12, #1624]
	ldr r8, [r12, #136]
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
	ldr r7, [r12, #1628]
	ldr r8, [r12, #140]
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
	ldr r7, [r12, #1632]
	ldr r8, [r12, #144]
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
	ldr r7, [r12, #1636]
	ldr r8, [r12, #148]
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
	ldr r7, [r12, #1640]
	ldr r8, [r12, #152]
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
	ldr r7, [r12, #1644]
	ldr r8, [r12, #156]
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
	ldr r5, [r12, #1600]
	ldr r4, [r12, #1604]
	orr r5, r5, r4
	ldr r4, [r12, #1608]
	orr r5, r5, r4
	ldr r4, [r12, #1612]
	orr r5, r5, r4
	ldr r4, [r12, #1616]
	orr r5, r5, r4
	ldr r4, [r12, #1620]
	orr r5, r5, r4
	ldr r4, [r12, #1624]
	orr r5, r5, r4
	ldr r4, [r12, #1628]
	orr r5, r5, r4
	ldr r4, [r12, #1632]
	orr r5, r5, r4
	ldr r4, [r12, #1636]
	orr r5, r5, r4
	ldr r4, [r12, #1640]
	orr r5, r5, r4
	ldr r4, [r12, #1644]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r5, [r12, #832]
	ldr r4, [r12, #836]
	orr r5, r5, r4
	ldr r4, [r12, #840]
	orr r5, r5, r4
	ldr r4, [r12, #844]
	orr r5, r5, r4
	ldr r4, [r12, #848]
	orr r5, r5, r4
	ldr r4, [r12, #852]
	orr r5, r5, r4
	ldr r4, [r12, #856]
	orr r5, r5, r4
	ldr r4, [r12, #860]
	orr r5, r5, r4
	ldr r4, [r12, #864]
	orr r5, r5, r4
	ldr r4, [r12, #868]
	orr r5, r5, r4
	ldr r4, [r12, #872]
	orr r5, r5, r4
	ldr r4, [r12, #876]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r10, [r12, #2176]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1744]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1748]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #1752]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1756]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1760]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1764]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1768]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1772]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1776]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1780]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1784]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1788]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #2128]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #93]
	ldr r4, [r12, #2132]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #89]
	ldr r4, [r12, #2136]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #85]
	ldr r4, [r12, #2140]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #81]
	ldr r4, [r12, #2144]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #2148]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #2152]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #2156]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #65]
	ldr r4, [r12, #2160]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #2164]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #2168]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #2172]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
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

vg_ec_brainpoolp384r1_public_key_umaal:
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
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1552]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1556]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1560]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1564]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1568]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1572]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1576]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1580]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1584]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1588]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1592]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1596]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1600]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1604]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1608]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1612]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1616]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1620]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1624]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1628]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1632]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1636]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1640]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1644]
	ldr r4, [r1, #44]
	rev r4, r4
	str r4, [r12, #1648]
	ldr r4, [r1, #40]
	rev r4, r4
	str r4, [r12, #1652]
	ldr r4, [r1, #36]
	rev r4, r4
	str r4, [r12, #1656]
	ldr r4, [r1, #32]
	rev r4, r4
	str r4, [r12, #1660]
	ldr r4, [r1, #28]
	rev r4, r4
	str r4, [r12, #1664]
	ldr r4, [r1, #24]
	rev r4, r4
	str r4, [r12, #1668]
	ldr r4, [r1, #20]
	rev r4, r4
	str r4, [r12, #1672]
	ldr r4, [r1, #16]
	rev r4, r4
	str r4, [r12, #1676]
	ldr r4, [r1, #12]
	rev r4, r4
	str r4, [r12, #1680]
	ldr r4, [r1, #8]
	rev r4, r4
	str r4, [r12, #1684]
	ldr r4, [r1, #4]
	rev r4, r4
	str r4, [r12, #1688]
	ldr r4, [r1, #0]
	rev r4, r4
	str r4, [r12, #1692]
	movw r4, #60499
	movt r4, #12551
	str r4, [r12, #64]
	movw r4, #19
	movt r4, #34631
	str r4, [r12, #68]
	movw r4, #6769
	movt r4, #36893
	str r4, [r12, #72]
	movw r4, #42793
	movt r4, #44243
	str r4, [r12, #76]
	movw r4, #4387
	movt r4, #32695
	str r4, [r12, #80]
	movw r4, #55833
	movt r4, #4785
	str r4, [r12, #84]
	movw r4, #22196
	movt r4, #60756
	str r4, [r12, #88]
	movw r4, #28937
	movt r4, #5423
	str r4, [r12, #92]
	movw r4, #16863
	movt r4, #20710
	str r4, [r12, #96]
	movw r4, #28542
	movt r4, #3933
	str r4, [r12, #100]
	movw r4, #27944
	movt r4, #41784
	str r4, [r12, #104]
	movw r4, #7810
	movt r4, #36025
	str r4, [r12, #108]
	movw r4, #25957
	movt r4, #59652
	str r4, [r12, #112]
	movw r4, #12802
	movt r4, #15240
	str r4, [r12, #116]
	movw r4, #49936
	movt r4, #27519
	str r4, [r12, #120]
	movw r4, #46767
	movt r4, #53050
	str r4, [r12, #124]
	movw r4, #9639
	movt r4, #44036
	str r4, [r12, #128]
	movw r4, #28268
	movt r4, #7958
	str r4, [r12, #132]
	movw r4, #22195
	movt r4, #60756
	str r4, [r12, #136]
	movw r4, #28937
	movt r4, #5423
	str r4, [r12, #140]
	movw r4, #16863
	movt r4, #20710
	str r4, [r12, #144]
	movw r4, #28542
	movt r4, #3933
	str r4, [r12, #148]
	movw r4, #27944
	movt r4, #41784
	str r4, [r12, #152]
	movw r4, #7810
	movt r4, #36025
	str r4, [r12, #156]
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
	movw r4, #0
	movt r4, #0
	str r4, [r12, #224]
	movw r4, #0
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
	movw r4, #1
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
	movw r4, #0
	movt r4, #0
	str r4, [r12, #288]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #292]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #296]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #300]
	movw r4, #5037
	movt r4, #52984
	str r4, [r12, #304]
	movw r4, #65516
	movt r4, #30904
	str r4, [r12, #308]
	movw r4, #58766
	movt r4, #28642
	str r4, [r12, #312]
	movw r4, #22742
	movt r4, #21292
	str r4, [r12, #316]
	movw r4, #61148
	movt r4, #32840
	str r4, [r12, #320]
	movw r4, #9702
	movt r4, #60750
	str r4, [r12, #324]
	movw r4, #43339
	movt r4, #4779
	str r4, [r12, #328]
	movw r4, #36598
	movt r4, #60112
	str r4, [r12, #332]
	movw r4, #48672
	movt r4, #44825
	str r4, [r12, #336]
	movw r4, #36993
	movt r4, #61602
	str r4, [r12, #340]
	movw r4, #37591
	movt r4, #23751
	str r4, [r12, #344]
	movw r4, #57725
	movt r4, #29510
	str r4, [r12, #348]
	movw r4, #15513
	movt r4, #18028
	str r4, [r12, #352]
	movw r4, #47253
	movt r4, #56102
	str r4, [r12, #356]
	movw r4, #45179
	movt r4, #61783
	str r4, [r12, #360]
	movw r4, #62462
	movt r4, #30167
	str r4, [r12, #364]
	movw r4, #3508
	movt r4, #55281
	str r4, [r12, #368]
	movw r4, #29113
	movt r4, #37735
	str r4, [r12, #372]
	movw r4, #37748
	movt r4, #13650
	str r4, [r12, #376]
	movw r4, #59877
	movt r4, #59391
	str r4, [r12, #380]
	movw r4, #3168
	movt r4, #17072
	str r4, [r12, #384]
	movw r4, #36831
	movt r4, #16394
	str r4, [r12, #388]
	movw r4, #49361
	movt r4, #41704
	str r4, [r12, #392]
	movw r4, #32801
	movt r4, #31795
	str r4, [r12, #396]
	movw r4, #47092
	movt r4, #53586
	str r4, [r12, #400]
	movw r4, #63914
	movt r4, #54730
	str r4, [r12, #404]
	movw r4, #5431
	movt r4, #53489
	str r4, [r12, #408]
	movw r4, #16430
	movt r4, #62905
	str r4, [r12, #412]
	movw r4, #15210
	movt r4, #26029
	str r4, [r12, #416]
	movw r4, #10802
	movt r4, #22123
	str r4, [r12, #420]
	movw r4, #42454
	movt r4, #3603
	str r4, [r12, #424]
	movw r4, #14190
	movt r4, #12436
	str r4, [r12, #428]
	movw r4, #11832
	movt r4, #9345
	str r4, [r12, #432]
	movw r4, #37895
	movt r4, #29244
	str r4, [r12, #436]
	movw r4, #9942
	movt r4, #5531
	str r4, [r12, #440]
	movw r4, #20078
	movt r4, #17152
	str r4, [r12, #444]
	movw r4, #64449
	movt r4, #54328
	str r4, [r12, #448]
	movw r4, #57067
	movt r4, #41353
	str r4, [r12, #452]
	movw r4, #34495
	movt r4, #54696
	str r4, [r12, #456]
	movw r4, #33000
	movt r4, #26364
	str r4, [r12, #460]
	movw r4, #12067
	movt r4, #40224
	str r4, [r12, #464]
	movw r4, #30953
	movt r4, #38083
	str r4, [r12, #468]
	movw r4, #8548
	movt r4, #63836
	str r4, [r12, #472]
	movw r4, #9806
	movt r4, #1675
	str r4, [r12, #476]
	movw r4, #153
	movt r4, #47821
	str r4, [r12, #480]
	movw r4, #3535
	movt r4, #40157
	str r4, [r12, #484]
	movw r4, #16321
	movt r4, #35061
	str r4, [r12, #488]
	movw r4, #30003
	movt r4, #34048
	str r4, [r12, #492]
	movw r4, #16549
	movt r4, #3553
	str r4, [r12, #496]
	movw r4, #45873
	movt r4, #59192
	str r4, [r12, #500]
	movw r4, #28501
	movt r4, #51097
	str r4, [r12, #504]
	movw r4, #53830
	movt r4, #62944
	str r4, [r12, #508]
	movw r4, #14332
	movt r4, #36615
	str r4, [r12, #512]
	movw r4, #2467
	movt r4, #63619
	str r4, [r12, #516]
	movw r4, #37399
	movt r4, #54641
	str r4, [r12, #520]
	movw r4, #44244
	movt r4, #41344
	str r4, [r12, #524]
	movw r4, #56758
	movt r4, #20257
	str r4, [r12, #528]
	movw r4, #9574
	movt r4, #50710
	str r4, [r12, #532]
	movw r4, #26805
	movt r4, #17801
	str r4, [r12, #536]
	movw r4, #41058
	movt r4, #11508
	str r4, [r12, #540]
	movw r4, #7310
	movt r4, #56951
	str r4, [r12, #544]
	movw r4, #54178
	movt r4, #44110
	str r4, [r12, #548]
	movw r4, #27502
	movt r4, #12075
	str r4, [r12, #552]
	movw r4, #20000
	movt r4, #14118
	str r4, [r12, #556]
	movw r4, #26762
	movt r4, #38914
	str r4, [r12, #560]
	movw r4, #32315
	movt r4, #10898
	str r4, [r12, #564]
	movw r4, #18687
	movt r4, #21207
	str r4, [r12, #568]
	movw r4, #29899
	movt r4, #22346
	str r4, [r12, #572]
	movw r4, #24539
	movt r4, #25878
	str r4, [r12, #576]
	movw r4, #28105
	movt r4, #36744
	str r4, [r12, #580]
	movw r4, #38850
	movt r4, #24910
	str r4, [r12, #584]
	movw r4, #37914
	movt r4, #3304
	str r4, [r12, #588]
	movw r4, #39579
	movt r4, #5883
	str r4, [r12, #592]
	movw r4, #52733
	movt r4, #50295
	str r4, [r12, #596]
	movw r4, #15599
	movt r4, #38016
	str r4, [r12, #600]
	movw r4, #18768
	movt r4, #12485
	str r4, [r12, #604]
	movw r4, #55896
	movt r4, #21499
	str r4, [r12, #608]
	movw r4, #37267
	movt r4, #57577
	str r4, [r12, #612]
	movw r4, #43340
	movt r4, #4779
	str r4, [r12, #616]
	movw r4, #36598
	movt r4, #60112
	str r4, [r12, #620]
	movw r4, #48672
	movt r4, #44825
	str r4, [r12, #624]
	movw r4, #36993
	movt r4, #61602
	str r4, [r12, #628]
	movw r4, #37591
	movt r4, #23751
	str r4, [r12, #632]
	movw r4, #57725
	movt r4, #29510
	str r4, [r12, #636]
	movw r4, #60497
	movt r4, #12551
	str r4, [r12, #640]
	movw r4, #19
	movt r4, #34631
	str r4, [r12, #644]
	movw r4, #6769
	movt r4, #36893
	str r4, [r12, #648]
	movw r4, #42793
	movt r4, #44243
	str r4, [r12, #652]
	movw r4, #4387
	movt r4, #32695
	str r4, [r12, #656]
	movw r4, #55833
	movt r4, #4785
	str r4, [r12, #660]
	movw r4, #22196
	movt r4, #60756
	str r4, [r12, #664]
	movw r4, #28937
	movt r4, #5423
	str r4, [r12, #668]
	movw r4, #16863
	movt r4, #20710
	str r4, [r12, #672]
	movw r4, #28542
	movt r4, #3933
	str r4, [r12, #676]
	movw r4, #27944
	movt r4, #41784
	str r4, [r12, #680]
	movw r4, #7810
	movt r4, #36025
	str r4, [r12, #684]
	movw r4, #25955
	movt r4, #59652
	str r4, [r12, #688]
	movw r4, #12802
	movt r4, #15240
	str r4, [r12, #692]
	movw r4, #49936
	movt r4, #27519
	str r4, [r12, #696]
	movw r4, #46767
	movt r4, #53050
	str r4, [r12, #700]
	movw r4, #9639
	movt r4, #44036
	str r4, [r12, #704]
	movw r4, #28268
	movt r4, #7958
	str r4, [r12, #708]
	movw r4, #22195
	movt r4, #60756
	str r4, [r12, #712]
	movw r4, #28937
	movt r4, #5423
	str r4, [r12, #716]
	movw r4, #16863
	movt r4, #20710
	str r4, [r12, #720]
	movw r4, #28542
	movt r4, #3933
	str r4, [r12, #724]
	movw r4, #27944
	movt r4, #41784
	str r4, [r12, #728]
	movw r4, #7810
	movt r4, #36025
	str r4, [r12, #732]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #736]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #740]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #744]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #748]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #752]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #756]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #760]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #764]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #768]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #772]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #776]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #780]
	movw r4, #5037
	movt r4, #52984
	str r4, [r12, #784]
	movw r4, #65516
	movt r4, #30904
	str r4, [r12, #788]
	movw r4, #58766
	movt r4, #28642
	str r4, [r12, #792]
	movw r4, #22742
	movt r4, #21292
	str r4, [r12, #796]
	movw r4, #61148
	movt r4, #32840
	str r4, [r12, #800]
	movw r4, #9702
	movt r4, #60750
	str r4, [r12, #804]
	movw r4, #43339
	movt r4, #4779
	str r4, [r12, #808]
	movw r4, #36598
	movt r4, #60112
	str r4, [r12, #812]
	movw r4, #48672
	movt r4, #44825
	str r4, [r12, #816]
	movw r4, #36993
	movt r4, #61602
	str r4, [r12, #820]
	movw r4, #37591
	movt r4, #23751
	str r4, [r12, #824]
	movw r4, #57725
	movt r4, #29510
	str r4, [r12, #828]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #832]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #836]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #840]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #844]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #848]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #852]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #856]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #860]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #864]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #868]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #872]
	movw r4, #0
	movt r4, #0
	str r4, [r12, #876]
	mov r4, #0
	sub r4, r4, #1
	str r4, [r12, #2176]
	mov r11, #48
20:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #1552]
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
	mov r11, #48
21:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #640]
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
	bne 21b
	mov r11, #48
22:
	sub r11, r11, #1
	add r4, r12, r11
	ldrb r4, [r4, #688]
	add r5, r12, r11, lsl #3
	add r5, r5, #4096
	and r7, r4, #1
	strb r7, [r5, #768]
	lsr r7, r4, #1
	and r7, r7, #1
	strb r7, [r5, #769]
	lsr r7, r4, #2
	and r7, r7, #1
	strb r7, [r5, #770]
	lsr r7, r4, #3
	and r7, r7, #1
	strb r7, [r5, #771]
	lsr r7, r4, #4
	and r7, r7, #1
	strb r7, [r5, #772]
	lsr r7, r4, #5
	and r7, r7, #1
	strb r7, [r5, #773]
	lsr r7, r4, #6
	and r7, r7, #1
	strb r7, [r5, #774]
	lsr r7, r4, #7
	and r7, r7, #1
	strb r7, [r5, #775]
	cmp r11, #0
	bne 22b
	ldr r4, [r12, #448]
	str r4, [r12, #3120]
	ldr r4, [r12, #452]
	str r4, [r12, #3124]
	ldr r4, [r12, #456]
	str r4, [r12, #3128]
	ldr r4, [r12, #460]
	str r4, [r12, #3132]
	ldr r4, [r12, #464]
	str r4, [r12, #3136]
	ldr r4, [r12, #468]
	str r4, [r12, #3140]
	ldr r4, [r12, #472]
	str r4, [r12, #3144]
	ldr r4, [r12, #476]
	str r4, [r12, #3148]
	ldr r4, [r12, #480]
	str r4, [r12, #3152]
	ldr r4, [r12, #484]
	str r4, [r12, #3156]
	ldr r4, [r12, #488]
	str r4, [r12, #3160]
	ldr r4, [r12, #492]
	str r4, [r12, #3164]
	ldr r4, [r12, #496]
	str r4, [r12, #3168]
	ldr r4, [r12, #500]
	str r4, [r12, #3172]
	ldr r4, [r12, #504]
	str r4, [r12, #3176]
	ldr r4, [r12, #508]
	str r4, [r12, #3180]
	ldr r4, [r12, #512]
	str r4, [r12, #3184]
	ldr r4, [r12, #516]
	str r4, [r12, #3188]
	ldr r4, [r12, #520]
	str r4, [r12, #3192]
	ldr r4, [r12, #524]
	str r4, [r12, #3196]
	ldr r4, [r12, #528]
	str r4, [r12, #3200]
	ldr r4, [r12, #532]
	str r4, [r12, #3204]
	ldr r4, [r12, #536]
	str r4, [r12, #3208]
	ldr r4, [r12, #540]
	str r4, [r12, #3212]
	ldr r4, [r12, #304]
	str r4, [r12, #3216]
	ldr r4, [r12, #308]
	str r4, [r12, #3220]
	ldr r4, [r12, #312]
	str r4, [r12, #3224]
	ldr r4, [r12, #316]
	str r4, [r12, #3228]
	ldr r4, [r12, #320]
	str r4, [r12, #3232]
	ldr r4, [r12, #324]
	str r4, [r12, #3236]
	ldr r4, [r12, #328]
	str r4, [r12, #3240]
	ldr r4, [r12, #332]
	str r4, [r12, #3244]
	ldr r4, [r12, #336]
	str r4, [r12, #3248]
	ldr r4, [r12, #340]
	str r4, [r12, #3252]
	ldr r4, [r12, #344]
	str r4, [r12, #3256]
	ldr r4, [r12, #348]
	str r4, [r12, #3260]
	ldr r4, [r12, #352]
	str r4, [r12, #3264]
	ldr r4, [r12, #356]
	str r4, [r12, #3268]
	ldr r4, [r12, #360]
	str r4, [r12, #3272]
	ldr r4, [r12, #364]
	str r4, [r12, #3276]
	ldr r4, [r12, #368]
	str r4, [r12, #3280]
	ldr r4, [r12, #372]
	str r4, [r12, #3284]
	ldr r4, [r12, #376]
	str r4, [r12, #3288]
	ldr r4, [r12, #380]
	str r4, [r12, #3292]
	ldr r4, [r12, #384]
	str r4, [r12, #3296]
	ldr r4, [r12, #388]
	str r4, [r12, #3300]
	ldr r4, [r12, #392]
	str r4, [r12, #3304]
	ldr r4, [r12, #396]
	str r4, [r12, #3308]
	ldr r4, [r12, #400]
	str r4, [r12, #3312]
	ldr r4, [r12, #404]
	str r4, [r12, #3316]
	ldr r4, [r12, #408]
	str r4, [r12, #3320]
	ldr r4, [r12, #412]
	str r4, [r12, #3324]
	ldr r4, [r12, #416]
	str r4, [r12, #3328]
	ldr r4, [r12, #420]
	str r4, [r12, #3332]
	ldr r4, [r12, #424]
	str r4, [r12, #3336]
	ldr r4, [r12, #428]
	str r4, [r12, #3340]
	ldr r4, [r12, #432]
	str r4, [r12, #3344]
	ldr r4, [r12, #436]
	str r4, [r12, #3348]
	ldr r4, [r12, #440]
	str r4, [r12, #3352]
	ldr r4, [r12, #444]
	str r4, [r12, #3356]
	mov r11, #384
23:
	sub r11, r11, #1
	ldr r4, [r12, #736]
	str r4, [r12, #2976]
	ldr r4, [r12, #740]
	str r4, [r12, #2980]
	ldr r4, [r12, #744]
	str r4, [r12, #2984]
	ldr r4, [r12, #748]
	str r4, [r12, #2988]
	ldr r4, [r12, #752]
	str r4, [r12, #2992]
	ldr r4, [r12, #756]
	str r4, [r12, #2996]
	ldr r4, [r12, #760]
	str r4, [r12, #3000]
	ldr r4, [r12, #764]
	str r4, [r12, #3004]
	ldr r4, [r12, #768]
	str r4, [r12, #3008]
	ldr r4, [r12, #772]
	str r4, [r12, #3012]
	ldr r4, [r12, #776]
	str r4, [r12, #3016]
	ldr r4, [r12, #780]
	str r4, [r12, #3020]
	ldr r4, [r12, #784]
	str r4, [r12, #3024]
	ldr r4, [r12, #788]
	str r4, [r12, #3028]
	ldr r4, [r12, #792]
	str r4, [r12, #3032]
	ldr r4, [r12, #796]
	str r4, [r12, #3036]
	ldr r4, [r12, #800]
	str r4, [r12, #3040]
	ldr r4, [r12, #804]
	str r4, [r12, #3044]
	ldr r4, [r12, #808]
	str r4, [r12, #3048]
	ldr r4, [r12, #812]
	str r4, [r12, #3052]
	ldr r4, [r12, #816]
	str r4, [r12, #3056]
	ldr r4, [r12, #820]
	str r4, [r12, #3060]
	ldr r4, [r12, #824]
	str r4, [r12, #3064]
	ldr r4, [r12, #828]
	str r4, [r12, #3068]
	ldr r4, [r12, #832]
	str r4, [r12, #3072]
	ldr r4, [r12, #836]
	str r4, [r12, #3076]
	ldr r4, [r12, #840]
	str r4, [r12, #3080]
	ldr r4, [r12, #844]
	str r4, [r12, #3084]
	ldr r4, [r12, #848]
	str r4, [r12, #3088]
	ldr r4, [r12, #852]
	str r4, [r12, #3092]
	ldr r4, [r12, #856]
	str r4, [r12, #3096]
	ldr r4, [r12, #860]
	str r4, [r12, #3100]
	ldr r4, [r12, #864]
	str r4, [r12, #3104]
	ldr r4, [r12, #868]
	str r4, [r12, #3108]
	ldr r4, [r12, #872]
	str r4, [r12, #3112]
	ldr r4, [r12, #876]
	str r4, [r12, #3116]
	mov r10, lr
	mov r0, r12
	bl {vg_brainpoolp384r1_point_double_umaal}
	mov lr, r10
	ldr r4, [r12, #2832]
	str r4, [r12, #2976]
	ldr r4, [r12, #2836]
	str r4, [r12, #2980]
	ldr r4, [r12, #2840]
	str r4, [r12, #2984]
	ldr r4, [r12, #2844]
	str r4, [r12, #2988]
	ldr r4, [r12, #2848]
	str r4, [r12, #2992]
	ldr r4, [r12, #2852]
	str r4, [r12, #2996]
	ldr r4, [r12, #2856]
	str r4, [r12, #3000]
	ldr r4, [r12, #2860]
	str r4, [r12, #3004]
	ldr r4, [r12, #2864]
	str r4, [r12, #3008]
	ldr r4, [r12, #2868]
	str r4, [r12, #3012]
	ldr r4, [r12, #2872]
	str r4, [r12, #3016]
	ldr r4, [r12, #2876]
	str r4, [r12, #3020]
	ldr r4, [r12, #2880]
	str r4, [r12, #3024]
	ldr r4, [r12, #2884]
	str r4, [r12, #3028]
	ldr r4, [r12, #2888]
	str r4, [r12, #3032]
	ldr r4, [r12, #2892]
	str r4, [r12, #3036]
	ldr r4, [r12, #2896]
	str r4, [r12, #3040]
	ldr r4, [r12, #2900]
	str r4, [r12, #3044]
	ldr r4, [r12, #2904]
	str r4, [r12, #3048]
	ldr r4, [r12, #2908]
	str r4, [r12, #3052]
	ldr r4, [r12, #2912]
	str r4, [r12, #3056]
	ldr r4, [r12, #2916]
	str r4, [r12, #3060]
	ldr r4, [r12, #2920]
	str r4, [r12, #3064]
	ldr r4, [r12, #2924]
	str r4, [r12, #3068]
	ldr r4, [r12, #2928]
	str r4, [r12, #3072]
	ldr r4, [r12, #2932]
	str r4, [r12, #3076]
	ldr r4, [r12, #2936]
	str r4, [r12, #3080]
	ldr r4, [r12, #2940]
	str r4, [r12, #3084]
	ldr r4, [r12, #2944]
	str r4, [r12, #3088]
	ldr r4, [r12, #2948]
	str r4, [r12, #3092]
	ldr r4, [r12, #2952]
	str r4, [r12, #3096]
	ldr r4, [r12, #2956]
	str r4, [r12, #3100]
	ldr r4, [r12, #2960]
	str r4, [r12, #3104]
	ldr r4, [r12, #2964]
	str r4, [r12, #3108]
	ldr r4, [r12, #2968]
	str r4, [r12, #3112]
	ldr r4, [r12, #2972]
	str r4, [r12, #3116]
	mov r10, lr
	mov r0, r12
	bl {vg_brainpoolp384r1_point_add_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #0]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #2976]
	ldr r5, [r12, #2832]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #736]
	ldr r4, [r12, #2980]
	ldr r5, [r12, #2836]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #740]
	ldr r4, [r12, #2984]
	ldr r5, [r12, #2840]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #744]
	ldr r4, [r12, #2988]
	ldr r5, [r12, #2844]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #748]
	ldr r4, [r12, #2992]
	ldr r5, [r12, #2848]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #752]
	ldr r4, [r12, #2996]
	ldr r5, [r12, #2852]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #756]
	ldr r4, [r12, #3000]
	ldr r5, [r12, #2856]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #760]
	ldr r4, [r12, #3004]
	ldr r5, [r12, #2860]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #764]
	ldr r4, [r12, #3008]
	ldr r5, [r12, #2864]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #768]
	ldr r4, [r12, #3012]
	ldr r5, [r12, #2868]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #772]
	ldr r4, [r12, #3016]
	ldr r5, [r12, #2872]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #776]
	ldr r4, [r12, #3020]
	ldr r5, [r12, #2876]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #780]
	ldr r4, [r12, #3024]
	ldr r5, [r12, #2880]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #784]
	ldr r4, [r12, #3028]
	ldr r5, [r12, #2884]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #788]
	ldr r4, [r12, #3032]
	ldr r5, [r12, #2888]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #792]
	ldr r4, [r12, #3036]
	ldr r5, [r12, #2892]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #796]
	ldr r4, [r12, #3040]
	ldr r5, [r12, #2896]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #800]
	ldr r4, [r12, #3044]
	ldr r5, [r12, #2900]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #804]
	ldr r4, [r12, #3048]
	ldr r5, [r12, #2904]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #808]
	ldr r4, [r12, #3052]
	ldr r5, [r12, #2908]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #812]
	ldr r4, [r12, #3056]
	ldr r5, [r12, #2912]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #816]
	ldr r4, [r12, #3060]
	ldr r5, [r12, #2916]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #820]
	ldr r4, [r12, #3064]
	ldr r5, [r12, #2920]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #824]
	ldr r4, [r12, #3068]
	ldr r5, [r12, #2924]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #828]
	ldr r4, [r12, #3072]
	ldr r5, [r12, #2928]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #832]
	ldr r4, [r12, #3076]
	ldr r5, [r12, #2932]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #836]
	ldr r4, [r12, #3080]
	ldr r5, [r12, #2936]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #840]
	ldr r4, [r12, #3084]
	ldr r5, [r12, #2940]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #844]
	ldr r4, [r12, #3088]
	ldr r5, [r12, #2944]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #848]
	ldr r4, [r12, #3092]
	ldr r5, [r12, #2948]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #852]
	ldr r4, [r12, #3096]
	ldr r5, [r12, #2952]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #856]
	ldr r4, [r12, #3100]
	ldr r5, [r12, #2956]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #860]
	ldr r4, [r12, #3104]
	ldr r5, [r12, #2960]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #864]
	ldr r4, [r12, #3108]
	ldr r5, [r12, #2964]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #868]
	ldr r4, [r12, #3112]
	ldr r5, [r12, #2968]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #872]
	ldr r4, [r12, #3116]
	ldr r5, [r12, #2972]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #876]
	cmp r11, #0
	bne 23b
	ldr r4, [r12, #304]
	str r4, [r12, #1456]
	ldr r4, [r12, #308]
	str r4, [r12, #1460]
	ldr r4, [r12, #312]
	str r4, [r12, #1464]
	ldr r4, [r12, #316]
	str r4, [r12, #1468]
	ldr r4, [r12, #320]
	str r4, [r12, #1472]
	ldr r4, [r12, #324]
	str r4, [r12, #1476]
	ldr r4, [r12, #328]
	str r4, [r12, #1480]
	ldr r4, [r12, #332]
	str r4, [r12, #1484]
	ldr r4, [r12, #336]
	str r4, [r12, #1488]
	ldr r4, [r12, #340]
	str r4, [r12, #1492]
	ldr r4, [r12, #344]
	str r4, [r12, #1496]
	ldr r4, [r12, #348]
	str r4, [r12, #1500]
	mov r11, #384
24:
	sub r11, r11, #1
	mov r10, lr
	mov r0, r12
	movw r1, #1456
	movw r2, #1456
	movw r3, #1456
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1504
	movw r2, #1456
	movw r3, #832
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	add r4, r12, r11
	add r4, r4, #4096
	ldrb r4, [r4, #384]
	mov r5, #0
	sub r10, r5, r4
	ldr r4, [r12, #1456]
	ldr r5, [r12, #1504]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1456]
	ldr r4, [r12, #1460]
	ldr r5, [r12, #1508]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1460]
	ldr r4, [r12, #1464]
	ldr r5, [r12, #1512]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1464]
	ldr r4, [r12, #1468]
	ldr r5, [r12, #1516]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1468]
	ldr r4, [r12, #1472]
	ldr r5, [r12, #1520]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1472]
	ldr r4, [r12, #1476]
	ldr r5, [r12, #1524]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1476]
	ldr r4, [r12, #1480]
	ldr r5, [r12, #1528]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1480]
	ldr r4, [r12, #1484]
	ldr r5, [r12, #1532]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1484]
	ldr r4, [r12, #1488]
	ldr r5, [r12, #1536]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1488]
	ldr r4, [r12, #1492]
	ldr r5, [r12, #1540]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1492]
	ldr r4, [r12, #1496]
	ldr r5, [r12, #1544]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1496]
	ldr r4, [r12, #1500]
	ldr r5, [r12, #1548]
	eor r5, r5, r4
	and r5, r5, r10
	eor r4, r4, r5
	str r4, [r12, #1500]
	cmp r11, #0
	bne 24b
	mov r10, lr
	mov r0, r12
	movw r1, #1696
	movw r2, #736
	movw r3, #1456
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1744
	movw r2, #1696
	movw r3, #256
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #1888
	movw r2, #784
	movw r3, #1456
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	mov r10, lr
	mov r0, r12
	movw r1, #2128
	movw r2, #1888
	movw r3, #256
	bl {vg_brainpoolp384r1_mul_mod_p_umaal}
	mov lr, r10
	movw r6, #65535
	mov r3, #1
	ldr r7, [r12, #1600]
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
	ldr r7, [r12, #1604]
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
	ldr r7, [r12, #1608]
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
	ldr r7, [r12, #1612]
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
	ldr r7, [r12, #1616]
	ldr r8, [r12, #128]
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
	ldr r7, [r12, #1620]
	ldr r8, [r12, #132]
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
	ldr r7, [r12, #1624]
	ldr r8, [r12, #136]
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
	ldr r7, [r12, #1628]
	ldr r8, [r12, #140]
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
	ldr r7, [r12, #1632]
	ldr r8, [r12, #144]
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
	ldr r7, [r12, #1636]
	ldr r8, [r12, #148]
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
	ldr r7, [r12, #1640]
	ldr r8, [r12, #152]
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
	ldr r7, [r12, #1644]
	ldr r8, [r12, #156]
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
	ldr r5, [r12, #1600]
	ldr r4, [r12, #1604]
	orr r5, r5, r4
	ldr r4, [r12, #1608]
	orr r5, r5, r4
	ldr r4, [r12, #1612]
	orr r5, r5, r4
	ldr r4, [r12, #1616]
	orr r5, r5, r4
	ldr r4, [r12, #1620]
	orr r5, r5, r4
	ldr r4, [r12, #1624]
	orr r5, r5, r4
	ldr r4, [r12, #1628]
	orr r5, r5, r4
	ldr r4, [r12, #1632]
	orr r5, r5, r4
	ldr r4, [r12, #1636]
	orr r5, r5, r4
	ldr r4, [r12, #1640]
	orr r5, r5, r4
	ldr r4, [r12, #1644]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	and r5, r5, r9
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r5, [r12, #832]
	ldr r4, [r12, #836]
	orr r5, r5, r4
	ldr r4, [r12, #840]
	orr r5, r5, r4
	ldr r4, [r12, #844]
	orr r5, r5, r4
	ldr r4, [r12, #848]
	orr r5, r5, r4
	ldr r4, [r12, #852]
	orr r5, r5, r4
	ldr r4, [r12, #856]
	orr r5, r5, r4
	ldr r4, [r12, #860]
	orr r5, r5, r4
	ldr r4, [r12, #864]
	orr r5, r5, r4
	ldr r4, [r12, #868]
	orr r5, r5, r4
	ldr r4, [r12, #872]
	orr r5, r5, r4
	ldr r4, [r12, #876]
	orr r5, r5, r4
	mov r4, #0
	sub r4, r4, r5
	orr r4, r4, r5
	lsr r4, r4, #31
	mov r5, #0
	sub r5, r5, r4
	ldr r4, [r12, #2176]
	and r4, r4, r5
	str r4, [r12, #2176]
	ldr r10, [r12, #2176]
	mov r4, #4
	and r4, r4, r10
	strb r4, [lr, #0]
	ldr r4, [r12, #1744]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #45]
	ldr r4, [r12, #1748]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #41]
	ldr r4, [r12, #1752]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #37]
	ldr r4, [r12, #1756]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #33]
	ldr r4, [r12, #1760]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #29]
	ldr r4, [r12, #1764]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #25]
	ldr r4, [r12, #1768]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #21]
	ldr r4, [r12, #1772]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #17]
	ldr r4, [r12, #1776]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #13]
	ldr r4, [r12, #1780]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #9]
	ldr r4, [r12, #1784]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #5]
	ldr r4, [r12, #1788]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #1]
	ldr r4, [r12, #2128]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #93]
	ldr r4, [r12, #2132]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #89]
	ldr r4, [r12, #2136]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #85]
	ldr r4, [r12, #2140]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #81]
	ldr r4, [r12, #2144]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #77]
	ldr r4, [r12, #2148]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #73]
	ldr r4, [r12, #2152]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #69]
	ldr r4, [r12, #2156]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #65]
	ldr r4, [r12, #2160]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #61]
	ldr r4, [r12, #2164]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #57]
	ldr r4, [r12, #2168]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #53]
	ldr r4, [r12, #2172]
	and r4, r4, r10
	rev r4, r4
	str r4, [lr, #49]
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
