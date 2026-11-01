// The functions of `src/internal/vg_mldsa_ntt.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_ntt:
	push {r4}
	push {r5}
	push {r6}
	push {r7}
	push {r8}
	push {r9}
	push {r10}
	movw r12, #1
	movt r12, #0
	str r12, [r1, #0]
	movw r12, #24066
	movt r12, #73
	str r12, [r1, #4]
	movw r12, #30055
	movt r12, #57
	str r12, [r1, #8]
	movw r12, #25961
	movt r12, #57
	str r12, [r1, #12]
	movw r12, #1579
	movt r12, #79
	str r12, [r1, #16]
	movw r12, #57203
	movt r12, #83
	str r12, [r1, #20]
	movw r12, #57395
	movt r12, #79
	str r12, [r1, #24]
	movw r12, #1643
	movt r12, #79
	str r12, [r1, #28]
	movw r12, #45486
	movt r12, #118
	str r12, [r1, #32]
	movw r12, #3541
	movt r12, #54
	str r12, [r1, #36]
	movw r12, #60848
	movt r12, #40
	str r12, [r1, #40]
	movw r12, #32740
	movt r12, #32
	str r12, [r1, #44]
	movw r12, #29315
	movt r12, #57
	str r12, [r1, #48]
	movw r12, #35146
	movt r12, #112
	str r12, [r1, #52]
	movw r12, #33170
	movt r12, #8
	str r12, [r1, #56]
	movw r12, #15816
	movt r12, #109
	str r12, [r1, #60]
	movw r12, #29332
	movt r12, #76
	str r12, [r1, #64]
	movw r12, #57524
	movt r12, #65
	str r12, [r1, #68]
	movw r12, #41938
	movt r12, #40
	str r12, [r1, #72]
	movw r12, #21130
	movt r12, #102
	str r12, [r1, #76]
	movw r12, #6311
	movt r12, #74
	str r12, [r1, #80]
	movw r12, #16436
	movt r12, #121
	str r12, [r1, #84]
	movw r12, #21230
	movt r12, #10
	str r12, [r1, #88]
	movw r12, #32129
	movt r12, #107
	str r12, [r1, #92]
	movw r12, #40733
	movt r12, #78
	str r12, [r1, #96]
	movw r12, #10359
	movt r12, #26
	str r12, [r1, #100]
	movw r12, #29151
	movt r12, #37
	str r12, [r1, #104]
	movw r12, #18926
	movt r12, #22
	str r12, [r1, #108]
	movw r12, #4541
	movt r12, #118
	str r12, [r1, #112]
	movw r12, #11191
	movt r12, #73
	str r12, [r1, #116]
	movw r12, #63127
	movt r12, #42
	str r12, [r1, #120]
	movw r12, #55509
	movt r12, #34
	str r12, [r1, #124]
	movw r12, #63274
	movt r12, #54
	str r12, [r1, #128]
	movw r12, #37150
	movt r12, #48
	str r12, [r1, #132]
	movw r12, #53567
	movt r12, #41
	str r12, [r1, #136]
	movw r12, #9843
	movt r12, #73
	str r12, [r1, #140]
	movw r12, #26719
	movt r12, #80
	str r12, [r1, #144]
	movw r12, #4258
	movt r12, #32
	str r12, [r1, #148]
	movw r12, #34807
	movt r12, #56
	str r12, [r1, #152]
	movw r12, #45763
	movt r12, #17
	str r12, [r1, #156]
	movw r12, #932
	movt r12, #6
	str r12, [r1, #160]
	movw r12, #11245
	movt r12, #14
	str r12, [r1, #164]
	movw r12, #46892
	movt r12, #16
	str r12, [r1, #168]
	movw r12, #24373
	movt r12, #74
	str r12, [r1, #172]
	movw r12, #40213
	movt r12, #31
	str r12, [r1, #176]
	movw r12, #36052
	movt r12, #66
	str r12, [r1, #180]
	movw r12, #30708
	movt r12, #49
	str r12, [r1, #184]
	movw r12, #58898
	movt r12, #32
	str r12, [r1, #188]
	movw r12, #7197
	movt r12, #52
	str r12, [r1, #192]
	movw r12, #55411
	movt r12, #26
	str r12, [r1, #196]
	movw r12, #26241
	movt r12, #115
	str r12, [r1, #200]
	movw r12, #21823
	movt r12, #73
	str r12, [r1, #204]
	movw r12, #21238
	movt r12, #57
	str r12, [r1, #208]
	movw r12, #22090
	movt r12, #98
	str r12, [r1, #212]
	movw r12, #44293
	movt r12, #101
	str r12, [r1, #216]
	movw r12, #39452
	movt r12, #67
	str r12, [r1, #220]
	movw r12, #43615
	movt r12, #83
	str r12, [r1, #224]
	movw r12, #46626
	movt r12, #48
	str r12, [r1, #228]
	movw r12, #32568
	movt r12, #8
	str r12, [r1, #232]
	movw r12, #3693
	movt r12, #59
	str r12, [r1, #236]
	movw r12, #33754
	movt r12, #44
	str r12, [r1, #240]
	movw r12, #18798
	movt r12, #28
	str r12, [r1, #244]
	movw r12, #3627
	movt r12, #51
	str r12, [r1, #248]
	movw r12, #23408
	movt r12, #28
	str r12, [r1, #252]
	movw r12, #58353
	movt r12, #46
	str r12, [r1, #256]
	movw r12, #32441
	movt r12, #19
	str r12, [r1, #260]
	movw r12, #43312
	movt r12, #87
	str r12, [r1, #264]
	movw r12, #50927
	movt r12, #58
	str r12, [r1, #268]
	movw r12, #54604
	movt r12, #63
	str r12, [r1, #272]
	movw r12, #45802
	movt r12, #78
	str r12, [r1, #276]
	movw r12, #16097
	movt r12, #80
	str r12, [r1, #280]
	movw r12, #45429
	movt r12, #123
	str r12, [r1, #284]
	movw r12, #18612
	movt r12, #38
	str r12, [r1, #288]
	movw r12, #62038
	movt r12, #30
	str r12, [r1, #292]
	movw r12, #37026
	movt r12, #29
	str r12, [r1, #296]
	movw r12, #42708
	movt r12, #69
	str r12, [r1, #300]
	movw r12, #58779
	movt r12, #42
	str r12, [r1, #304]
	movw r12, #22684
	movt r12, #82
	str r12, [r1, #308]
	movw r12, #61941
	movt r12, #110
	str r12, [r1, #312]
	movw r12, #29320
	movt r12, #63
	str r12, [r1, #316]
	movw r12, #20738
	movt r12, #23
	str r12, [r1, #320]
	movw r12, #23897
	movt r12, #7
	str r12, [r1, #324]
	movw r12, #34746
	movt r12, #17
	str r12, [r1, #328]
	movw r12, #44201
	movt r12, #82
	str r12, [r1, #332]
	movw r12, #16030
	movt r12, #119
	str r12, [r1, #336]
	movw r12, #38616
	movt r12, #2
	str r12, [r1, #340]
	movw r12, #37612
	movt r12, #37
	str r12, [r1, #344]
	movw r12, #65298
	movt r12, #76
	str r12, [r1, #348]
	movw r12, #19688
	movt r12, #64
	str r12, [r1, #352]
	movw r12, #42370
	movt r12, #74
	str r12, [r1, #356]
	movw r12, #21734
	movt r12, #30
	str r12, [r1, #360]
	movw r12, #5825
	movt r12, #79
	str r12, [r1, #364]
	movw r12, #32377
	movt r12, #26
	str r12, [r1, #368]
	movw r12, #38799
	movt r12, #3
	str r12, [r1, #372]
	movw r12, #18455
	movt r12, #78
	str r12, [r1, #376]
	movw r12, #47193
	movt r12, #49
	str r12, [r1, #380]
	movw r12, #33996
	movt r12, #88
	str r12, [r1, #384]
	movw r12, #18471
	movt r12, #27
	str r12, [r1, #388]
	movw r12, #25552
	movt r12, #91
	str r12, [r1, #392]
	movw r12, #30842
	movt r12, #93
	str r12, [r1, #396]
	movw r12, #8798
	movt r12, #53
	str r12, [r1, #400]
	movw r12, #3198
	movt r12, #64
	str r12, [r1, #404]
	movw r12, #2513
	movt r12, #108
	str r12, [r1, #408]
	movw r12, #54578
	movt r12, #91
	str r12, [r1, #412]
	movw r12, #50387
	movt r12, #107
	str r12, [r1, #416]
	movw r12, #36555
	movt r12, #37
	str r12, [r1, #420]
	movw r12, #21324
	movt r12, #46
	str r12, [r1, #424]
	movw r12, #31340
	movt r12, #9
	str r12, [r1, #428]
	movw r12, #34848
	movt r12, #59
	str r12, [r1, #432]
	movw r12, #10332
	movt r12, #109
	str r12, [r1, #436]
	movw r12, #42232
	movt r12, #44
	str r12, [r1, #440]
	movw r12, #31914
	movt r12, #51
	str r12, [r1, #444]
	movw r12, #45728
	movt r12, #20
	str r12, [r1, #448]
	movw r12, #34102
	movt r12, #85
	str r12, [r1, #452]
	movw r12, #61830
	movt r12, #40
	str r12, [r1, #456]
	movw r12, #31069
	movt r12, #85
	str r12, [r1, #460]
	movw r12, #63088
	movt r12, #74
	str r12, [r1, #464]
	movw r12, #19078
	movt r12, #35
	str r12, [r1, #468]
	movw r12, #59430
	movt r12, #117
	str r12, [r1, #472]
	movw r12, #56934
	movt r12, #120
	str r12, [r1, #476]
	movw r12, #21132
	movt r12, #5
	str r12, [r1, #480]
	movw r12, #57177
	movt r12, #122
	str r12, [r1, #484]
	movw r12, #28183
	movt r12, #15
	str r12, [r1, #488]
	movw r12, #62426
	movt r12, #91
	str r12, [r1, #492]
	movw r12, #39806
	movt r12, #69
	str r12, [r1, #496]
	movw r12, #35636
	movt r12, #98
	str r12, [r1, #500]
	movw r12, #48843
	movt r12, #93
	str r12, [r1, #504]
	movw r12, #40571
	movt r12, #26
	str r12, [r1, #508]
	movw r12, #1753
	movt r12, #0
	str r12, [r1, #512]
	movw r12, #22469
	movt r12, #98
	str r12, [r1, #516]
	movw r12, #19260
	movt r12, #87
	str r12, [r1, #520]
	movw r12, #43247
	movt r12, #105
	str r12, [r1, #524]
	movw r12, #38968
	movt r12, #40
	str r12, [r1, #528]
	movw r12, #46590
	movt r12, #100
	str r12, [r1, #532]
	movw r12, #63733
	movt r12, #126
	str r12, [r1, #536]
	movw r12, #20088
	movt r12, #42
	str r12, [r1, #540]
	movw r12, #2595
	movt r12, #18
	str r12, [r1, #544]
	movw r12, #21672
	movt r12, #1
	str r12, [r1, #548]
	movw r12, #47103
	movt r12, #9
	str r12, [r1, #552]
	movw r12, #24199
	movt r12, #67
	str r12, [r1, #556]
	movw r12, #32760
	movt r12, #67
	str r12, [r1, #560]
	movw r12, #54708
	movt r12, #92
	str r12, [r1, #564]
	movw r12, #49230
	movt r12, #77
	str r12, [r1, #568]
	movw r12, #10415
	movt r12, #71
	str r12, [r1, #572]
	movw r12, #29533
	movt r12, #127
	str r12, [r1, #576]
	movw r12, #36109
	movt r12, #12
	str r12, [r1, #580]
	movw r12, #26325
	movt r12, #15
	str r12, [r1, #584]
	movw r12, #28032
	movt r12, #90
	str r12, [r1, #588]
	movw r12, #43928
	movt r12, #97
	str r12, [r1, #592]
	movw r12, #23958
	movt r12, #24
	str r12, [r1, #596]
	movw r12, #32561
	movt r12, #67
	str r12, [r1, #600]
	movw r12, #33432
	movt r12, #70
	str r12, [r1, #604]
	movw r12, #10592
	movt r12, #102
	str r12, [r1, #608]
	movw r12, #54649
	movt r12, #75
	str r12, [r1, #612]
	movw r12, #56838
	movt r12, #40
	str r12, [r1, #616]
	movw r12, #23949
	movt r12, #70
	str r12, [r1, #620]
	movw r12, #45283
	movt r12, #73
	str r12, [r1, #624]
	movw r12, #46132
	movt r12, #9
	str r12, [r1, #628]
	movw r12, #3507
	movt r12, #124
	str r12, [r1, #632]
	movw r12, #26800
	movt r12, #90
	str r12, [r1, #636]
	movw r12, #39849
	movt r12, #64
	str r12, [r1, #640]
	movw r12, #54229
	movt r12, #100
	str r12, [r1, #644]
	movw r12, #30250
	movt r12, #33
	str r12, [r1, #648]
	movw r12, #34193
	movt r12, #101
	str r12, [r1, #652]
	movw r12, #28217
	movt r12, #36
	str r12, [r1, #656]
	movw r12, #50075
	movt r12, #72
	str r12, [r1, #660]
	movw r12, #51033
	movt r12, #123
	str r12, [r1, #664]
	movw r12, #22617
	movt r12, #79
	str r12, [r1, #668]
	movw r12, #11698
	movt r12, #57
	str r12, [r1, #672]
	movw r12, #2339
	movt r12, #35
	str r12, [r1, #676]
	movw r12, #60263
	movt r12, #18
	str r12, [r1, #680]
	movw r12, #19954
	movt r12, #69
	str r12, [r1, #684]
	movw r12, #49948
	movt r12, #48
	str r12, [r1, #688]
	movw r12, #21540
	movt r12, #40
	str r12, [r1, #692]
	movw r12, #9006
	movt r12, #19
	str r12, [r1, #696]
	movw r12, #44928
	movt r12, #127
	str r12, [r1, #700]
	movw r12, #49099
	movt r12, #45
	str r12, [r1, #704]
	movw r12, #10763
	movt r12, #2
	str r12, [r1, #708]
	movw r12, #33580
	movt r12, #126
	str r12, [r1, #712]
	movw r12, #22650
	movt r12, #38
	str r12, [r1, #716]
	movw r12, #13173
	movt r12, #107
	str r12, [r1, #720]
	movw r12, #23414
	movt r12, #9
	str r12, [r1, #724]
	movw r12, #57804
	movt r12, #107
	str r12, [r1, #728]
	movw r12, #1566
	movt r12, #94
	str r12, [r1, #732]
	movw r12, #57357
	movt r12, #120
	str r12, [r1, #736]
	movw r12, #35895
	movt r12, #98
	str r12, [r1, #740]
	movw r12, #42500
	movt r12, #61
	str r12, [r1, #744]
	movw r12, #58684
	movt r12, #74
	str r12, [r1, #748]
	movw r12, #7528
	movt r12, #31
	str r12, [r1, #752]
	movw r12, #12475
	movt r12, #99
	str r12, [r1, #756]
	movw r12, #25016
	movt r12, #115
	str r12, [r1, #760]
	movw r12, #41068
	movt r12, #94
	str r12, [r1, #764]
	movw r12, #6855
	movt r12, #103
	str r12, [r1, #768]
	movw r12, #8134
	movt r12, #32
	str r12, [r1, #772]
	movw r12, #42239
	movt r12, #91
	str r12, [r1, #776]
	movw r12, #55154
	movt r12, #96
	str r12, [r1, #780]
	movw r12, #61953
	movt r12, #8
	str r12, [r1, #784]
	movw r12, #57380
	movt r12, #109
	str r12, [r1, #788]
	movw r12, #3693
	movt r12, #8
	str r12, [r1, #792]
	movw r12, #910
	movt r12, #86
	str r12, [r1, #796]
	movw r12, #22152
	movt r12, #105
	str r12, [r1, #800]
	movw r12, #27966
	movt r12, #30
	str r12, [r1, #804]
	movw r12, #957
	movt r12, #38
	str r12, [r1, #808]
	movw r12, #40442
	movt r12, #106
	str r12, [r1, #812]
	movw r12, #49175
	movt r12, #7
	str r12, [r1, #816]
	movw r12, #49108
	movt r12, #109
	str r12, [r1, #820]
	movw r12, #53437
	movt r12, #116
	str r12, [r1, #824]
	movw r12, #57827
	movt r12, #99
	str r12, [r1, #828]
	movw r12, #38259
	movt r12, #81
	str r12, [r1, #832]
	movw r12, #46605
	movt r12, #122
	str r12, [r1, #836]
	movw r12, #26554
	movt r12, #40
	str r12, [r1, #840]
	movw r12, #60628
	movt r12, #45
	str r12, [r1, #844]
	movw r12, #396
	movt r12, #88
	str r12, [r1, #848]
	movw r12, #19701
	movt r12, #63
	str r12, [r1, #852]
	movw r12, #28681
	movt r12, #11
	str r12, [r1, #856]
	movw r12, #32291
	movt r12, #66
	str r12, [r1, #860]
	movw r12, #48439
	movt r12, #60
	str r12, [r1, #864]
	movw r12, #13107
	movt r12, #39
	str r12, [r1, #868]
	movw r12, #14679
	movt r12, #103
	str r12, [r1, #872]
	movw r12, #19293
	movt r12, #26
	str r12, [r1, #876]
	movw r12, #26918
	movt r12, #25
	str r12, [r1, #880]
	movw r12, #61958
	movt r12, #30
	str r12, [r1, #884]
	movw r12, #49486
	movt r12, #17
	str r12, [r1, #888]
	movw r12, #30408
	movt r12, #76
	str r12, [r1, #892]
	movw r12, #62511
	movt r12, #60
	str r12, [r1, #896]
	movw r12, #45466
	movt r12, #127
	str r12, [r1, #900]
	movw r12, #63084
	movt r12, #106
	str r12, [r1, #904]
	movw r12, #5737
	movt r12, #46
	str r12, [r1, #908]
	movw r12, #21206
	movt r12, #51
	str r12, [r1, #912]
	movw r12, #18272
	movt r12, #3
	str r12, [r1, #916]
	movw r12, #21088
	movt r12, #8
	str r12, [r1, #920]
	movw r12, #7800
	movt r12, #116
	str r12, [r1, #924]
	movw r12, #25366
	movt r12, #47
	str r12, [r1, #928]
	movw r12, #2577
	movt r12, #111
	str r12, [r1, #932]
	movw r12, #49393
	movt r12, #7
	str r12, [r1, #936]
	movw r12, #27915
	movt r12, #119
	str r12, [r1, #940]
	movw r12, #8176
	movt r12, #13
	str r12, [r1, #944]
	movw r12, #22564
	movt r12, #52
	str r12, [r1, #948]
	movw r12, #9172
	movt r12, #2
	str r12, [r1, #952]
	movw r12, #50521
	movt r12, #104
	str r12, [r1, #956]
	movw r12, #34949
	movt r12, #94
	str r12, [r1, #960]
	movw r12, #43570
	movt r12, #47
	str r12, [r1, #964]
	movw r12, #64613
	movt r12, #35
	str r12, [r1, #968]
	movw r12, #26946
	movt r12, #94
	str r12, [r1, #972]
	movw r12, #57581
	movt r12, #81
	str r12, [r1, #976]
	movw r12, #44467
	movt r12, #101
	str r12, [r1, #980]
	movw r12, #42470
	movt r12, #44
	str r12, [r1, #984]
	movw r12, #57854
	movt r12, #121
	str r12, [r1, #988]
	movw r12, #16484
	movt r12, #123
	str r12, [r1, #992]
	movw r12, #57821
	movt r12, #53
	str r12, [r1, #996]
	movw r12, #15020
	movt r12, #67
	str r12, [r1, #1000]
	movw r12, #19166
	movt r12, #70
	str r12, [r1, #1004]
	movw r12, #65044
	movt r12, #28
	str r12, [r1, #1008]
	movw r12, #61902
	movt r12, #115
	str r12, [r1, #1012]
	movw r12, #5902
	movt r12, #16
	str r12, [r1, #1016]
	movw r12, #46807
	movt r12, #116
	str r12, [r1, #1020]
	movw r4, #57345
	movt r4, #127
	add r1, r1, #4
	mov r2, #1
20:
	ldr r8, [r1, #0]
	lsr r5, r8, #14
	lsl r6, r8, #18
	lsr r6, r6, #25
	lsl r7, r8, #25
	lsr r7, r7, #25
	add r1, r1, #4
	mov r3, #128
21:
	ldr r8, [r0, #512]
	mul r9, r8, r5
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r6
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r7
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	sub r9, r9, r4
	lsr r12, r9, #31
	mul r12, r12, r4
	add r9, r9, r12
	ldr r8, [r0, #0]
	sub r10, r8, r9
	lsr r12, r10, #31
	mul r12, r12, r4
	add r10, r10, r12
	str r10, [r0, #512]
	add r8, r8, r9
	sub r8, r8, r4
	lsr r12, r8, #31
	mul r12, r12, r4
	add r8, r8, r12
	str r8, [r0, #0]
	add r0, r0, #4
	subs r3, r3, #1
	bne 21b
	add r0, r0, #512
	subs r2, r2, #1
	bne 20b
	sub r0, r0, #1024
	mov r2, #2
22:
	ldr r8, [r1, #0]
	lsr r5, r8, #14
	lsl r6, r8, #18
	lsr r6, r6, #25
	lsl r7, r8, #25
	lsr r7, r7, #25
	add r1, r1, #4
	mov r3, #64
23:
	ldr r8, [r0, #256]
	mul r9, r8, r5
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r6
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r7
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	sub r9, r9, r4
	lsr r12, r9, #31
	mul r12, r12, r4
	add r9, r9, r12
	ldr r8, [r0, #0]
	sub r10, r8, r9
	lsr r12, r10, #31
	mul r12, r12, r4
	add r10, r10, r12
	str r10, [r0, #256]
	add r8, r8, r9
	sub r8, r8, r4
	lsr r12, r8, #31
	mul r12, r12, r4
	add r8, r8, r12
	str r8, [r0, #0]
	add r0, r0, #4
	subs r3, r3, #1
	bne 23b
	add r0, r0, #256
	subs r2, r2, #1
	bne 22b
	sub r0, r0, #1024
	mov r2, #4
24:
	ldr r8, [r1, #0]
	lsr r5, r8, #14
	lsl r6, r8, #18
	lsr r6, r6, #25
	lsl r7, r8, #25
	lsr r7, r7, #25
	add r1, r1, #4
	mov r3, #32
25:
	ldr r8, [r0, #128]
	mul r9, r8, r5
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r6
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r7
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	sub r9, r9, r4
	lsr r12, r9, #31
	mul r12, r12, r4
	add r9, r9, r12
	ldr r8, [r0, #0]
	sub r10, r8, r9
	lsr r12, r10, #31
	mul r12, r12, r4
	add r10, r10, r12
	str r10, [r0, #128]
	add r8, r8, r9
	sub r8, r8, r4
	lsr r12, r8, #31
	mul r12, r12, r4
	add r8, r8, r12
	str r8, [r0, #0]
	add r0, r0, #4
	subs r3, r3, #1
	bne 25b
	add r0, r0, #128
	subs r2, r2, #1
	bne 24b
	sub r0, r0, #1024
	mov r2, #8
26:
	ldr r8, [r1, #0]
	lsr r5, r8, #14
	lsl r6, r8, #18
	lsr r6, r6, #25
	lsl r7, r8, #25
	lsr r7, r7, #25
	add r1, r1, #4
	mov r3, #16
27:
	ldr r8, [r0, #64]
	mul r9, r8, r5
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r6
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r7
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	sub r9, r9, r4
	lsr r12, r9, #31
	mul r12, r12, r4
	add r9, r9, r12
	ldr r8, [r0, #0]
	sub r10, r8, r9
	lsr r12, r10, #31
	mul r12, r12, r4
	add r10, r10, r12
	str r10, [r0, #64]
	add r8, r8, r9
	sub r8, r8, r4
	lsr r12, r8, #31
	mul r12, r12, r4
	add r8, r8, r12
	str r8, [r0, #0]
	add r0, r0, #4
	subs r3, r3, #1
	bne 27b
	add r0, r0, #64
	subs r2, r2, #1
	bne 26b
	sub r0, r0, #1024
	mov r2, #16
28:
	ldr r8, [r1, #0]
	lsr r5, r8, #14
	lsl r6, r8, #18
	lsr r6, r6, #25
	lsl r7, r8, #25
	lsr r7, r7, #25
	add r1, r1, #4
	mov r3, #8
29:
	ldr r8, [r0, #32]
	mul r9, r8, r5
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r6
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r7
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	sub r9, r9, r4
	lsr r12, r9, #31
	mul r12, r12, r4
	add r9, r9, r12
	ldr r8, [r0, #0]
	sub r10, r8, r9
	lsr r12, r10, #31
	mul r12, r12, r4
	add r10, r10, r12
	str r10, [r0, #32]
	add r8, r8, r9
	sub r8, r8, r4
	lsr r12, r8, #31
	mul r12, r12, r4
	add r8, r8, r12
	str r8, [r0, #0]
	add r0, r0, #4
	subs r3, r3, #1
	bne 29b
	add r0, r0, #32
	subs r2, r2, #1
	bne 28b
	sub r0, r0, #1024
	mov r2, #32
210:
	ldr r8, [r1, #0]
	lsr r5, r8, #14
	lsl r6, r8, #18
	lsr r6, r6, #25
	lsl r7, r8, #25
	lsr r7, r7, #25
	add r1, r1, #4
	mov r3, #4
211:
	ldr r8, [r0, #16]
	mul r9, r8, r5
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r6
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r7
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	sub r9, r9, r4
	lsr r12, r9, #31
	mul r12, r12, r4
	add r9, r9, r12
	ldr r8, [r0, #0]
	sub r10, r8, r9
	lsr r12, r10, #31
	mul r12, r12, r4
	add r10, r10, r12
	str r10, [r0, #16]
	add r8, r8, r9
	sub r8, r8, r4
	lsr r12, r8, #31
	mul r12, r12, r4
	add r8, r8, r12
	str r8, [r0, #0]
	add r0, r0, #4
	subs r3, r3, #1
	bne 211b
	add r0, r0, #16
	subs r2, r2, #1
	bne 210b
	sub r0, r0, #1024
	mov r2, #64
212:
	ldr r8, [r1, #0]
	lsr r5, r8, #14
	lsl r6, r8, #18
	lsr r6, r6, #25
	lsl r7, r8, #25
	lsr r7, r7, #25
	add r1, r1, #4
	mov r3, #2
213:
	ldr r8, [r0, #8]
	mul r9, r8, r5
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r6
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r7
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	sub r9, r9, r4
	lsr r12, r9, #31
	mul r12, r12, r4
	add r9, r9, r12
	ldr r8, [r0, #0]
	sub r10, r8, r9
	lsr r12, r10, #31
	mul r12, r12, r4
	add r10, r10, r12
	str r10, [r0, #8]
	add r8, r8, r9
	sub r8, r8, r4
	lsr r12, r8, #31
	mul r12, r12, r4
	add r8, r8, r12
	str r8, [r0, #0]
	add r0, r0, #4
	subs r3, r3, #1
	bne 213b
	add r0, r0, #8
	subs r2, r2, #1
	bne 212b
	sub r0, r0, #1024
	mov r2, #128
214:
	ldr r8, [r1, #0]
	lsr r5, r8, #14
	lsl r6, r8, #18
	lsr r6, r6, #25
	lsl r7, r8, #25
	lsr r7, r7, #25
	add r1, r1, #4
	mov r3, #1
215:
	ldr r8, [r0, #4]
	mul r9, r8, r5
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r6
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	mul r12, r8, r7
	add r9, r12, r9, lsl #7
	lsr r12, r9, #23
	mul r12, r12, r4
	sub r9, r9, r12
	sub r9, r9, r4
	lsr r12, r9, #31
	mul r12, r12, r4
	add r9, r9, r12
	ldr r8, [r0, #0]
	sub r10, r8, r9
	lsr r12, r10, #31
	mul r12, r12, r4
	add r10, r10, r12
	str r10, [r0, #4]
	add r8, r8, r9
	sub r8, r8, r4
	lsr r12, r8, #31
	mul r12, r12, r4
	add r8, r8, r12
	str r8, [r0, #0]
	add r0, r0, #4
	subs r3, r3, #1
	bne 215b
	add r0, r0, #4
	subs r2, r2, #1
	bne 214b
	sub r0, r0, #1024
	ldr r10, [sp], #4
	ldr r9, [sp], #4
	ldr r8, [sp], #4
	ldr r7, [sp], #4
	ldr r6, [sp], #4
	ldr r5, [sp], #4
	ldr r4, [sp], #4
	bx lr
