// The functions of `src/mldsa.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_ntt:
	stdu %r1, -48(%r1)
	std %r14, 32(%r1)
	stdu %r1, -48(%r1)
	std %r15, 32(%r1)
	lis %r12, 0
	ori %r12, %r12, 1
	stw %r12, 0(%r4)
	lis %r12, 73
	ori %r12, %r12, 24066
	stw %r12, 4(%r4)
	lis %r12, 57
	ori %r12, %r12, 30055
	stw %r12, 8(%r4)
	lis %r12, 57
	ori %r12, %r12, 25961
	stw %r12, 12(%r4)
	lis %r12, 79
	ori %r12, %r12, 1579
	stw %r12, 16(%r4)
	lis %r12, 83
	ori %r12, %r12, 57203
	stw %r12, 20(%r4)
	lis %r12, 79
	ori %r12, %r12, 57395
	stw %r12, 24(%r4)
	lis %r12, 79
	ori %r12, %r12, 1643
	stw %r12, 28(%r4)
	lis %r12, 118
	ori %r12, %r12, 45486
	stw %r12, 32(%r4)
	lis %r12, 54
	ori %r12, %r12, 3541
	stw %r12, 36(%r4)
	lis %r12, 40
	ori %r12, %r12, 60848
	stw %r12, 40(%r4)
	lis %r12, 32
	ori %r12, %r12, 32740
	stw %r12, 44(%r4)
	lis %r12, 57
	ori %r12, %r12, 29315
	stw %r12, 48(%r4)
	lis %r12, 112
	ori %r12, %r12, 35146
	stw %r12, 52(%r4)
	lis %r12, 8
	ori %r12, %r12, 33170
	stw %r12, 56(%r4)
	lis %r12, 109
	ori %r12, %r12, 15816
	stw %r12, 60(%r4)
	lis %r12, 76
	ori %r12, %r12, 29332
	stw %r12, 64(%r4)
	lis %r12, 65
	ori %r12, %r12, 57524
	stw %r12, 68(%r4)
	lis %r12, 40
	ori %r12, %r12, 41938
	stw %r12, 72(%r4)
	lis %r12, 102
	ori %r12, %r12, 21130
	stw %r12, 76(%r4)
	lis %r12, 74
	ori %r12, %r12, 6311
	stw %r12, 80(%r4)
	lis %r12, 121
	ori %r12, %r12, 16436
	stw %r12, 84(%r4)
	lis %r12, 10
	ori %r12, %r12, 21230
	stw %r12, 88(%r4)
	lis %r12, 107
	ori %r12, %r12, 32129
	stw %r12, 92(%r4)
	lis %r12, 78
	ori %r12, %r12, 40733
	stw %r12, 96(%r4)
	lis %r12, 26
	ori %r12, %r12, 10359
	stw %r12, 100(%r4)
	lis %r12, 37
	ori %r12, %r12, 29151
	stw %r12, 104(%r4)
	lis %r12, 22
	ori %r12, %r12, 18926
	stw %r12, 108(%r4)
	lis %r12, 118
	ori %r12, %r12, 4541
	stw %r12, 112(%r4)
	lis %r12, 73
	ori %r12, %r12, 11191
	stw %r12, 116(%r4)
	lis %r12, 42
	ori %r12, %r12, 63127
	stw %r12, 120(%r4)
	lis %r12, 34
	ori %r12, %r12, 55509
	stw %r12, 124(%r4)
	lis %r12, 54
	ori %r12, %r12, 63274
	stw %r12, 128(%r4)
	lis %r12, 48
	ori %r12, %r12, 37150
	stw %r12, 132(%r4)
	lis %r12, 41
	ori %r12, %r12, 53567
	stw %r12, 136(%r4)
	lis %r12, 73
	ori %r12, %r12, 9843
	stw %r12, 140(%r4)
	lis %r12, 80
	ori %r12, %r12, 26719
	stw %r12, 144(%r4)
	lis %r12, 32
	ori %r12, %r12, 4258
	stw %r12, 148(%r4)
	lis %r12, 56
	ori %r12, %r12, 34807
	stw %r12, 152(%r4)
	lis %r12, 17
	ori %r12, %r12, 45763
	stw %r12, 156(%r4)
	lis %r12, 6
	ori %r12, %r12, 932
	stw %r12, 160(%r4)
	lis %r12, 14
	ori %r12, %r12, 11245
	stw %r12, 164(%r4)
	lis %r12, 16
	ori %r12, %r12, 46892
	stw %r12, 168(%r4)
	lis %r12, 74
	ori %r12, %r12, 24373
	stw %r12, 172(%r4)
	lis %r12, 31
	ori %r12, %r12, 40213
	stw %r12, 176(%r4)
	lis %r12, 66
	ori %r12, %r12, 36052
	stw %r12, 180(%r4)
	lis %r12, 49
	ori %r12, %r12, 30708
	stw %r12, 184(%r4)
	lis %r12, 32
	ori %r12, %r12, 58898
	stw %r12, 188(%r4)
	lis %r12, 52
	ori %r12, %r12, 7197
	stw %r12, 192(%r4)
	lis %r12, 26
	ori %r12, %r12, 55411
	stw %r12, 196(%r4)
	lis %r12, 115
	ori %r12, %r12, 26241
	stw %r12, 200(%r4)
	lis %r12, 73
	ori %r12, %r12, 21823
	stw %r12, 204(%r4)
	lis %r12, 57
	ori %r12, %r12, 21238
	stw %r12, 208(%r4)
	lis %r12, 98
	ori %r12, %r12, 22090
	stw %r12, 212(%r4)
	lis %r12, 101
	ori %r12, %r12, 44293
	stw %r12, 216(%r4)
	lis %r12, 67
	ori %r12, %r12, 39452
	stw %r12, 220(%r4)
	lis %r12, 83
	ori %r12, %r12, 43615
	stw %r12, 224(%r4)
	lis %r12, 48
	ori %r12, %r12, 46626
	stw %r12, 228(%r4)
	lis %r12, 8
	ori %r12, %r12, 32568
	stw %r12, 232(%r4)
	lis %r12, 59
	ori %r12, %r12, 3693
	stw %r12, 236(%r4)
	lis %r12, 44
	ori %r12, %r12, 33754
	stw %r12, 240(%r4)
	lis %r12, 28
	ori %r12, %r12, 18798
	stw %r12, 244(%r4)
	lis %r12, 51
	ori %r12, %r12, 3627
	stw %r12, 248(%r4)
	lis %r12, 28
	ori %r12, %r12, 23408
	stw %r12, 252(%r4)
	lis %r12, 46
	ori %r12, %r12, 58353
	stw %r12, 256(%r4)
	lis %r12, 19
	ori %r12, %r12, 32441
	stw %r12, 260(%r4)
	lis %r12, 87
	ori %r12, %r12, 43312
	stw %r12, 264(%r4)
	lis %r12, 58
	ori %r12, %r12, 50927
	stw %r12, 268(%r4)
	lis %r12, 63
	ori %r12, %r12, 54604
	stw %r12, 272(%r4)
	lis %r12, 78
	ori %r12, %r12, 45802
	stw %r12, 276(%r4)
	lis %r12, 80
	ori %r12, %r12, 16097
	stw %r12, 280(%r4)
	lis %r12, 123
	ori %r12, %r12, 45429
	stw %r12, 284(%r4)
	lis %r12, 38
	ori %r12, %r12, 18612
	stw %r12, 288(%r4)
	lis %r12, 30
	ori %r12, %r12, 62038
	stw %r12, 292(%r4)
	lis %r12, 29
	ori %r12, %r12, 37026
	stw %r12, 296(%r4)
	lis %r12, 69
	ori %r12, %r12, 42708
	stw %r12, 300(%r4)
	lis %r12, 42
	ori %r12, %r12, 58779
	stw %r12, 304(%r4)
	lis %r12, 82
	ori %r12, %r12, 22684
	stw %r12, 308(%r4)
	lis %r12, 110
	ori %r12, %r12, 61941
	stw %r12, 312(%r4)
	lis %r12, 63
	ori %r12, %r12, 29320
	stw %r12, 316(%r4)
	lis %r12, 23
	ori %r12, %r12, 20738
	stw %r12, 320(%r4)
	lis %r12, 7
	ori %r12, %r12, 23897
	stw %r12, 324(%r4)
	lis %r12, 17
	ori %r12, %r12, 34746
	stw %r12, 328(%r4)
	lis %r12, 82
	ori %r12, %r12, 44201
	stw %r12, 332(%r4)
	lis %r12, 119
	ori %r12, %r12, 16030
	stw %r12, 336(%r4)
	lis %r12, 2
	ori %r12, %r12, 38616
	stw %r12, 340(%r4)
	lis %r12, 37
	ori %r12, %r12, 37612
	stw %r12, 344(%r4)
	lis %r12, 76
	ori %r12, %r12, 65298
	stw %r12, 348(%r4)
	lis %r12, 64
	ori %r12, %r12, 19688
	stw %r12, 352(%r4)
	lis %r12, 74
	ori %r12, %r12, 42370
	stw %r12, 356(%r4)
	lis %r12, 30
	ori %r12, %r12, 21734
	stw %r12, 360(%r4)
	lis %r12, 79
	ori %r12, %r12, 5825
	stw %r12, 364(%r4)
	lis %r12, 26
	ori %r12, %r12, 32377
	stw %r12, 368(%r4)
	lis %r12, 3
	ori %r12, %r12, 38799
	stw %r12, 372(%r4)
	lis %r12, 78
	ori %r12, %r12, 18455
	stw %r12, 376(%r4)
	lis %r12, 49
	ori %r12, %r12, 47193
	stw %r12, 380(%r4)
	lis %r12, 88
	ori %r12, %r12, 33996
	stw %r12, 384(%r4)
	lis %r12, 27
	ori %r12, %r12, 18471
	stw %r12, 388(%r4)
	lis %r12, 91
	ori %r12, %r12, 25552
	stw %r12, 392(%r4)
	lis %r12, 93
	ori %r12, %r12, 30842
	stw %r12, 396(%r4)
	lis %r12, 53
	ori %r12, %r12, 8798
	stw %r12, 400(%r4)
	lis %r12, 64
	ori %r12, %r12, 3198
	stw %r12, 404(%r4)
	lis %r12, 108
	ori %r12, %r12, 2513
	stw %r12, 408(%r4)
	lis %r12, 91
	ori %r12, %r12, 54578
	stw %r12, 412(%r4)
	lis %r12, 107
	ori %r12, %r12, 50387
	stw %r12, 416(%r4)
	lis %r12, 37
	ori %r12, %r12, 36555
	stw %r12, 420(%r4)
	lis %r12, 46
	ori %r12, %r12, 21324
	stw %r12, 424(%r4)
	lis %r12, 9
	ori %r12, %r12, 31340
	stw %r12, 428(%r4)
	lis %r12, 59
	ori %r12, %r12, 34848
	stw %r12, 432(%r4)
	lis %r12, 109
	ori %r12, %r12, 10332
	stw %r12, 436(%r4)
	lis %r12, 44
	ori %r12, %r12, 42232
	stw %r12, 440(%r4)
	lis %r12, 51
	ori %r12, %r12, 31914
	stw %r12, 444(%r4)
	lis %r12, 20
	ori %r12, %r12, 45728
	stw %r12, 448(%r4)
	lis %r12, 85
	ori %r12, %r12, 34102
	stw %r12, 452(%r4)
	lis %r12, 40
	ori %r12, %r12, 61830
	stw %r12, 456(%r4)
	lis %r12, 85
	ori %r12, %r12, 31069
	stw %r12, 460(%r4)
	lis %r12, 74
	ori %r12, %r12, 63088
	stw %r12, 464(%r4)
	lis %r12, 35
	ori %r12, %r12, 19078
	stw %r12, 468(%r4)
	lis %r12, 117
	ori %r12, %r12, 59430
	stw %r12, 472(%r4)
	lis %r12, 120
	ori %r12, %r12, 56934
	stw %r12, 476(%r4)
	lis %r12, 5
	ori %r12, %r12, 21132
	stw %r12, 480(%r4)
	lis %r12, 122
	ori %r12, %r12, 57177
	stw %r12, 484(%r4)
	lis %r12, 15
	ori %r12, %r12, 28183
	stw %r12, 488(%r4)
	lis %r12, 91
	ori %r12, %r12, 62426
	stw %r12, 492(%r4)
	lis %r12, 69
	ori %r12, %r12, 39806
	stw %r12, 496(%r4)
	lis %r12, 98
	ori %r12, %r12, 35636
	stw %r12, 500(%r4)
	lis %r12, 93
	ori %r12, %r12, 48843
	stw %r12, 504(%r4)
	lis %r12, 26
	ori %r12, %r12, 40571
	stw %r12, 508(%r4)
	lis %r12, 0
	ori %r12, %r12, 1753
	stw %r12, 512(%r4)
	lis %r12, 98
	ori %r12, %r12, 22469
	stw %r12, 516(%r4)
	lis %r12, 87
	ori %r12, %r12, 19260
	stw %r12, 520(%r4)
	lis %r12, 105
	ori %r12, %r12, 43247
	stw %r12, 524(%r4)
	lis %r12, 40
	ori %r12, %r12, 38968
	stw %r12, 528(%r4)
	lis %r12, 100
	ori %r12, %r12, 46590
	stw %r12, 532(%r4)
	lis %r12, 126
	ori %r12, %r12, 63733
	stw %r12, 536(%r4)
	lis %r12, 42
	ori %r12, %r12, 20088
	stw %r12, 540(%r4)
	lis %r12, 18
	ori %r12, %r12, 2595
	stw %r12, 544(%r4)
	lis %r12, 1
	ori %r12, %r12, 21672
	stw %r12, 548(%r4)
	lis %r12, 9
	ori %r12, %r12, 47103
	stw %r12, 552(%r4)
	lis %r12, 67
	ori %r12, %r12, 24199
	stw %r12, 556(%r4)
	lis %r12, 67
	ori %r12, %r12, 32760
	stw %r12, 560(%r4)
	lis %r12, 92
	ori %r12, %r12, 54708
	stw %r12, 564(%r4)
	lis %r12, 77
	ori %r12, %r12, 49230
	stw %r12, 568(%r4)
	lis %r12, 71
	ori %r12, %r12, 10415
	stw %r12, 572(%r4)
	lis %r12, 127
	ori %r12, %r12, 29533
	stw %r12, 576(%r4)
	lis %r12, 12
	ori %r12, %r12, 36109
	stw %r12, 580(%r4)
	lis %r12, 15
	ori %r12, %r12, 26325
	stw %r12, 584(%r4)
	lis %r12, 90
	ori %r12, %r12, 28032
	stw %r12, 588(%r4)
	lis %r12, 97
	ori %r12, %r12, 43928
	stw %r12, 592(%r4)
	lis %r12, 24
	ori %r12, %r12, 23958
	stw %r12, 596(%r4)
	lis %r12, 67
	ori %r12, %r12, 32561
	stw %r12, 600(%r4)
	lis %r12, 70
	ori %r12, %r12, 33432
	stw %r12, 604(%r4)
	lis %r12, 102
	ori %r12, %r12, 10592
	stw %r12, 608(%r4)
	lis %r12, 75
	ori %r12, %r12, 54649
	stw %r12, 612(%r4)
	lis %r12, 40
	ori %r12, %r12, 56838
	stw %r12, 616(%r4)
	lis %r12, 70
	ori %r12, %r12, 23949
	stw %r12, 620(%r4)
	lis %r12, 73
	ori %r12, %r12, 45283
	stw %r12, 624(%r4)
	lis %r12, 9
	ori %r12, %r12, 46132
	stw %r12, 628(%r4)
	lis %r12, 124
	ori %r12, %r12, 3507
	stw %r12, 632(%r4)
	lis %r12, 90
	ori %r12, %r12, 26800
	stw %r12, 636(%r4)
	lis %r12, 64
	ori %r12, %r12, 39849
	stw %r12, 640(%r4)
	lis %r12, 100
	ori %r12, %r12, 54229
	stw %r12, 644(%r4)
	lis %r12, 33
	ori %r12, %r12, 30250
	stw %r12, 648(%r4)
	lis %r12, 101
	ori %r12, %r12, 34193
	stw %r12, 652(%r4)
	lis %r12, 36
	ori %r12, %r12, 28217
	stw %r12, 656(%r4)
	lis %r12, 72
	ori %r12, %r12, 50075
	stw %r12, 660(%r4)
	lis %r12, 123
	ori %r12, %r12, 51033
	stw %r12, 664(%r4)
	lis %r12, 79
	ori %r12, %r12, 22617
	stw %r12, 668(%r4)
	lis %r12, 57
	ori %r12, %r12, 11698
	stw %r12, 672(%r4)
	lis %r12, 35
	ori %r12, %r12, 2339
	stw %r12, 676(%r4)
	lis %r12, 18
	ori %r12, %r12, 60263
	stw %r12, 680(%r4)
	lis %r12, 69
	ori %r12, %r12, 19954
	stw %r12, 684(%r4)
	lis %r12, 48
	ori %r12, %r12, 49948
	stw %r12, 688(%r4)
	lis %r12, 40
	ori %r12, %r12, 21540
	stw %r12, 692(%r4)
	lis %r12, 19
	ori %r12, %r12, 9006
	stw %r12, 696(%r4)
	lis %r12, 127
	ori %r12, %r12, 44928
	stw %r12, 700(%r4)
	lis %r12, 45
	ori %r12, %r12, 49099
	stw %r12, 704(%r4)
	lis %r12, 2
	ori %r12, %r12, 10763
	stw %r12, 708(%r4)
	lis %r12, 126
	ori %r12, %r12, 33580
	stw %r12, 712(%r4)
	lis %r12, 38
	ori %r12, %r12, 22650
	stw %r12, 716(%r4)
	lis %r12, 107
	ori %r12, %r12, 13173
	stw %r12, 720(%r4)
	lis %r12, 9
	ori %r12, %r12, 23414
	stw %r12, 724(%r4)
	lis %r12, 107
	ori %r12, %r12, 57804
	stw %r12, 728(%r4)
	lis %r12, 94
	ori %r12, %r12, 1566
	stw %r12, 732(%r4)
	lis %r12, 120
	ori %r12, %r12, 57357
	stw %r12, 736(%r4)
	lis %r12, 98
	ori %r12, %r12, 35895
	stw %r12, 740(%r4)
	lis %r12, 61
	ori %r12, %r12, 42500
	stw %r12, 744(%r4)
	lis %r12, 74
	ori %r12, %r12, 58684
	stw %r12, 748(%r4)
	lis %r12, 31
	ori %r12, %r12, 7528
	stw %r12, 752(%r4)
	lis %r12, 99
	ori %r12, %r12, 12475
	stw %r12, 756(%r4)
	lis %r12, 115
	ori %r12, %r12, 25016
	stw %r12, 760(%r4)
	lis %r12, 94
	ori %r12, %r12, 41068
	stw %r12, 764(%r4)
	lis %r12, 103
	ori %r12, %r12, 6855
	stw %r12, 768(%r4)
	lis %r12, 32
	ori %r12, %r12, 8134
	stw %r12, 772(%r4)
	lis %r12, 91
	ori %r12, %r12, 42239
	stw %r12, 776(%r4)
	lis %r12, 96
	ori %r12, %r12, 55154
	stw %r12, 780(%r4)
	lis %r12, 8
	ori %r12, %r12, 61953
	stw %r12, 784(%r4)
	lis %r12, 109
	ori %r12, %r12, 57380
	stw %r12, 788(%r4)
	lis %r12, 8
	ori %r12, %r12, 3693
	stw %r12, 792(%r4)
	lis %r12, 86
	ori %r12, %r12, 910
	stw %r12, 796(%r4)
	lis %r12, 105
	ori %r12, %r12, 22152
	stw %r12, 800(%r4)
	lis %r12, 30
	ori %r12, %r12, 27966
	stw %r12, 804(%r4)
	lis %r12, 38
	ori %r12, %r12, 957
	stw %r12, 808(%r4)
	lis %r12, 106
	ori %r12, %r12, 40442
	stw %r12, 812(%r4)
	lis %r12, 7
	ori %r12, %r12, 49175
	stw %r12, 816(%r4)
	lis %r12, 109
	ori %r12, %r12, 49108
	stw %r12, 820(%r4)
	lis %r12, 116
	ori %r12, %r12, 53437
	stw %r12, 824(%r4)
	lis %r12, 99
	ori %r12, %r12, 57827
	stw %r12, 828(%r4)
	lis %r12, 81
	ori %r12, %r12, 38259
	stw %r12, 832(%r4)
	lis %r12, 122
	ori %r12, %r12, 46605
	stw %r12, 836(%r4)
	lis %r12, 40
	ori %r12, %r12, 26554
	stw %r12, 840(%r4)
	lis %r12, 45
	ori %r12, %r12, 60628
	stw %r12, 844(%r4)
	lis %r12, 88
	ori %r12, %r12, 396
	stw %r12, 848(%r4)
	lis %r12, 63
	ori %r12, %r12, 19701
	stw %r12, 852(%r4)
	lis %r12, 11
	ori %r12, %r12, 28681
	stw %r12, 856(%r4)
	lis %r12, 66
	ori %r12, %r12, 32291
	stw %r12, 860(%r4)
	lis %r12, 60
	ori %r12, %r12, 48439
	stw %r12, 864(%r4)
	lis %r12, 39
	ori %r12, %r12, 13107
	stw %r12, 868(%r4)
	lis %r12, 103
	ori %r12, %r12, 14679
	stw %r12, 872(%r4)
	lis %r12, 26
	ori %r12, %r12, 19293
	stw %r12, 876(%r4)
	lis %r12, 25
	ori %r12, %r12, 26918
	stw %r12, 880(%r4)
	lis %r12, 30
	ori %r12, %r12, 61958
	stw %r12, 884(%r4)
	lis %r12, 17
	ori %r12, %r12, 49486
	stw %r12, 888(%r4)
	lis %r12, 76
	ori %r12, %r12, 30408
	stw %r12, 892(%r4)
	lis %r12, 60
	ori %r12, %r12, 62511
	stw %r12, 896(%r4)
	lis %r12, 127
	ori %r12, %r12, 45466
	stw %r12, 900(%r4)
	lis %r12, 106
	ori %r12, %r12, 63084
	stw %r12, 904(%r4)
	lis %r12, 46
	ori %r12, %r12, 5737
	stw %r12, 908(%r4)
	lis %r12, 51
	ori %r12, %r12, 21206
	stw %r12, 912(%r4)
	lis %r12, 3
	ori %r12, %r12, 18272
	stw %r12, 916(%r4)
	lis %r12, 8
	ori %r12, %r12, 21088
	stw %r12, 920(%r4)
	lis %r12, 116
	ori %r12, %r12, 7800
	stw %r12, 924(%r4)
	lis %r12, 47
	ori %r12, %r12, 25366
	stw %r12, 928(%r4)
	lis %r12, 111
	ori %r12, %r12, 2577
	stw %r12, 932(%r4)
	lis %r12, 7
	ori %r12, %r12, 49393
	stw %r12, 936(%r4)
	lis %r12, 119
	ori %r12, %r12, 27915
	stw %r12, 940(%r4)
	lis %r12, 13
	ori %r12, %r12, 8176
	stw %r12, 944(%r4)
	lis %r12, 52
	ori %r12, %r12, 22564
	stw %r12, 948(%r4)
	lis %r12, 2
	ori %r12, %r12, 9172
	stw %r12, 952(%r4)
	lis %r12, 104
	ori %r12, %r12, 50521
	stw %r12, 956(%r4)
	lis %r12, 94
	ori %r12, %r12, 34949
	stw %r12, 960(%r4)
	lis %r12, 47
	ori %r12, %r12, 43570
	stw %r12, 964(%r4)
	lis %r12, 35
	ori %r12, %r12, 64613
	stw %r12, 968(%r4)
	lis %r12, 94
	ori %r12, %r12, 26946
	stw %r12, 972(%r4)
	lis %r12, 81
	ori %r12, %r12, 57581
	stw %r12, 976(%r4)
	lis %r12, 101
	ori %r12, %r12, 44467
	stw %r12, 980(%r4)
	lis %r12, 44
	ori %r12, %r12, 42470
	stw %r12, 984(%r4)
	lis %r12, 121
	ori %r12, %r12, 57854
	stw %r12, 988(%r4)
	lis %r12, 123
	ori %r12, %r12, 16484
	stw %r12, 992(%r4)
	lis %r12, 53
	ori %r12, %r12, 57821
	stw %r12, 996(%r4)
	lis %r12, 67
	ori %r12, %r12, 15020
	stw %r12, 1000(%r4)
	lis %r12, 70
	ori %r12, %r12, 19166
	stw %r12, 1004(%r4)
	lis %r12, 28
	ori %r12, %r12, 65044
	stw %r12, 1008(%r4)
	lis %r12, 115
	ori %r12, %r12, 61902
	stw %r12, 1012(%r4)
	lis %r12, 16
	ori %r12, %r12, 5902
	stw %r12, 1016(%r4)
	lis %r12, 116
	ori %r12, %r12, 46807
	stw %r12, 1020(%r4)
	lis %r8, 512
	ori %r8, %r8, 32796
	rldicr %r8, %r8, 16, 47
	ori %r8, %r8, 1537
	lis %r9, 127
	ori %r9, %r9, 57345
	addi %r3, %r3, 1024
	addi %r4, %r4, 4
	li %r10, 512
20:
	addi %r5, %r3, -1024
21:
	lwz %r7, 0(%r4)
	addi %r4, %r4, 4
	add %r6, %r5, %r10
	rldicl %r11, %r10, 62, 2
22:
	lwz %r12, 0(%r5)
	lwz %r0, 0(%r6)
	mulld %r0, %r7, %r0
	mulhdu %r14, %r0, %r8
	mulld %r14, %r14, %r9
	subf %r0, %r14, %r0
	subf %r0, %r9, %r0
	rldicl %r14, %r0, 1, 63
	mulld %r14, %r14, %r9
	add %r0, %r0, %r14
	subf %r14, %r0, %r12
	rldicl %r15, %r14, 1, 63
	mulld %r15, %r15, %r9
	add %r14, %r14, %r15
	stw %r14, 0(%r6)
	add %r12, %r12, %r0
	subf %r12, %r9, %r12
	rldicl %r15, %r12, 1, 63
	mulld %r15, %r15, %r9
	add %r12, %r12, %r15
	stw %r12, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	addi %r5, %r6, 0
	subf %r0, %r3, %r5
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	rldicl %r10, %r10, 63, 1
	addi %r0, %r10, -2
	cmpldi %cr0, %r0, 0
	bne %cr0, 20b
	ld %r15, 32(%r1)
	addi %r1, %r1, 48
	ld %r14, 32(%r1)
	addi %r1, %r1, 48
	blr

vg_mldsa_inv_ntt:
	stdu %r1, -48(%r1)
	std %r14, 32(%r1)
	stdu %r1, -48(%r1)
	std %r15, 32(%r1)
	lis %r12, 127
	ori %r12, %r12, 57344
	stw %r12, 0(%r4)
	lis %r12, 54
	ori %r12, %r12, 33279
	stw %r12, 4(%r4)
	lis %r12, 70
	ori %r12, %r12, 27290
	stw %r12, 8(%r4)
	lis %r12, 70
	ori %r12, %r12, 31384
	stw %r12, 12(%r4)
	lis %r12, 48
	ori %r12, %r12, 55766
	stw %r12, 16(%r4)
	lis %r12, 44
	ori %r12, %r12, 142
	stw %r12, 20(%r4)
	lis %r12, 47
	ori %r12, %r12, 65486
	stw %r12, 24(%r4)
	lis %r12, 48
	ori %r12, %r12, 55702
	stw %r12, 28(%r4)
	lis %r12, 9
	ori %r12, %r12, 11859
	stw %r12, 32(%r4)
	lis %r12, 73
	ori %r12, %r12, 53804
	stw %r12, 36(%r4)
	lis %r12, 86
	ori %r12, %r12, 62033
	stw %r12, 40(%r4)
	lis %r12, 95
	ori %r12, %r12, 24605
	stw %r12, 44(%r4)
	lis %r12, 70
	ori %r12, %r12, 28030
	stw %r12, 48(%r4)
	lis %r12, 15
	ori %r12, %r12, 22199
	stw %r12, 52(%r4)
	lis %r12, 119
	ori %r12, %r12, 24175
	stw %r12, 56(%r4)
	lis %r12, 18
	ori %r12, %r12, 41529
	stw %r12, 60(%r4)
	lis %r12, 51
	ori %r12, %r12, 28013
	stw %r12, 64(%r4)
	lis %r12, 61
	ori %r12, %r12, 65357
	stw %r12, 68(%r4)
	lis %r12, 87
	ori %r12, %r12, 15407
	stw %r12, 72(%r4)
	lis %r12, 25
	ori %r12, %r12, 36215
	stw %r12, 76(%r4)
	lis %r12, 53
	ori %r12, %r12, 51034
	stw %r12, 80(%r4)
	lis %r12, 6
	ori %r12, %r12, 40909
	stw %r12, 84(%r4)
	lis %r12, 117
	ori %r12, %r12, 36115
	stw %r12, 88(%r4)
	lis %r12, 20
	ori %r12, %r12, 25216
	stw %r12, 92(%r4)
	lis %r12, 49
	ori %r12, %r12, 16612
	stw %r12, 96(%r4)
	lis %r12, 101
	ori %r12, %r12, 46986
	stw %r12, 100(%r4)
	lis %r12, 90
	ori %r12, %r12, 28194
	stw %r12, 104(%r4)
	lis %r12, 105
	ori %r12, %r12, 38419
	stw %r12, 108(%r4)
	lis %r12, 9
	ori %r12, %r12, 52804
	stw %r12, 112(%r4)
	lis %r12, 54
	ori %r12, %r12, 46154
	stw %r12, 116(%r4)
	lis %r12, 84
	ori %r12, %r12, 59754
	stw %r12, 120(%r4)
	lis %r12, 93
	ori %r12, %r12, 1836
	stw %r12, 124(%r4)
	lis %r12, 72
	ori %r12, %r12, 59607
	stw %r12, 128(%r4)
	lis %r12, 79
	ori %r12, %r12, 20195
	stw %r12, 132(%r4)
	lis %r12, 86
	ori %r12, %r12, 3778
	stw %r12, 136(%r4)
	lis %r12, 54
	ori %r12, %r12, 47502
	stw %r12, 140(%r4)
	lis %r12, 47
	ori %r12, %r12, 30626
	stw %r12, 144(%r4)
	lis %r12, 95
	ori %r12, %r12, 53087
	stw %r12, 148(%r4)
	lis %r12, 71
	ori %r12, %r12, 22538
	stw %r12, 152(%r4)
	lis %r12, 110
	ori %r12, %r12, 11582
	stw %r12, 156(%r4)
	lis %r12, 121
	ori %r12, %r12, 56413
	stw %r12, 160(%r4)
	lis %r12, 113
	ori %r12, %r12, 46100
	stw %r12, 164(%r4)
	lis %r12, 111
	ori %r12, %r12, 10453
	stw %r12, 168(%r4)
	lis %r12, 53
	ori %r12, %r12, 32972
	stw %r12, 172(%r4)
	lis %r12, 96
	ori %r12, %r12, 17132
	stw %r12, 176(%r4)
	lis %r12, 61
	ori %r12, %r12, 21293
	stw %r12, 180(%r4)
	lis %r12, 78
	ori %r12, %r12, 26637
	stw %r12, 184(%r4)
	lis %r12, 94
	ori %r12, %r12, 63983
	stw %r12, 188(%r4)
	lis %r12, 75
	ori %r12, %r12, 50148
	stw %r12, 192(%r4)
	lis %r12, 101
	ori %r12, %r12, 1934
	stw %r12, 196(%r4)
	lis %r12, 12
	ori %r12, %r12, 31104
	stw %r12, 200(%r4)
	lis %r12, 54
	ori %r12, %r12, 35522
	stw %r12, 204(%r4)
	lis %r12, 70
	ori %r12, %r12, 36107
	stw %r12, 208(%r4)
	lis %r12, 29
	ori %r12, %r12, 35255
	stw %r12, 212(%r4)
	lis %r12, 26
	ori %r12, %r12, 13052
	stw %r12, 216(%r4)
	lis %r12, 60
	ori %r12, %r12, 17893
	stw %r12, 220(%r4)
	lis %r12, 44
	ori %r12, %r12, 13730
	stw %r12, 224(%r4)
	lis %r12, 79
	ori %r12, %r12, 10719
	stw %r12, 228(%r4)
	lis %r12, 119
	ori %r12, %r12, 24777
	stw %r12, 232(%r4)
	lis %r12, 68
	ori %r12, %r12, 53652
	stw %r12, 236(%r4)
	lis %r12, 83
	ori %r12, %r12, 23591
	stw %r12, 240(%r4)
	lis %r12, 99
	ori %r12, %r12, 38547
	stw %r12, 244(%r4)
	lis %r12, 76
	ori %r12, %r12, 53718
	stw %r12, 248(%r4)
	lis %r12, 99
	ori %r12, %r12, 33937
	stw %r12, 252(%r4)
	lis %r12, 80
	ori %r12, %r12, 64528
	stw %r12, 256(%r4)
	lis %r12, 108
	ori %r12, %r12, 24904
	stw %r12, 260(%r4)
	lis %r12, 40
	ori %r12, %r12, 14033
	stw %r12, 264(%r4)
	lis %r12, 69
	ori %r12, %r12, 6418
	stw %r12, 268(%r4)
	lis %r12, 64
	ori %r12, %r12, 2741
	stw %r12, 272(%r4)
	lis %r12, 49
	ori %r12, %r12, 11543
	stw %r12, 276(%r4)
	lis %r12, 47
	ori %r12, %r12, 41248
	stw %r12, 280(%r4)
	lis %r12, 4
	ori %r12, %r12, 11916
	stw %r12, 284(%r4)
	lis %r12, 89
	ori %r12, %r12, 38733
	stw %r12, 288(%r4)
	lis %r12, 96
	ori %r12, %r12, 60843
	stw %r12, 292(%r4)
	lis %r12, 98
	ori %r12, %r12, 20319
	stw %r12, 296(%r4)
	lis %r12, 58
	ori %r12, %r12, 14637
	stw %r12, 300(%r4)
	lis %r12, 84
	ori %r12, %r12, 64102
	stw %r12, 304(%r4)
	lis %r12, 45
	ori %r12, %r12, 34661
	stw %r12, 308(%r4)
	lis %r12, 16
	ori %r12, %r12, 60940
	stw %r12, 312(%r4)
	lis %r12, 64
	ori %r12, %r12, 28025
	stw %r12, 316(%r4)
	lis %r12, 104
	ori %r12, %r12, 36607
	stw %r12, 320(%r4)
	lis %r12, 120
	ori %r12, %r12, 33448
	stw %r12, 324(%r4)
	lis %r12, 110
	ori %r12, %r12, 22599
	stw %r12, 328(%r4)
	lis %r12, 45
	ori %r12, %r12, 13144
	stw %r12, 332(%r4)
	lis %r12, 8
	ori %r12, %r12, 41315
	stw %r12, 336(%r4)
	lis %r12, 125
	ori %r12, %r12, 18729
	stw %r12, 340(%r4)
	lis %r12, 90
	ori %r12, %r12, 19733
	stw %r12, 344(%r4)
	lis %r12, 50
	ori %r12, %r12, 57583
	stw %r12, 348(%r4)
	lis %r12, 63
	ori %r12, %r12, 37657
	stw %r12, 352(%r4)
	lis %r12, 53
	ori %r12, %r12, 14975
	stw %r12, 356(%r4)
	lis %r12, 97
	ori %r12, %r12, 35611
	stw %r12, 360(%r4)
	lis %r12, 48
	ori %r12, %r12, 51520
	stw %r12, 364(%r4)
	lis %r12, 101
	ori %r12, %r12, 24968
	stw %r12, 368(%r4)
	lis %r12, 124
	ori %r12, %r12, 18546
	stw %r12, 372(%r4)
	lis %r12, 49
	ori %r12, %r12, 38890
	stw %r12, 376(%r4)
	lis %r12, 78
	ori %r12, %r12, 10152
	stw %r12, 380(%r4)
	lis %r12, 39
	ori %r12, %r12, 23349
	stw %r12, 384(%r4)
	lis %r12, 100
	ori %r12, %r12, 38874
	stw %r12, 388(%r4)
	lis %r12, 36
	ori %r12, %r12, 31793
	stw %r12, 392(%r4)
	lis %r12, 34
	ori %r12, %r12, 26503
	stw %r12, 396(%r4)
	lis %r12, 74
	ori %r12, %r12, 48547
	stw %r12, 400(%r4)
	lis %r12, 63
	ori %r12, %r12, 54147
	stw %r12, 404(%r4)
	lis %r12, 19
	ori %r12, %r12, 54832
	stw %r12, 408(%r4)
	lis %r12, 36
	ori %r12, %r12, 2767
	stw %r12, 412(%r4)
	lis %r12, 20
	ori %r12, %r12, 6958
	stw %r12, 416(%r4)
	lis %r12, 90
	ori %r12, %r12, 20790
	stw %r12, 420(%r4)
	lis %r12, 81
	ori %r12, %r12, 36021
	stw %r12, 424(%r4)
	lis %r12, 118
	ori %r12, %r12, 26005
	stw %r12, 428(%r4)
	lis %r12, 68
	ori %r12, %r12, 22497
	stw %r12, 432(%r4)
	lis %r12, 18
	ori %r12, %r12, 47013
	stw %r12, 436(%r4)
	lis %r12, 83
	ori %r12, %r12, 15113
	stw %r12, 440(%r4)
	lis %r12, 76
	ori %r12, %r12, 25431
	stw %r12, 444(%r4)
	lis %r12, 107
	ori %r12, %r12, 11617
	stw %r12, 448(%r4)
	lis %r12, 42
	ori %r12, %r12, 23243
	stw %r12, 452(%r4)
	lis %r12, 86
	ori %r12, %r12, 61051
	stw %r12, 456(%r4)
	lis %r12, 42
	ori %r12, %r12, 26276
	stw %r12, 460(%r4)
	lis %r12, 52
	ori %r12, %r12, 59793
	stw %r12, 464(%r4)
	lis %r12, 92
	ori %r12, %r12, 38267
	stw %r12, 468(%r4)
	lis %r12, 9
	ori %r12, %r12, 63451
	stw %r12, 472(%r4)
	lis %r12, 7
	ori %r12, %r12, 411
	stw %r12, 476(%r4)
	lis %r12, 122
	ori %r12, %r12, 36213
	stw %r12, 480(%r4)
	lis %r12, 5
	ori %r12, %r12, 168
	stw %r12, 484(%r4)
	lis %r12, 112
	ori %r12, %r12, 29162
	stw %r12, 488(%r4)
	lis %r12, 35
	ori %r12, %r12, 60455
	stw %r12, 492(%r4)
	lis %r12, 58
	ori %r12, %r12, 17539
	stw %r12, 496(%r4)
	lis %r12, 29
	ori %r12, %r12, 21709
	stw %r12, 500(%r4)
	lis %r12, 34
	ori %r12, %r12, 8502
	stw %r12, 504(%r4)
	lis %r12, 101
	ori %r12, %r12, 16774
	stw %r12, 508(%r4)
	lis %r12, 127
	ori %r12, %r12, 55592
	stw %r12, 512(%r4)
	lis %r12, 29
	ori %r12, %r12, 34876
	stw %r12, 516(%r4)
	lis %r12, 40
	ori %r12, %r12, 38085
	stw %r12, 520(%r4)
	lis %r12, 22
	ori %r12, %r12, 14098
	stw %r12, 524(%r4)
	lis %r12, 87
	ori %r12, %r12, 18377
	stw %r12, 528(%r4)
	lis %r12, 27
	ori %r12, %r12, 10755
	stw %r12, 532(%r4)
	lis %r12, 0
	ori %r12, %r12, 59148
	stw %r12, 536(%r4)
	lis %r12, 85
	ori %r12, %r12, 37257
	stw %r12, 540(%r4)
	lis %r12, 109
	ori %r12, %r12, 54750
	stw %r12, 544(%r4)
	lis %r12, 126
	ori %r12, %r12, 35673
	stw %r12, 548(%r4)
	lis %r12, 118
	ori %r12, %r12, 10242
	stw %r12, 552(%r4)
	lis %r12, 60
	ori %r12, %r12, 33146
	stw %r12, 556(%r4)
	lis %r12, 60
	ori %r12, %r12, 24585
	stw %r12, 560(%r4)
	lis %r12, 35
	ori %r12, %r12, 2637
	stw %r12, 564(%r4)
	lis %r12, 50
	ori %r12, %r12, 8115
	stw %r12, 568(%r4)
	lis %r12, 56
	ori %r12, %r12, 46930
	stw %r12, 572(%r4)
	lis %r12, 0
	ori %r12, %r12, 27812
	stw %r12, 576(%r4)
	lis %r12, 115
	ori %r12, %r12, 21236
	stw %r12, 580(%r4)
	lis %r12, 112
	ori %r12, %r12, 31020
	stw %r12, 584(%r4)
	lis %r12, 37
	ori %r12, %r12, 29313
	stw %r12, 588(%r4)
	lis %r12, 30
	ori %r12, %r12, 13417
	stw %r12, 592(%r4)
	lis %r12, 103
	ori %r12, %r12, 33387
	stw %r12, 596(%r4)
	lis %r12, 60
	ori %r12, %r12, 24784
	stw %r12, 600(%r4)
	lis %r12, 57
	ori %r12, %r12, 23913
	stw %r12, 604(%r4)
	lis %r12, 25
	ori %r12, %r12, 46753
	stw %r12, 608(%r4)
	lis %r12, 52
	ori %r12, %r12, 2696
	stw %r12, 612(%r4)
	lis %r12, 87
	ori %r12, %r12, 507
	stw %r12, 616(%r4)
	lis %r12, 57
	ori %r12, %r12, 33396
	stw %r12, 620(%r4)
	lis %r12, 54
	ori %r12, %r12, 12062
	stw %r12, 624(%r4)
	lis %r12, 118
	ori %r12, %r12, 11213
	stw %r12, 628(%r4)
	lis %r12, 3
	ori %r12, %r12, 53838
	stw %r12, 632(%r4)
	lis %r12, 37
	ori %r12, %r12, 30545
	stw %r12, 636(%r4)
	lis %r12, 63
	ori %r12, %r12, 17496
	stw %r12, 640(%r4)
	lis %r12, 27
	ori %r12, %r12, 3116
	stw %r12, 644(%r4)
	lis %r12, 94
	ori %r12, %r12, 27095
	stw %r12, 648(%r4)
	lis %r12, 26
	ori %r12, %r12, 23152
	stw %r12, 652(%r4)
	lis %r12, 91
	ori %r12, %r12, 29128
	stw %r12, 656(%r4)
	lis %r12, 55
	ori %r12, %r12, 7270
	stw %r12, 660(%r4)
	lis %r12, 4
	ori %r12, %r12, 6312
	stw %r12, 664(%r4)
	lis %r12, 48
	ori %r12, %r12, 34728
	stw %r12, 668(%r4)
	lis %r12, 70
	ori %r12, %r12, 45647
	stw %r12, 672(%r4)
	lis %r12, 92
	ori %r12, %r12, 55006
	stw %r12, 676(%r4)
	lis %r12, 108
	ori %r12, %r12, 62618
	stw %r12, 680(%r4)
	lis %r12, 58
	ori %r12, %r12, 37391
	stw %r12, 684(%r4)
	lis %r12, 79
	ori %r12, %r12, 7397
	stw %r12, 688(%r4)
	lis %r12, 87
	ori %r12, %r12, 35805
	stw %r12, 692(%r4)
	lis %r12, 108
	ori %r12, %r12, 48339
	stw %r12, 696(%r4)
	lis %r12, 0
	ori %r12, %r12, 12417
	stw %r12, 700(%r4)
	lis %r12, 82
	ori %r12, %r12, 8246
	stw %r12, 704(%r4)
	lis %r12, 125
	ori %r12, %r12, 46582
	stw %r12, 708(%r4)
	lis %r12, 1
	ori %r12, %r12, 23765
	stw %r12, 712(%r4)
	lis %r12, 89
	ori %r12, %r12, 34695
	stw %r12, 716(%r4)
	lis %r12, 20
	ori %r12, %r12, 44172
	stw %r12, 720(%r4)
	lis %r12, 118
	ori %r12, %r12, 33931
	stw %r12, 724(%r4)
	lis %r12, 19
	ori %r12, %r12, 65077
	stw %r12, 728(%r4)
	lis %r12, 33
	ori %r12, %r12, 55779
	stw %r12, 732(%r4)
	lis %r12, 6
	ori %r12, %r12, 65524
	stw %r12, 736(%r4)
	lis %r12, 29
	ori %r12, %r12, 21450
	stw %r12, 740(%r4)
	lis %r12, 66
	ori %r12, %r12, 14845
	stw %r12, 744(%r4)
	lis %r12, 52
	ori %r12, %r12, 64197
	stw %r12, 748(%r4)
	lis %r12, 96
	ori %r12, %r12, 49817
	stw %r12, 752(%r4)
	lis %r12, 28
	ori %r12, %r12, 44870
	stw %r12, 756(%r4)
	lis %r12, 12
	ori %r12, %r12, 32329
	stw %r12, 760(%r4)
	lis %r12, 33
	ori %r12, %r12, 16277
	stw %r12, 764(%r4)
	lis %r12, 24
	ori %r12, %r12, 50490
	stw %r12, 768(%r4)
	lis %r12, 95
	ori %r12, %r12, 49211
	stw %r12, 772(%r4)
	lis %r12, 36
	ori %r12, %r12, 15106
	stw %r12, 776(%r4)
	lis %r12, 31
	ori %r12, %r12, 2191
	stw %r12, 780(%r4)
	lis %r12, 118
	ori %r12, %r12, 60928
	stw %r12, 784(%r4)
	lis %r12, 17
	ori %r12, %r12, 65501
	stw %r12, 788(%r4)
	lis %r12, 119
	ori %r12, %r12, 53652
	stw %r12, 792(%r4)
	lis %r12, 41
	ori %r12, %r12, 56435
	stw %r12, 796(%r4)
	lis %r12, 22
	ori %r12, %r12, 35193
	stw %r12, 800(%r4)
	lis %r12, 97
	ori %r12, %r12, 29379
	stw %r12, 804(%r4)
	lis %r12, 89
	ori %r12, %r12, 56388
	stw %r12, 808(%r4)
	lis %r12, 21
	ori %r12, %r12, 16903
	stw %r12, 812(%r4)
	lis %r12, 120
	ori %r12, %r12, 8170
	stw %r12, 816(%r4)
	lis %r12, 18
	ori %r12, %r12, 8237
	stw %r12, 820(%r4)
	lis %r12, 11
	ori %r12, %r12, 3908
	stw %r12, 824(%r4)
	lis %r12, 27
	ori %r12, %r12, 65054
	stw %r12, 828(%r4)
	lis %r12, 46
	ori %r12, %r12, 19086
	stw %r12, 832(%r4)
	lis %r12, 5
	ori %r12, %r12, 10740
	stw %r12, 836(%r4)
	lis %r12, 87
	ori %r12, %r12, 30791
	stw %r12, 840(%r4)
	lis %r12, 81
	ori %r12, %r12, 62253
	stw %r12, 844(%r4)
	lis %r12, 39
	ori %r12, %r12, 56949
	stw %r12, 848(%r4)
	lis %r12, 64
	ori %r12, %r12, 37644
	stw %r12, 852(%r4)
	lis %r12, 116
	ori %r12, %r12, 28664
	stw %r12, 856(%r4)
	lis %r12, 61
	ori %r12, %r12, 25054
	stw %r12, 860(%r4)
	lis %r12, 67
	ori %r12, %r12, 8906
	stw %r12, 864(%r4)
	lis %r12, 88
	ori %r12, %r12, 44238
	stw %r12, 868(%r4)
	lis %r12, 24
	ori %r12, %r12, 42666
	stw %r12, 872(%r4)
	lis %r12, 101
	ori %r12, %r12, 38052
	stw %r12, 876(%r4)
	lis %r12, 102
	ori %r12, %r12, 30427
	stw %r12, 880(%r4)
	lis %r12, 96
	ori %r12, %r12, 60923
	stw %r12, 884(%r4)
	lis %r12, 110
	ori %r12, %r12, 7859
	stw %r12, 888(%r4)
	lis %r12, 51
	ori %r12, %r12, 26937
	stw %r12, 892(%r4)
	lis %r12, 66
	ori %r12, %r12, 60370
	stw %r12, 896(%r4)
	lis %r12, 0
	ori %r12, %r12, 11879
	stw %r12, 900(%r4)
	lis %r12, 20
	ori %r12, %r12, 59797
	stw %r12, 904(%r4)
	lis %r12, 81
	ori %r12, %r12, 51608
	stw %r12, 908(%r4)
	lis %r12, 76
	ori %r12, %r12, 36139
	stw %r12, 912(%r4)
	lis %r12, 124
	ori %r12, %r12, 39073
	stw %r12, 916(%r4)
	lis %r12, 119
	ori %r12, %r12, 36257
	stw %r12, 920(%r4)
	lis %r12, 11
	ori %r12, %r12, 49545
	stw %r12, 924(%r4)
	lis %r12, 80
	ori %r12, %r12, 31979
	stw %r12, 928(%r4)
	lis %r12, 16
	ori %r12, %r12, 54768
	stw %r12, 932(%r4)
	lis %r12, 120
	ori %r12, %r12, 7952
	stw %r12, 936(%r4)
	lis %r12, 8
	ori %r12, %r12, 29430
	stw %r12, 940(%r4)
	lis %r12, 114
	ori %r12, %r12, 49169
	stw %r12, 944(%r4)
	lis %r12, 75
	ori %r12, %r12, 34781
	stw %r12, 948(%r4)
	lis %r12, 125
	ori %r12, %r12, 48173
	stw %r12, 952(%r4)
	lis %r12, 23
	ori %r12, %r12, 6824
	stw %r12, 956(%r4)
	lis %r12, 33
	ori %r12, %r12, 22396
	stw %r12, 960(%r4)
	lis %r12, 80
	ori %r12, %r12, 13775
	stw %r12, 964(%r4)
	lis %r12, 91
	ori %r12, %r12, 58268
	stw %r12, 968(%r4)
	lis %r12, 33
	ori %r12, %r12, 30399
	stw %r12, 972(%r4)
	lis %r12, 45
	ori %r12, %r12, 65300
	stw %r12, 976(%r4)
	lis %r12, 26
	ori %r12, %r12, 12878
	stw %r12, 980(%r4)
	lis %r12, 83
	ori %r12, %r12, 14875
	stw %r12, 984(%r4)
	lis %r12, 5
	ori %r12, %r12, 65027
	stw %r12, 988(%r4)
	lis %r12, 4
	ori %r12, %r12, 40861
	stw %r12, 992(%r4)
	lis %r12, 73
	ori %r12, %r12, 65060
	stw %r12, 996(%r4)
	lis %r12, 60
	ori %r12, %r12, 42325
	stw %r12, 1000(%r4)
	lis %r12, 57
	ori %r12, %r12, 38179
	stw %r12, 1004(%r4)
	lis %r12, 98
	ori %r12, %r12, 57837
	stw %r12, 1008(%r4)
	lis %r12, 11
	ori %r12, %r12, 60979
	stw %r12, 1012(%r4)
	lis %r12, 111
	ori %r12, %r12, 51443
	stw %r12, 1016(%r4)
	lis %r12, 11
	ori %r12, %r12, 10538
	stw %r12, 1020(%r4)
	lis %r8, 512
	ori %r8, %r8, 32796
	rldicr %r8, %r8, 16, 47
	ori %r8, %r8, 1537
	lis %r9, 127
	ori %r9, %r9, 57345
	addi %r3, %r3, 1024
	addi %r4, %r4, 1020
	li %r10, 4
20:
	addi %r5, %r3, -1024
21:
	lwz %r7, 0(%r4)
	addi %r4, %r4, -4
	add %r6, %r5, %r10
	rldicl %r11, %r10, 62, 2
22:
	lwz %r12, 0(%r5)
	lwz %r0, 0(%r6)
	add %r14, %r12, %r0
	subf %r14, %r9, %r14
	rldicl %r15, %r14, 1, 63
	mulld %r15, %r15, %r9
	add %r14, %r14, %r15
	stw %r14, 0(%r5)
	subf %r0, %r0, %r12
	rldicl %r15, %r0, 1, 63
	mulld %r15, %r15, %r9
	add %r0, %r0, %r15
	mulld %r0, %r7, %r0
	mulhdu %r14, %r0, %r8
	mulld %r14, %r14, %r9
	subf %r0, %r14, %r0
	subf %r0, %r9, %r0
	rldicl %r14, %r0, 1, 63
	mulld %r14, %r14, %r9
	add %r0, %r0, %r14
	stw %r0, 0(%r6)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	addi %r5, %r6, 0
	subf %r0, %r3, %r5
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	rldicr %r10, %r10, 1, 62
	addi %r0, %r10, -1024
	cmpldi %cr0, %r0, 0
	bne %cr0, 20b
	lis %r7, 127
	ori %r7, %r7, 24609
	addi %r5, %r3, -1024
	li %r11, 256
23:
	lwz %r12, 0(%r5)
	mulld %r12, %r12, %r7
	mulhdu %r14, %r12, %r8
	mulld %r14, %r14, %r9
	subf %r12, %r14, %r12
	subf %r12, %r9, %r12
	rldicl %r14, %r12, 1, 63
	mulld %r14, %r14, %r9
	add %r12, %r12, %r14
	stw %r12, 0(%r5)
	addi %r5, %r5, 4
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	ld %r15, 32(%r1)
	addi %r1, %r1, 48
	ld %r14, 32(%r1)
	addi %r1, %r1, 48
	blr

vg_mldsa_multiply_ntt:
	lis %r8, 512
	ori %r8, %r8, 32796
	rldicr %r8, %r8, 16, 47
	ori %r8, %r8, 1537
	lis %r9, 127
	ori %r9, %r9, 57345
	li %r6, 256
20:
	lwz %r7, 0(%r4)
	lwz %r10, 0(%r5)
	mulld %r7, %r7, %r10
	mulhdu %r10, %r7, %r8
	mulld %r10, %r10, %r9
	subf %r7, %r10, %r7
	subf %r7, %r9, %r7
	rldicl %r10, %r7, 1, 63
	mulld %r10, %r10, %r9
	add %r7, %r7, %r10
	stw %r7, 0(%r3)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	blr

vg_mldsa_multiply_add_ntt:
	lis %r8, 512
	ori %r8, %r8, 32796
	rldicr %r8, %r8, 16, 47
	ori %r8, %r8, 1537
	lis %r9, 127
	ori %r9, %r9, 57345
	li %r6, 256
20:
	lwz %r7, 0(%r4)
	lwz %r10, 0(%r5)
	mulld %r7, %r7, %r10
	lwz %r10, 0(%r3)
	add %r7, %r7, %r10
	mulhdu %r10, %r7, %r8
	mulld %r10, %r10, %r9
	subf %r7, %r10, %r7
	subf %r7, %r9, %r7
	rldicl %r10, %r7, 1, 63
	mulld %r10, %r10, %r9
	add %r7, %r7, %r10
	stw %r7, 0(%r3)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	blr

vg_mldsa_add:
	li %r5, 256
	lis %r8, 127
	ori %r8, %r8, 57345
20:
	lwz %r6, 0(%r3)
	lwz %r7, 0(%r4)
	add %r6, %r6, %r7
	subf %r6, %r8, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 0(%r3)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr

vg_mldsa_sub:
	li %r5, 256
	lis %r8, 127
	ori %r8, %r8, 57345
20:
	lwz %r6, 0(%r3)
	lwz %r7, 0(%r4)
	subf %r6, %r7, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 0(%r3)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr

vg_mldsa_simple_bit_pack:
	addi %r10, %r3, 0
	addi %r11, %r5, 0
	li %r9, 15
	subf %r9, %r9, %r4
	cmplwi %cr0, %r9, 0
	beq %cr0, 20f
	li %r9, 43
	subf %r9, %r9, %r4
	cmplwi %cr0, %r9, 0
	beq %cr0, 22f
	li %r12, 64
24:
	li %r8, 0
	lwz %r9, 0(%r10)
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 4(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 8(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 3(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 4(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 16
	addi %r11, %r11, 5
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	b 23f
22:
	li %r12, 64
25:
	li %r8, 0
	lwz %r9, 0(%r10)
	add %r8, %r8, %r9
	lwz %r9, 4(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 8(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 16
	addi %r11, %r11, 3
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
23:
	b 21f
20:
	li %r12, 128
26:
	li %r8, 0
	lwz %r9, 0(%r10)
	add %r8, %r8, %r9
	lwz %r9, 4(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 8
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
21:
	blr

vg_mldsa_bit_pack:
	addi %r10, %r3, 0
	addi %r11, %r6, 0
	lis %r7, 127
	ori %r7, %r7, 57345
	li %r9, 2
	subf %r9, %r9, %r5
	cmplwi %cr0, %r9, 0
	beq %cr0, 20f
	li %r9, 4
	subf %r9, %r9, %r5
	cmplwi %cr0, %r9, 0
	beq %cr0, 22f
	li %r9, 4096
	subf %r9, %r9, %r5
	cmplwi %cr0, %r9, 0
	beq %cr0, 24f
	lis %r9, 2
	subf %r9, %r9, %r5
	cmplwi %cr0, %r9, 0
	beq %cr0, 26f
	lis %r4, 8
	li %r12, 128
28:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 3(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 4(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 8
	addi %r11, %r11, 5
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	b 27f
26:
	lis %r4, 2
	li %r12, 64
29:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 3(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 8(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 4(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 5(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 6(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 7(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 8(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 16
	addi %r11, %r11, 9
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 29b
27:
	b 25f
24:
	li %r4, 4096
	li %r12, 32
210:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 5, 58
	add %r8, %r8, %r9
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 8(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	stb %r8, 3(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 7, 56
	add %r8, %r8, %r9
	stb %r8, 4(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 5(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 16(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 6(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 7(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 20(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 1, 62
	add %r8, %r8, %r9
	stb %r8, 8(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 24(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 9(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 10(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 28(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 3, 60
	add %r8, %r8, %r9
	stb %r8, 11(%r11)
	rldicl %r8, %r8, 56, 8
	stb %r8, 12(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 32
	addi %r11, %r11, 13
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
25:
	b 23f
22:
	li %r4, 4
	li %r12, 128
211:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 8
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
23:
	b 21f
20:
	li %r4, 2
	li %r12, 32
212:
	li %r8, 0
	lwz %r9, 0(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	add %r8, %r8, %r9
	lwz %r9, 4(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 3, 60
	add %r8, %r8, %r9
	lwz %r9, 8(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	stb %r8, 0(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 12(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 1, 62
	add %r8, %r8, %r9
	lwz %r9, 16(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lwz %r9, 20(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 7, 56
	add %r8, %r8, %r9
	stb %r8, 1(%r11)
	rldicl %r8, %r8, 56, 8
	lwz %r9, 24(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	lwz %r9, 28(%r10)
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	rldicr %r9, %r9, 5, 58
	add %r8, %r8, %r9
	stb %r8, 2(%r11)
	rldicl %r8, %r8, 56, 8
	addi %r10, %r10, 32
	addi %r11, %r11, 3
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
21:
	blr

vg_mldsa_bit_unpack:
	addi %r10, %r3, 0
	addi %r11, %r7, 0
	lis %r7, 127
	ori %r7, %r7, 57345
	li %r9, 2
	subf %r9, %r9, %r6
	cmplwi %cr0, %r9, 0
	beq %cr0, 20f
	li %r9, 4
	subf %r9, %r9, %r6
	cmplwi %cr0, %r9, 0
	beq %cr0, 22f
	li %r9, 4096
	subf %r9, %r9, %r6
	cmplwi %cr0, %r9, 0
	beq %cr0, 24f
	lis %r9, 2
	subf %r9, %r9, %r6
	cmplwi %cr0, %r9, 0
	beq %cr0, 26f
	lis %r4, 8
	li %r12, 128
28:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 16, 47
	add %r8, %r8, %r9
	rldicr %r9, %r8, 44, 19
	rldicl %r9, %r9, 20, 44
	rldicl %r8, %r8, 44, 20
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 44, 19
	rldicl %r9, %r9, 20, 44
	rldicl %r8, %r8, 44, 20
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	addi %r10, %r10, 5
	addi %r11, %r11, 8
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	b 27f
26:
	lis %r4, 2
	li %r12, 64
29:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 16, 47
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 14, 49
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	lbz %r9, 5(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 6(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 8(%r11)
	lbz %r9, 7(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	lbz %r9, 8(%r10)
	rldicr %r9, %r9, 10, 53
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 12(%r11)
	addi %r10, %r10, 9
	addi %r11, %r11, 16
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 29b
27:
	b 25f
24:
	li %r4, 4096
	li %r12, 32
210:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 3, 60
	add %r8, %r8, %r9
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 11, 52
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 8(%r11)
	lbz %r9, 5(%r10)
	rldicr %r9, %r9, 1, 62
	add %r8, %r8, %r9
	lbz %r9, 6(%r10)
	rldicr %r9, %r9, 9, 54
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 12(%r11)
	lbz %r9, 7(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 8(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 16(%r11)
	lbz %r9, 9(%r10)
	rldicr %r9, %r9, 7, 56
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 20(%r11)
	lbz %r9, 10(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	lbz %r9, 11(%r10)
	rldicr %r9, %r9, 10, 53
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 24(%r11)
	lbz %r9, 12(%r10)
	rldicr %r9, %r9, 5, 58
	add %r8, %r8, %r9
	rldicr %r9, %r8, 51, 12
	rldicl %r9, %r9, 13, 51
	rldicl %r8, %r8, 51, 13
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 28(%r11)
	addi %r10, %r10, 13
	addi %r11, %r11, 32
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
25:
	b 23f
22:
	li %r4, 4
	li %r12, 128
211:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	rldicr %r9, %r8, 60, 3
	rldicl %r9, %r9, 4, 60
	rldicl %r8, %r8, 60, 4
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	rldicr %r9, %r8, 60, 3
	rldicl %r9, %r9, 4, 60
	rldicl %r8, %r8, 60, 4
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	addi %r10, %r10, 1
	addi %r11, %r11, 8
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
23:
	b 21f
20:
	li %r4, 2
	li %r12, 32
212:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 8(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 12(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 16(%r11)
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 1, 62
	add %r8, %r8, %r9
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 20(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 24(%r11)
	rldicr %r9, %r8, 61, 2
	rldicl %r9, %r9, 3, 61
	rldicl %r8, %r8, 61, 3
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 28(%r11)
	addi %r10, %r10, 3
	addi %r11, %r11, 32
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
21:
	blr

vg_mldsa_unpack_t1:
	addi %r10, %r3, 0
	addi %r11, %r4, 0
	li %r12, 64
20:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	rldicr %r9, %r8, 54, 9
	rldicl %r9, %r9, 10, 54
	rldicl %r8, %r8, 54, 10
	rldicr %r9, %r9, 13, 50
	stw %r9, 0(%r11)
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	rldicr %r9, %r8, 54, 9
	rldicl %r9, %r9, 10, 54
	rldicl %r8, %r8, 54, 10
	rldicr %r9, %r9, 13, 50
	stw %r9, 4(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	rldicr %r9, %r8, 54, 9
	rldicl %r9, %r9, 10, 54
	rldicl %r8, %r8, 54, 10
	rldicr %r9, %r9, 13, 50
	stw %r9, 8(%r11)
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	rldicr %r9, %r8, 54, 9
	rldicl %r9, %r9, 10, 54
	rldicl %r8, %r8, 54, 10
	rldicr %r9, %r9, 13, 50
	stw %r9, 12(%r11)
	addi %r10, %r10, 5
	addi %r11, %r11, 16
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	blr

vg_mldsa_hint_bit_pack:
	rldicr %r5, %r5, 32, 31
	rldicl %r5, %r5, 32, 32
	subf %r4, %r5, %r7
	addi %r9, %r7, 0
	li %r0, 0
	addi %r10, %r6, 0
20:
	stb %r0, 0(%r10)
	addi %r10, %r10, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 20b
	addi %r9, %r4, 0
	add %r10, %r6, %r5
	li %r11, 0
21:
	li %r12, 0
22:
	lwz %r8, 0(%r3)
	cmplwi %cr0, %r8, 0
	beq %cr0, 23f
	add %r8, %r6, %r11
	stb %r12, 0(%r8)
	addi %r11, %r11, 1
	b 24f
23:
24:
	addi %r3, %r3, 4
	addi %r12, %r12, 1
	addi %r8, %r12, -256
	cmpldi %cr0, %r8, 0
	bne %cr0, 22b
	stb %r11, 0(%r10)
	addi %r10, %r10, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 21b
	blr

vg_mldsa_hint_bit_unpack:
	rldicr %r5, %r5, 32, 31
	rldicl %r5, %r5, 32, 32
	subf %r12, %r5, %r4
	addi %r9, %r7, 0
	li %r0, 0
	addi %r10, %r6, 0
20:
	stw %r0, 0(%r10)
	addi %r10, %r10, 4
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 20b
	li %r11, 0
	add %r10, %r3, %r5
21:
	subf %r0, %r11, %r5
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 22f
	b 23f
22:
	lbz %r8, 0(%r10)
	subf %r0, %r11, %r8
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	li %r11, 256
	b 25f
24:
	subf %r0, %r8, %r5
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 26f
	li %r11, 256
	b 27f
26:
	subf %r0, %r8, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 28f
	add %r9, %r3, %r11
	lbz %r9, 0(%r9)
	rldicr %r9, %r9, 2, 61
	add %r9, %r6, %r9
	li %r0, 1
	stw %r0, 0(%r9)
	addi %r11, %r11, 1
	subf %r0, %r8, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 210f
212:
	add %r9, %r3, %r11
	lbz %r0, 0(%r9)
	addi %r9, %r9, -1
	lbz %r9, 0(%r9)
	subf %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 213f
	add %r9, %r3, %r11
	lbz %r9, 0(%r9)
	rldicr %r9, %r9, 2, 61
	add %r9, %r6, %r9
	li %r0, 1
	stw %r0, 0(%r9)
	addi %r11, %r11, 1
	b 214f
213:
	li %r11, 256
214:
	subf %r0, %r8, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	bne %cr0, 212b
	b 211f
210:
211:
	b 29f
28:
29:
27:
25:
23:
	addi %r10, %r10, 1
	addi %r6, %r6, 1024
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	subf %r0, %r5, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	beq %cr0, 215f
217:
	add %r9, %r3, %r11
	lbz %r9, 0(%r9)
	cmpldi %cr0, %r9, 0
	beq %cr0, 218f
	li %r11, 256
	b 219f
218:
	addi %r11, %r11, 1
219:
	subf %r0, %r5, %r11
	rldicl %r0, %r0, 1, 63
	cmpldi %cr0, %r0, 0
	bne %cr0, 217b
	b 216f
215:
216:
	subf %r0, %r11, %r5
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	subf %r3, %r0, %r3
	blr

vg_mldsa_power2round:
	li %r6, 256
	lis %r7, 127
	ori %r7, %r7, 57345
20:
	lwz %r8, 0(%r3)
	addi %r8, %r8, 4095
	rldicl %r9, %r8, 51, 13
	stw %r9, 0(%r4)
	rldicr %r10, %r9, 13, 50
	subf %r8, %r10, %r8
	addi %r8, %r8, -4095
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r7
	add %r8, %r8, %r9
	stw %r8, 0(%r5)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	blr

vg_mldsa_high_bits:
	lis %r7, 3
	ori %r7, %r7, 65280
	subf %r0, %r7, %r4
	cmplwi %cr0, %r0, 0
	beq %cr0, 20f
	lis %r10, 0
	ori %r10, %r10, 11275
	lis %r11, 128
	ori %r11, %r11, 0
	li %r12, 44
	li %r6, 256
22:
	lwz %r8, 0(%r3)
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 40, 24
	addi %r8, %r8, -44
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	stw %r8, 0(%r5)
	addi %r3, %r3, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
	lis %r10, 0
	ori %r10, %r10, 1025
	lis %r11, 32
	ori %r11, %r11, 0
	li %r12, 16
	li %r6, 256
23:
	lwz %r8, 0(%r3)
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 42, 22
	addi %r8, %r8, -16
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	stw %r8, 0(%r5)
	addi %r3, %r3, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 23b
21:
	blr

vg_mldsa_low_bits:
	lis %r7, 3
	ori %r7, %r7, 65280
	subf %r0, %r7, %r4
	cmplwi %cr0, %r0, 0
	beq %cr0, 20f
	lis %r10, 0
	ori %r10, %r10, 11275
	lis %r11, 128
	ori %r11, %r11, 0
	li %r12, 44
	lis %r4, 2
	ori %r4, %r4, 59392
	lis %r7, 127
	ori %r7, %r7, 57345
	li %r6, 256
22:
	lwz %r8, 0(%r3)
	lwz %r0, 0(%r3)
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 40, 24
	addi %r8, %r8, -44
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	mulld %r8, %r8, %r4
	subf %r0, %r8, %r0
	rldicl %r9, %r0, 1, 63
	mulld %r9, %r9, %r7
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	addi %r3, %r3, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
	lis %r10, 0
	ori %r10, %r10, 1025
	lis %r11, 32
	ori %r11, %r11, 0
	li %r12, 16
	lis %r4, 7
	ori %r4, %r4, 65024
	lis %r7, 127
	ori %r7, %r7, 57345
	li %r6, 256
23:
	lwz %r8, 0(%r3)
	lwz %r0, 0(%r3)
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 42, 22
	addi %r8, %r8, -16
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	mulld %r8, %r8, %r4
	subf %r0, %r8, %r0
	rldicl %r9, %r0, 1, 63
	mulld %r9, %r9, %r7
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	addi %r3, %r3, 4
	addi %r5, %r5, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 23b
21:
	blr

vg_mldsa_norm_lt:
	rlwinm %r4, %r4, 0, 0, 31
	li %r9, 1
	li %r10, 256
	lis %r5, 127
	ori %r5, %r5, 57345
20:
	lwz %r6, 0(%r3)
	subf %r7, %r4, %r6
	rldicl %r7, %r7, 1, 63
	subf %r8, %r6, %r5
	subf %r8, %r4, %r8
	rldicl %r8, %r8, 1, 63
	or %r7, %r7, %r8
	and %r9, %r9, %r7
	addi %r3, %r3, 4
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 20b
	or %r3, %r9, %r9
	blr

vg_mldsa_make_hint:
	lis %r7, 3
	ori %r7, %r7, 65280
	subf %r0, %r7, %r5
	cmplwi %cr0, %r0, 0
	beq %cr0, 20f
	lis %r10, 0
	ori %r10, %r10, 11275
	lis %r11, 128
	ori %r11, %r11, 0
	li %r12, 44
	lis %r5, 127
	ori %r5, %r5, 57345
	li %r7, 256
	li %r0, 0
22:
	lwz %r8, 0(%r4)
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 40, 24
	addi %r8, %r8, -44
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	stw %r8, 0(%r6)
	lwz %r8, 0(%r4)
	lwz %r9, 0(%r3)
	add %r8, %r8, %r9
	subf %r8, %r5, %r8
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r5
	add %r8, %r8, %r9
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 40, 24
	addi %r8, %r8, -44
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	lwz %r9, 0(%r6)
	xor %r8, %r8, %r9
	addi %r8, %r8, 63
	rldicl %r8, %r8, 58, 6
	stw %r8, 0(%r6)
	add %r0, %r0, %r8
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r6, %r6, 4
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 22b
	or %r3, %r0, %r0
	b 21f
20:
	lis %r10, 0
	ori %r10, %r10, 1025
	lis %r11, 32
	ori %r11, %r11, 0
	li %r12, 16
	lis %r5, 127
	ori %r5, %r5, 57345
	li %r7, 256
	li %r0, 0
23:
	lwz %r8, 0(%r4)
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 42, 22
	addi %r8, %r8, -16
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	stw %r8, 0(%r6)
	lwz %r8, 0(%r4)
	lwz %r9, 0(%r3)
	add %r8, %r8, %r9
	subf %r8, %r5, %r8
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r5
	add %r8, %r8, %r9
	addi %r8, %r8, 127
	rldicl %r8, %r8, 57, 7
	mulld %r8, %r8, %r10
	add %r8, %r8, %r11
	rldicl %r8, %r8, 42, 22
	addi %r8, %r8, -16
	rldicl %r9, %r8, 1, 63
	mulld %r9, %r9, %r12
	add %r8, %r8, %r9
	lwz %r9, 0(%r6)
	xor %r8, %r8, %r9
	addi %r8, %r8, 63
	rldicl %r8, %r8, 58, 6
	stw %r8, 0(%r6)
	add %r0, %r0, %r8
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r6, %r6, 4
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 23b
	or %r3, %r0, %r0
21:
	blr

vg_mldsa_use_hint:
	lis %r7, 3
	ori %r7, %r7, 65280
	subf %r0, %r7, %r5
	cmplwi %cr0, %r0, 0
	beq %cr0, 20f
	lis %r10, 0
	ori %r10, %r10, 11275
	lis %r11, 128
	ori %r11, %r11, 0
	li %r12, 44
	lis %r5, 2
	ori %r5, %r5, 59392
	li %r7, 256
22:
	lwz %r8, 0(%r4)
	lwz %r9, 0(%r4)
	addi %r9, %r9, 127
	rldicl %r9, %r9, 57, 7
	mulld %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicl %r9, %r9, 40, 24
	mulld %r0, %r9, %r5
	subf %r0, %r8, %r0
	rldicl %r0, %r0, 1, 63
	rldicr %r0, %r0, 1, 62
	lwz %r8, 0(%r3)
	addi %r8, %r8, -1
	rldicl %r8, %r8, 1, 63
	add %r9, %r9, %r0
	mulld %r0, %r0, %r8
	subf %r9, %r0, %r9
	add %r9, %r9, %r8
	addi %r9, %r9, -1
	rldicl %r8, %r9, 1, 63
	mulld %r8, %r8, %r12
	add %r9, %r9, %r8
	addi %r9, %r9, -44
	rldicl %r8, %r9, 1, 63
	mulld %r8, %r8, %r12
	add %r9, %r9, %r8
	stw %r9, 0(%r6)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r6, %r6, 4
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 22b
	b 21f
20:
	lis %r10, 0
	ori %r10, %r10, 1025
	lis %r11, 32
	ori %r11, %r11, 0
	li %r12, 16
	lis %r5, 7
	ori %r5, %r5, 65024
	li %r7, 256
23:
	lwz %r8, 0(%r4)
	lwz %r9, 0(%r4)
	addi %r9, %r9, 127
	rldicl %r9, %r9, 57, 7
	mulld %r9, %r9, %r10
	add %r9, %r9, %r11
	rldicl %r9, %r9, 42, 22
	mulld %r0, %r9, %r5
	subf %r0, %r8, %r0
	rldicl %r0, %r0, 1, 63
	rldicr %r0, %r0, 1, 62
	lwz %r8, 0(%r3)
	addi %r8, %r8, -1
	rldicl %r8, %r8, 1, 63
	add %r9, %r9, %r0
	mulld %r0, %r0, %r8
	subf %r9, %r0, %r9
	add %r9, %r9, %r8
	addi %r9, %r9, -1
	rldicl %r8, %r9, 1, 63
	mulld %r8, %r8, %r12
	add %r9, %r9, %r8
	addi %r9, %r9, -16
	rldicl %r8, %r9, 1, 63
	mulld %r8, %r8, %r12
	add %r9, %r9, %r8
	stw %r9, 0(%r6)
	addi %r3, %r3, 4
	addi %r4, %r4, 4
	addi %r6, %r6, 4
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 23b
21:
	blr

vg_mldsa_rej_ntt_poly:
	mflr %r0
	std %r27, 2000(%r5)
	std %r28, 2008(%r5)
	std %r29, 2016(%r5)
	std %r30, 2024(%r5)
	std %r31, 2032(%r5)
	std %r0, 2040(%r5)
	addi %r31, %r5, 0
	addi %r30, %r4, 0
	addi %r29, %r3, 0
	li %r28, 34
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	addi %r3, %r31, 0
	li %r4, 168
	li %r5, 0
	addi %r6, %r29, 0
	addi %r7, %r28, 0
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 168
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r31, 0
	li %r4, 168
	li %r5, 0
	addi %r6, %r31, 840
	li %r7, 1008
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r3, %r31, 840
	addi %r4, %r30, 0
	li %r5, 0
	li %r6, 336
	lis %r7, 127
	ori %r7, %r7, 57345
20:
	lbz %r8, 0(%r3)
	lbz %r9, 1(%r3)
	lbz %r10, 2(%r3)
	rldicr %r9, %r9, 8, 55
	rldicr %r10, %r10, 57, 6
	rldicl %r10, %r10, 23, 41
	add %r10, %r10, %r9
	add %r10, %r10, %r8
	subf %r12, %r7, %r10
	rldicl %r12, %r12, 1, 63
	addi %r11, %r5, -256
	rldicl %r11, %r11, 1, 63
	and %r12, %r12, %r11
	cmpldi %cr0, %r12, 0
	beq %cr0, 21f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 22f
21:
22:
	addi %r3, %r3, 3
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	rldicl %r3, %r5, 56, 8
	ld %r0, 2040(%r31)
	mtlr %r0
	ld %r27, 2000(%r31)
	ld %r28, 2008(%r31)
	ld %r29, 2016(%r31)
	ld %r30, 2024(%r31)
	ld %r31, 2032(%r31)
	blr

vg_mldsa_rej_bounded_poly:
	mflr %r0
	std %r27, 2000(%r6)
	std %r28, 2008(%r6)
	std %r29, 2016(%r6)
	std %r30, 2024(%r6)
	std %r31, 2032(%r6)
	std %r0, 2040(%r6)
	addi %r31, %r6, 0
	addi %r30, %r5, 0
	addi %r29, %r3, 0
	li %r28, 66
	rldicr %r27, %r4, 32, 31
	rldicl %r27, %r27, 32, 32
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	addi %r3, %r31, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r29, 0
	addi %r7, %r28, 0
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r31, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r31, 840
	li %r7, 544
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	addi %r12, %r27, -2
	cmpldi %cr0, %r12, 0
	beq %cr0, 20f
	addi %r3, %r31, 840
	addi %r4, %r30, 0
	li %r5, 0
	li %r6, 544
	lis %r7, 127
	ori %r7, %r7, 57345
22:
	lbz %r8, 0(%r3)
	rldicr %r9, %r8, 60, 3
	rldicl %r9, %r9, 4, 60
	addi %r12, %r9, -9
	rldicl %r12, %r12, 1, 63
	addi %r11, %r5, -256
	rldicl %r11, %r11, 1, 63
	and %r12, %r12, %r11
	li %r10, 4
	subf %r10, %r9, %r10
	rldicl %r11, %r10, 1, 63
	mulld %r11, %r11, %r7
	add %r10, %r10, %r11
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 24f
23:
24:
	rldicl %r9, %r8, 60, 4
	addi %r12, %r9, -9
	rldicl %r12, %r12, 1, 63
	addi %r11, %r5, -256
	rldicl %r11, %r11, 1, 63
	and %r12, %r12, %r11
	li %r10, 4
	subf %r10, %r9, %r10
	rldicl %r11, %r10, 1, 63
	mulld %r11, %r11, %r7
	add %r10, %r10, %r11
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 26f
25:
26:
	addi %r3, %r3, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 22b
	b 21f
20:
	addi %r3, %r31, 840
	addi %r4, %r30, 0
	li %r5, 0
	li %r6, 544
	lis %r7, 127
	ori %r7, %r7, 57345
27:
	lbz %r8, 0(%r3)
	rldicr %r9, %r8, 60, 3
	rldicl %r9, %r9, 4, 60
	addi %r12, %r9, -15
	rldicl %r12, %r12, 1, 63
	addi %r11, %r5, -256
	rldicl %r11, %r11, 1, 63
	and %r12, %r12, %r11
	addi %r9, %r9, -10
	rldicl %r11, %r9, 1, 63
	rldicr %r10, %r11, 3, 60
	add %r9, %r9, %r10
	rldicr %r10, %r11, 1, 62
	add %r9, %r9, %r10
	addi %r9, %r9, -5
	rldicl %r11, %r9, 1, 63
	rldicr %r10, %r11, 2, 61
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	li %r10, 2
	subf %r10, %r9, %r10
	rldicl %r11, %r10, 1, 63
	mulld %r11, %r11, %r7
	add %r10, %r10, %r11
	cmpldi %cr0, %r12, 0
	beq %cr0, 28f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 29f
28:
29:
	rldicl %r9, %r8, 60, 4
	addi %r12, %r9, -15
	rldicl %r12, %r12, 1, 63
	addi %r11, %r5, -256
	rldicl %r11, %r11, 1, 63
	and %r12, %r12, %r11
	addi %r9, %r9, -10
	rldicl %r11, %r9, 1, 63
	rldicr %r10, %r11, 3, 60
	add %r9, %r9, %r10
	rldicr %r10, %r11, 1, 62
	add %r9, %r9, %r10
	addi %r9, %r9, -5
	rldicl %r11, %r9, 1, 63
	rldicr %r10, %r11, 2, 61
	add %r9, %r9, %r10
	add %r9, %r9, %r11
	li %r10, 2
	subf %r10, %r9, %r10
	rldicl %r11, %r10, 1, 63
	mulld %r11, %r11, %r7
	add %r10, %r10, %r11
	cmpldi %cr0, %r12, 0
	beq %cr0, 210f
	stw %r10, 0(%r4)
	addi %r4, %r4, 4
	addi %r5, %r5, 1
	b 211f
210:
211:
	addi %r3, %r3, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 27b
21:
	rldicl %r3, %r5, 56, 8
	ld %r0, 2040(%r31)
	mtlr %r0
	ld %r27, 2000(%r31)
	ld %r28, 2008(%r31)
	ld %r29, 2016(%r31)
	ld %r30, 2024(%r31)
	ld %r31, 2032(%r31)
	blr

vg_mldsa_expand_mask_poly:
	mflr %r0
	std %r27, 2000(%r6)
	std %r28, 2008(%r6)
	std %r29, 2016(%r6)
	std %r30, 2024(%r6)
	std %r31, 2032(%r6)
	std %r0, 2040(%r6)
	addi %r31, %r6, 0
	addi %r30, %r5, 0
	addi %r29, %r3, 0
	li %r28, 66
	rldicr %r27, %r4, 32, 31
	rldicl %r27, %r27, 32, 32
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	addi %r3, %r31, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r29, 0
	addi %r7, %r28, 0
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r31, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r31, 840
	li %r7, 640
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	lis %r12, 2
	subf %r12, %r12, %r27
	cmpldi %cr0, %r12, 0
	beq %cr0, 20f
	addi %r10, %r31, 840
	addi %r11, %r30, 0
	lis %r7, 127
	ori %r7, %r7, 57345
	lis %r4, 8
	li %r12, 128
22:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 16, 47
	add %r8, %r8, %r9
	rldicr %r9, %r8, 44, 19
	rldicl %r9, %r9, 20, 44
	rldicl %r8, %r8, 44, 20
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 44, 19
	rldicl %r9, %r9, 20, 44
	rldicl %r8, %r8, 44, 20
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	addi %r10, %r10, 5
	addi %r11, %r11, 8
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	b 21f
20:
	addi %r10, %r31, 840
	addi %r11, %r30, 0
	lis %r7, 127
	ori %r7, %r7, 57345
	lis %r4, 2
	li %r12, 64
23:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 16, 47
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 0(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 14, 49
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 4(%r11)
	lbz %r9, 5(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	lbz %r9, 6(%r10)
	rldicr %r9, %r9, 12, 51
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 8(%r11)
	lbz %r9, 7(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	lbz %r9, 8(%r10)
	rldicr %r9, %r9, 10, 53
	add %r8, %r8, %r9
	rldicr %r9, %r8, 46, 17
	rldicl %r9, %r9, 18, 46
	rldicl %r8, %r8, 46, 18
	subf %r9, %r9, %r4
	rldicl %r0, %r9, 1, 63
	mulld %r0, %r0, %r7
	add %r9, %r9, %r0
	stw %r9, 12(%r11)
	addi %r10, %r10, 9
	addi %r11, %r11, 16
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
21:
	ld %r0, 2040(%r31)
	mtlr %r0
	ld %r27, 2000(%r31)
	ld %r28, 2008(%r31)
	ld %r29, 2016(%r31)
	ld %r30, 2024(%r31)
	ld %r31, 2032(%r31)
	blr

vg_mldsa_sample_in_ball:
	mflr %r0
	std %r27, 2000(%r7)
	std %r28, 2008(%r7)
	std %r29, 2016(%r7)
	std %r30, 2024(%r7)
	std %r31, 2032(%r7)
	std %r0, 2040(%r7)
	addi %r31, %r7, 0
	addi %r30, %r6, 0
	addi %r29, %r3, 0
	addi %r28, %r4, 0
	rldicr %r27, %r5, 32, 31
	rldicl %r27, %r27, 32, 32
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	std %r0, 16(%r31)
	std %r0, 24(%r31)
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	std %r0, 64(%r31)
	std %r0, 72(%r31)
	std %r0, 80(%r31)
	std %r0, 88(%r31)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	std %r0, 128(%r31)
	std %r0, 136(%r31)
	std %r0, 144(%r31)
	std %r0, 152(%r31)
	std %r0, 160(%r31)
	std %r0, 168(%r31)
	std %r0, 176(%r31)
	std %r0, 184(%r31)
	std %r0, 192(%r31)
	addi %r3, %r31, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r29, 0
	addi %r7, %r28, 0
	addi %r8, %r31, 200
	bl {vg_keccak_absorb_scratch}
	addi %r5, %r3, 0
	addi %r3, %r31, 0
	li %r4, 136
	li %r6, 31
	addi %r7, %r31, 200
	bl {vg_keccak_pad_scratch}
	addi %r3, %r31, 0
	li %r4, 136
	li %r5, 0
	addi %r6, %r31, 840
	li %r7, 272
	addi %r8, %r31, 200
	bl {vg_keccak_squeeze_scratch}
	li %r12, 0
	addi %r4, %r30, 0
	li %r6, 256
20:
	stw %r12, 0(%r4)
	addi %r4, %r4, 4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	ld %r9, 840(%r31)
	li %r5, 256
	subf %r5, %r27, %r5
	rldicr %r4, %r5, 2, 61
	add %r4, %r30, %r4
	addi %r3, %r31, 848
	li %r6, 264
	lis %r7, 127
	ori %r7, %r7, 57343
21:
	addi %r12, %r5, -256
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	lbz %r8, 0(%r3)
	subf %r11, %r8, %r5
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	beq %cr0, 24f
	b 25f
24:
	rldicr %r10, %r8, 2, 61
	add %r10, %r30, %r10
	lwz %r11, 0(%r10)
	stw %r11, 0(%r4)
	rldicr %r12, %r9, 63, 0
	rldicl %r12, %r12, 1, 63
	mulld %r12, %r12, %r7
	addi %r12, %r12, 1
	stw %r12, 0(%r10)
	rldicl %r9, %r9, 63, 1
	addi %r4, %r4, 4
	addi %r5, %r5, 1
25:
	b 23f
22:
23:
	addi %r3, %r3, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 21b
	rldicl %r3, %r5, 56, 8
	ld %r0, 2040(%r31)
	mtlr %r0
	ld %r27, 2000(%r31)
	ld %r28, 2008(%r31)
	ld %r29, 2016(%r31)
	ld %r30, 2024(%r31)
	ld %r31, 2032(%r31)
	blr
