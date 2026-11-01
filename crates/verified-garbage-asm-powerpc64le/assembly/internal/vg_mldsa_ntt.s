// The functions of `src/internal/vg_mldsa_ntt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
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
