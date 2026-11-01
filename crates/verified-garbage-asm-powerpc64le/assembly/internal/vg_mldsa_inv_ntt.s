// The functions of `src/internal/vg_mldsa_inv_ntt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
