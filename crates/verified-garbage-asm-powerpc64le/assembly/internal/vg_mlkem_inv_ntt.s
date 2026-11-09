// The functions of `src/internal/vg_mlkem_inv_ntt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_inv_ntt:
	li %r12, 1
	stw %r12, 0(%r4)
	lis %r12, 19
	ori %r12, %r12, 44983
	stw %r12, 4(%r4)
	li %r12, 1729
	stw %r12, 8(%r4)
	lis %r12, -31499
	ori %r12, %r12, 50613
	stw %r12, 12(%r4)
	li %r12, 2580
	stw %r12, 16(%r4)
	lis %r12, -14746
	ori %r12, %r12, 58468
	stw %r12, 20(%r4)
	li %r12, 3289
	stw %r12, 24(%r4)
	lis %r12, -788
	ori %r12, %r12, 35671
	stw %r12, 28(%r4)
	li %r12, 2642
	stw %r12, 32(%r4)
	lis %r12, -13525
	ori %r12, %r12, 29391
	stw %r12, 36(%r4)
	li %r12, 630
	stw %r12, 40(%r4)
	lis %r12, 12402
	ori %r12, %r12, 27994
	stw %r12, 44(%r4)
	li %r12, 1897
	stw %r12, 48(%r4)
	lis %r12, -28191
	ori %r12, %r12, 5649
	stw %r12, 52(%r4)
	li %r12, 848
	stw %r12, 56(%r4)
	lis %r12, 16694
	ori %r12, %r12, 3976
	stw %r12, 60(%r4)
	li %r12, 1062
	stw %r12, 64(%r4)
	lis %r12, 20906
	ori %r12, %r12, 62169
	stw %r12, 68(%r4)
	li %r12, 1919
	stw %r12, 72(%r4)
	lis %r12, -27758
	ori %r12, %r12, 12244
	stw %r12, 76(%r4)
	li %r12, 193
	stw %r12, 80(%r4)
	lis %r12, 3799
	ori %r12, %r12, 31045
	stw %r12, 84(%r4)
	li %r12, 797
	stw %r12, 88(%r4)
	lis %r12, 15690
	ori %r12, %r12, 3582
	stw %r12, 92(%r4)
	li %r12, 2786
	stw %r12, 96(%r4)
	lis %r12, -10690
	ori %r12, %r12, 18938
	stw %r12, 100(%r4)
	li %r12, 3260
	stw %r12, 104(%r4)
	lis %r12, -1359
	ori %r12, %r12, 41872
	stw %r12, 108(%r4)
	li %r12, 569
	stw %r12, 112(%r4)
	lis %r12, 11201
	ori %r12, %r12, 36518
	stw %r12, 116(%r4)
	li %r12, 1746
	stw %r12, 120(%r4)
	lis %r12, -31164
	ori %r12, %r12, 28899
	stw %r12, 124(%r4)
	li %r12, 296
	stw %r12, 128(%r4)
	lis %r12, 5827
	ori %r12, %r12, 11280
	stw %r12, 132(%r4)
	li %r12, 2447
	stw %r12, 136(%r4)
	lis %r12, -17364
	ori %r12, %r12, 39451
	stw %r12, 140(%r4)
	li %r12, 1339
	stw %r12, 144(%r4)
	lis %r12, 26360
	ori %r12, %r12, 5197
	stw %r12, 148(%r4)
	li %r12, 1476
	stw %r12, 152(%r4)
	lis %r12, 29057
	ori %r12, %r12, 7539
	stw %r12, 156(%r4)
	li %r12, 3046
	stw %r12, 160(%r4)
	lis %r12, -5572
	ori %r12, %r12, 49215
	stw %r12, 164(%r4)
	li %r12, 56
	stw %r12, 168(%r4)
	lis %r12, 1102
	ori %r12, %r12, 28702
	stw %r12, 172(%r4)
	li %r12, 2240
	stw %r12, 176(%r4)
	lis %r12, -21439
	ori %r12, %r12, 33998
	stw %r12, 180(%r4)
	li %r12, 1333
	stw %r12, 184(%r4)
	lis %r12, 26241
	ori %r12, %r12, 62976
	stw %r12, 188(%r4)
	li %r12, 1426
	stw %r12, 192(%r4)
	lis %r12, 28072
	ori %r12, %r12, 52129
	stw %r12, 196(%r4)
	li %r12, 2094
	stw %r12, 200(%r4)
	lis %r12, -24313
	ori %r12, %r12, 20021
	stw %r12, 204(%r4)
	li %r12, 535
	stw %r12, 208(%r4)
	lis %r12, 10532
	ori %r12, %r12, 14410
	stw %r12, 212(%r4)
	li %r12, 2882
	stw %r12, 216(%r4)
	lis %r12, -8800
	ori %r12, %r12, 11969
	stw %r12, 220(%r4)
	li %r12, 2393
	stw %r12, 224(%r4)
	lis %r12, -18427
	ori %r12, %r12, 35179
	stw %r12, 228(%r4)
	li %r12, 2879
	stw %r12, 232(%r4)
	lis %r12, -8859
	ori %r12, %r12, 8091
	stw %r12, 236(%r4)
	li %r12, 1974
	stw %r12, 240(%r4)
	lis %r12, -26676
	ori %r12, %r12, 61500
	stw %r12, 244(%r4)
	li %r12, 821
	stw %r12, 248(%r4)
	lis %r12, 16162
	ori %r12, %r12, 34608
	stw %r12, 252(%r4)
	li %r12, 289
	stw %r12, 256(%r4)
	lis %r12, 5689
	ori %r12, %r12, 24076
	stw %r12, 260(%r4)
	li %r12, 331
	stw %r12, 264(%r4)
	lis %r12, 6516
	ori %r12, %r12, 12835
	stw %r12, 268(%r4)
	li %r12, 3253
	stw %r12, 272(%r4)
	lis %r12, -1497
	ori %r12, %r12, 54669
	stw %r12, 276(%r4)
	li %r12, 1756
	stw %r12, 280(%r4)
	lis %r12, -30967
	ori %r12, %r12, 19981
	stw %r12, 284(%r4)
	li %r12, 1197
	stw %r12, 288(%r4)
	lis %r12, 23564
	ori %r12, %r12, 40081
	stw %r12, 292(%r4)
	li %r12, 2304
	stw %r12, 296(%r4)
	lis %r12, -20179
	ori %r12, %r12, 29352
	stw %r12, 300(%r4)
	li %r12, 2277
	stw %r12, 304(%r4)
	lis %r12, -20711
	ori %r12, %r12, 59984
	stw %r12, 308(%r4)
	li %r12, 2055
	stw %r12, 312(%r4)
	lis %r12, -25081
	ori %r12, %r12, 35140
	stw %r12, 316(%r4)
	li %r12, 650
	stw %r12, 320(%r4)
	lis %r12, 12796
	ori %r12, %r12, 10158
	stw %r12, 324(%r4)
	li %r12, 1977
	stw %r12, 328(%r4)
	lis %r12, -26617
	ori %r12, %r12, 65378
	stw %r12, 332(%r4)
	li %r12, 2513
	stw %r12, 336(%r4)
	lis %r12, -16065
	ori %r12, %r12, 59236
	stw %r12, 340(%r4)
	li %r12, 632
	stw %r12, 344(%r4)
	lis %r12, 12441
	ori %r12, %r12, 52424
	stw %r12, 348(%r4)
	li %r12, 2865
	stw %r12, 352(%r4)
	lis %r12, -9135
	ori %r12, %r12, 33683
	stw %r12, 356(%r4)
	li %r12, 33
	stw %r12, 360(%r4)
	lis %r12, 649
	ori %r12, %r12, 42660
	stw %r12, 364(%r4)
	li %r12, 1320
	stw %r12, 368(%r4)
	lis %r12, 25986
	ori %r12, %r12, 2480
	stw %r12, 372(%r4)
	li %r12, 1915
	stw %r12, 376(%r4)
	lis %r12, -27837
	ori %r12, %r12, 28919
	stw %r12, 380(%r4)
	li %r12, 2319
	stw %r12, 384(%r4)
	lis %r12, -19884
	ori %r12, %r12, 48743
	stw %r12, 388(%r4)
	li %r12, 1435
	stw %r12, 392(%r4)
	lis %r12, 28249
	ori %r12, %r12, 63764
	stw %r12, 396(%r4)
	li %r12, 807
	stw %r12, 400(%r4)
	lis %r12, 15886
	ori %r12, %r12, 60200
	stw %r12, 404(%r4)
	li %r12, 452
	stw %r12, 408(%r4)
	lis %r12, 8898
	ori %r12, %r12, 16339
	stw %r12, 412(%r4)
	li %r12, 1438
	stw %r12, 416(%r4)
	lis %r12, 28309
	ori %r12, %r12, 2106
	stw %r12, 420(%r4)
	li %r12, 2868
	stw %r12, 424(%r4)
	lis %r12, -9076
	ori %r12, %r12, 37561
	stw %r12, 428(%r4)
	li %r12, 1534
	stw %r12, 432(%r4)
	lis %r12, 30198
	ori %r12, %r12, 60673
	stw %r12, 436(%r4)
	li %r12, 2402
	stw %r12, 440(%r4)
	lis %r12, -18250
	ori %r12, %r12, 46814
	stw %r12, 444(%r4)
	li %r12, 2647
	stw %r12, 448(%r4)
	lis %r12, -13427
	ori %r12, %r12, 57700
	stw %r12, 452(%r4)
	li %r12, 2617
	stw %r12, 456(%r4)
	lis %r12, -14017
	ori %r12, %r12, 18918
	stw %r12, 460(%r4)
	li %r12, 1481
	stw %r12, 464(%r4)
	lis %r12, 29155
	ori %r12, %r12, 35848
	stw %r12, 468(%r4)
	li %r12, 648
	stw %r12, 472(%r4)
	lis %r12, 12756
	ori %r12, %r12, 51263
	stw %r12, 476(%r4)
	li %r12, 2474
	stw %r12, 480(%r4)
	lis %r12, -16832
	ori %r12, %r12, 8819
	stw %r12, 484(%r4)
	li %r12, 3110
	stw %r12, 488(%r4)
	lis %r12, -4312
	ori %r12, %r12, 44569
	stw %r12, 492(%r4)
	li %r12, 1227
	stw %r12, 496(%r4)
	lis %r12, 24155
	ori %r12, %r12, 13327
	stw %r12, 500(%r4)
	li %r12, 910
	stw %r12, 504(%r4)
	lis %r12, 17914
	ori %r12, %r12, 40435
	stw %r12, 508(%r4)
	li %r12, 17
	stw %r12, 512(%r4)
	lis %r12, 334
	ori %r12, %r12, 43821
	stw %r12, 516(%r4)
	li %r12, 2761
	stw %r12, 520(%r4)
	lis %r12, -11182
	ori %r12, %r12, 8465
	stw %r12, 524(%r4)
	li %r12, 583
	stw %r12, 528(%r4)
	lis %r12, 11477
	ori %r12, %r12, 10925
	stw %r12, 532(%r4)
	li %r12, 2649
	stw %r12, 536(%r4)
	lis %r12, -13387
	ori %r12, %r12, 16595
	stw %r12, 540(%r4)
	li %r12, 1637
	stw %r12, 544(%r4)
	lis %r12, 32226
	ori %r12, %r12, 40908
	stw %r12, 548(%r4)
	li %r12, 723
	stw %r12, 552(%r4)
	lis %r12, 14233
	ori %r12, %r12, 17146
	stw %r12, 556(%r4)
	li %r12, 2288
	stw %r12, 560(%r4)
	lis %r12, -20494
	ori %r12, %r12, 30513
	stw %r12, 564(%r4)
	li %r12, 1100
	stw %r12, 568(%r4)
	lis %r12, 21655
	ori %r12, %r12, 2067
	stw %r12, 572(%r4)
	li %r12, 1409
	stw %r12, 576(%r4)
	lis %r12, 27738
	ori %r12, %r12, 8307
	stw %r12, 580(%r4)
	li %r12, 2662
	stw %r12, 584(%r4)
	lis %r12, -13131
	ori %r12, %r12, 11555
	stw %r12, 588(%r4)
	li %r12, 3281
	stw %r12, 592(%r4)
	lis %r12, -945
	ori %r12, %r12, 3484
	stw %r12, 596(%r4)
	li %r12, 233
	stw %r12, 600(%r4)
	lis %r12, 4586
	ori %r12, %r12, 60909
	stw %r12, 604(%r4)
	li %r12, 756
	stw %r12, 608(%r4)
	lis %r12, 14882
	ori %r12, %r12, 59807
	stw %r12, 612(%r4)
	li %r12, 2156
	stw %r12, 616(%r4)
	lis %r12, -23093
	ori %r12, %r12, 56480
	stw %r12, 620(%r4)
	li %r12, 3015
	stw %r12, 624(%r4)
	lis %r12, -6182
	ori %r12, %r12, 30986
	stw %r12, 628(%r4)
	li %r12, 3050
	stw %r12, 632(%r4)
	lis %r12, -5493
	ori %r12, %r12, 32541
	stw %r12, 636(%r4)
	li %r12, 1703
	stw %r12, 640(%r4)
	lis %r12, -32011
	ori %r12, %r12, 60693
	stw %r12, 644(%r4)
	li %r12, 1651
	stw %r12, 648(%r4)
	lis %r12, 32502
	ori %r12, %r12, 15316
	stw %r12, 652(%r4)
	li %r12, 2789
	stw %r12, 656(%r4)
	lis %r12, -10631
	ori %r12, %r12, 22816
	stw %r12, 660(%r4)
	li %r12, 1789
	stw %r12, 664(%r4)
	lis %r12, -30318
	ori %r12, %r12, 62642
	stw %r12, 668(%r4)
	li %r12, 1847
	stw %r12, 672(%r4)
	lis %r12, -29176
	ori %r12, %r12, 50239
	stw %r12, 676(%r4)
	li %r12, 952
	stw %r12, 680(%r4)
	lis %r12, 18741
	ori %r12, %r12, 29194
	stw %r12, 684(%r4)
	li %r12, 1461
	stw %r12, 688(%r4)
	lis %r12, 28761
	ori %r12, %r12, 53684
	stw %r12, 692(%r4)
	li %r12, 2687
	stw %r12, 696(%r4)
	lis %r12, -12639
	ori %r12, %r12, 22029
	stw %r12, 700(%r4)
	li %r12, 939
	stw %r12, 704(%r4)
	lis %r12, 18485
	ori %r12, %r12, 34234
	stw %r12, 708(%r4)
	li %r12, 2308
	stw %r12, 712(%r4)
	lis %r12, -20100
	ori %r12, %r12, 12678
	stw %r12, 716(%r4)
	li %r12, 2437
	stw %r12, 720(%r4)
	lis %r12, -17561
	ori %r12, %r12, 48369
	stw %r12, 724(%r4)
	li %r12, 2388
	stw %r12, 728(%r4)
	lis %r12, -18525
	ori %r12, %r12, 6870
	stw %r12, 732(%r4)
	li %r12, 733
	stw %r12, 736(%r4)
	lis %r12, 14430
	ori %r12, %r12, 8228
	stw %r12, 740(%r4)
	li %r12, 2337
	stw %r12, 744(%r4)
	lis %r12, -19529
	ori %r12, %r12, 6476
	stw %r12, 748(%r4)
	li %r12, 268
	stw %r12, 752(%r4)
	lis %r12, 5275
	ori %r12, %r12, 62464
	stw %r12, 756(%r4)
	li %r12, 641
	stw %r12, 760(%r4)
	lis %r12, 12618
	ori %r12, %r12, 64059
	stw %r12, 764(%r4)
	li %r12, 1584
	stw %r12, 768(%r4)
	lis %r12, 31183
	ori %r12, %r12, 16083
	stw %r12, 772(%r4)
	li %r12, 2298
	stw %r12, 776(%r4)
	lis %r12, -20297
	ori %r12, %r12, 21595
	stw %r12, 780(%r4)
	li %r12, 2037
	stw %r12, 784(%r4)
	lis %r12, -25435
	ori %r12, %r12, 11870
	stw %r12, 788(%r4)
	li %r12, 3220
	stw %r12, 792(%r4)
	lis %r12, -2146
	ori %r12, %r12, 12008
	stw %r12, 796(%r4)
	li %r12, 375
	stw %r12, 800(%r4)
	lis %r12, 7382
	ori %r12, %r12, 26025
	stw %r12, 804(%r4)
	li %r12, 2549
	stw %r12, 808(%r4)
	lis %r12, -15356
	ori %r12, %r12, 40238
	stw %r12, 812(%r4)
	li %r12, 2090
	stw %r12, 816(%r4)
	lis %r12, -24392
	ori %r12, %r12, 36695
	stw %r12, 820(%r4)
	li %r12, 1645
	stw %r12, 824(%r4)
	lis %r12, 32384
	ori %r12, %r12, 7559
	stw %r12, 828(%r4)
	li %r12, 1063
	stw %r12, 832(%r4)
	lis %r12, 20926
	ori %r12, %r12, 41617
	stw %r12, 836(%r4)
	li %r12, 319
	stw %r12, 840(%r4)
	lis %r12, 6279
	ori %r12, %r12, 62858
	stw %r12, 844(%r4)
	li %r12, 2773
	stw %r12, 848(%r4)
	lis %r12, -10946
	ori %r12, %r12, 23978
	stw %r12, 852(%r4)
	li %r12, 757
	stw %r12, 856(%r4)
	lis %r12, 14902
	ori %r12, %r12, 39254
	stw %r12, 860(%r4)
	li %r12, 2099
	stw %r12, 864(%r4)
	lis %r12, -24215
	ori %r12, %r12, 48330
	stw %r12, 868(%r4)
	li %r12, 561
	stw %r12, 872(%r4)
	lis %r12, 11044
	ori %r12, %r12, 4331
	stw %r12, 876(%r4)
	li %r12, 2466
	stw %r12, 880(%r4)
	lis %r12, -16990
	ori %r12, %r12, 42168
	stw %r12, 884(%r4)
	li %r12, 2594
	stw %r12, 888(%r4)
	lis %r12, -14470
	ori %r12, %r12, 32876
	stw %r12, 892(%r4)
	li %r12, 2804
	stw %r12, 896(%r4)
	lis %r12, -10336
	ori %r12, %r12, 42207
	stw %r12, 900(%r4)
	li %r12, 1092
	stw %r12, 904(%r4)
	lis %r12, 21497
	ori %r12, %r12, 35415
	stw %r12, 908(%r4)
	li %r12, 403
	stw %r12, 912(%r4)
	lis %r12, 7933
	ori %r12, %r12, 40376
	stw %r12, 916(%r4)
	li %r12, 1026
	stw %r12, 920(%r4)
	lis %r12, 20198
	ori %r12, %r12, 15630
	stw %r12, 924(%r4)
	li %r12, 1143
	stw %r12, 928(%r4)
	lis %r12, 22501
	ori %r12, %r12, 35809
	stw %r12, 932(%r4)
	li %r12, 2150
	stw %r12, 936(%r4)
	lis %r12, -23211
	ori %r12, %r12, 48723
	stw %r12, 940(%r4)
	li %r12, 2775
	stw %r12, 944(%r4)
	lis %r12, -10907
	ori %r12, %r12, 48408
	stw %r12, 948(%r4)
	li %r12, 886
	stw %r12, 952(%r4)
	lis %r12, 17442
	ori %r12, %r12, 9410
	stw %r12, 956(%r4)
	li %r12, 1722
	stw %r12, 960(%r4)
	lis %r12, -31637
	ori %r12, %r12, 63409
	stw %r12, 964(%r4)
	li %r12, 1212
	stw %r12, 968(%r4)
	lis %r12, 23859
	ori %r12, %r12, 59472
	stw %r12, 972(%r4)
	li %r12, 1874
	stw %r12, 976(%r4)
	lis %r12, -28644
	ori %r12, %r12, 19607
	stw %r12, 980(%r4)
	li %r12, 1029
	stw %r12, 984(%r4)
	lis %r12, 20257
	ori %r12, %r12, 19509
	stw %r12, 988(%r4)
	li %r12, 2110
	stw %r12, 992(%r4)
	lis %r12, -23998
	ori %r12, %r12, 18859
	stw %r12, 996(%r4)
	li %r12, 2935
	stw %r12, 1000(%r4)
	lis %r12, -7757
	ori %r12, %r12, 36793
	stw %r12, 1004(%r4)
	li %r12, 885
	stw %r12, 1008(%r4)
	lis %r12, 17422
	ori %r12, %r12, 29962
	stw %r12, 1012(%r4)
	li %r12, 2154
	stw %r12, 1016(%r4)
	lis %r12, -23132
	ori %r12, %r12, 32049
	stw %r12, 1020(%r4)
	vspltisw %v14, 0
	lis %r11, 0
	ori %r11, %r11, 3329
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 3329
	lis %r12, 0
	ori %r12, %r12, 3329
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 0
	ori %r12, %r12, 3329
	mtvsrd 32, %r11
	mtvsrd 47, %r12
	vsldoi %v0, %v14, %v0, 8
	vsldoi %v0, %v0, %v15, 8
	lis %r11, 1
	ori %r11, %r11, 515
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 4113
	ori %r11, %r11, 4627
	lis %r12, 2057
	ori %r12, %r12, 2571
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6169
	ori %r12, %r12, 6683
	mtvsrd 33, %r11
	mtvsrd 47, %r12
	vsldoi %v1, %v14, %v1, 8
	vsldoi %v1, %v1, %v15, 8
	lis %r11, 1
	ori %r11, %r11, 515
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 1029
	ori %r11, %r11, 1543
	lis %r12, 4113
	ori %r12, %r12, 4627
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5141
	ori %r12, %r12, 5655
	mtvsrd 34, %r11
	mtvsrd 47, %r12
	vsldoi %v2, %v14, %v2, 8
	vsldoi %v2, %v2, %v15, 8
	lis %r11, 2057
	ori %r11, %r11, 2571
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 3085
	ori %r11, %r11, 3599
	lis %r12, 6169
	ori %r12, %r12, 6683
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7197
	ori %r12, %r12, 7711
	mtvsrd 35, %r11
	mtvsrd 47, %r12
	vsldoi %v3, %v14, %v3, 8
	vsldoi %v3, %v3, %v15, 8
	lis %r11, 1029
	ori %r11, %r11, 1543
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 1029
	ori %r11, %r11, 1543
	lis %r12, 3085
	ori %r12, %r12, 3599
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 3085
	ori %r12, %r12, 3599
	mtvsrd 44, %r11
	mtvsrd 47, %r12
	vsldoi %v12, %v14, %v12, 8
	vsldoi %v12, %v12, %v15, 8
	lis %r11, 1
	ori %r11, %r11, 515
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 1
	ori %r11, %r11, 515
	lis %r12, 2057
	ori %r12, %r12, 2571
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 2057
	ori %r12, %r12, 2571
	mtvsrd 45, %r11
	mtvsrd 47, %r12
	vsldoi %v13, %v14, %v13, 8
	vsldoi %v13, %v13, %v15, 8
	li %r7, 1008
	li %r5, 0
	li %r10, 32
20:
	lxvd2x 43, %r4, %r7
	vperm %v4, %v11, %v11, %v12
	vperm %v5, %v11, %v11, %v13
	addi %r6, %r5, 16
	lxvd2x 40, %r3, %r5
	lxvd2x 41, %r3, %r6
	vperm %v6, %v9, %v8, %v2
	vperm %v7, %v9, %v8, %v3
	vadduwm %v10, %v6, %v7
	vadduwm %v7, %v7, %v0
	vsubuwm %v7, %v7, %v6
	vsubuwm %v6, %v10, %v0
	vminuw %v6, %v10, %v6
	vmuleuw %v8, %v7, %v5
	vmulouw %v9, %v7, %v5
	vperm %v8, %v8, %v9, %v1
	vmuluwm %v9, %v7, %v4
	vmuluwm %v8, %v8, %v0
	vsubuwm %v8, %v9, %v8
	vsubuwm %v9, %v8, %v0
	vminuw %v8, %v8, %v9
	vperm %v9, %v6, %v8, %v2
	vperm %v10, %v6, %v8, %v3
	stxvd2x 41, %r3, %r6
	stxvd2x 42, %r3, %r5
	addi %r5, %r5, 32
	addi %r7, %r7, -16
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 20b
	li %r7, 504
	li %r9, 16
21:
	li %r5, 0
22:
	lxvd2x 43, %r4, %r7
	vspltw %v4, %v11, 1
	vspltw %v5, %v11, 0
	addi %r7, %r7, -8
	add %r6, %r5, %r9
	rldicl %r10, %r9, 60, 4
23:
	lxvd2x 38, %r3, %r5
	lxvd2x 39, %r3, %r6
	vadduwm %v10, %v6, %v7
	vadduwm %v7, %v7, %v0
	vsubuwm %v7, %v7, %v6
	vsubuwm %v6, %v10, %v0
	vminuw %v6, %v10, %v6
	vmuleuw %v8, %v7, %v5
	vmulouw %v9, %v7, %v5
	vperm %v8, %v8, %v9, %v1
	vmuluwm %v9, %v7, %v4
	vmuluwm %v8, %v8, %v0
	vsubuwm %v8, %v9, %v8
	vsubuwm %v9, %v8, %v0
	vminuw %v8, %v8, %v9
	stxvd2x 38, %r3, %r5
	stxvd2x 40, %r3, %r6
	addi %r5, %r5, 16
	addi %r6, %r6, 16
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 23b
	addi %r5, %r6, 0
	addi %r0, %r5, -1024
	cmpldi %cr0, %r0, 0
	bne %cr0, 22b
	rldicr %r9, %r9, 1, 62
	addi %r0, %r9, -1024
	cmpldi %cr0, %r0, 0
	bne %cr0, 21b
	vspltisw %v14, 0
	lis %r11, 0
	ori %r11, %r11, 3303
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 0
	ori %r11, %r11, 3303
	lis %r12, 0
	ori %r12, %r12, 3303
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 0
	ori %r12, %r12, 3303
	mtvsrd 36, %r11
	mtvsrd 47, %r12
	vsldoi %v4, %v14, %v4, 8
	vsldoi %v4, %v4, %v15, 8
	lis %r11, -512
	ori %r11, %r11, 10079
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 65024
	ori %r11, %r11, 10079
	lis %r12, -512
	ori %r12, %r12, 10079
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 65024
	ori %r12, %r12, 10079
	mtvsrd 37, %r11
	mtvsrd 47, %r12
	vsldoi %v5, %v14, %v5, 8
	vsldoi %v5, %v5, %v15, 8
	li %r5, 0
	li %r10, 64
24:
	lxvd2x 39, %r3, %r5
	vmuleuw %v8, %v7, %v5
	vmulouw %v9, %v7, %v5
	vperm %v8, %v8, %v9, %v1
	vmuluwm %v9, %v7, %v4
	vmuluwm %v8, %v8, %v0
	vsubuwm %v8, %v9, %v8
	vsubuwm %v9, %v8, %v0
	vminuw %v8, %v8, %v9
	stxvd2x 40, %r3, %r5
	addi %r5, %r5, 16
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 24b
	blr
