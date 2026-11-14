// The functions of `src/internal/vg_mldsa_ntt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_ntt:
	lis %r12, -27936
	ori %r12, %r12, 47881
	stw %r12, 4(%r4)
	lis %r12, 29447
	ori %r12, %r12, 36605
	stw %r12, 8(%r4)
	lis %r12, 29415
	ori %r12, %r12, 35580
	stw %r12, 12(%r4)
	lis %r12, -25037
	ori %r12, %r12, 57788
	stw %r12, 16(%r4)
	lis %r12, -22552
	ori %r12, %r12, 57063
	stw %r12, 20(%r4)
	lis %r12, -24600
	ori %r12, %r12, 24279
	stw %r12, 24(%r4)
	lis %r12, -25036
	ori %r12, %r12, 25052
	stw %r12, 28(%r4)
	lis %r12, -4706
	ori %r12, %r12, 49621
	stw %r12, 32(%r4)
	lis %r12, 27702
	ori %r12, %r12, 46805
	stw %r12, 36(%r4)
	lis %r12, 20975
	ori %r12, %r12, 56146
	stw %r12, 40(%r4)
	lis %r12, 16656
	ori %r12, %r12, 2944
	stw %r12, 44(%r4)
	lis %r12, 29441
	ori %r12, %r12, 50571
	stw %r12, 48(%r4)
	lis %r12, -7862
	ori %r12, %r12, 58614
	stw %r12, 52(%r4)
	lis %r12, 4359
	ori %r12, %r12, 26039
	stw %r12, 56(%r4)
	lis %r12, -9550
	ori %r12, %r12, 15065
	stw %r12, 60(%r4)
	lis %r12, -26357
	ori %r12, %r12, 27048
	stw %r12, 64(%r4)
	lis %r12, -31774
	ori %r12, %r12, 24464
	stw %r12, 68(%r4)
	lis %r12, 20827
	ori %r12, %r12, 64091
	stw %r12, 72(%r4)
	lis %r12, -13096
	ori %r12, %r12, 18552
	stw %r12, 76(%r4)
	lis %r12, -27562
	ori %r12, %r12, 25199
	stw %r12, 80(%r4)
	lis %r12, -3395
	ori %r12, %r12, 5471
	stw %r12, 84(%r4)
	lis %r12, 5291
	ori %r12, %r12, 1688
	stw %r12, 88(%r4)
	lis %r12, -10448
	ori %r12, %r12, 52356
	stw %r12, 92(%r4)
	lis %r12, -25243
	ori %r12, %r12, 37417
	stw %r12, 96(%r4)
	lis %r12, 13406
	ori %r12, %r12, 1304
	stw %r12, 100(%r4)
	lis %r12, 19190
	ori %r12, %r12, 31496
	stw %r12, 104(%r4)
	lis %r12, 11423
	ori %r12, %r12, 871
	stw %r12, 108(%r4)
	lis %r12, -5026
	ori %r12, %r12, 36811
	stw %r12, 112(%r4)
	lis %r12, -28036
	ori %r12, %r12, 3037
	stw %r12, 116(%r4)
	lis %r12, 22018
	ori %r12, %r12, 44543
	stw %r12, 120(%r4)
	lis %r12, 17859
	ori %r12, %r12, 6715
	stw %r12, 124(%r4)
	lis %r12, 28169
	ori %r12, %r12, 54681
	stw %r12, 128(%r4)
	lis %r12, 24890
	ori %r12, %r12, 35296
	stw %r12, 132(%r4)
	lis %r12, 21431
	ori %r12, %r12, 27443
	stw %r12, 136(%r4)
	lis %r12, -28047
	ori %r12, %r12, 33083
	stw %r12, 140(%r4)
	lis %r12, -24328
	ori %r12, %r12, 64252
	stw %r12, 144(%r4)
	lis %r12, 16433
	ori %r12, %r12, 20435
	stw %r12, 148(%r4)
	lis %r12, 28972
	ori %r12, %r12, 14379
	stw %r12, 152(%r4)
	lis %r12, 9070
	ori %r12, %r12, 24913
	stw %r12, 156(%r4)
	lis %r12, 3082
	ori %r12, %r12, 19066
	stw %r12, 160(%r4)
	lis %r12, 7262
	ori %r12, %r12, 61827
	stw %r12, 164(%r4)
	lis %r12, 8566
	ori %r12, %r12, 46442
	stw %r12, 168(%r4)
	lis %r12, -27421
	ori %r12, %r12, 41406
	stw %r12, 172(%r4)
	lis %r12, 16201
	ori %r12, %r12, 64512
	stw %r12, 176(%r4)
	lis %r12, -31430
	ori %r12, %r12, 62898
	stw %r12, 180(%r4)
	lis %r12, 25352
	ori %r12, %r12, 43364
	stw %r12, 184(%r4)
	lis %r12, 16860
	ori %r12, %r12, 39586
	stw %r12, 188(%r4)
	lis %r12, 26706
	ori %r12, %r12, 19906
	stw %r12, 192(%r4)
	lis %r12, 13758
	ori %r12, %r12, 21801
	stw %r12, 196(%r4)
	lis %r12, -6394
	ori %r12, %r12, 49634
	stw %r12, 200(%r4)
	lis %r12, -27953
	ori %r12, %r12, 12454
	stw %r12, 204(%r4)
	lis %r12, 29378
	ori %r12, %r12, 39873
	stw %r12, 208(%r4)
	lis %r12, -15139
	ori %r12, %r12, 51688
	stw %r12, 212(%r4)
	lis %r12, -13428
	ori %r12, %r12, 60323
	stw %r12, 216(%r4)
	lis %r12, -30890
	ori %r12, %r12, 3188
	stw %r12, 220(%r4)
	lis %r12, -22658
	ori %r12, %r12, 40024
	stw %r12, 224(%r4)
	lis %r12, 24964
	ori %r12, %r12, 42086
	stw %r12, 228(%r4)
	lis %r12, 4354
	ori %r12, %r12, 45194
	stw %r12, 232(%r4)
	lis %r12, 30266
	ori %r12, %r12, 26541
	stw %r12, 236(%r4)
	lis %r12, 22813
	ori %r12, %r12, 64204
	stw %r12, 240(%r4)
	lis %r12, 14497
	ori %r12, %r12, 975
	stw %r12, 244(%r4)
	lis %r12, 26165
	ori %r12, %r12, 58028
	stw %r12, 248(%r4)
	lis %r12, 14533
	ori %r12, %r12, 4306
	stw %r12, 252(%r4)
	lis %r12, 9991
	ori %r12, %r12, 13182
	stw %r12, 256(%r4)
	lis %r12, 24031
	ori %r12, %r12, 22810
	stw %r12, 260(%r4)
	lis %r12, 30123
	ori %r12, %r12, 18406
	stw %r12, 264(%r4)
	lis %r12, -20610
	ori %r12, %r12, 15920
	stw %r12, 268(%r4)
	lis %r12, -25203
	ori %r12, %r12, 13842
	stw %r12, 272(%r4)
	lis %r12, 32714
	ori %r12, %r12, 35234
	stw %r12, 276(%r4)
	lis %r12, -2144
	ori %r12, %r12, 53316
	stw %r12, 280(%r4)
	lis %r12, -24411
	ori %r12, %r12, 59961
	stw %r12, 284(%r4)
	lis %r12, 15860
	ori %r12, %r12, 10382
	stw %r12, 288(%r4)
	lis %r12, 19620
	ori %r12, %r12, 37002
	stw %r12, 292(%r4)
	lis %r12, -29840
	ori %r12, %r12, 33545
	stw %r12, 296(%r4)
	lis %r12, 15152
	ori %r12, %r12, 3981
	stw %r12, 300(%r4)
	lis %r12, -23334
	ori %r12, %r12, 27985
	stw %r12, 304(%r4)
	lis %r12, 21984
	ori %r12, %r12, 44415
	stw %r12, 308(%r4)
	lis %r12, 32516
	ori %r12, %r12, 53302
	stw %r12, 312(%r4)
	lis %r12, -8677
	ori %r12, %r12, 28447
	stw %r12, 316(%r4)
	lis %r12, 3774
	ori %r12, %r12, 24954
	stw %r12, 320(%r4)
	lis %r12, 11949
	ori %r12, %r12, 44814
	stw %r12, 324(%r4)
	lis %r12, -23166
	ori %r12, %r12, 45409
	stw %r12, 328(%r4)
	lis %r12, 8984
	ori %r12, %r12, 14792
	stw %r12, 332(%r4)
	lis %r12, 1326
	ori %r12, %r12, 64436
	stw %r12, 336(%r4)
	lis %r12, -4424
	ori %r12, %r12, 59484
	stw %r12, 340(%r4)
	lis %r12, -26076
	ori %r12, %r12, 44022
	stw %r12, 344(%r4)
	lis %r12, 19256
	ori %r12, %r12, 42386
	stw %r12, 348(%r4)
	lis %r12, -27280
	ori %r12, %r12, 24300
	stw %r12, 352(%r4)
	lis %r12, -32583
	ori %r12, %r12, 64893
	stw %r12, 356(%r4)
	lis %r12, -25003
	ori %r12, %r12, 5640
	stw %r12, 360(%r4)
	lis %r12, 15544
	ori %r12, %r12, 63940
	stw %r12, 364(%r4)
	lis %r12, 1840
	ori %r12, %r12, 59948
	stw %r12, 368(%r4)
	lis %r12, 13578
	ori %r12, %r12, 13346
	stw %r12, 372(%r4)
	lis %r12, 25481
	ori %r12, %r12, 37789
	stw %r12, 376(%r4)
	lis %r12, -25417
	ori %r12, %r12, 23197
	stw %r12, 380(%r4)
	lis %r12, 13981
	ori %r12, %r12, 62736
	stw %r12, 384(%r4)
	lis %r12, -20171
	ori %r12, %r12, 58390
	stw %r12, 388(%r4)
	lis %r12, -17633
	ori %r12, %r12, 47736
	stw %r12, 392(%r4)
	lis %r12, -18699
	ori %r12, %r12, 23529
	stw %r12, 396(%r4)
	lis %r12, -32711
	ori %r12, %r12, 2369
	stw %r12, 400(%r4)
	lis %r12, 27231
	ori %r12, %r12, 21248
	stw %r12, 404(%r4)
	lis %r12, -18472
	ori %r12, %r12, 22694
	stw %r12, 408(%r4)
	lis %r12, -10167
	ori %r12, %r12, 45756
	stw %r12, 412(%r4)
	lis %r12, 19248
	ori %r12, %r12, 24961
	stw %r12, 416(%r4)
	lis %r12, -10305
	ori %r12, %r12, 37941
	stw %r12, 420(%r4)
	lis %r12, 4857
	ori %r12, %r12, 38463
	stw %r12, 424(%r4)
	lis %r12, 23741
	ori %r12, %r12, 50872
	stw %r12, 428(%r4)
	lis %r12, -9593
	ori %r12, %r12, 22560
	stw %r12, 432(%r4)
	lis %r12, 30510
	ori %r12, %r12, 2708
	stw %r12, 436(%r4)
	lis %r12, 26387
	ori %r12, %r12, 6135
	stw %r12, 440(%r4)
	lis %r12, 22880
	ori %r12, %r12, 18271
	stw %r12, 444(%r4)
	lis %r12, -21707
	ori %r12, %r12, 14327
	stw %r12, 448(%r4)
	lis %r12, 10607
	ori %r12, %r12, 39828
	stw %r12, 452(%r4)
	lis %r12, -21731
	ori %r12, %r12, 32777
	stw %r12, 456(%r4)
	lis %r12, 20983
	ori %r12, %r12, 35134
	stw %r12, 460(%r4)
	lis %r12, 18086
	ori %r12, %r12, 46367
	stw %r12, 464(%r4)
	lis %r12, -27118
	ori %r12, %r12, 25452
	stw %r12, 468(%r4)
	lis %r12, -3591
	ori %r12, %r12, 18542
	stw %r12, 472(%r4)
	lis %r12, -5109
	ori %r12, %r12, 19707
	stw %r12, 476(%r4)
	lis %r12, -2564
	ori %r12, %r12, 12063
	stw %r12, 480(%r4)
	lis %r12, 2727
	ori %r12, %r12, 49627
	stw %r12, 484(%r4)
	lis %r12, -18411
	ori %r12, %r12, 47101
	stw %r12, 488(%r4)
	lis %r12, 7907
	ori %r12, %r12, 59067
	stw %r12, 492(%r4)
	lis %r12, -15033
	ori %r12, %r12, 47203
	stw %r12, 496(%r4)
	lis %r12, -29863
	ori %r12, %r12, 53597
	stw %r12, 500(%r4)
	lis %r12, 13642
	ori %r12, %r12, 18471
	stw %r12, 504(%r4)
	lis %r12, -17492
	ori %r12, %r12, 32680
	stw %r12, 508(%r4)
	lis %r12, -20798
	ori %r12, %r12, 10028
	stw %r12, 512(%r4)
	lis %r12, 13
	ori %r12, %r12, 46445
	stw %r12, 516(%r4)
	lis %r12, -463
	ori %r12, %r12, 29792
	stw %r12, 520(%r4)
	lis %r12, 20804
	ori %r12, %r12, 49293
	stw %r12, 524(%r4)
	lis %r12, -11386
	ori %r12, %r12, 48648
	stw %r12, 528(%r4)
	lis %r12, -15136
	ori %r12, %r12, 49318
	stw %r12, 532(%r4)
	lis %r12, 21682
	ori %r12, %r12, 7133
	stw %r12, 536(%r4)
	lis %r12, -13922
	ori %r12, %r12, 25093
	stw %r12, 540(%r4)
	lis %r12, 4980
	ori %r12, %r12, 56079
	stw %r12, 544(%r4)
	lis %r12, 9245
	ori %r12, %r12, 19723
	stw %r12, 548(%r4)
	lis %r12, -25689
	ori %r12, %r12, 33961
	stw %r12, 552(%r4)
	lis %r12, -30943
	ori %r12, %r12, 46943
	stw %r12, 556(%r4)
	lis %r12, -31010
	ori %r12, %r12, 50339
	stw %r12, 560(%r4)
	lis %r12, 681
	ori %r12, %r12, 64121
	stw %r12, 564(%r4)
	lis %r12, -29068
	ori %r12, %r12, 64033
	stw %r12, 568(%r4)
	lis %r12, -17959
	ori %r12, %r12, 56579
	stw %r12, 572(%r4)
	lis %r12, 7893
	ori %r12, %r12, 24346
	stw %r12, 576(%r4)
	lis %r12, -218
	ori %r12, %r12, 33186
	stw %r12, 580(%r4)
	lis %r12, -30944
	ori %r12, %r12, 10491
	stw %r12, 584(%r4)
	lis %r12, -15480
	ori %r12, %r12, 4221
	stw %r12, 588(%r4)
	lis %r12, -19192
	ori %r12, %r12, 16550
	stw %r12, 592(%r4)
	lis %r12, 6432
	ori %r12, %r12, 25062
	stw %r12, 596(%r4)
	lis %r12, -29400
	ori %r12, %r12, 30979
	stw %r12, 600(%r4)
	lis %r12, 12487
	ori %r12, %r12, 23925
	stw %r12, 604(%r4)
	lis %r12, 20944
	ori %r12, %r12, 32636
	stw %r12, 608(%r4)
	lis %r12, -13179
	ori %r12, %r12, 57310
	stw %r12, 612(%r4)
	lis %r12, -1959
	ori %r12, %r12, 31341
	stw %r12, 616(%r4)
	lis %r12, -27770
	ori %r12, %r12, 42626
	stw %r12, 620(%r4)
	lis %r12, -29474
	ori %r12, %r12, 20602
	stw %r12, 624(%r4)
	lis %r12, -26672
	ori %r12, %r12, 58633
	stw %r12, 628(%r4)
	lis %r12, -19202
	ori %r12, %r12, 40509
	stw %r12, 632(%r4)
	lis %r12, 4973
	ori %r12, %r12, 17193
	stw %r12, 636(%r4)
	lis %r12, 17149
	ori %r12, %r12, 4798
	stw %r12, 640(%r4)
	lis %r12, -32425
	ori %r12, %r12, 42727
	stw %r12, 644(%r4)
	lis %r12, -2100
	ori %r12, %r12, 41785
	stw %r12, 648(%r4)
	lis %r12, 18670
	ori %r12, %r12, 44313
	stw %r12, 652(%r4)
	lis %r12, -13507
	ori %r12, %r12, 61413
	stw %r12, 656(%r4)
	lis %r12, -13862
	ori %r12, %r12, 7924
	stw %r12, 660(%r4)
	lis %r12, -24872
	ori %r12, %r12, 26332
	stw %r12, 664(%r4)
	lis %r12, -28245
	ori %r12, %r12, 40900
	stw %r12, 668(%r4)
	lis %r12, 9696
	ori %r12, %r12, 17861
	stw %r12, 672(%r4)
	lis %r12, 29304
	ori %r12, %r12, 283
	stw %r12, 676(%r4)
	lis %r12, 9807
	ori %r12, %r12, 61359
	stw %r12, 680(%r4)
	lis %r12, 24990
	ori %r12, %r12, 40676
	stw %r12, 684(%r4)
	lis %r12, -30018
	ori %r12, %r12, 37519
	stw %r12, 688(%r4)
	lis %r12, 17955
	ori %r12, %r12, 52839
	stw %r12, 692(%r4)
	lis %r12, -98
	ori %r12, %r12, 58810
	stw %r12, 696(%r4)
	lis %r12, 20668
	ori %r12, %r12, 30332
	stw %r12, 700(%r4)
	lis %r12, -699
	ori %r12, %r12, 42863
	stw %r12, 704(%r4)
	lis %r12, 23446
	ori %r12, %r12, 31463
	stw %r12, 708(%r4)
	lis %r12, -10247
	ori %r12, %r12, 38069
	stw %r12, 712(%r4)
	lis %r12, -10596
	ori %r12, %r12, 36726
	stw %r12, 716(%r4)
	lis %r12, 19652
	ori %r12, %r12, 9327
	stw %r12, 720(%r4)
	lis %r12, 1109
	ori %r12, %r12, 11074
	stw %r12, 724(%r4)
	lis %r12, -17349
	ori %r12, %r12, 18777
	stw %r12, 728(%r4)
	lis %r12, 4795
	ori %r12, %r12, 39617
	stw %r12, 732(%r4)
	lis %r12, 31594
	ori %r12, %r12, 57793
	stw %r12, 736(%r4)
	lis %r12, -3588
	ori %r12, %r12, 38721
	stw %r12, 740(%r4)
	lis %r12, -6403
	ori %r12, %r12, 11645
	stw %r12, 744(%r4)
	lis %r12, 15946
	ori %r12, %r12, 25115
	stw %r12, 748(%r4)
	lis %r12, -27153
	ori %r12, %r12, 62160
	stw %r12, 752(%r4)
	lis %r12, -15031
	ori %r12, %r12, 48869
	stw %r12, 756(%r4)
	lis %r12, -17040
	ori %r12, %r12, 12945
	stw %r12, 760(%r4)
	lis %r12, -14701
	ori %r12, %r12, 6457
	stw %r12, 764(%r4)
	lis %r12, -18569
	ori %r12, %r12, 55943
	stw %r12, 768(%r4)
	lis %r12, -12695
	ori %r12, %r12, 9900
	stw %r12, 772(%r4)
	lis %r12, 4128
	ori %r12, %r12, 57880
	stw %r12, 776(%r4)
	lis %r12, 4584
	ori %r12, %r12, 31739
	stw %r12, 780(%r4)
	lis %r12, -15905
	ori %r12, %r12, 23122
	stw %r12, 784(%r4)
	lis %r12, 16463
	ori %r12, %r12, 40807
	stw %r12, 788(%r4)
	lis %r12, -21454
	ori %r12, %r12, 10033
	stw %r12, 792(%r4)
	lis %r12, -9225
	ori %r12, %r12, 17433
	stw %r12, 796(%r4)
	lis %r12, 19482
	ori %r12, %r12, 32775
	stw %r12, 800(%r4)
	lis %r12, -11551
	ori %r12, %r12, 50891
	stw %r12, 804(%r4)
	lis %r12, -5669
	ori %r12, %r12, 61224
	stw %r12, 808(%r4)
	lis %r12, 3972
	ori %r12, %r12, 3812
	stw %r12, 812(%r4)
	lis %r12, -10895
	ori %r12, %r12, 20136
	stw %r12, 816(%r4)
	lis %r12, 15593
	ori %r12, %r12, 46579
	stw %r12, 820(%r4)
	lis %r12, -14347
	ori %r12, %r12, 49632
	stw %r12, 824(%r4)
	lis %r12, -9290
	ori %r12, %r12, 37869
	stw %r12, 828(%r4)
	lis %r12, 20707
	ori %r12, %r12, 44105
	stw %r12, 832(%r4)
	lis %r12, -23725
	ori %r12, %r12, 47527
	stw %r12, 836(%r4)
	lis %r12, 5861
	ori %r12, %r12, 52037
	stw %r12, 840(%r4)
	lis %r12, -20433
	ori %r12, %r12, 8808
	stw %r12, 844(%r4)
	lis %r12, 23536
	ori %r12, %r12, 41840
	stw %r12, 848(%r4)
	lis %r12, -2647
	ori %r12, %r12, 33397
	stw %r12, 852(%r4)
	lis %r12, -31459
	ori %r12, %r12, 35928
	stw %r12, 856(%r4)
	lis %r12, 32441
	ori %r12, %r12, 38760
	stw %r12, 860(%r4)
	lis %r12, -12634
	ori %r12, %r12, 22008
	stw %r12, 864(%r4)
	lis %r12, 31128
	ori %r12, %r12, 54081
	stw %r12, 868(%r4)
	lis %r12, 9099
	ori %r12, %r12, 32408
	stw %r12, 872(%r4)
	lis %r12, 13023
	ori %r12, %r12, 859
	stw %r12, 876(%r4)
	lis %r12, 13475
	ori %r12, %r12, 57999
	stw %r12, 880(%r4)
	lis %r12, 20090
	ori %r12, %r12, 996
	stw %r12, 884(%r4)
	lis %r12, -26349
	ori %r12, %r12, 54210
	stw %r12, 888(%r4)
	lis %r12, 15859
	ori %r12, %r12, 34918
	stw %r12, 892(%r4)
	lis %r12, -10718
	ori %r12, %r12, 24299
	stw %r12, 896(%r4)
	lis %r12, 31238
	ori %r12, %r12, 57027
	stw %r12, 900(%r4)
	lis %r12, 4264
	ori %r12, %r12, 59929
	stw %r12, 904(%r4)
	lis %r12, 26303
	ori %r12, %r12, 23305
	stw %r12, 908(%r4)
	lis %r12, 23619
	ori %r12, %r12, 57920
	stw %r12, 912(%r4)
	lis %r12, -93
	ori %r12, %r12, 6855
	stw %r12, 916(%r4)
	lis %r12, -6025
	ori %r12, %r12, 3058
	stw %r12, 920(%r4)
	lis %r12, 1680
	ori %r12, %r12, 25611
	stw %r12, 924(%r4)
	lis %r12, 3973
	ori %r12, %r12, 50001
	stw %r12, 928(%r4)
	lis %r12, 24285
	ori %r12, %r12, 58042
	stw %r12, 932(%r4)
	lis %r12, 1096
	ori %r12, %r12, 47653
	stw %r12, 936(%r4)
	lis %r12, 6726
	ori %r12, %r12, 29031
	stw %r12, 940(%r4)
	lis %r12, -4331
	ori %r12, %r12, 55704
	stw %r12, 944(%r4)
	lis %r12, -8629
	ori %r12, %r12, 45872
	stw %r12, 948(%r4)
	lis %r12, -11841
	ori %r12, %r12, 8228
	stw %r12, 952(%r4)
	lis %r12, 26826
	ori %r12, %r12, 31180
	stw %r12, 956(%r4)
	lis %r12, 18442
	ori %r12, %r12, 52258
	stw %r12, 960(%r4)
	lis %r12, -17088
	ori %r12, %r12, 22683
	stw %r12, 964(%r4)
	lis %r12, 22882
	ori %r12, %r12, 9174
	stw %r12, 968(%r4)
	lis %r12, -23574
	ori %r12, %r12, 54125
	stw %r12, 972(%r4)
	lis %r12, -17151
	ori %r12, %r12, 49910
	stw %r12, 976(%r4)
	lis %r12, 24428
	ori %r12, %r12, 15952
	stw %r12, 980(%r4)
	lis %r12, -3072
	ori %r12, %r12, 64086
	stw %r12, 984(%r4)
	lis %r12, -13426
	ori %r12, %r12, 18426
	stw %r12, 988(%r4)
	lis %r12, -31082
	ori %r12, %r12, 64689
	stw %r12, 992(%r4)
	lis %r12, -2370
	ori %r12, %r12, 30127
	stw %r12, 996(%r4)
	lis %r12, 8246
	ori %r12, %r12, 10569
	stw %r12, 1000(%r4)
	lis %r12, 14858
	ori %r12, %r12, 43574
	stw %r12, 1004(%r4)
	lis %r12, -29512
	ori %r12, %r12, 59680
	stw %r12, 1008(%r4)
	lis %r12, 27614
	ori %r12, %r12, 45268
	stw %r12, 1012(%r4)
	lis %r12, -5720
	ori %r12, %r12, 5682
	stw %r12, 1016(%r4)
	lis %r12, -6115
	ori %r12, %r12, 41368
	stw %r12, 1020(%r4)
	lis %r12, 127
	ori %r12, %r12, 57345
	mtvsrd 36, %r12
	vspltw %v4, %v4, 1
	lis %r12, 1
	ori %r12, %r12, 515
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4113
	ori %r12, %r12, 4627
	lis %r11, 2057
	ori %r11, %r11, 2571
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 6169
	ori %r11, %r11, 6683
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v5, %v6, %v6, 8
	vsldoi %v5, %v5, %v7, 8
	lis %r12, 1
	ori %r12, %r12, 515
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4113
	ori %r12, %r12, 4627
	lis %r11, 1029
	ori %r11, %r11, 1543
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 5141
	ori %r11, %r11, 5655
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v16, %v6, %v6, 8
	vsldoi %v16, %v16, %v7, 8
	lis %r12, 2057
	ori %r12, %r12, 2571
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6169
	ori %r12, %r12, 6683
	lis %r11, 3085
	ori %r11, %r11, 3599
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 7197
	ori %r11, %r11, 7711
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v17, %v6, %v6, 8
	vsldoi %v17, %v17, %v7, 8
	lis %r12, 1
	ori %r12, %r12, 515
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1029
	ori %r12, %r12, 1543
	lis %r11, 4113
	ori %r11, %r11, 4627
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 5141
	ori %r11, %r11, 5655
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v18, %v6, %v6, 8
	vsldoi %v18, %v18, %v7, 8
	lis %r12, 2057
	ori %r12, %r12, 2571
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 3085
	ori %r12, %r12, 3599
	lis %r11, 6169
	ori %r11, %r11, 6683
	rldicr %r11, %r11, 32, 31
	oris %r11, %r11, 7197
	ori %r11, %r11, 7711
	mtvsrd 38, %r12
	mtvsrd 39, %r11
	vsldoi %v19, %v6, %v6, 8
	vsldoi %v19, %v19, %v7, 8
	li %r8, 512
	addi %r11, %r3, 1024
	li %r9, 0
	addi %r7, %r4, 0
20:
	addi %r5, %r3, 0
21:
	lxvd2x 35, %r7, %r9
	vspltw %v3, %v3, 0
	addi %r7, %r7, 4
	vmuleuw %v6, %v3, %v4
	vmulouw %v7, %v3, %v4
	vperm %v6, %v6, %v7, %v5
	vspltisw %v7, 1
	vadduwm %v2, %v6, %v7
	rldicl %r10, %r8, 60, 4
22:
	lxvd2x 32, %r5, %r9
	lxvd2x 33, %r5, %r8
	vmuleuw %v6, %v1, %v3
	vmulouw %v7, %v1, %v3
	vperm %v6, %v6, %v7, %v5
	vmuluwm %v7, %v1, %v2
	vmuluwm %v6, %v6, %v4
	vsubuwm %v7, %v7, %v6
	vsubuwm %v6, %v7, %v4
	vminuw %v7, %v7, %v6
	vadduwm %v6, %v0, %v7
	vsubuwm %v1, %v0, %v7
	vsubuwm %v0, %v6, %v4
	vminuw %v0, %v6, %v0
	vadduwm %v6, %v1, %v4
	vminuw %v1, %v1, %v6
	stxvd2x 32, %r5, %r9
	stxvd2x 33, %r5, %r8
	addi %r5, %r5, 16
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 22b
	add %r5, %r5, %r8
	subf %r12, %r11, %r5
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	rldicl %r8, %r8, 63, 1
	addi %r12, %r8, -8
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	addi %r5, %r3, 0
	li %r8, 16
	li %r11, 32
	li %r12, 48
	li %r10, 16
	addi %r6, %r4, 256
	addi %r7, %r4, 512
23:
	lxvd2x 40, %r5, %r9
	lxvd2x 41, %r5, %r8
	lxvd2x 42, %r5, %r11
	lxvd2x 43, %r5, %r12
	vperm %v12, %v8, %v9, %v16
	vperm %v13, %v8, %v9, %v17
	vperm %v14, %v10, %v11, %v16
	vperm %v15, %v10, %v11, %v17
	vperm %v8, %v12, %v14, %v18
	vperm %v9, %v12, %v14, %v19
	vperm %v10, %v13, %v15, %v18
	vperm %v11, %v13, %v15, %v19
	lxvd2x 35, %r6, %r9
	vmuleuw %v6, %v3, %v4
	vmulouw %v7, %v3, %v4
	vperm %v6, %v6, %v7, %v5
	vspltisw %v7, 1
	vadduwm %v2, %v6, %v7
	vmuleuw %v6, %v11, %v3
	vmulouw %v7, %v11, %v3
	vperm %v6, %v6, %v7, %v5
	vmuluwm %v7, %v11, %v2
	vmuluwm %v6, %v6, %v4
	vsubuwm %v7, %v7, %v6
	vsubuwm %v6, %v7, %v4
	vminuw %v7, %v7, %v6
	vadduwm %v6, %v9, %v7
	vsubuwm %v11, %v9, %v7
	vsubuwm %v9, %v6, %v4
	vminuw %v9, %v6, %v9
	vadduwm %v6, %v11, %v4
	vminuw %v11, %v11, %v6
	vmuleuw %v6, %v10, %v3
	vmulouw %v7, %v10, %v3
	vperm %v6, %v6, %v7, %v5
	vmuluwm %v7, %v10, %v2
	vmuluwm %v6, %v6, %v4
	vsubuwm %v7, %v7, %v6
	vsubuwm %v6, %v7, %v4
	vminuw %v7, %v7, %v6
	vadduwm %v6, %v8, %v7
	vsubuwm %v10, %v8, %v7
	vsubuwm %v8, %v6, %v4
	vminuw %v8, %v6, %v8
	vadduwm %v6, %v10, %v4
	vminuw %v10, %v10, %v6
	lxvd2x 35, %r7, %r9
	vmuleuw %v6, %v3, %v4
	vmulouw %v7, %v3, %v4
	vperm %v6, %v6, %v7, %v5
	vspltisw %v7, 1
	vadduwm %v2, %v6, %v7
	vmuleuw %v6, %v8, %v3
	vmulouw %v7, %v8, %v3
	vperm %v6, %v6, %v7, %v5
	vmuluwm %v7, %v8, %v2
	vmuluwm %v6, %v6, %v4
	vsubuwm %v7, %v7, %v6
	vsubuwm %v6, %v7, %v4
	vminuw %v7, %v7, %v6
	vadduwm %v6, %v9, %v7
	vsubuwm %v8, %v9, %v7
	vsubuwm %v9, %v6, %v4
	vminuw %v9, %v6, %v9
	vadduwm %v6, %v8, %v4
	vminuw %v8, %v8, %v6
	lxvd2x 35, %r7, %r8
	vmuleuw %v6, %v3, %v4
	vmulouw %v7, %v3, %v4
	vperm %v6, %v6, %v7, %v5
	vspltisw %v7, 1
	vadduwm %v2, %v6, %v7
	addi %r6, %r6, 16
	addi %r7, %r7, 32
	vmuleuw %v6, %v10, %v3
	vmulouw %v7, %v10, %v3
	vperm %v6, %v6, %v7, %v5
	vmuluwm %v7, %v10, %v2
	vmuluwm %v6, %v6, %v4
	vsubuwm %v7, %v7, %v6
	vsubuwm %v6, %v7, %v4
	vminuw %v7, %v7, %v6
	vadduwm %v6, %v11, %v7
	vsubuwm %v10, %v11, %v7
	vsubuwm %v11, %v6, %v4
	vminuw %v11, %v6, %v11
	vadduwm %v6, %v10, %v4
	vminuw %v10, %v10, %v6
	vperm %v12, %v8, %v9, %v16
	vperm %v13, %v8, %v9, %v17
	vperm %v14, %v10, %v11, %v16
	vperm %v15, %v10, %v11, %v17
	vperm %v8, %v12, %v14, %v18
	vperm %v9, %v12, %v14, %v19
	vperm %v10, %v13, %v15, %v18
	vperm %v11, %v13, %v15, %v19
	stxvd2x 40, %r5, %r9
	stxvd2x 41, %r5, %r8
	stxvd2x 42, %r5, %r11
	stxvd2x 43, %r5, %r12
	addi %r5, %r5, 64
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 23b
	blr
