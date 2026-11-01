// The functions of `src/internal/vg_ecdsa_brainpoolp384r1_sign.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp384r1_sign:
	std %r14, 0(%r7)
	std %r31, 8(%r7)
	mflr %r0
	std %r0, 16(%r7)
	or %r14, %r3, %r3
	or %r3, %r7, %r7
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 1552(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1560(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1568(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1576(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1584(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1592(%r3)
	li %r9, 40
	ldbrx %r8, %r4, %r9
	std %r8, 1600(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 1608(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1616(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1624(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1632(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 1640(%r3)
	li %r9, 40
	ldbrx %r8, %r5, %r9
	std %r8, 1648(%r3)
	li %r9, 32
	ldbrx %r8, %r5, %r9
	std %r8, 1656(%r3)
	li %r9, 24
	ldbrx %r8, %r5, %r9
	std %r8, 1664(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 1672(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 1680(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 1688(%r3)
	lis %r11, 12551
	ori %r11, %r11, 60499
	stw %r11, 64(%r3)
	lis %r11, -30905
	ori %r11, %r11, 19
	stw %r11, 68(%r3)
	lis %r11, -28643
	ori %r11, %r11, 6769
	stw %r11, 72(%r3)
	lis %r11, -21293
	ori %r11, %r11, 42793
	stw %r11, 76(%r3)
	lis %r11, 32695
	ori %r11, %r11, 4387
	stw %r11, 80(%r3)
	lis %r11, 4785
	ori %r11, %r11, 55833
	stw %r11, 84(%r3)
	lis %r11, -4780
	ori %r11, %r11, 22196
	stw %r11, 88(%r3)
	lis %r11, 5423
	ori %r11, %r11, 28937
	stw %r11, 92(%r3)
	lis %r11, 20710
	ori %r11, %r11, 16863
	stw %r11, 96(%r3)
	lis %r11, 3933
	ori %r11, %r11, 28542
	stw %r11, 100(%r3)
	lis %r11, -23752
	ori %r11, %r11, 27944
	stw %r11, 104(%r3)
	lis %r11, -29511
	ori %r11, %r11, 7810
	stw %r11, 108(%r3)
	lis %r11, -5884
	ori %r11, %r11, 25957
	stw %r11, 112(%r3)
	lis %r11, 15240
	ori %r11, %r11, 12802
	stw %r11, 116(%r3)
	lis %r11, 27519
	ori %r11, %r11, 49936
	stw %r11, 120(%r3)
	lis %r11, -12486
	ori %r11, %r11, 46767
	stw %r11, 124(%r3)
	lis %r11, -21500
	ori %r11, %r11, 9639
	stw %r11, 128(%r3)
	lis %r11, 7958
	ori %r11, %r11, 28268
	stw %r11, 132(%r3)
	lis %r11, -4780
	ori %r11, %r11, 22195
	stw %r11, 136(%r3)
	lis %r11, 5423
	ori %r11, %r11, 28937
	stw %r11, 140(%r3)
	lis %r11, 20710
	ori %r11, %r11, 16863
	stw %r11, 144(%r3)
	lis %r11, 3933
	ori %r11, %r11, 28542
	stw %r11, 148(%r3)
	lis %r11, -23752
	ori %r11, %r11, 27944
	stw %r11, 152(%r3)
	lis %r11, -29511
	ori %r11, %r11, 7810
	stw %r11, 156(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 208(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 212(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 216(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 220(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 236(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 240(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 244(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 252(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 256(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 260(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 264(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 268(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 276(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 280(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 284(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 288(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 292(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 296(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 300(%r3)
	lis %r11, -12552
	ori %r11, %r11, 5037
	stw %r11, 304(%r3)
	lis %r11, 30904
	ori %r11, %r11, 65516
	stw %r11, 308(%r3)
	lis %r11, 28642
	ori %r11, %r11, 58766
	stw %r11, 312(%r3)
	lis %r11, 21292
	ori %r11, %r11, 22742
	stw %r11, 316(%r3)
	lis %r11, -32696
	ori %r11, %r11, 61148
	stw %r11, 320(%r3)
	lis %r11, -4786
	ori %r11, %r11, 9702
	stw %r11, 324(%r3)
	lis %r11, 4779
	ori %r11, %r11, 43339
	stw %r11, 328(%r3)
	lis %r11, -5424
	ori %r11, %r11, 36598
	stw %r11, 332(%r3)
	lis %r11, -20711
	ori %r11, %r11, 48672
	stw %r11, 336(%r3)
	lis %r11, -3934
	ori %r11, %r11, 36993
	stw %r11, 340(%r3)
	lis %r11, 23751
	ori %r11, %r11, 37591
	stw %r11, 344(%r3)
	lis %r11, 29510
	ori %r11, %r11, 57725
	stw %r11, 348(%r3)
	lis %r11, 18028
	ori %r11, %r11, 15513
	stw %r11, 352(%r3)
	lis %r11, -9434
	ori %r11, %r11, 47253
	stw %r11, 356(%r3)
	lis %r11, -3753
	ori %r11, %r11, 45179
	stw %r11, 360(%r3)
	lis %r11, 30167
	ori %r11, %r11, 62462
	stw %r11, 364(%r3)
	lis %r11, -10255
	ori %r11, %r11, 3508
	stw %r11, 368(%r3)
	lis %r11, -27801
	ori %r11, %r11, 29113
	stw %r11, 372(%r3)
	lis %r11, 13650
	ori %r11, %r11, 37748
	stw %r11, 376(%r3)
	lis %r11, -6145
	ori %r11, %r11, 59877
	stw %r11, 380(%r3)
	lis %r11, 17072
	ori %r11, %r11, 3168
	stw %r11, 384(%r3)
	lis %r11, 16394
	ori %r11, %r11, 36831
	stw %r11, 388(%r3)
	lis %r11, -23832
	ori %r11, %r11, 49361
	stw %r11, 392(%r3)
	lis %r11, 31795
	ori %r11, %r11, 32801
	stw %r11, 396(%r3)
	lis %r11, -11950
	ori %r11, %r11, 47092
	stw %r11, 400(%r3)
	lis %r11, -10806
	ori %r11, %r11, 63914
	stw %r11, 404(%r3)
	lis %r11, -12047
	ori %r11, %r11, 5431
	stw %r11, 408(%r3)
	lis %r11, -2631
	ori %r11, %r11, 16430
	stw %r11, 412(%r3)
	lis %r11, 26029
	ori %r11, %r11, 15210
	stw %r11, 416(%r3)
	lis %r11, 22123
	ori %r11, %r11, 10802
	stw %r11, 420(%r3)
	lis %r11, 3603
	ori %r11, %r11, 42454
	stw %r11, 424(%r3)
	lis %r11, 12436
	ori %r11, %r11, 14190
	stw %r11, 428(%r3)
	lis %r11, 9345
	ori %r11, %r11, 11832
	stw %r11, 432(%r3)
	lis %r11, 29244
	ori %r11, %r11, 37895
	stw %r11, 436(%r3)
	lis %r11, 5531
	ori %r11, %r11, 9942
	stw %r11, 440(%r3)
	lis %r11, 17152
	ori %r11, %r11, 20078
	stw %r11, 444(%r3)
	lis %r11, -11208
	ori %r11, %r11, 64449
	stw %r11, 448(%r3)
	lis %r11, -24183
	ori %r11, %r11, 57067
	stw %r11, 452(%r3)
	lis %r11, -10840
	ori %r11, %r11, 34495
	stw %r11, 456(%r3)
	lis %r11, 26364
	ori %r11, %r11, 33000
	stw %r11, 460(%r3)
	lis %r11, -25312
	ori %r11, %r11, 12067
	stw %r11, 464(%r3)
	lis %r11, -27453
	ori %r11, %r11, 30953
	stw %r11, 468(%r3)
	lis %r11, -1700
	ori %r11, %r11, 8548
	stw %r11, 472(%r3)
	lis %r11, 1675
	ori %r11, %r11, 9806
	stw %r11, 476(%r3)
	lis %r11, -17715
	ori %r11, %r11, 153
	stw %r11, 480(%r3)
	lis %r11, -25379
	ori %r11, %r11, 3535
	stw %r11, 484(%r3)
	lis %r11, -30475
	ori %r11, %r11, 16321
	stw %r11, 488(%r3)
	lis %r11, -31488
	ori %r11, %r11, 30003
	stw %r11, 492(%r3)
	lis %r11, 3553
	ori %r11, %r11, 16549
	stw %r11, 496(%r3)
	lis %r11, -6344
	ori %r11, %r11, 45873
	stw %r11, 500(%r3)
	lis %r11, -14439
	ori %r11, %r11, 28501
	stw %r11, 504(%r3)
	lis %r11, -2592
	ori %r11, %r11, 53830
	stw %r11, 508(%r3)
	lis %r11, -28921
	ori %r11, %r11, 14332
	stw %r11, 512(%r3)
	lis %r11, -1917
	ori %r11, %r11, 2467
	stw %r11, 516(%r3)
	lis %r11, -10895
	ori %r11, %r11, 37399
	stw %r11, 520(%r3)
	lis %r11, -24192
	ori %r11, %r11, 44244
	stw %r11, 524(%r3)
	lis %r11, 20257
	ori %r11, %r11, 56758
	stw %r11, 528(%r3)
	lis %r11, -14826
	ori %r11, %r11, 9574
	stw %r11, 532(%r3)
	lis %r11, 17801
	ori %r11, %r11, 26805
	stw %r11, 536(%r3)
	lis %r11, 11508
	ori %r11, %r11, 41058
	stw %r11, 540(%r3)
	lis %r11, -8585
	ori %r11, %r11, 7310
	stw %r11, 544(%r3)
	lis %r11, -21426
	ori %r11, %r11, 54178
	stw %r11, 548(%r3)
	lis %r11, 12075
	ori %r11, %r11, 27502
	stw %r11, 552(%r3)
	lis %r11, 14118
	ori %r11, %r11, 20000
	stw %r11, 556(%r3)
	lis %r11, -26622
	ori %r11, %r11, 26762
	stw %r11, 560(%r3)
	lis %r11, 10898
	ori %r11, %r11, 32315
	stw %r11, 564(%r3)
	lis %r11, 21207
	ori %r11, %r11, 18687
	stw %r11, 568(%r3)
	lis %r11, 22346
	ori %r11, %r11, 29899
	stw %r11, 572(%r3)
	lis %r11, 25878
	ori %r11, %r11, 24539
	stw %r11, 576(%r3)
	lis %r11, -28792
	ori %r11, %r11, 28105
	stw %r11, 580(%r3)
	lis %r11, 24910
	ori %r11, %r11, 38850
	stw %r11, 584(%r3)
	lis %r11, 3304
	ori %r11, %r11, 37914
	stw %r11, 588(%r3)
	lis %r11, 5883
	ori %r11, %r11, 39579
	stw %r11, 592(%r3)
	lis %r11, -15241
	ori %r11, %r11, 52733
	stw %r11, 596(%r3)
	lis %r11, -27520
	ori %r11, %r11, 15599
	stw %r11, 600(%r3)
	lis %r11, 12485
	ori %r11, %r11, 18768
	stw %r11, 604(%r3)
	lis %r11, 21499
	ori %r11, %r11, 55896
	stw %r11, 608(%r3)
	lis %r11, -7959
	ori %r11, %r11, 37267
	stw %r11, 612(%r3)
	lis %r11, 4779
	ori %r11, %r11, 43340
	stw %r11, 616(%r3)
	lis %r11, -5424
	ori %r11, %r11, 36598
	stw %r11, 620(%r3)
	lis %r11, -20711
	ori %r11, %r11, 48672
	stw %r11, 624(%r3)
	lis %r11, -3934
	ori %r11, %r11, 36993
	stw %r11, 628(%r3)
	lis %r11, 23751
	ori %r11, %r11, 37591
	stw %r11, 632(%r3)
	lis %r11, 29510
	ori %r11, %r11, 57725
	stw %r11, 636(%r3)
	lis %r11, 12551
	ori %r11, %r11, 60497
	stw %r11, 640(%r3)
	lis %r11, -30905
	ori %r11, %r11, 19
	stw %r11, 644(%r3)
	lis %r11, -28643
	ori %r11, %r11, 6769
	stw %r11, 648(%r3)
	lis %r11, -21293
	ori %r11, %r11, 42793
	stw %r11, 652(%r3)
	lis %r11, 32695
	ori %r11, %r11, 4387
	stw %r11, 656(%r3)
	lis %r11, 4785
	ori %r11, %r11, 55833
	stw %r11, 660(%r3)
	lis %r11, -4780
	ori %r11, %r11, 22196
	stw %r11, 664(%r3)
	lis %r11, 5423
	ori %r11, %r11, 28937
	stw %r11, 668(%r3)
	lis %r11, 20710
	ori %r11, %r11, 16863
	stw %r11, 672(%r3)
	lis %r11, 3933
	ori %r11, %r11, 28542
	stw %r11, 676(%r3)
	lis %r11, -23752
	ori %r11, %r11, 27944
	stw %r11, 680(%r3)
	lis %r11, -29511
	ori %r11, %r11, 7810
	stw %r11, 684(%r3)
	lis %r11, -5884
	ori %r11, %r11, 25955
	stw %r11, 688(%r3)
	lis %r11, 15240
	ori %r11, %r11, 12802
	stw %r11, 692(%r3)
	lis %r11, 27519
	ori %r11, %r11, 49936
	stw %r11, 696(%r3)
	lis %r11, -12486
	ori %r11, %r11, 46767
	stw %r11, 700(%r3)
	lis %r11, -21500
	ori %r11, %r11, 9639
	stw %r11, 704(%r3)
	lis %r11, 7958
	ori %r11, %r11, 28268
	stw %r11, 708(%r3)
	lis %r11, -4780
	ori %r11, %r11, 22195
	stw %r11, 712(%r3)
	lis %r11, 5423
	ori %r11, %r11, 28937
	stw %r11, 716(%r3)
	lis %r11, 20710
	ori %r11, %r11, 16863
	stw %r11, 720(%r3)
	lis %r11, 3933
	ori %r11, %r11, 28542
	stw %r11, 724(%r3)
	lis %r11, -23752
	ori %r11, %r11, 27944
	stw %r11, 728(%r3)
	lis %r11, -29511
	ori %r11, %r11, 7810
	stw %r11, 732(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 736(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 740(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 744(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 748(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 752(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 756(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 760(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 764(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 768(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 772(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 776(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 780(%r3)
	lis %r11, -12552
	ori %r11, %r11, 5037
	stw %r11, 784(%r3)
	lis %r11, 30904
	ori %r11, %r11, 65516
	stw %r11, 788(%r3)
	lis %r11, 28642
	ori %r11, %r11, 58766
	stw %r11, 792(%r3)
	lis %r11, 21292
	ori %r11, %r11, 22742
	stw %r11, 796(%r3)
	lis %r11, -32696
	ori %r11, %r11, 61148
	stw %r11, 800(%r3)
	lis %r11, -4786
	ori %r11, %r11, 9702
	stw %r11, 804(%r3)
	lis %r11, 4779
	ori %r11, %r11, 43339
	stw %r11, 808(%r3)
	lis %r11, -5424
	ori %r11, %r11, 36598
	stw %r11, 812(%r3)
	lis %r11, -20711
	ori %r11, %r11, 48672
	stw %r11, 816(%r3)
	lis %r11, -3934
	ori %r11, %r11, 36993
	stw %r11, 820(%r3)
	lis %r11, 23751
	ori %r11, %r11, 37591
	stw %r11, 824(%r3)
	lis %r11, 29510
	ori %r11, %r11, 57725
	stw %r11, 828(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 832(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 836(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 840(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 844(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 848(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 852(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 856(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 860(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 864(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 868(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 872(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 876(%r3)
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 2176(%r3)
	li %r31, 48
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1552(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4096(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4097(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4098(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4099(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4100(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4101(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4102(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4103(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	li %r31, 48
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 640(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4480(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4481(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4482(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4483(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4484(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4485(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4486(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4487(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r31, 48
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 688(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4864(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4865(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4866(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4867(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4868(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4869(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4870(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4871(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	ld %r4, 448(%r3)
	std %r4, 3120(%r3)
	ld %r4, 456(%r3)
	std %r4, 3128(%r3)
	ld %r4, 464(%r3)
	std %r4, 3136(%r3)
	ld %r4, 472(%r3)
	std %r4, 3144(%r3)
	ld %r4, 480(%r3)
	std %r4, 3152(%r3)
	ld %r4, 488(%r3)
	std %r4, 3160(%r3)
	ld %r4, 496(%r3)
	std %r4, 3168(%r3)
	ld %r4, 504(%r3)
	std %r4, 3176(%r3)
	ld %r4, 512(%r3)
	std %r4, 3184(%r3)
	ld %r4, 520(%r3)
	std %r4, 3192(%r3)
	ld %r4, 528(%r3)
	std %r4, 3200(%r3)
	ld %r4, 536(%r3)
	std %r4, 3208(%r3)
	ld %r4, 304(%r3)
	std %r4, 3216(%r3)
	ld %r4, 312(%r3)
	std %r4, 3224(%r3)
	ld %r4, 320(%r3)
	std %r4, 3232(%r3)
	ld %r4, 328(%r3)
	std %r4, 3240(%r3)
	ld %r4, 336(%r3)
	std %r4, 3248(%r3)
	ld %r4, 344(%r3)
	std %r4, 3256(%r3)
	ld %r4, 352(%r3)
	std %r4, 3264(%r3)
	ld %r4, 360(%r3)
	std %r4, 3272(%r3)
	ld %r4, 368(%r3)
	std %r4, 3280(%r3)
	ld %r4, 376(%r3)
	std %r4, 3288(%r3)
	ld %r4, 384(%r3)
	std %r4, 3296(%r3)
	ld %r4, 392(%r3)
	std %r4, 3304(%r3)
	ld %r4, 400(%r3)
	std %r4, 3312(%r3)
	ld %r4, 408(%r3)
	std %r4, 3320(%r3)
	ld %r4, 416(%r3)
	std %r4, 3328(%r3)
	ld %r4, 424(%r3)
	std %r4, 3336(%r3)
	ld %r4, 432(%r3)
	std %r4, 3344(%r3)
	ld %r4, 440(%r3)
	std %r4, 3352(%r3)
	li %r31, 384
23:
	addi %r31, %r31, -1
	ld %r4, 736(%r3)
	std %r4, 2976(%r3)
	ld %r4, 744(%r3)
	std %r4, 2984(%r3)
	ld %r4, 752(%r3)
	std %r4, 2992(%r3)
	ld %r4, 760(%r3)
	std %r4, 3000(%r3)
	ld %r4, 768(%r3)
	std %r4, 3008(%r3)
	ld %r4, 776(%r3)
	std %r4, 3016(%r3)
	ld %r4, 784(%r3)
	std %r4, 3024(%r3)
	ld %r4, 792(%r3)
	std %r4, 3032(%r3)
	ld %r4, 800(%r3)
	std %r4, 3040(%r3)
	ld %r4, 808(%r3)
	std %r4, 3048(%r3)
	ld %r4, 816(%r3)
	std %r4, 3056(%r3)
	ld %r4, 824(%r3)
	std %r4, 3064(%r3)
	ld %r4, 832(%r3)
	std %r4, 3072(%r3)
	ld %r4, 840(%r3)
	std %r4, 3080(%r3)
	ld %r4, 848(%r3)
	std %r4, 3088(%r3)
	ld %r4, 856(%r3)
	std %r4, 3096(%r3)
	ld %r4, 864(%r3)
	std %r4, 3104(%r3)
	ld %r4, 872(%r3)
	std %r4, 3112(%r3)
	bl {vg_brainpoolp384r1_point_double}
	ld %r4, 2832(%r3)
	std %r4, 2976(%r3)
	ld %r4, 2840(%r3)
	std %r4, 2984(%r3)
	ld %r4, 2848(%r3)
	std %r4, 2992(%r3)
	ld %r4, 2856(%r3)
	std %r4, 3000(%r3)
	ld %r4, 2864(%r3)
	std %r4, 3008(%r3)
	ld %r4, 2872(%r3)
	std %r4, 3016(%r3)
	ld %r4, 2880(%r3)
	std %r4, 3024(%r3)
	ld %r4, 2888(%r3)
	std %r4, 3032(%r3)
	ld %r4, 2896(%r3)
	std %r4, 3040(%r3)
	ld %r4, 2904(%r3)
	std %r4, 3048(%r3)
	ld %r4, 2912(%r3)
	std %r4, 3056(%r3)
	ld %r4, 2920(%r3)
	std %r4, 3064(%r3)
	ld %r4, 2928(%r3)
	std %r4, 3072(%r3)
	ld %r4, 2936(%r3)
	std %r4, 3080(%r3)
	ld %r4, 2944(%r3)
	std %r4, 3088(%r3)
	ld %r4, 2952(%r3)
	std %r4, 3096(%r3)
	ld %r4, 2960(%r3)
	std %r4, 3104(%r3)
	ld %r4, 2968(%r3)
	std %r4, 3112(%r3)
	bl {vg_brainpoolp384r1_point_add}
	add %r4, %r3, %r31
	lbz %r4, 4096(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 2976(%r3)
	ld %r5, 2832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 736(%r3)
	ld %r4, 2984(%r3)
	ld %r5, 2840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 744(%r3)
	ld %r4, 2992(%r3)
	ld %r5, 2848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 752(%r3)
	ld %r4, 3000(%r3)
	ld %r5, 2856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 760(%r3)
	ld %r4, 3008(%r3)
	ld %r5, 2864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 768(%r3)
	ld %r4, 3016(%r3)
	ld %r5, 2872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 776(%r3)
	ld %r4, 3024(%r3)
	ld %r5, 2880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 3032(%r3)
	ld %r5, 2888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 3040(%r3)
	ld %r5, 2896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 3048(%r3)
	ld %r5, 2904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 3056(%r3)
	ld %r5, 2912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 3064(%r3)
	ld %r5, 2920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	ld %r4, 3072(%r3)
	ld %r5, 2928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 832(%r3)
	ld %r4, 3080(%r3)
	ld %r5, 2936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 840(%r3)
	ld %r4, 3088(%r3)
	ld %r5, 2944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 848(%r3)
	ld %r4, 3096(%r3)
	ld %r5, 2952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 856(%r3)
	ld %r4, 3104(%r3)
	ld %r5, 2960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 864(%r3)
	ld %r4, 3112(%r3)
	ld %r5, 2968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 872(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	ld %r4, 304(%r3)
	std %r4, 1456(%r3)
	ld %r4, 312(%r3)
	std %r4, 1464(%r3)
	ld %r4, 320(%r3)
	std %r4, 1472(%r3)
	ld %r4, 328(%r3)
	std %r4, 1480(%r3)
	ld %r4, 336(%r3)
	std %r4, 1488(%r3)
	ld %r4, 344(%r3)
	std %r4, 1496(%r3)
	li %r31, 384
24:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1504
	li %r5, 1456
	li %r6, 832
	bl {vg_brainpoolp384r1_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 4480(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 1456(%r3)
	ld %r5, 1504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1456(%r3)
	ld %r4, 1464(%r3)
	ld %r5, 1512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1464(%r3)
	ld %r4, 1472(%r3)
	ld %r5, 1520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r4, 1480(%r3)
	ld %r5, 1528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1480(%r3)
	ld %r4, 1488(%r3)
	ld %r5, 1536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1488(%r3)
	ld %r4, 1496(%r3)
	ld %r5, 1544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1496(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 1696
	li %r5, 736
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1744
	li %r5, 1696
	li %r6, 256
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1792
	li %r5, 1744
	li %r6, 208
	bl {vg_brainpoolp384r1_add_mod_n}
	li %r4, 1840
	li %r5, 1552
	li %r6, 544
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1600(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1604(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1608(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1612(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1616(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1620(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1624(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1628(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1632(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1636(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1640(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1644(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1600(%r3)
	ld %r4, 1608(%r3)
	or %r5, %r5, %r4
	ld %r4, 1616(%r3)
	or %r5, %r5, %r4
	ld %r4, 1624(%r3)
	or %r5, %r5, %r4
	ld %r4, 1632(%r3)
	or %r5, %r5, %r4
	ld %r4, 1640(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1552(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1556(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1560(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1564(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1568(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1572(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1576(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1580(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1584(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1588(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1592(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1596(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1552(%r3)
	ld %r4, 1560(%r3)
	or %r5, %r5, %r4
	ld %r4, 1568(%r3)
	or %r5, %r5, %r4
	ld %r4, 1576(%r3)
	or %r5, %r5, %r4
	ld %r4, 1584(%r3)
	or %r5, %r5, %r4
	ld %r4, 1592(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r5, 1792(%r3)
	ld %r4, 1800(%r3)
	or %r5, %r5, %r4
	ld %r4, 1808(%r3)
	or %r5, %r5, %r4
	ld %r4, 1816(%r3)
	or %r5, %r5, %r4
	ld %r4, 1824(%r3)
	or %r5, %r5, %r4
	ld %r4, 1832(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r4, 592(%r3)
	std %r4, 1456(%r3)
	ld %r4, 600(%r3)
	std %r4, 1464(%r3)
	ld %r4, 608(%r3)
	std %r4, 1472(%r3)
	ld %r4, 616(%r3)
	std %r4, 1480(%r3)
	ld %r4, 624(%r3)
	std %r4, 1488(%r3)
	ld %r4, 632(%r3)
	std %r4, 1496(%r3)
	li %r31, 384
25:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1504
	li %r5, 1456
	li %r6, 1840
	bl {vg_brainpoolp384r1_mul_mod_n}
	add %r4, %r3, %r31
	lbz %r4, 4864(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 1456(%r3)
	ld %r5, 1504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1456(%r3)
	ld %r4, 1464(%r3)
	ld %r5, 1512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1464(%r3)
	ld %r4, 1472(%r3)
	ld %r5, 1520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1472(%r3)
	ld %r4, 1480(%r3)
	ld %r5, 1528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1480(%r3)
	ld %r4, 1488(%r3)
	ld %r5, 1536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1488(%r3)
	ld %r4, 1496(%r3)
	ld %r5, 1544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1496(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 1888
	li %r5, 1792
	li %r6, 544
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1936
	li %r5, 1600
	li %r6, 544
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1984
	li %r5, 1648
	li %r6, 544
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 2032
	li %r5, 1888
	li %r6, 1936
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 2032
	li %r5, 2032
	li %r6, 1984
	bl {vg_brainpoolp384r1_add_mod_n}
	li %r4, 2080
	li %r5, 1456
	li %r6, 2032
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 2128
	li %r5, 2080
	li %r6, 256
	bl {vg_brainpoolp384r1_mul_mod_n}
	ld %r5, 2128(%r3)
	ld %r4, 2136(%r3)
	or %r5, %r5, %r4
	ld %r4, 2144(%r3)
	or %r5, %r5, %r4
	ld %r4, 2152(%r3)
	or %r5, %r5, %r4
	ld %r4, 2160(%r3)
	or %r5, %r5, %r4
	ld %r4, 2168(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r10, 2176(%r3)
	ld %r4, 1792(%r3)
	and %r4, %r4, %r10
	li %r6, 40
	stdbrx %r4, %r14, %r6
	ld %r4, 1800(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	ld %r4, 1808(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 1816(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 1824(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 1832(%r3)
	and %r4, %r4, %r10
	li %r6, 0
	stdbrx %r4, %r14, %r6
	ld %r4, 2128(%r3)
	and %r4, %r4, %r10
	li %r6, 88
	stdbrx %r4, %r14, %r6
	ld %r4, 2136(%r3)
	and %r4, %r4, %r10
	li %r6, 80
	stdbrx %r4, %r14, %r6
	ld %r4, 2144(%r3)
	and %r4, %r4, %r10
	li %r6, 72
	stdbrx %r4, %r14, %r6
	ld %r4, 2152(%r3)
	and %r4, %r4, %r10
	li %r6, 64
	stdbrx %r4, %r14, %r6
	ld %r4, 2160(%r3)
	and %r4, %r4, %r10
	li %r6, 56
	stdbrx %r4, %r14, %r6
	ld %r4, 2168(%r3)
	and %r4, %r4, %r10
	li %r6, 48
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
