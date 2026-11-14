// The functions of `src/ecdh_brainpoolp384r1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_brainpoolp384r1:
	std %r14, 0(%r6)
	std %r31, 8(%r6)
	mflr %r0
	std %r0, 16(%r6)
	or %r14, %r3, %r3
	or %r3, %r6, %r6
	li %r9, 40
	ldbrx %r8, %r4, %r9
	std %r8, 1552(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 1560(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1568(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1576(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1584(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
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
	ldbrx %r8, %r4, %r9
	std %r8, 1648(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 1656(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 1664(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 1672(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 1680(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
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
	or %r12, %r5, %r5
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
	lis %r11, 16566
	ori %r11, %r11, 19422
	stw %r11, 1936(%r3)
	lis %r11, 2172
	ori %r11, %r11, 61439
	stw %r11, 1940(%r3)
	lis %r11, 15743
	ori %r11, %r11, 55653
	stw %r11, 1944(%r3)
	lis %r11, 21330
	ori %r11, %r11, 33588
	stw %r11, 1948(%r3)
	lis %r11, -13932
	ori %r11, %r11, 2201
	stw %r11, 1952(%r3)
	lis %r11, -29144
	ori %r11, %r11, 63900
	stw %r11, 1956(%r3)
	lis %r11, -26344
	ori %r11, %r11, 54703
	stw %r11, 1960(%r3)
	lis %r11, 25108
	ori %r11, %r11, 401
	stw %r11, 1964(%r3)
	lis %r11, -23170
	ori %r11, %r11, 1324
	stw %r11, 1968(%r3)
	lis %r11, -10810
	ori %r11, %r11, 61243
	stw %r11, 1972(%r3)
	lis %r11, 6029
	ori %r11, %r11, 63554
	stw %r11, 1976(%r3)
	lis %r11, 14015
	ori %r11, %r11, 26755
	stw %r11, 1980(%r3)
	lis %r11, 200
	ori %r11, %r11, 57709
	stw %r11, 1984(%r3)
	lis %r11, 7941
	ori %r11, %r11, 65002
	stw %r11, 1988(%r3)
	lis %r11, 8282
	ori %r11, %r11, 4067
	stw %r11, 1992(%r3)
	lis %r11, 13870
	ori %r11, %r11, 63432
	stw %r11, 1996(%r3)
	lis %r11, -2271
	ori %r11, %r11, 28378
	stw %r11, 2000(%r3)
	lis %r11, -12876
	ori %r11, %r11, 22211
	stw %r11, 2004(%r3)
	lis %r11, -393
	ori %r11, %r11, 65240
	stw %r11, 2008(%r3)
	lis %r11, 5953
	ori %r11, %r11, 14375
	stw %r11, 2012(%r3)
	lis %r11, -11827
	ori %r11, %r11, 9565
	stw %r11, 2016(%r3)
	lis %r11, 11059
	ori %r11, %r11, 22145
	stw %r11, 2020(%r3)
	lis %r11, -6074
	ori %r11, %r11, 34474
	stw %r11, 2024(%r3)
	lis %r11, 17725
	ori %r11, %r11, 52986
	stw %r11, 2028(%r3)
	addi %r6, %r12, 1
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 1648(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1656(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1664(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1672(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1680(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1688(%r3)
	addi %r6, %r6, 48
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 1792(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1800(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1808(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1816(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1824(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1832(%r3)
	lbz %r4, 0(%r12)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1648(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1652(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1656(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1660(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1664(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1668(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1672(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1676(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1680(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1684(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1688(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1692(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1792(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1796(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1800(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1804(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1808(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1812(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1816(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1820(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1824(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1828(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1832(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1836(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	li %r4, 1696
	li %r5, 1648
	li %r6, 1936
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1744
	li %r5, 1792
	li %r6, 1936
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1840
	li %r5, 1744
	li %r6, 1744
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 2032
	li %r5, 1696
	li %r6, 1696
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 2080
	li %r5, 2032
	li %r6, 1696
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 2032
	li %r5, 352
	li %r6, 1696
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1888
	li %r5, 2080
	li %r6, 2032
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 2080
	li %r5, 1888
	li %r6, 1984
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 2032
	li %r5, 1840
	li %r6, 2080
	bl {vg_brainpoolp384r1_sub_mod_p}
	ld %r5, 2032(%r3)
	ld %r4, 2040(%r3)
	or %r5, %r5, %r4
	ld %r4, 2048(%r3)
	or %r5, %r5, %r4
	ld %r4, 2056(%r3)
	or %r5, %r5, %r4
	ld %r4, 2064(%r3)
	or %r5, %r5, %r4
	ld %r4, 2072(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	li %r4, 0
	subf %r5, %r5, %r4
	addi %r5, %r5, -1
	ld %r4, 2176(%r3)
	and %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r10, 2176(%r3)
	ld %r4, 448(%r3)
	ld %r5, 1696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1888(%r3)
	ld %r4, 456(%r3)
	ld %r5, 1704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1896(%r3)
	ld %r4, 464(%r3)
	ld %r5, 1712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1904(%r3)
	ld %r4, 472(%r3)
	ld %r5, 1720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1912(%r3)
	ld %r4, 480(%r3)
	ld %r5, 1728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1920(%r3)
	ld %r4, 488(%r3)
	ld %r5, 1736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1928(%r3)
	ld %r4, 496(%r3)
	ld %r5, 1744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2128(%r3)
	ld %r4, 504(%r3)
	ld %r5, 1752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2136(%r3)
	ld %r4, 512(%r3)
	ld %r5, 1760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2144(%r3)
	ld %r4, 520(%r3)
	ld %r5, 1768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2152(%r3)
	ld %r4, 528(%r3)
	ld %r5, 1776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2160(%r3)
	ld %r4, 536(%r3)
	ld %r5, 1784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2168(%r3)
	ld %r4, 208(%r3)
	std %r4, 5248(%r3)
	ld %r4, 216(%r3)
	std %r4, 5256(%r3)
	ld %r4, 224(%r3)
	std %r4, 5264(%r3)
	ld %r4, 232(%r3)
	std %r4, 5272(%r3)
	ld %r4, 240(%r3)
	std %r4, 5280(%r3)
	ld %r4, 248(%r3)
	std %r4, 5288(%r3)
	ld %r4, 304(%r3)
	std %r4, 5296(%r3)
	ld %r4, 312(%r3)
	std %r4, 5304(%r3)
	ld %r4, 320(%r3)
	std %r4, 5312(%r3)
	ld %r4, 328(%r3)
	std %r4, 5320(%r3)
	ld %r4, 336(%r3)
	std %r4, 5328(%r3)
	ld %r4, 344(%r3)
	std %r4, 5336(%r3)
	ld %r4, 208(%r3)
	std %r4, 5344(%r3)
	ld %r4, 216(%r3)
	std %r4, 5352(%r3)
	ld %r4, 224(%r3)
	std %r4, 5360(%r3)
	ld %r4, 232(%r3)
	std %r4, 5368(%r3)
	ld %r4, 240(%r3)
	std %r4, 5376(%r3)
	ld %r4, 248(%r3)
	std %r4, 5384(%r3)
	ld %r4, 1888(%r3)
	std %r4, 5392(%r3)
	ld %r4, 1896(%r3)
	std %r4, 5400(%r3)
	ld %r4, 1904(%r3)
	std %r4, 5408(%r3)
	ld %r4, 1912(%r3)
	std %r4, 5416(%r3)
	ld %r4, 1920(%r3)
	std %r4, 5424(%r3)
	ld %r4, 1928(%r3)
	std %r4, 5432(%r3)
	ld %r4, 2128(%r3)
	std %r4, 5440(%r3)
	ld %r4, 2136(%r3)
	std %r4, 5448(%r3)
	ld %r4, 2144(%r3)
	std %r4, 5456(%r3)
	ld %r4, 2152(%r3)
	std %r4, 5464(%r3)
	ld %r4, 2160(%r3)
	std %r4, 5472(%r3)
	ld %r4, 2168(%r3)
	std %r4, 5480(%r3)
	ld %r4, 304(%r3)
	std %r4, 5488(%r3)
	ld %r4, 312(%r3)
	std %r4, 5496(%r3)
	ld %r4, 320(%r3)
	std %r4, 5504(%r3)
	ld %r4, 328(%r3)
	std %r4, 5512(%r3)
	ld %r4, 336(%r3)
	std %r4, 5520(%r3)
	ld %r4, 344(%r3)
	std %r4, 5528(%r3)
	ld %r4, 1888(%r3)
	std %r4, 880(%r3)
	ld %r4, 1896(%r3)
	std %r4, 888(%r3)
	ld %r4, 1904(%r3)
	std %r4, 896(%r3)
	ld %r4, 1912(%r3)
	std %r4, 904(%r3)
	ld %r4, 1920(%r3)
	std %r4, 912(%r3)
	ld %r4, 1928(%r3)
	std %r4, 920(%r3)
	ld %r4, 2128(%r3)
	std %r4, 928(%r3)
	ld %r4, 2136(%r3)
	std %r4, 936(%r3)
	ld %r4, 2144(%r3)
	std %r4, 944(%r3)
	ld %r4, 2152(%r3)
	std %r4, 952(%r3)
	ld %r4, 2160(%r3)
	std %r4, 960(%r3)
	ld %r4, 2168(%r3)
	std %r4, 968(%r3)
	ld %r4, 304(%r3)
	std %r4, 976(%r3)
	ld %r4, 312(%r3)
	std %r4, 984(%r3)
	ld %r4, 320(%r3)
	std %r4, 992(%r3)
	ld %r4, 328(%r3)
	std %r4, 1000(%r3)
	ld %r4, 336(%r3)
	std %r4, 1008(%r3)
	ld %r4, 344(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 5536(%r3)
	ld %r4, 1032(%r3)
	std %r4, 5544(%r3)
	ld %r4, 1040(%r3)
	std %r4, 5552(%r3)
	ld %r4, 1048(%r3)
	std %r4, 5560(%r3)
	ld %r4, 1056(%r3)
	std %r4, 5568(%r3)
	ld %r4, 1064(%r3)
	std %r4, 5576(%r3)
	ld %r4, 1072(%r3)
	std %r4, 5584(%r3)
	ld %r4, 1080(%r3)
	std %r4, 5592(%r3)
	ld %r4, 1088(%r3)
	std %r4, 5600(%r3)
	ld %r4, 1096(%r3)
	std %r4, 5608(%r3)
	ld %r4, 1104(%r3)
	std %r4, 5616(%r3)
	ld %r4, 1112(%r3)
	std %r4, 5624(%r3)
	ld %r4, 1120(%r3)
	std %r4, 5632(%r3)
	ld %r4, 1128(%r3)
	std %r4, 5640(%r3)
	ld %r4, 1136(%r3)
	std %r4, 5648(%r3)
	ld %r4, 1144(%r3)
	std %r4, 5656(%r3)
	ld %r4, 1152(%r3)
	std %r4, 5664(%r3)
	ld %r4, 1160(%r3)
	std %r4, 5672(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 5680(%r3)
	ld %r4, 1032(%r3)
	std %r4, 5688(%r3)
	ld %r4, 1040(%r3)
	std %r4, 5696(%r3)
	ld %r4, 1048(%r3)
	std %r4, 5704(%r3)
	ld %r4, 1056(%r3)
	std %r4, 5712(%r3)
	ld %r4, 1064(%r3)
	std %r4, 5720(%r3)
	ld %r4, 1072(%r3)
	std %r4, 5728(%r3)
	ld %r4, 1080(%r3)
	std %r4, 5736(%r3)
	ld %r4, 1088(%r3)
	std %r4, 5744(%r3)
	ld %r4, 1096(%r3)
	std %r4, 5752(%r3)
	ld %r4, 1104(%r3)
	std %r4, 5760(%r3)
	ld %r4, 1112(%r3)
	std %r4, 5768(%r3)
	ld %r4, 1120(%r3)
	std %r4, 5776(%r3)
	ld %r4, 1128(%r3)
	std %r4, 5784(%r3)
	ld %r4, 1136(%r3)
	std %r4, 5792(%r3)
	ld %r4, 1144(%r3)
	std %r4, 5800(%r3)
	ld %r4, 1152(%r3)
	std %r4, 5808(%r3)
	ld %r4, 1160(%r3)
	std %r4, 5816(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 5824(%r3)
	ld %r4, 1032(%r3)
	std %r4, 5832(%r3)
	ld %r4, 1040(%r3)
	std %r4, 5840(%r3)
	ld %r4, 1048(%r3)
	std %r4, 5848(%r3)
	ld %r4, 1056(%r3)
	std %r4, 5856(%r3)
	ld %r4, 1064(%r3)
	std %r4, 5864(%r3)
	ld %r4, 1072(%r3)
	std %r4, 5872(%r3)
	ld %r4, 1080(%r3)
	std %r4, 5880(%r3)
	ld %r4, 1088(%r3)
	std %r4, 5888(%r3)
	ld %r4, 1096(%r3)
	std %r4, 5896(%r3)
	ld %r4, 1104(%r3)
	std %r4, 5904(%r3)
	ld %r4, 1112(%r3)
	std %r4, 5912(%r3)
	ld %r4, 1120(%r3)
	std %r4, 5920(%r3)
	ld %r4, 1128(%r3)
	std %r4, 5928(%r3)
	ld %r4, 1136(%r3)
	std %r4, 5936(%r3)
	ld %r4, 1144(%r3)
	std %r4, 5944(%r3)
	ld %r4, 1152(%r3)
	std %r4, 5952(%r3)
	ld %r4, 1160(%r3)
	std %r4, 5960(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 5968(%r3)
	ld %r4, 1032(%r3)
	std %r4, 5976(%r3)
	ld %r4, 1040(%r3)
	std %r4, 5984(%r3)
	ld %r4, 1048(%r3)
	std %r4, 5992(%r3)
	ld %r4, 1056(%r3)
	std %r4, 6000(%r3)
	ld %r4, 1064(%r3)
	std %r4, 6008(%r3)
	ld %r4, 1072(%r3)
	std %r4, 6016(%r3)
	ld %r4, 1080(%r3)
	std %r4, 6024(%r3)
	ld %r4, 1088(%r3)
	std %r4, 6032(%r3)
	ld %r4, 1096(%r3)
	std %r4, 6040(%r3)
	ld %r4, 1104(%r3)
	std %r4, 6048(%r3)
	ld %r4, 1112(%r3)
	std %r4, 6056(%r3)
	ld %r4, 1120(%r3)
	std %r4, 6064(%r3)
	ld %r4, 1128(%r3)
	std %r4, 6072(%r3)
	ld %r4, 1136(%r3)
	std %r4, 6080(%r3)
	ld %r4, 1144(%r3)
	std %r4, 6088(%r3)
	ld %r4, 1152(%r3)
	std %r4, 6096(%r3)
	ld %r4, 1160(%r3)
	std %r4, 6104(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 6112(%r3)
	ld %r4, 1032(%r3)
	std %r4, 6120(%r3)
	ld %r4, 1040(%r3)
	std %r4, 6128(%r3)
	ld %r4, 1048(%r3)
	std %r4, 6136(%r3)
	ld %r4, 1056(%r3)
	std %r4, 6144(%r3)
	ld %r4, 1064(%r3)
	std %r4, 6152(%r3)
	ld %r4, 1072(%r3)
	std %r4, 6160(%r3)
	ld %r4, 1080(%r3)
	std %r4, 6168(%r3)
	ld %r4, 1088(%r3)
	std %r4, 6176(%r3)
	ld %r4, 1096(%r3)
	std %r4, 6184(%r3)
	ld %r4, 1104(%r3)
	std %r4, 6192(%r3)
	ld %r4, 1112(%r3)
	std %r4, 6200(%r3)
	ld %r4, 1120(%r3)
	std %r4, 6208(%r3)
	ld %r4, 1128(%r3)
	std %r4, 6216(%r3)
	ld %r4, 1136(%r3)
	std %r4, 6224(%r3)
	ld %r4, 1144(%r3)
	std %r4, 6232(%r3)
	ld %r4, 1152(%r3)
	std %r4, 6240(%r3)
	ld %r4, 1160(%r3)
	std %r4, 6248(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 6256(%r3)
	ld %r4, 1032(%r3)
	std %r4, 6264(%r3)
	ld %r4, 1040(%r3)
	std %r4, 6272(%r3)
	ld %r4, 1048(%r3)
	std %r4, 6280(%r3)
	ld %r4, 1056(%r3)
	std %r4, 6288(%r3)
	ld %r4, 1064(%r3)
	std %r4, 6296(%r3)
	ld %r4, 1072(%r3)
	std %r4, 6304(%r3)
	ld %r4, 1080(%r3)
	std %r4, 6312(%r3)
	ld %r4, 1088(%r3)
	std %r4, 6320(%r3)
	ld %r4, 1096(%r3)
	std %r4, 6328(%r3)
	ld %r4, 1104(%r3)
	std %r4, 6336(%r3)
	ld %r4, 1112(%r3)
	std %r4, 6344(%r3)
	ld %r4, 1120(%r3)
	std %r4, 6352(%r3)
	ld %r4, 1128(%r3)
	std %r4, 6360(%r3)
	ld %r4, 1136(%r3)
	std %r4, 6368(%r3)
	ld %r4, 1144(%r3)
	std %r4, 6376(%r3)
	ld %r4, 1152(%r3)
	std %r4, 6384(%r3)
	ld %r4, 1160(%r3)
	std %r4, 6392(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 6400(%r3)
	ld %r4, 1032(%r3)
	std %r4, 6408(%r3)
	ld %r4, 1040(%r3)
	std %r4, 6416(%r3)
	ld %r4, 1048(%r3)
	std %r4, 6424(%r3)
	ld %r4, 1056(%r3)
	std %r4, 6432(%r3)
	ld %r4, 1064(%r3)
	std %r4, 6440(%r3)
	ld %r4, 1072(%r3)
	std %r4, 6448(%r3)
	ld %r4, 1080(%r3)
	std %r4, 6456(%r3)
	ld %r4, 1088(%r3)
	std %r4, 6464(%r3)
	ld %r4, 1096(%r3)
	std %r4, 6472(%r3)
	ld %r4, 1104(%r3)
	std %r4, 6480(%r3)
	ld %r4, 1112(%r3)
	std %r4, 6488(%r3)
	ld %r4, 1120(%r3)
	std %r4, 6496(%r3)
	ld %r4, 1128(%r3)
	std %r4, 6504(%r3)
	ld %r4, 1136(%r3)
	std %r4, 6512(%r3)
	ld %r4, 1144(%r3)
	std %r4, 6520(%r3)
	ld %r4, 1152(%r3)
	std %r4, 6528(%r3)
	ld %r4, 1160(%r3)
	std %r4, 6536(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 6544(%r3)
	ld %r4, 1032(%r3)
	std %r4, 6552(%r3)
	ld %r4, 1040(%r3)
	std %r4, 6560(%r3)
	ld %r4, 1048(%r3)
	std %r4, 6568(%r3)
	ld %r4, 1056(%r3)
	std %r4, 6576(%r3)
	ld %r4, 1064(%r3)
	std %r4, 6584(%r3)
	ld %r4, 1072(%r3)
	std %r4, 6592(%r3)
	ld %r4, 1080(%r3)
	std %r4, 6600(%r3)
	ld %r4, 1088(%r3)
	std %r4, 6608(%r3)
	ld %r4, 1096(%r3)
	std %r4, 6616(%r3)
	ld %r4, 1104(%r3)
	std %r4, 6624(%r3)
	ld %r4, 1112(%r3)
	std %r4, 6632(%r3)
	ld %r4, 1120(%r3)
	std %r4, 6640(%r3)
	ld %r4, 1128(%r3)
	std %r4, 6648(%r3)
	ld %r4, 1136(%r3)
	std %r4, 6656(%r3)
	ld %r4, 1144(%r3)
	std %r4, 6664(%r3)
	ld %r4, 1152(%r3)
	std %r4, 6672(%r3)
	ld %r4, 1160(%r3)
	std %r4, 6680(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 6688(%r3)
	ld %r4, 1032(%r3)
	std %r4, 6696(%r3)
	ld %r4, 1040(%r3)
	std %r4, 6704(%r3)
	ld %r4, 1048(%r3)
	std %r4, 6712(%r3)
	ld %r4, 1056(%r3)
	std %r4, 6720(%r3)
	ld %r4, 1064(%r3)
	std %r4, 6728(%r3)
	ld %r4, 1072(%r3)
	std %r4, 6736(%r3)
	ld %r4, 1080(%r3)
	std %r4, 6744(%r3)
	ld %r4, 1088(%r3)
	std %r4, 6752(%r3)
	ld %r4, 1096(%r3)
	std %r4, 6760(%r3)
	ld %r4, 1104(%r3)
	std %r4, 6768(%r3)
	ld %r4, 1112(%r3)
	std %r4, 6776(%r3)
	ld %r4, 1120(%r3)
	std %r4, 6784(%r3)
	ld %r4, 1128(%r3)
	std %r4, 6792(%r3)
	ld %r4, 1136(%r3)
	std %r4, 6800(%r3)
	ld %r4, 1144(%r3)
	std %r4, 6808(%r3)
	ld %r4, 1152(%r3)
	std %r4, 6816(%r3)
	ld %r4, 1160(%r3)
	std %r4, 6824(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 6832(%r3)
	ld %r4, 1032(%r3)
	std %r4, 6840(%r3)
	ld %r4, 1040(%r3)
	std %r4, 6848(%r3)
	ld %r4, 1048(%r3)
	std %r4, 6856(%r3)
	ld %r4, 1056(%r3)
	std %r4, 6864(%r3)
	ld %r4, 1064(%r3)
	std %r4, 6872(%r3)
	ld %r4, 1072(%r3)
	std %r4, 6880(%r3)
	ld %r4, 1080(%r3)
	std %r4, 6888(%r3)
	ld %r4, 1088(%r3)
	std %r4, 6896(%r3)
	ld %r4, 1096(%r3)
	std %r4, 6904(%r3)
	ld %r4, 1104(%r3)
	std %r4, 6912(%r3)
	ld %r4, 1112(%r3)
	std %r4, 6920(%r3)
	ld %r4, 1120(%r3)
	std %r4, 6928(%r3)
	ld %r4, 1128(%r3)
	std %r4, 6936(%r3)
	ld %r4, 1136(%r3)
	std %r4, 6944(%r3)
	ld %r4, 1144(%r3)
	std %r4, 6952(%r3)
	ld %r4, 1152(%r3)
	std %r4, 6960(%r3)
	ld %r4, 1160(%r3)
	std %r4, 6968(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 6976(%r3)
	ld %r4, 1032(%r3)
	std %r4, 6984(%r3)
	ld %r4, 1040(%r3)
	std %r4, 6992(%r3)
	ld %r4, 1048(%r3)
	std %r4, 7000(%r3)
	ld %r4, 1056(%r3)
	std %r4, 7008(%r3)
	ld %r4, 1064(%r3)
	std %r4, 7016(%r3)
	ld %r4, 1072(%r3)
	std %r4, 7024(%r3)
	ld %r4, 1080(%r3)
	std %r4, 7032(%r3)
	ld %r4, 1088(%r3)
	std %r4, 7040(%r3)
	ld %r4, 1096(%r3)
	std %r4, 7048(%r3)
	ld %r4, 1104(%r3)
	std %r4, 7056(%r3)
	ld %r4, 1112(%r3)
	std %r4, 7064(%r3)
	ld %r4, 1120(%r3)
	std %r4, 7072(%r3)
	ld %r4, 1128(%r3)
	std %r4, 7080(%r3)
	ld %r4, 1136(%r3)
	std %r4, 7088(%r3)
	ld %r4, 1144(%r3)
	std %r4, 7096(%r3)
	ld %r4, 1152(%r3)
	std %r4, 7104(%r3)
	ld %r4, 1160(%r3)
	std %r4, 7112(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 7120(%r3)
	ld %r4, 1032(%r3)
	std %r4, 7128(%r3)
	ld %r4, 1040(%r3)
	std %r4, 7136(%r3)
	ld %r4, 1048(%r3)
	std %r4, 7144(%r3)
	ld %r4, 1056(%r3)
	std %r4, 7152(%r3)
	ld %r4, 1064(%r3)
	std %r4, 7160(%r3)
	ld %r4, 1072(%r3)
	std %r4, 7168(%r3)
	ld %r4, 1080(%r3)
	std %r4, 7176(%r3)
	ld %r4, 1088(%r3)
	std %r4, 7184(%r3)
	ld %r4, 1096(%r3)
	std %r4, 7192(%r3)
	ld %r4, 1104(%r3)
	std %r4, 7200(%r3)
	ld %r4, 1112(%r3)
	std %r4, 7208(%r3)
	ld %r4, 1120(%r3)
	std %r4, 7216(%r3)
	ld %r4, 1128(%r3)
	std %r4, 7224(%r3)
	ld %r4, 1136(%r3)
	std %r4, 7232(%r3)
	ld %r4, 1144(%r3)
	std %r4, 7240(%r3)
	ld %r4, 1152(%r3)
	std %r4, 7248(%r3)
	ld %r4, 1160(%r3)
	std %r4, 7256(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 7264(%r3)
	ld %r4, 1032(%r3)
	std %r4, 7272(%r3)
	ld %r4, 1040(%r3)
	std %r4, 7280(%r3)
	ld %r4, 1048(%r3)
	std %r4, 7288(%r3)
	ld %r4, 1056(%r3)
	std %r4, 7296(%r3)
	ld %r4, 1064(%r3)
	std %r4, 7304(%r3)
	ld %r4, 1072(%r3)
	std %r4, 7312(%r3)
	ld %r4, 1080(%r3)
	std %r4, 7320(%r3)
	ld %r4, 1088(%r3)
	std %r4, 7328(%r3)
	ld %r4, 1096(%r3)
	std %r4, 7336(%r3)
	ld %r4, 1104(%r3)
	std %r4, 7344(%r3)
	ld %r4, 1112(%r3)
	std %r4, 7352(%r3)
	ld %r4, 1120(%r3)
	std %r4, 7360(%r3)
	ld %r4, 1128(%r3)
	std %r4, 7368(%r3)
	ld %r4, 1136(%r3)
	std %r4, 7376(%r3)
	ld %r4, 1144(%r3)
	std %r4, 7384(%r3)
	ld %r4, 1152(%r3)
	std %r4, 7392(%r3)
	ld %r4, 1160(%r3)
	std %r4, 7400(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 880
	li %r6, 1888
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1888
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 7408(%r3)
	ld %r4, 1032(%r3)
	std %r4, 7416(%r3)
	ld %r4, 1040(%r3)
	std %r4, 7424(%r3)
	ld %r4, 1048(%r3)
	std %r4, 7432(%r3)
	ld %r4, 1056(%r3)
	std %r4, 7440(%r3)
	ld %r4, 1064(%r3)
	std %r4, 7448(%r3)
	ld %r4, 1072(%r3)
	std %r4, 7456(%r3)
	ld %r4, 1080(%r3)
	std %r4, 7464(%r3)
	ld %r4, 1088(%r3)
	std %r4, 7472(%r3)
	ld %r4, 1096(%r3)
	std %r4, 7480(%r3)
	ld %r4, 1104(%r3)
	std %r4, 7488(%r3)
	ld %r4, 1112(%r3)
	std %r4, 7496(%r3)
	ld %r4, 1120(%r3)
	std %r4, 7504(%r3)
	ld %r4, 1128(%r3)
	std %r4, 7512(%r3)
	ld %r4, 1136(%r3)
	std %r4, 7520(%r3)
	ld %r4, 1144(%r3)
	std %r4, 7528(%r3)
	ld %r4, 1152(%r3)
	std %r4, 7536(%r3)
	ld %r4, 1160(%r3)
	std %r4, 7544(%r3)
	ld %r4, 1024(%r3)
	std %r4, 880(%r3)
	ld %r4, 1032(%r3)
	std %r4, 888(%r3)
	ld %r4, 1040(%r3)
	std %r4, 896(%r3)
	ld %r4, 1048(%r3)
	std %r4, 904(%r3)
	ld %r4, 1056(%r3)
	std %r4, 912(%r3)
	ld %r4, 1064(%r3)
	std %r4, 920(%r3)
	ld %r4, 1072(%r3)
	std %r4, 928(%r3)
	ld %r4, 1080(%r3)
	std %r4, 936(%r3)
	ld %r4, 1088(%r3)
	std %r4, 944(%r3)
	ld %r4, 1096(%r3)
	std %r4, 952(%r3)
	ld %r4, 1104(%r3)
	std %r4, 960(%r3)
	ld %r4, 1112(%r3)
	std %r4, 968(%r3)
	ld %r4, 1120(%r3)
	std %r4, 976(%r3)
	ld %r4, 1128(%r3)
	std %r4, 984(%r3)
	ld %r4, 1136(%r3)
	std %r4, 992(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1000(%r3)
	ld %r4, 1152(%r3)
	std %r4, 1008(%r3)
	ld %r4, 1160(%r3)
	std %r4, 1016(%r3)
	ld %r4, 208(%r3)
	std %r4, 736(%r3)
	ld %r4, 216(%r3)
	std %r4, 744(%r3)
	ld %r4, 224(%r3)
	std %r4, 752(%r3)
	ld %r4, 232(%r3)
	std %r4, 760(%r3)
	ld %r4, 240(%r3)
	std %r4, 768(%r3)
	ld %r4, 248(%r3)
	std %r4, 776(%r3)
	ld %r4, 304(%r3)
	std %r4, 784(%r3)
	ld %r4, 312(%r3)
	std %r4, 792(%r3)
	ld %r4, 320(%r3)
	std %r4, 800(%r3)
	ld %r4, 328(%r3)
	std %r4, 808(%r3)
	ld %r4, 336(%r3)
	std %r4, 816(%r3)
	ld %r4, 344(%r3)
	std %r4, 824(%r3)
	ld %r4, 208(%r3)
	std %r4, 832(%r3)
	ld %r4, 216(%r3)
	std %r4, 840(%r3)
	ld %r4, 224(%r3)
	std %r4, 848(%r3)
	ld %r4, 232(%r3)
	std %r4, 856(%r3)
	ld %r4, 240(%r3)
	std %r4, 864(%r3)
	ld %r4, 248(%r3)
	std %r4, 872(%r3)
	li %r31, 96
23:
	addi %r31, %r31, -1
	li %r4, 880
	li %r5, 736
	li %r6, 832
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1168
	li %r5, 832
	li %r6, 832
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 928
	li %r5, 784
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 976
	li %r5, 832
	li %r6, 208
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 880
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1312
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1312
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 976
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1120
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1360
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1312
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1312
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1072
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1072
	li %r5, 1360
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 1024
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1312
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1312
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1120
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 976
	li %r5, 1072
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 880
	li %r5, 1360
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1312
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1312
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 928
	li %r5, 1312
	li %r6, 880
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 928
	li %r5, 1360
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 880
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1312
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1312
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 976
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1120
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1360
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1312
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1312
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1072
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1072
	li %r5, 1360
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 1024
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1312
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1312
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1120
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 976
	li %r5, 1072
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 880
	li %r5, 1360
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1312
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1312
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 928
	li %r5, 1312
	li %r6, 880
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 928
	li %r5, 1360
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 736
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1168
	li %r5, 976
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 832
	li %r5, 1168
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 784
	li %r5, 928
	li %r6, 208
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r5, 832(%r3)
	ld %r4, 840(%r3)
	or %r5, %r5, %r4
	ld %r4, 848(%r3)
	or %r5, %r5, %r4
	ld %r4, 856(%r3)
	or %r5, %r5, %r4
	ld %r4, 864(%r3)
	or %r5, %r5, %r4
	ld %r4, 872(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	or %r10, %r5, %r5
	ld %r4, 304(%r3)
	ld %r5, 784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 784(%r3)
	ld %r4, 312(%r3)
	ld %r5, 792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 792(%r3)
	ld %r4, 320(%r3)
	ld %r5, 800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 800(%r3)
	ld %r4, 328(%r3)
	ld %r5, 808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 808(%r3)
	ld %r4, 336(%r3)
	ld %r5, 816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 816(%r3)
	ld %r4, 344(%r3)
	ld %r5, 824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 824(%r3)
	rldicr %r4, %r31, 2, 61
	add %r4, %r3, %r4
	lbz %r9, 4099(%r4)
	add %r9, %r9, %r9
	lbz %r5, 4098(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4097(%r4)
	add %r9, %r9, %r5
	add %r9, %r9, %r9
	lbz %r5, 4096(%r4)
	add %r9, %r9, %r5
	li %r5, 0
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 5248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 5256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 5264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 5272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 5280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 5288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 5296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 5304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 5312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 5320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 5328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 5336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 5344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 5352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 5360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 5368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 5376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 5384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 1
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 5392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 5400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 5408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 5416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 5424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 5432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 5440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 5448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 5456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 5464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 5472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 5480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 5488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 5496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 5504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 5512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 5520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 5528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 2
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 5536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 5544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 5552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 5560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 5568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 5576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 5584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 5592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 5600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 5608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 5616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 5624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 5632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 5640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 5648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 5656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 5664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 5672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 3
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 5680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 5688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 5696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 5704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 5712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 5720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 5728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 5736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 5744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 5752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 5760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 5768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 5776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 5784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 5792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 5800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 5808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 5816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 4
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 5824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 5832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 5840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 5848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 5856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 5864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 5872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 5880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 5888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 5896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 5904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 5912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 5920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 5928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 5936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 5944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 5952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 5960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 5
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 5968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 5976(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 5984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 5992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 6000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 6008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 6016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 6024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 6032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 6040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 6048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 6056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 6064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 6072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 6080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 6088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 6096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 6104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 6
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 6112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 6120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 6128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 6136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 6144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 6152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 6160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 6168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 6176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 6184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 6192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 6200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 6208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 6216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 6224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 6232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 6240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 6248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 7
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 6256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 6264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 6272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 6280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 6288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 6296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 6304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 6312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 6320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 6328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 6336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 6344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 6352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 6360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 6368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 6376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 6384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 6392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 8
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 6400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 6408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 6416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 6424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 6432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 6440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 6448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 6456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 6464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 6472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 6480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 6488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 6496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 6504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 6512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 6520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 6528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 6536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 9
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 6544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 6552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 6560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 6568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 6576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 6584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 6592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 6600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 6608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 6616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 6624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 6632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 6640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 6648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 6656(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 6664(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 6672(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 6680(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 10
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 6688(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 6696(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 6704(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 6712(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 6720(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 6728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 6736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 6744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 6752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 6760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 6768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 6776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 6784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 6792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 6800(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 6808(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 6816(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 6824(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 11
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 6832(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 6840(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 6848(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 6856(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 6864(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 6872(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 6880(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 6888(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 6896(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 6904(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 6912(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 6920(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 6928(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 6936(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 6944(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 6952(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 6960(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 6968(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 12
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 6976(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 6984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 6992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 7000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 7008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 7016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 7024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 7032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 7040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 7048(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 7056(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 7064(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 7072(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 7080(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 7088(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 7096(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 7104(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 7112(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 13
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 7120(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 7128(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 7136(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 7144(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 7152(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 7160(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 7168(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 7176(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 7184(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 7192(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 7200(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 7208(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 7216(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 7224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 7232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 7240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 7248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 7256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 14
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 7264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 7272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 7280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 7288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 7296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 7304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 7312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 7320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 7328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 7336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 7344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 7352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 7360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 7368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 7376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 7384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 7392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 7400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r5, 15
	xor %r10, %r9, %r5
	addi %r10, %r10, -1
	rldicl %r10, %r10, 1, 63
	li %r5, 0
	subf %r10, %r10, %r5
	ld %r4, 880(%r3)
	ld %r5, 7408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 880(%r3)
	ld %r4, 888(%r3)
	ld %r5, 7416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 888(%r3)
	ld %r4, 896(%r3)
	ld %r5, 7424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 896(%r3)
	ld %r4, 904(%r3)
	ld %r5, 7432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 904(%r3)
	ld %r4, 912(%r3)
	ld %r5, 7440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 912(%r3)
	ld %r4, 920(%r3)
	ld %r5, 7448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 920(%r3)
	ld %r4, 928(%r3)
	ld %r5, 7456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 928(%r3)
	ld %r4, 936(%r3)
	ld %r5, 7464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 936(%r3)
	ld %r4, 944(%r3)
	ld %r5, 7472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 944(%r3)
	ld %r4, 952(%r3)
	ld %r5, 7480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 952(%r3)
	ld %r4, 960(%r3)
	ld %r5, 7488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 968(%r3)
	ld %r5, 7496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 976(%r3)
	ld %r5, 7504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 984(%r3)
	ld %r5, 7512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 992(%r3)
	ld %r5, 7520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1000(%r3)
	ld %r5, 7528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1008(%r3)
	ld %r5, 7536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1016(%r3)
	ld %r5, 7544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	li %r4, 1168
	li %r5, 736
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 784
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 832
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 736
	li %r6, 784
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 928
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1360
	li %r5, 736
	li %r6, 832
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1408
	li %r5, 784
	li %r6, 832
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 928
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1024
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1120
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1408
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 1024(%r3)
	std %r4, 736(%r3)
	ld %r4, 1032(%r3)
	std %r4, 744(%r3)
	ld %r4, 1040(%r3)
	std %r4, 752(%r3)
	ld %r4, 1048(%r3)
	std %r4, 760(%r3)
	ld %r4, 1056(%r3)
	std %r4, 768(%r3)
	ld %r4, 1064(%r3)
	std %r4, 776(%r3)
	ld %r4, 1072(%r3)
	std %r4, 784(%r3)
	ld %r4, 1080(%r3)
	std %r4, 792(%r3)
	ld %r4, 1088(%r3)
	std %r4, 800(%r3)
	ld %r4, 1096(%r3)
	std %r4, 808(%r3)
	ld %r4, 1104(%r3)
	std %r4, 816(%r3)
	ld %r4, 1112(%r3)
	std %r4, 824(%r3)
	ld %r4, 1120(%r3)
	std %r4, 832(%r3)
	ld %r4, 1128(%r3)
	std %r4, 840(%r3)
	ld %r4, 1136(%r3)
	std %r4, 848(%r3)
	ld %r4, 1144(%r3)
	std %r4, 856(%r3)
	ld %r4, 1152(%r3)
	std %r4, 864(%r3)
	ld %r4, 1160(%r3)
	std %r4, 872(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	ld %r4, 832(%r3)
	std %r4, 880(%r3)
	ld %r4, 840(%r3)
	std %r4, 888(%r3)
	ld %r4, 848(%r3)
	std %r4, 896(%r3)
	ld %r4, 856(%r3)
	std %r4, 904(%r3)
	ld %r4, 864(%r3)
	std %r4, 912(%r3)
	ld %r4, 872(%r3)
	std %r4, 920(%r3)
	li %r4, 1264
	li %r5, 832
	li %r6, 832
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 928
	li %r5, 880
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 976
	li %r5, 928
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1024
	li %r5, 976
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1120
	li %r5, 1072
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1168
	li %r5, 1120
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	ld %r4, 880(%r3)
	std %r4, 1456(%r3)
	ld %r4, 888(%r3)
	std %r4, 1464(%r3)
	ld %r4, 896(%r3)
	std %r4, 1472(%r3)
	ld %r4, 904(%r3)
	std %r4, 1480(%r3)
	ld %r4, 912(%r3)
	std %r4, 1488(%r3)
	ld %r4, 920(%r3)
	std %r4, 1496(%r3)
	li %r31, 5
24:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
25:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
26:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 7
27:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 2
28:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 8
29:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 2
210:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
211:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
212:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 8
213:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 3
214:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
215:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 11
216:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
217:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 3
218:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
219:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 3
220:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
221:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 2
222:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
223:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 7
224:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
225:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 3
226:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 8
227:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
228:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 1
229:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
230:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
231:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
232:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
233:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
234:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 8
235:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 3
236:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
237:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
238:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 2
239:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
240:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
241:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
242:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 9
243:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
244:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
245:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
246:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
247:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
248:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
249:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
250:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
251:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 1
252:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
253:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 7
254:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
255:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
256:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1120
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
257:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
258:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
259:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 259b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 2
260:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
261:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 261b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
262:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 262b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 3
263:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 263b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 10
264:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 264b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 2
265:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 265b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 7
266:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 266b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
267:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 267b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 5
268:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 268b
	li %r4, 1456
	li %r5, 1456
	li %r6, 928
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 7
269:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 269b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 2
270:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 270b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
271:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 271b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1024
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 15
272:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 272b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
273:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 273b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1072
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 1
274:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 274b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
275:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 275b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 9
276:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 276b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
277:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 277b
	li %r4, 1456
	li %r5, 1456
	li %r6, 1168
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 1
278:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 278b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 6
279:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 279b
	li %r4, 1456
	li %r5, 1456
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r31, 4
280:
	addi %r31, %r31, -1
	li %r4, 1456
	li %r5, 1456
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 280b
	li %r4, 1456
	li %r5, 1456
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1696
	li %r5, 736
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1744
	li %r5, 1696
	li %r6, 256
	bl {vg_brainpoolp384r1_mul_mod_p}
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
	ld %r5, 832(%r3)
	ld %r4, 840(%r3)
	or %r5, %r5, %r4
	ld %r4, 848(%r3)
	or %r5, %r5, %r4
	ld %r4, 856(%r3)
	or %r5, %r5, %r4
	ld %r4, 864(%r3)
	or %r5, %r5, %r4
	ld %r4, 872(%r3)
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
	ld %r4, 1744(%r3)
	and %r4, %r4, %r10
	li %r6, 40
	stdbrx %r4, %r14, %r6
	ld %r4, 1752(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	ld %r4, 1760(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 1768(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 1776(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 1784(%r3)
	and %r4, %r4, %r10
	li %r6, 0
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
