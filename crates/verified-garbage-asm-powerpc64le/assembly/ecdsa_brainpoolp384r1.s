// The functions of `src/ecdsa_brainpoolp384r1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp384r1_verify:
	std %r14, 0(%r6)
	std %r31, 8(%r6)
	mflr %r0
	std %r0, 16(%r6)
	or %r14, %r3, %r3
	or %r3, %r6, %r6
	li %r9, 40
	ldbrx %r8, %r5, %r9
	std %r8, 1552(%r3)
	li %r9, 32
	ldbrx %r8, %r5, %r9
	std %r8, 1560(%r3)
	li %r9, 24
	ldbrx %r8, %r5, %r9
	std %r8, 1568(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 1576(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 1584(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
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
	addi %r6, %r12, 48
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 1504(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 1512(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 1520(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 1528(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 1536(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 1544(%r3)
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
	addi %r6, %r14, 1
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
	lbz %r4, 0(%r14)
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
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 1504(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1508(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1512(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1516(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1520(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1524(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1528(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1532(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1536(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1540(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1544(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 1548(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 1504(%r3)
	ld %r4, 1512(%r3)
	or %r5, %r5, %r4
	ld %r4, 1520(%r3)
	or %r5, %r5, %r4
	ld %r4, 1528(%r3)
	or %r5, %r5, %r4
	ld %r4, 1536(%r3)
	or %r5, %r5, %r4
	ld %r4, 1544(%r3)
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
	li %r4, 1840
	li %r5, 1504
	li %r6, 544
	bl {vg_brainpoolp384r1_mul_mod_n}
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
23:
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
	bne %cr0, 23b
	li %r4, 1984
	li %r5, 1600
	li %r6, 544
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1936
	li %r5, 1552
	li %r6, 544
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 2032
	li %r5, 1984
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 2080
	li %r5, 1936
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1696
	li %r5, 2032
	li %r6, 256
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1744
	li %r5, 2080
	li %r6, 256
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r31, 48
24:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1696(%r4)
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
	bne %cr0, 24b
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
25:
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
	bne %cr0, 25b
	ld %r4, 736(%r3)
	std %r4, 2032(%r3)
	ld %r4, 744(%r3)
	std %r4, 2040(%r3)
	ld %r4, 752(%r3)
	std %r4, 2048(%r3)
	ld %r4, 760(%r3)
	std %r4, 2056(%r3)
	ld %r4, 768(%r3)
	std %r4, 2064(%r3)
	ld %r4, 776(%r3)
	std %r4, 2072(%r3)
	ld %r4, 784(%r3)
	std %r4, 2080(%r3)
	ld %r4, 792(%r3)
	std %r4, 2088(%r3)
	ld %r4, 800(%r3)
	std %r4, 2096(%r3)
	ld %r4, 808(%r3)
	std %r4, 2104(%r3)
	ld %r4, 816(%r3)
	std %r4, 2112(%r3)
	ld %r4, 824(%r3)
	std %r4, 2120(%r3)
	ld %r4, 832(%r3)
	std %r4, 1840(%r3)
	ld %r4, 840(%r3)
	std %r4, 1848(%r3)
	ld %r4, 848(%r3)
	std %r4, 1856(%r3)
	ld %r4, 856(%r3)
	std %r4, 1864(%r3)
	ld %r4, 864(%r3)
	std %r4, 1872(%r3)
	ld %r4, 872(%r3)
	std %r4, 1880(%r3)
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
	li %r31, 48
26:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 1744(%r4)
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
	bne %cr0, 26b
	ld %r4, 1888(%r3)
	std %r4, 3120(%r3)
	ld %r4, 1896(%r3)
	std %r4, 3128(%r3)
	ld %r4, 1904(%r3)
	std %r4, 3136(%r3)
	ld %r4, 1912(%r3)
	std %r4, 3144(%r3)
	ld %r4, 1920(%r3)
	std %r4, 3152(%r3)
	ld %r4, 1928(%r3)
	std %r4, 3160(%r3)
	ld %r4, 2128(%r3)
	std %r4, 3168(%r3)
	ld %r4, 2136(%r3)
	std %r4, 3176(%r3)
	ld %r4, 2144(%r3)
	std %r4, 3184(%r3)
	ld %r4, 2152(%r3)
	std %r4, 3192(%r3)
	ld %r4, 2160(%r3)
	std %r4, 3200(%r3)
	ld %r4, 2168(%r3)
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
27:
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
	bne %cr0, 27b
	li %r4, 1168
	li %r5, 2032
	li %r6, 736
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1216
	li %r5, 2080
	li %r6, 784
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1264
	li %r5, 1840
	li %r6, 832
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1312
	li %r5, 2032
	li %r6, 2080
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1360
	li %r5, 736
	li %r6, 784
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
	li %r5, 2032
	li %r6, 1840
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 736
	li %r6, 832
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
	li %r5, 2080
	li %r6, 1840
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 880
	li %r5, 784
	li %r6, 832
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 880
	li %r5, 1216
	li %r6, 1264
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 880
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 976
	li %r5, 352
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 880
	li %r5, 400
	li %r6, 1264
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 976
	li %r5, 880
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 880
	li %r5, 1216
	li %r6, 976
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 976
	li %r5, 1216
	li %r6, 976
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 928
	li %r5, 880
	li %r6, 976
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
	li %r4, 928
	li %r5, 928
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 880
	li %r5, 1312
	li %r6, 880
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1168
	bl {vg_brainpoolp384r1_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 976
	li %r5, 1408
	li %r6, 976
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 1168
	bl {vg_brainpoolp384r1_add_mod_p}
	ld %r4, 880(%r3)
	std %r4, 736(%r3)
	ld %r4, 888(%r3)
	std %r4, 744(%r3)
	ld %r4, 896(%r3)
	std %r4, 752(%r3)
	ld %r4, 904(%r3)
	std %r4, 760(%r3)
	ld %r4, 912(%r3)
	std %r4, 768(%r3)
	ld %r4, 920(%r3)
	std %r4, 776(%r3)
	ld %r4, 928(%r3)
	std %r4, 784(%r3)
	ld %r4, 936(%r3)
	std %r4, 792(%r3)
	ld %r4, 944(%r3)
	std %r4, 800(%r3)
	ld %r4, 952(%r3)
	std %r4, 808(%r3)
	ld %r4, 960(%r3)
	std %r4, 816(%r3)
	ld %r4, 968(%r3)
	std %r4, 824(%r3)
	ld %r4, 976(%r3)
	std %r4, 832(%r3)
	ld %r4, 984(%r3)
	std %r4, 840(%r3)
	ld %r4, 992(%r3)
	std %r4, 848(%r3)
	ld %r4, 1000(%r3)
	std %r4, 856(%r3)
	ld %r4, 1008(%r3)
	std %r4, 864(%r3)
	ld %r4, 1016(%r3)
	std %r4, 872(%r3)
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
28:
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
	bne %cr0, 28b
	li %r4, 1696
	li %r5, 736
	li %r6, 1456
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1744
	li %r5, 1696
	li %r6, 256
	bl {vg_brainpoolp384r1_mul_mod_p}
	li %r4, 1888
	li %r5, 1744
	li %r6, 544
	bl {vg_brainpoolp384r1_mul_mod_n}
	li %r4, 1984
	li %r5, 1888
	li %r6, 1936
	bl {vg_brainpoolp384r1_sub_mod_n}
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
	ld %r5, 1984(%r3)
	ld %r4, 1992(%r3)
	or %r5, %r5, %r4
	ld %r4, 2000(%r3)
	or %r5, %r5, %r4
	ld %r4, 2008(%r3)
	or %r5, %r5, %r4
	ld %r4, 2016(%r3)
	or %r5, %r5, %r4
	ld %r4, 2024(%r3)
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
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr

vg_ecdsa_brainpoolp384r1_sign:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -592(%r1)
	addi %r11, %r1, 0
	std %r3, 200(%r11)
	std %r4, 192(%r11)
	std %r5, 184(%r11)
	std %r7, 176(%r11)
	std %r8, 224(%r11)
	ld %r9, 32(%r8)
	std %r9, 208(%r11)
	ld %r9, 40(%r8)
	std %r9, 216(%r11)
	addi %r11, %r1, 0
	li %r9, 0
	std %r9, 304(%r11)
	std %r9, 312(%r11)
	std %r9, 320(%r11)
	std %r9, 328(%r11)
	std %r9, 336(%r11)
	std %r9, 344(%r11)
	std %r9, 352(%r11)
	std %r9, 360(%r11)
	std %r9, 368(%r11)
	ld %r6, 208(%r11)
	li %r9, 48
	subfc %r10, %r9, %r6
	subfe %r10, %r10, %r10
	xor %r12, %r6, %r9
	and %r12, %r12, %r10
	xor %r6, %r9, %r12
	addi %r5, %r1, 352
	subf %r5, %r6, %r5
	ld %r4, 184(%r11)
20:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	addi %r11, %r1, 0
	addi %r9, %r1, 304
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 44
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -5884
	ori %r12, %r12, 25957
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 40
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, 15240
	ori %r12, %r12, 12802
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 36
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, 27519
	ori %r12, %r12, 49936
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 32
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, -12486
	ori %r12, %r12, 46767
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 28
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -21500
	ori %r12, %r12, 9639
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 24
	lwbrx %r7, %r9, %r8
	stw %r7, 116(%r11)
	lis %r12, 7958
	ori %r12, %r12, 28268
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 52(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 120(%r11)
	lis %r12, -4780
	ori %r12, %r12, 22195
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 56(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 124(%r11)
	lis %r12, 5423
	ori %r12, %r12, 28937
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 60(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 128(%r11)
	lis %r12, 20710
	ori %r12, %r12, 16863
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 64(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 132(%r11)
	lis %r12, 3933
	ori %r12, %r12, 28542
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 68(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 136(%r11)
	lis %r12, -23752
	ori %r12, %r12, 27944
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 72(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
	lwbrx %r7, %r9, %r8
	stw %r7, 140(%r11)
	lis %r12, -29511
	ori %r12, %r12, 7810
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 76(%r11)
	rldicl %r10, %r7, 32, 32
	li %r12, 0
	subf %r10, %r10, %r12
	lwz %r7, 96(%r11)
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 276
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 272
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 268
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 264
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 260
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 256
	stwbrx %r7, %r11, %r12
	lwz %r7, 120(%r11)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 252
	stwbrx %r7, %r11, %r12
	lwz %r7, 124(%r11)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 248
	stwbrx %r7, %r11, %r12
	lwz %r7, 128(%r11)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 244
	stwbrx %r7, %r11, %r12
	lwz %r7, 132(%r11)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 240
	stwbrx %r7, %r11, %r12
	lwz %r7, 136(%r11)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 236
	stwbrx %r7, %r11, %r12
	lwz %r7, 140(%r11)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 232
	stwbrx %r7, %r11, %r12
	addi %r11, %r1, 0
	lis %r9, 257
	ori %r9, %r9, 257
	li %r10, 0
	stw %r9, 96(%r11)
	stw %r10, 32(%r11)
	stw %r9, 100(%r11)
	stw %r10, 36(%r11)
	stw %r9, 104(%r11)
	stw %r10, 40(%r11)
	stw %r9, 108(%r11)
	stw %r10, 44(%r11)
	stw %r9, 112(%r11)
	stw %r10, 48(%r11)
	stw %r9, 116(%r11)
	stw %r10, 52(%r11)
	stw %r9, 120(%r11)
	stw %r10, 56(%r11)
	stw %r9, 124(%r11)
	stw %r10, 60(%r11)
	stw %r9, 128(%r11)
	stw %r10, 64(%r11)
	stw %r9, 132(%r11)
	stw %r10, 68(%r11)
	stw %r9, 136(%r11)
	stw %r10, 72(%r11)
	stw %r9, 140(%r11)
	stw %r10, 76(%r11)
	stw %r9, 144(%r11)
	stw %r10, 80(%r11)
	stw %r9, 148(%r11)
	stw %r10, 84(%r11)
	stw %r9, 152(%r11)
	stw %r10, 88(%r11)
	stw %r9, 156(%r11)
	stw %r10, 92(%r11)
	addi %r11, %r1, 0
	ld %r9, 176(%r11)
	ld %r10, 192(%r11)
	li %r8, 0
	stb %r8, 2256(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2257(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2261(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2265(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2269(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2273(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 232(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 236(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 240(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 244(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 248(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 252(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2349(%r9)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r12, 2256
	li %r6, 97
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 97
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 0(%r12)
	std %r9, 3072(%r12)
	ld %r9, 8(%r12)
	std %r9, 3080(%r12)
	ld %r9, 16(%r12)
	std %r9, 3088(%r12)
	ld %r9, 24(%r12)
	std %r9, 3096(%r12)
	ld %r9, 32(%r12)
	std %r9, 3104(%r12)
	ld %r9, 40(%r12)
	std %r9, 3112(%r12)
	ld %r9, 48(%r12)
	std %r9, 3120(%r12)
	ld %r9, 56(%r12)
	std %r9, 3128(%r12)
	ld %r9, 64(%r12)
	std %r9, 3136(%r12)
	ld %r9, 72(%r12)
	std %r9, 3144(%r12)
	ld %r9, 80(%r12)
	std %r9, 3152(%r12)
	ld %r9, 88(%r12)
	std %r9, 3160(%r12)
	ld %r9, 96(%r12)
	std %r9, 3168(%r12)
	ld %r9, 104(%r12)
	std %r9, 3176(%r12)
	ld %r9, 112(%r12)
	std %r9, 3184(%r12)
	ld %r9, 120(%r12)
	std %r9, 3192(%r12)
	ld %r9, 128(%r12)
	std %r9, 3200(%r12)
	ld %r9, 136(%r12)
	std %r9, 3208(%r12)
	ld %r9, 144(%r12)
	std %r9, 3216(%r12)
	ld %r9, 152(%r12)
	std %r9, 3224(%r12)
	ld %r9, 160(%r12)
	std %r9, 3232(%r12)
	ld %r9, 168(%r12)
	std %r9, 3240(%r12)
	ld %r9, 176(%r12)
	std %r9, 3248(%r12)
	ld %r9, 184(%r12)
	std %r9, 3256(%r12)
	ld %r9, 192(%r12)
	std %r9, 3264(%r12)
	ld %r9, 200(%r12)
	std %r9, 3272(%r12)
	ld %r9, 208(%r12)
	std %r9, 3280(%r12)
	ld %r9, 216(%r12)
	std %r9, 3288(%r12)
	ld %r9, 224(%r12)
	std %r9, 3296(%r12)
	ld %r9, 232(%r12)
	std %r9, 3304(%r12)
	ld %r9, 240(%r12)
	std %r9, 3312(%r12)
	ld %r9, 248(%r12)
	std %r9, 3320(%r12)
	ld %r9, 256(%r12)
	std %r9, 3328(%r12)
	ld %r9, 264(%r12)
	std %r9, 3336(%r12)
	ld %r9, 272(%r12)
	std %r9, 3344(%r12)
	ld %r9, 280(%r12)
	std %r9, 3352(%r12)
	ld %r9, 288(%r12)
	std %r9, 3360(%r12)
	ld %r9, 296(%r12)
	std %r9, 3368(%r12)
	ld %r9, 304(%r12)
	std %r9, 3376(%r12)
	ld %r9, 312(%r12)
	std %r9, 3384(%r12)
	ld %r9, 320(%r12)
	std %r9, 3392(%r12)
	ld %r9, 328(%r12)
	std %r9, 3400(%r12)
	ld %r9, 336(%r12)
	std %r9, 3408(%r12)
	ld %r9, 344(%r12)
	std %r9, 3416(%r12)
	ld %r9, 352(%r12)
	std %r9, 3424(%r12)
	ld %r9, 360(%r12)
	std %r9, 3432(%r12)
	ld %r9, 368(%r12)
	std %r9, 3440(%r12)
	ld %r9, 376(%r12)
	std %r9, 3448(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r9, 176(%r11)
	ld %r10, 192(%r11)
	li %r8, 1
	stb %r8, 2256(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2257(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2261(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2265(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2269(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2273(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 232(%r11)
	stw %r8, 2305(%r9)
	lwz %r8, 236(%r11)
	stw %r8, 2309(%r9)
	lwz %r8, 240(%r11)
	stw %r8, 2313(%r9)
	lwz %r8, 244(%r11)
	stw %r8, 2317(%r9)
	lwz %r8, 248(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 252(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2349(%r9)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 3072(%r12)
	std %r9, 0(%r12)
	ld %r9, 3080(%r12)
	std %r9, 8(%r12)
	ld %r9, 3088(%r12)
	std %r9, 16(%r12)
	ld %r9, 3096(%r12)
	std %r9, 24(%r12)
	ld %r9, 3104(%r12)
	std %r9, 32(%r12)
	ld %r9, 3112(%r12)
	std %r9, 40(%r12)
	ld %r9, 3120(%r12)
	std %r9, 48(%r12)
	ld %r9, 3128(%r12)
	std %r9, 56(%r12)
	ld %r9, 3136(%r12)
	std %r9, 64(%r12)
	ld %r9, 3144(%r12)
	std %r9, 72(%r12)
	ld %r9, 3152(%r12)
	std %r9, 80(%r12)
	ld %r9, 3160(%r12)
	std %r9, 88(%r12)
	ld %r9, 3168(%r12)
	std %r9, 96(%r12)
	ld %r9, 3176(%r12)
	std %r9, 104(%r12)
	ld %r9, 3184(%r12)
	std %r9, 112(%r12)
	ld %r9, 3192(%r12)
	std %r9, 120(%r12)
	ld %r9, 3200(%r12)
	std %r9, 128(%r12)
	ld %r9, 3208(%r12)
	std %r9, 136(%r12)
	ld %r9, 3216(%r12)
	std %r9, 144(%r12)
	ld %r9, 3224(%r12)
	std %r9, 152(%r12)
	ld %r9, 3232(%r12)
	std %r9, 160(%r12)
	ld %r9, 3240(%r12)
	std %r9, 168(%r12)
	ld %r9, 3248(%r12)
	std %r9, 176(%r12)
	ld %r9, 3256(%r12)
	std %r9, 184(%r12)
	ld %r9, 3264(%r12)
	std %r9, 192(%r12)
	ld %r9, 3272(%r12)
	std %r9, 200(%r12)
	ld %r9, 3280(%r12)
	std %r9, 208(%r12)
	ld %r9, 3288(%r12)
	std %r9, 216(%r12)
	ld %r9, 3296(%r12)
	std %r9, 224(%r12)
	ld %r9, 3304(%r12)
	std %r9, 232(%r12)
	ld %r9, 3312(%r12)
	std %r9, 240(%r12)
	ld %r9, 3320(%r12)
	std %r9, 248(%r12)
	ld %r9, 3328(%r12)
	std %r9, 256(%r12)
	ld %r9, 3336(%r12)
	std %r9, 264(%r12)
	ld %r9, 3344(%r12)
	std %r9, 272(%r12)
	ld %r9, 3352(%r12)
	std %r9, 280(%r12)
	ld %r9, 3360(%r12)
	std %r9, 288(%r12)
	ld %r9, 3368(%r12)
	std %r9, 296(%r12)
	ld %r9, 3376(%r12)
	std %r9, 304(%r12)
	ld %r9, 3384(%r12)
	std %r9, 312(%r12)
	ld %r9, 3392(%r12)
	std %r9, 320(%r12)
	ld %r9, 3400(%r12)
	std %r9, 328(%r12)
	ld %r9, 3408(%r12)
	std %r9, 336(%r12)
	ld %r9, 3416(%r12)
	std %r9, 344(%r12)
	ld %r9, 3424(%r12)
	std %r9, 352(%r12)
	ld %r9, 3432(%r12)
	std %r9, 360(%r12)
	ld %r9, 3440(%r12)
	std %r9, 368(%r12)
	ld %r9, 3448(%r12)
	std %r9, 376(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r12, 2256
	li %r6, 97
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 97
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 0(%r12)
	std %r9, 3072(%r12)
	ld %r9, 8(%r12)
	std %r9, 3080(%r12)
	ld %r9, 16(%r12)
	std %r9, 3088(%r12)
	ld %r9, 24(%r12)
	std %r9, 3096(%r12)
	ld %r9, 32(%r12)
	std %r9, 3104(%r12)
	ld %r9, 40(%r12)
	std %r9, 3112(%r12)
	ld %r9, 48(%r12)
	std %r9, 3120(%r12)
	ld %r9, 56(%r12)
	std %r9, 3128(%r12)
	ld %r9, 64(%r12)
	std %r9, 3136(%r12)
	ld %r9, 72(%r12)
	std %r9, 3144(%r12)
	ld %r9, 80(%r12)
	std %r9, 3152(%r12)
	ld %r9, 88(%r12)
	std %r9, 3160(%r12)
	ld %r9, 96(%r12)
	std %r9, 3168(%r12)
	ld %r9, 104(%r12)
	std %r9, 3176(%r12)
	ld %r9, 112(%r12)
	std %r9, 3184(%r12)
	ld %r9, 120(%r12)
	std %r9, 3192(%r12)
	ld %r9, 128(%r12)
	std %r9, 3200(%r12)
	ld %r9, 136(%r12)
	std %r9, 3208(%r12)
	ld %r9, 144(%r12)
	std %r9, 3216(%r12)
	ld %r9, 152(%r12)
	std %r9, 3224(%r12)
	ld %r9, 160(%r12)
	std %r9, 3232(%r12)
	ld %r9, 168(%r12)
	std %r9, 3240(%r12)
	ld %r9, 176(%r12)
	std %r9, 3248(%r12)
	ld %r9, 184(%r12)
	std %r9, 3256(%r12)
	ld %r9, 192(%r12)
	std %r9, 3264(%r12)
	ld %r9, 200(%r12)
	std %r9, 3272(%r12)
	ld %r9, 208(%r12)
	std %r9, 3280(%r12)
	ld %r9, 216(%r12)
	std %r9, 3288(%r12)
	ld %r9, 224(%r12)
	std %r9, 3296(%r12)
	ld %r9, 232(%r12)
	std %r9, 3304(%r12)
	ld %r9, 240(%r12)
	std %r9, 3312(%r12)
	ld %r9, 248(%r12)
	std %r9, 3320(%r12)
	ld %r9, 256(%r12)
	std %r9, 3328(%r12)
	ld %r9, 264(%r12)
	std %r9, 3336(%r12)
	ld %r9, 272(%r12)
	std %r9, 3344(%r12)
	ld %r9, 280(%r12)
	std %r9, 3352(%r12)
	ld %r9, 288(%r12)
	std %r9, 3360(%r12)
	ld %r9, 296(%r12)
	std %r9, 3368(%r12)
	ld %r9, 304(%r12)
	std %r9, 3376(%r12)
	ld %r9, 312(%r12)
	std %r9, 3384(%r12)
	ld %r9, 320(%r12)
	std %r9, 3392(%r12)
	ld %r9, 328(%r12)
	std %r9, 3400(%r12)
	ld %r9, 336(%r12)
	std %r9, 3408(%r12)
	ld %r9, 344(%r12)
	std %r9, 3416(%r12)
	ld %r9, 352(%r12)
	std %r9, 3424(%r12)
	ld %r9, 360(%r12)
	std %r9, 3432(%r12)
	ld %r9, 368(%r12)
	std %r9, 3440(%r12)
	ld %r9, 376(%r12)
	std %r9, 3448(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	li %r9, 128
	addi %r11, %r1, 0
	std %r9, 168(%r11)
21:
	li %r9, 0
	addi %r11, %r1, 0
	std %r9, 160(%r11)
22:
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 3072(%r12)
	std %r9, 0(%r12)
	ld %r9, 3080(%r12)
	std %r9, 8(%r12)
	ld %r9, 3088(%r12)
	std %r9, 16(%r12)
	ld %r9, 3096(%r12)
	std %r9, 24(%r12)
	ld %r9, 3104(%r12)
	std %r9, 32(%r12)
	ld %r9, 3112(%r12)
	std %r9, 40(%r12)
	ld %r9, 3120(%r12)
	std %r9, 48(%r12)
	ld %r9, 3128(%r12)
	std %r9, 56(%r12)
	ld %r9, 3136(%r12)
	std %r9, 64(%r12)
	ld %r9, 3144(%r12)
	std %r9, 72(%r12)
	ld %r9, 3152(%r12)
	std %r9, 80(%r12)
	ld %r9, 3160(%r12)
	std %r9, 88(%r12)
	ld %r9, 3168(%r12)
	std %r9, 96(%r12)
	ld %r9, 3176(%r12)
	std %r9, 104(%r12)
	ld %r9, 3184(%r12)
	std %r9, 112(%r12)
	ld %r9, 3192(%r12)
	std %r9, 120(%r12)
	ld %r9, 3200(%r12)
	std %r9, 128(%r12)
	ld %r9, 3208(%r12)
	std %r9, 136(%r12)
	ld %r9, 3216(%r12)
	std %r9, 144(%r12)
	ld %r9, 3224(%r12)
	std %r9, 152(%r12)
	ld %r9, 3232(%r12)
	std %r9, 160(%r12)
	ld %r9, 3240(%r12)
	std %r9, 168(%r12)
	ld %r9, 3248(%r12)
	std %r9, 176(%r12)
	ld %r9, 3256(%r12)
	std %r9, 184(%r12)
	ld %r9, 3264(%r12)
	std %r9, 192(%r12)
	ld %r9, 3272(%r12)
	std %r9, 200(%r12)
	ld %r9, 3280(%r12)
	std %r9, 208(%r12)
	ld %r9, 3288(%r12)
	std %r9, 216(%r12)
	ld %r9, 3296(%r12)
	std %r9, 224(%r12)
	ld %r9, 3304(%r12)
	std %r9, 232(%r12)
	ld %r9, 3312(%r12)
	std %r9, 240(%r12)
	ld %r9, 3320(%r12)
	std %r9, 248(%r12)
	ld %r9, 3328(%r12)
	std %r9, 256(%r12)
	ld %r9, 3336(%r12)
	std %r9, 264(%r12)
	ld %r9, 3344(%r12)
	std %r9, 272(%r12)
	ld %r9, 3352(%r12)
	std %r9, 280(%r12)
	ld %r9, 3360(%r12)
	std %r9, 288(%r12)
	ld %r9, 3368(%r12)
	std %r9, 296(%r12)
	ld %r9, 3376(%r12)
	std %r9, 304(%r12)
	ld %r9, 3384(%r12)
	std %r9, 312(%r12)
	ld %r9, 3392(%r12)
	std %r9, 320(%r12)
	ld %r9, 3400(%r12)
	std %r9, 328(%r12)
	ld %r9, 3408(%r12)
	std %r9, 336(%r12)
	ld %r9, 3416(%r12)
	std %r9, 344(%r12)
	ld %r9, 3424(%r12)
	std %r9, 352(%r12)
	ld %r9, 3432(%r12)
	std %r9, 360(%r12)
	ld %r9, 3440(%r12)
	std %r9, 368(%r12)
	ld %r9, 3448(%r12)
	std %r9, 376(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	addi %r4, %r1, 96
	addi %r5, %r1, 448
	ld %r9, 160(%r11)
	add %r5, %r5, %r9
	ld %r6, 208(%r11)
23:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 23b
	addi %r11, %r1, 0
	ld %r9, 160(%r11)
	ld %r10, 208(%r11)
	add %r9, %r9, %r10
	std %r9, 160(%r11)
	li %r10, 48
	subfc %r12, %r10, %r9
	subfe %r12, %r12, %r12
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	addi %r11, %r1, 0
	ld %r3, 200(%r11)
	ld %r4, 192(%r11)
	addi %r5, %r1, 304
	addi %r6, %r1, 448
	ld %r7, 176(%r11)
	bl {vg_ecdsa_brainpoolp384r1_sign_k}
	addi %r11, %r1, 0
	ld %r9, 168(%r11)
	addi %r9, %r9, -1
	std %r9, 168(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 24f
	li %r12, 0
	b 25f
24:
	addi %r11, %r1, 0
	ld %r9, 176(%r11)
	ld %r10, 192(%r11)
	li %r8, 0
	stb %r8, 2256(%r9)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	ld %r6, 208(%r11)
	add %r4, %r4, %r6
	addi %r5, %r12, 2256
	li %r6, 1
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 1
	addi %r6, %r1, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	addi %r5, %r1, 32
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	ld %r9, 0(%r12)
	std %r9, 3072(%r12)
	ld %r9, 8(%r12)
	std %r9, 3080(%r12)
	ld %r9, 16(%r12)
	std %r9, 3088(%r12)
	ld %r9, 24(%r12)
	std %r9, 3096(%r12)
	ld %r9, 32(%r12)
	std %r9, 3104(%r12)
	ld %r9, 40(%r12)
	std %r9, 3112(%r12)
	ld %r9, 48(%r12)
	std %r9, 3120(%r12)
	ld %r9, 56(%r12)
	std %r9, 3128(%r12)
	ld %r9, 64(%r12)
	std %r9, 3136(%r12)
	ld %r9, 72(%r12)
	std %r9, 3144(%r12)
	ld %r9, 80(%r12)
	std %r9, 3152(%r12)
	ld %r9, 88(%r12)
	std %r9, 3160(%r12)
	ld %r9, 96(%r12)
	std %r9, 3168(%r12)
	ld %r9, 104(%r12)
	std %r9, 3176(%r12)
	ld %r9, 112(%r12)
	std %r9, 3184(%r12)
	ld %r9, 120(%r12)
	std %r9, 3192(%r12)
	ld %r9, 128(%r12)
	std %r9, 3200(%r12)
	ld %r9, 136(%r12)
	std %r9, 3208(%r12)
	ld %r9, 144(%r12)
	std %r9, 3216(%r12)
	ld %r9, 152(%r12)
	std %r9, 3224(%r12)
	ld %r9, 160(%r12)
	std %r9, 3232(%r12)
	ld %r9, 168(%r12)
	std %r9, 3240(%r12)
	ld %r9, 176(%r12)
	std %r9, 3248(%r12)
	ld %r9, 184(%r12)
	std %r9, 3256(%r12)
	ld %r9, 192(%r12)
	std %r9, 3264(%r12)
	ld %r9, 200(%r12)
	std %r9, 3272(%r12)
	ld %r9, 208(%r12)
	std %r9, 3280(%r12)
	ld %r9, 216(%r12)
	std %r9, 3288(%r12)
	ld %r9, 224(%r12)
	std %r9, 3296(%r12)
	ld %r9, 232(%r12)
	std %r9, 3304(%r12)
	ld %r9, 240(%r12)
	std %r9, 3312(%r12)
	ld %r9, 248(%r12)
	std %r9, 3320(%r12)
	ld %r9, 256(%r12)
	std %r9, 3328(%r12)
	ld %r9, 264(%r12)
	std %r9, 3336(%r12)
	ld %r9, 272(%r12)
	std %r9, 3344(%r12)
	ld %r9, 280(%r12)
	std %r9, 3352(%r12)
	ld %r9, 288(%r12)
	std %r9, 3360(%r12)
	ld %r9, 296(%r12)
	std %r9, 3368(%r12)
	ld %r9, 304(%r12)
	std %r9, 3376(%r12)
	ld %r9, 312(%r12)
	std %r9, 3384(%r12)
	ld %r9, 320(%r12)
	std %r9, 3392(%r12)
	ld %r9, 328(%r12)
	std %r9, 3400(%r12)
	ld %r9, 336(%r12)
	std %r9, 3408(%r12)
	ld %r9, 344(%r12)
	std %r9, 3416(%r12)
	ld %r9, 352(%r12)
	std %r9, 3424(%r12)
	ld %r9, 360(%r12)
	std %r9, 3432(%r12)
	ld %r9, 368(%r12)
	std %r9, 3440(%r12)
	ld %r9, 376(%r12)
	std %r9, 3448(%r12)
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	ld %r4, 216(%r11)
	addi %r5, %r1, 96
	ld %r6, 208(%r11)
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 176(%r11)
	addi %r3, %r12, 0
	addi %r4, %r12, 192
	ld %r5, 216(%r11)
	ld %r6, 208(%r11)
	add %r5, %r5, %r6
	addi %r5, %r5, 0
	addi %r6, %r1, 96
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 224(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	li %r12, 1
25:
	cmpldi %cr0, %r12, 0
	bne %cr0, 21b
	addi %r11, %r1, 0
	li %r12, 0
	std %r12, 32(%r11)
	std %r12, 40(%r11)
	std %r12, 48(%r11)
	std %r12, 56(%r11)
	std %r12, 64(%r11)
	std %r12, 72(%r11)
	std %r12, 80(%r11)
	std %r12, 88(%r11)
	std %r12, 96(%r11)
	std %r12, 104(%r11)
	std %r12, 112(%r11)
	std %r12, 120(%r11)
	std %r12, 128(%r11)
	std %r12, 136(%r11)
	std %r12, 144(%r11)
	std %r12, 152(%r11)
	std %r12, 232(%r11)
	std %r12, 240(%r11)
	std %r12, 248(%r11)
	std %r12, 256(%r11)
	std %r12, 264(%r11)
	std %r12, 272(%r11)
	std %r12, 280(%r11)
	std %r12, 288(%r11)
	std %r12, 296(%r11)
	std %r12, 304(%r11)
	std %r12, 312(%r11)
	std %r12, 320(%r11)
	std %r12, 328(%r11)
	std %r12, 336(%r11)
	std %r12, 344(%r11)
	std %r12, 352(%r11)
	std %r12, 360(%r11)
	std %r12, 368(%r11)
	std %r12, 376(%r11)
	std %r12, 384(%r11)
	std %r12, 392(%r11)
	std %r12, 400(%r11)
	std %r12, 408(%r11)
	std %r12, 416(%r11)
	std %r12, 424(%r11)
	std %r12, 432(%r11)
	std %r12, 440(%r11)
	std %r12, 448(%r11)
	std %r12, 456(%r11)
	std %r12, 464(%r11)
	std %r12, 472(%r11)
	std %r12, 480(%r11)
	std %r12, 488(%r11)
	std %r12, 496(%r11)
	std %r12, 504(%r11)
	std %r12, 512(%r11)
	std %r12, 520(%r11)
	std %r12, 528(%r11)
	std %r12, 536(%r11)
	std %r12, 544(%r11)
	std %r12, 552(%r11)
	std %r12, 560(%r11)
	std %r12, 568(%r11)
	std %r12, 576(%r11)
	std %r12, 584(%r11)
	addi %r1, %r1, 592
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
