// The functions of `src/ec_p521_compressed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_p521_compress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2296(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2304(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2312(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2320(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2328(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2336(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2344(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2352(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2360(%r3)
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2368(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2376(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2384(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2392(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2400(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2408(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2416(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2424(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2432(%r3)
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 64(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 68(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 72(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 76(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 80(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 84(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 88(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 92(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 96(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 100(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 104(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 108(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 112(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 116(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 120(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 124(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 128(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 132(%r3)
	lis %r11, -28360
	ori %r11, %r11, 25609
	stw %r11, 136(%r3)
	lis %r11, -17553
	ori %r11, %r11, 46878
	stw %r11, 140(%r3)
	lis %r11, -30308
	ori %r11, %r11, 18350
	stw %r11, 144(%r3)
	lis %r11, 15285
	ori %r11, %r11, 51640
	stw %r11, 148(%r3)
	lis %r11, -2295
	ori %r11, %r11, 42448
	stw %r11, 152(%r3)
	lis %r11, 32716
	ori %r11, %r11, 328
	stw %r11, 156(%r3)
	lis %r11, -16593
	ori %r11, %r11, 38507
	stw %r11, 160(%r3)
	lis %r11, 20870
	ori %r11, %r11, 34691
	stw %r11, 164(%r3)
	lis %r11, -1
	ori %r11, %r11, 65530
	stw %r11, 168(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 172(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 176(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 180(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 184(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 188(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 192(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 196(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 200(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 204(%r3)
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
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 304(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 308(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 312(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 316(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 320(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 324(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 328(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 332(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 336(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 340(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 344(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 348(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 352(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 356(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 360(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 364(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 368(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 372(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 376(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 380(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 384(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 388(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 392(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 396(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 400(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 404(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 408(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 412(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 416(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 420(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 424(%r3)
	lis %r11, 128
	ori %r11, %r11, 0
	stw %r11, 428(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 432(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 436(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 440(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 444(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 448(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 452(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 456(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 460(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 464(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 468(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 472(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 476(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 480(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 484(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 488(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 492(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 496(%r3)
	lis %r11, -385
	ori %r11, %r11, 65535
	stw %r11, 500(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 504(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 508(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 512(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 516(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 520(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 524(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 528(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 532(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 536(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 540(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 544(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 548(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 552(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 556(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 560(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 564(%r3)
	lis %r11, 2825
	ori %r11, %r11, 10901
	stw %r11, 568(%r3)
	lis %r11, -32707
	ori %r11, %r11, 12271
	stw %r11, 572(%r3)
	lis %r11, -16736
	ori %r11, %r11, 63582
	stw %r11, 576(%r3)
	lis %r11, 27366
	ori %r11, %r11, 59311
	stw %r11, 580(%r3)
	lis %r11, 19547
	ori %r11, %r11, 49743
	stw %r11, 584(%r3)
	lis %r11, -30000
	ori %r11, %r11, 11727
	stw %r11, 588(%r3)
	lis %r11, 7129
	ori %r11, %r11, 35486
	stw %r11, 592(%r3)
	lis %r11, 14497
	ori %r11, %r11, 31777
	stw %r11, 596(%r3)
	lis %r11, -1310
	ori %r11, %r11, 48605
	stw %r11, 600(%r3)
	lis %r11, -11775
	ori %r11, %r11, 9685
	stw %r11, 604(%r3)
	lis %r11, 23126
	ori %r11, %r11, 27022
	stw %r11, 608(%r3)
	lis %r11, -4715
	ori %r11, %r11, 3790
	stw %r11, 612(%r3)
	lis %r11, -30362
	ori %r11, %r11, 36000
	stw %r11, 616(%r3)
	lis %r11, 26100
	ori %r11, %r11, 18347
	stw %r11, 620(%r3)
	lis %r11, 28945
	ori %r11, %r11, 51169
	stw %r11, 624(%r3)
	lis %r11, 12123
	ori %r11, %r11, 59186
	stw %r11, 628(%r3)
	lis %r11, 0
	ori %r11, %r11, 231
	stw %r11, 632(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 636(%r3)
	lis %r11, -32339
	ori %r11, %r11, 49409
	stw %r11, 640(%r3)
	lis %r11, -19663
	ori %r11, %r11, 41315
	stw %r11, 644(%r3)
	lis %r11, 6369
	ori %r11, %r11, 29406
	stw %r11, 648(%r3)
	lis %r11, 19964
	ori %r11, %r11, 48959
	stw %r11, 652(%r3)
	lis %r11, -7998
	ori %r11, %r11, 46369
	stw %r11, 656(%r3)
	lis %r11, 28441
	ori %r11, %r11, 42073
	stw %r11, 660(%r3)
	lis %r11, -27695
	ori %r11, %r11, 32724
	stw %r11, 664(%r3)
	lis %r11, -27521
	ori %r11, %r11, 3808
	stw %r11, 668(%r3)
	lis %r11, 15351
	ori %r11, %r11, 62380
	stw %r11, 672(%r3)
	lis %r11, -8880
	ori %r11, %r11, 42415
	stw %r11, 676(%r3)
	lis %r11, -20427
	ori %r11, %r11, 42654
	stw %r11, 680(%r3)
	lis %r11, -28420
	ori %r11, %r11, 5207
	stw %r11, 684(%r3)
	lis %r11, -25470
	ori %r11, %r11, 40922
	stw %r11, 688(%r3)
	lis %r11, 8526
	ori %r11, %r11, 12864
	stw %r11, 692(%r3)
	lis %r11, -19695
	ori %r11, %r11, 51930
	stw %r11, 696(%r3)
	lis %r11, -6449
	ori %r11, %r11, 8037
	stw %r11, 700(%r3)
	lis %r11, 0
	ori %r11, %r11, 116
	stw %r11, 704(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 708(%r3)
	lis %r11, 23198
	ori %r11, %r11, 9870
	stw %r11, 712(%r3)
	lis %r11, 10310
	ori %r11, %r11, 3658
	stw %r11, 716(%r3)
	lis %r11, 15183
	ori %r11, %r11, 59571
	stw %r11, 720(%r3)
	lis %r11, 8260
	ori %r11, %r11, 24394
	stw %r11, 724(%r3)
	lis %r11, 17233
	ori %r11, %r11, 14689
	stw %r11, 728(%r3)
	lis %r11, -20326
	ori %r11, %r11, 40504
	stw %r11, 732(%r3)
	lis %r11, -32609
	ori %r11, %r11, 54915
	stw %r11, 736(%r3)
	lis %r11, 8290
	ori %r11, %r11, 43100
	stw %r11, 740(%r3)
	lis %r11, 19631
	ori %r11, %r11, 31251
	stw %r11, 744(%r3)
	lis %r11, 5707
	ori %r11, %r11, 63289
	stw %r11, 748(%r3)
	lis %r11, -29805
	ori %r11, %r11, 40755
	stw %r11, 752(%r3)
	lis %r11, 13323
	ori %r11, %r11, 55262
	stw %r11, 756(%r3)
	lis %r11, 9387
	ori %r11, %r11, 52642
	stw %r11, 760(%r3)
	lis %r11, -4916
	ori %r11, %r11, 31394
	stw %r11, 764(%r3)
	lis %r11, -9706
	ori %r11, %r11, 16013
	stw %r11, 768(%r3)
	lis %r11, 558
	ori %r11, %r11, 17711
	stw %r11, 772(%r3)
	lis %r11, 0
	ori %r11, %r11, 480
	stw %r11, 776(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 780(%r3)
	lis %r11, -12523
	ori %r11, %r11, 56580
	stw %r11, 784(%r3)
	lis %r11, 4988
	ori %r11, %r11, 53325
	stw %r11, 788(%r3)
	lis %r11, -6828
	ori %r11, %r11, 32419
	stw %r11, 792(%r3)
	lis %r11, -2297
	ori %r11, %r11, 47836
	stw %r11, 796(%r3)
	lis %r11, 31045
	ori %r11, %r11, 29695
	stw %r11, 800(%r3)
	lis %r11, 4775
	ori %r11, %r11, 36152
	stw %r11, 804(%r3)
	lis %r11, 22519
	ori %r11, %r11, 24070
	stw %r11, 808(%r3)
	lis %r11, -11406
	ori %r11, %r11, 7925
	stw %r11, 812(%r3)
	lis %r11, 11849
	ori %r11, %r11, 51163
	stw %r11, 816(%r3)
	lis %r11, -8850
	ori %r11, %r11, 9176
	stw %r11, 820(%r3)
	lis %r11, -18571
	ori %r11, %r11, 28222
	stw %r11, 824(%r3)
	lis %r11, -12301
	ori %r11, %r11, 53570
	stw %r11, 828(%r3)
	lis %r11, -22299
	ori %r11, %r11, 26556
	stw %r11, 832(%r3)
	lis %r11, 23500
	ori %r11, %r11, 28001
	stw %r11, 836(%r3)
	lis %r11, 18733
	ori %r11, %r11, 3397
	stw %r11, 840(%r3)
	lis %r11, 11662
	ori %r11, %r11, 977
	stw %r11, 844(%r3)
	lis %r11, 0
	ori %r11, %r11, 61
	stw %r11, 848(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 852(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 856(%r3)
	lis %r11, -1152
	ori %r11, %r11, 0
	stw %r11, 860(%r3)
	lis %r11, 28855
	ori %r11, %r11, 25549
	stw %r11, 864(%r3)
	lis %r11, 10402
	ori %r11, %r11, 18468
	stw %r11, 868(%r3)
	lis %r11, 9147
	ori %r11, %r11, 12764
	stw %r11, 872(%r3)
	lis %r11, 6114
	ori %r11, %r11, 9499
	stw %r11, 876(%r3)
	lis %r11, 23428
	ori %r11, %r11, 31533
	stw %r11, 880(%r3)
	lis %r11, -13760
	ori %r11, %r11, 6655
	stw %r11, 884(%r3)
	lis %r11, 15904
	ori %r11, %r11, 26676
	stw %r11, 888(%r3)
	lis %r11, 727
	ori %r11, %r11, 15548
	stw %r11, 892(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 896(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 900(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 904(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 908(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 912(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 916(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 920(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 924(%r3)
	lis %r11, -1
	ori %r11, %r11, 65533
	stw %r11, 928(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 932(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 936(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 940(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 944(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 948(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 952(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 956(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 960(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 964(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 968(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 972(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 976(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 980(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 984(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 988(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 992(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 996(%r3)
	lis %r11, -28360
	ori %r11, %r11, 25607
	stw %r11, 1000(%r3)
	lis %r11, -17553
	ori %r11, %r11, 46878
	stw %r11, 1004(%r3)
	lis %r11, -30308
	ori %r11, %r11, 18350
	stw %r11, 1008(%r3)
	lis %r11, 15285
	ori %r11, %r11, 51640
	stw %r11, 1012(%r3)
	lis %r11, -2295
	ori %r11, %r11, 42448
	stw %r11, 1016(%r3)
	lis %r11, 32716
	ori %r11, %r11, 328
	stw %r11, 1020(%r3)
	lis %r11, -16593
	ori %r11, %r11, 38507
	stw %r11, 1024(%r3)
	lis %r11, 20870
	ori %r11, %r11, 34691
	stw %r11, 1028(%r3)
	lis %r11, -1
	ori %r11, %r11, 65530
	stw %r11, 1032(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1036(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1040(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1044(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1048(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1052(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1056(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1060(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 1064(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1068(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1072(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1076(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1080(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1084(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1088(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1092(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1096(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1100(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1104(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1108(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1112(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1116(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1120(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1124(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1128(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1132(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1136(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1140(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1144(%r3)
	lis %r11, 128
	ori %r11, %r11, 0
	stw %r11, 1148(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1152(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1156(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1160(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1164(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1168(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1172(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1176(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1180(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1184(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1188(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1192(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1196(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1200(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1204(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1208(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1212(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1216(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1220(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1236(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1240(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1244(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1252(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1256(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1260(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1264(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1268(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1276(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1280(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1284(%r3)
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 3232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2872(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2876(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2880(%r3)
	lis %r11, 0
	ori %r11, %r11, 16384
	stw %r11, 2884(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2888(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2892(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2896(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2900(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2904(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2908(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2912(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2916(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2920(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2924(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2928(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2932(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2936(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2940(%r3)
	lis %r11, -20904
	ori %r11, %r11, 25479
	stw %r11, 2944(%r3)
	lis %r11, -32748
	ori %r11, %r11, 25935
	stw %r11, 2948(%r3)
	lis %r11, -5579
	ori %r11, %r11, 43039
	stw %r11, 2952(%r3)
	lis %r11, 30967
	ori %r11, %r11, 41615
	stw %r11, 2956(%r3)
	lis %r11, -15330
	ori %r11, %r11, 38426
	stw %r11, 2960(%r3)
	lis %r11, -31846
	ori %r11, %r11, 47599
	stw %r11, 2964(%r3)
	lis %r11, 24221
	ori %r11, %r11, 55519
	stw %r11, 2968(%r3)
	lis %r11, -17013
	ori %r11, %r11, 10592
	stw %r11, 2972(%r3)
	lis %r11, -22282
	ori %r11, %r11, 16201
	stw %r11, 2976(%r3)
	lis %r11, -3925
	ori %r11, %r11, 3228
	stw %r11, 2980(%r3)
	lis %r11, -14137
	ori %r11, %r11, 30852
	stw %r11, 2984(%r3)
	lis %r11, -1572
	ori %r11, %r11, 23108
	stw %r11, 2988(%r3)
	lis %r11, 11724
	ori %r11, %r11, 55690
	stw %r11, 2992(%r3)
	lis %r11, 30545
	ori %r11, %r11, 27961
	stw %r11, 2996(%r3)
	lis %r11, -12197
	ori %r11, %r11, 17056
	stw %r11, 3000(%r3)
	lis %r11, 4041
	ori %r11, %r11, 19728
	stw %r11, 3004(%r3)
	lis %r11, 0
	ori %r11, %r11, 77
	stw %r11, 3008(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3012(%r3)
	addi %r6, %r12, 1
	li %r9, 58
	ldbrx %r8, %r6, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r6, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r6, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r6, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r6, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r6, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r6, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r6, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	addi %r6, %r6, 66
	li %r9, 58
	ldbrx %r8, %r6, %r9
	std %r8, 2656(%r3)
	li %r9, 50
	ldbrx %r8, %r6, %r9
	std %r8, 2664(%r3)
	li %r9, 42
	ldbrx %r8, %r6, %r9
	std %r8, 2672(%r3)
	li %r9, 34
	ldbrx %r8, %r6, %r9
	std %r8, 2680(%r3)
	li %r9, 26
	ldbrx %r8, %r6, %r9
	std %r8, 2688(%r3)
	li %r9, 18
	ldbrx %r8, %r6, %r9
	std %r8, 2696(%r3)
	li %r9, 10
	ldbrx %r8, %r6, %r9
	std %r8, 2704(%r3)
	li %r9, 2
	ldbrx %r8, %r6, %r9
	std %r8, 2712(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2720(%r3)
	lbz %r4, 0(%r12)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2440(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2444(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2448(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2452(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2456(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2460(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2464(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2468(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2472(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2476(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2480(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2484(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2488(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2492(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2496(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2500(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2504(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2508(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2656(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2660(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2664(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2668(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2672(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2676(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2680(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2684(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2688(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2692(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2696(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2700(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2704(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2708(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2712(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2716(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2720(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2724(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r4, 2512
	li %r5, 2440
	li %r6, 2872
	bl {vg_p521_mul_mod_p}
	li %r4, 2584
	li %r5, 2656
	li %r6, 2872
	bl {vg_p521_mul_mod_p}
	li %r4, 2728
	li %r5, 2584
	li %r6, 2584
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 2512
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 3088
	li %r5, 3016
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 496
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 2800
	li %r5, 3088
	li %r6, 3016
	bl {vg_p521_add_mod_p}
	li %r4, 3088
	li %r5, 2800
	li %r6, 2944
	bl {vg_p521_add_mod_p}
	li %r4, 3016
	li %r5, 2728
	li %r6, 3088
	bl {vg_p521_sub_mod_p}
	ld %r5, 3016(%r3)
	ld %r4, 3024(%r3)
	or %r5, %r5, %r4
	ld %r4, 3032(%r3)
	or %r5, %r5, %r4
	ld %r4, 3040(%r3)
	or %r5, %r5, %r4
	ld %r4, 3048(%r3)
	or %r5, %r5, %r4
	ld %r4, 3056(%r3)
	or %r5, %r5, %r4
	ld %r4, 3064(%r3)
	or %r5, %r5, %r4
	ld %r4, 3072(%r3)
	or %r5, %r5, %r4
	ld %r4, 3080(%r3)
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
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r10, 3232(%r3)
	ld %r4, 640(%r3)
	ld %r5, 2512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2800(%r3)
	ld %r4, 648(%r3)
	ld %r5, 2520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2808(%r3)
	ld %r4, 656(%r3)
	ld %r5, 2528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2816(%r3)
	ld %r4, 664(%r3)
	ld %r5, 2536(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2824(%r3)
	ld %r4, 672(%r3)
	ld %r5, 2544(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2832(%r3)
	ld %r4, 680(%r3)
	ld %r5, 2552(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2840(%r3)
	ld %r4, 688(%r3)
	ld %r5, 2560(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2848(%r3)
	ld %r4, 696(%r3)
	ld %r5, 2568(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2856(%r3)
	ld %r4, 704(%r3)
	ld %r5, 2576(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2864(%r3)
	ld %r4, 712(%r3)
	ld %r5, 2584(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3160(%r3)
	ld %r4, 720(%r3)
	ld %r5, 2592(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3168(%r3)
	ld %r4, 728(%r3)
	ld %r5, 2600(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3176(%r3)
	ld %r4, 736(%r3)
	ld %r5, 2608(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3184(%r3)
	ld %r4, 744(%r3)
	ld %r5, 2616(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3192(%r3)
	ld %r4, 752(%r3)
	ld %r5, 2624(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3200(%r3)
	ld %r4, 760(%r3)
	ld %r5, 2632(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3208(%r3)
	ld %r4, 768(%r3)
	ld %r5, 2640(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3216(%r3)
	ld %r4, 776(%r3)
	ld %r5, 2648(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 3224(%r3)
	ld %r10, 3232(%r3)
	ld %r4, 2656(%r3)
	li %r5, 1
	and %r4, %r4, %r5
	addi %r4, %r4, 2
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 2440(%r3)
	and %r4, %r4, %r10
	li %r6, 59
	stdbrx %r4, %r14, %r6
	ld %r4, 2448(%r3)
	and %r4, %r4, %r10
	li %r6, 51
	stdbrx %r4, %r14, %r6
	ld %r4, 2456(%r3)
	and %r4, %r4, %r10
	li %r6, 43
	stdbrx %r4, %r14, %r6
	ld %r4, 2464(%r3)
	and %r4, %r4, %r10
	li %r6, 35
	stdbrx %r4, %r14, %r6
	ld %r4, 2472(%r3)
	and %r4, %r4, %r10
	li %r6, 27
	stdbrx %r4, %r14, %r6
	ld %r4, 2480(%r3)
	and %r4, %r4, %r10
	li %r6, 19
	stdbrx %r4, %r14, %r6
	ld %r4, 2488(%r3)
	and %r4, %r4, %r10
	li %r6, 11
	stdbrx %r4, %r14, %r6
	ld %r4, 2496(%r3)
	and %r4, %r4, %r10
	li %r6, 3
	stdbrx %r4, %r14, %r6
	ld %r4, 2504(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 1(%r14)
	stb %r4, 2(%r14)
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr

vg_ec_p521_decompress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2296(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2304(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2312(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2320(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2328(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2336(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2344(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2352(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2360(%r3)
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2368(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2376(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2384(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2392(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2400(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2408(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2416(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2424(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2432(%r3)
	li %r9, 58
	ldbrx %r8, %r12, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r12, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r12, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r12, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r12, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r12, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r12, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r12, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 64(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 68(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 72(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 76(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 80(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 84(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 88(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 92(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 96(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 100(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 104(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 108(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 112(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 116(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 120(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 124(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 128(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 132(%r3)
	lis %r11, -28360
	ori %r11, %r11, 25609
	stw %r11, 136(%r3)
	lis %r11, -17553
	ori %r11, %r11, 46878
	stw %r11, 140(%r3)
	lis %r11, -30308
	ori %r11, %r11, 18350
	stw %r11, 144(%r3)
	lis %r11, 15285
	ori %r11, %r11, 51640
	stw %r11, 148(%r3)
	lis %r11, -2295
	ori %r11, %r11, 42448
	stw %r11, 152(%r3)
	lis %r11, 32716
	ori %r11, %r11, 328
	stw %r11, 156(%r3)
	lis %r11, -16593
	ori %r11, %r11, 38507
	stw %r11, 160(%r3)
	lis %r11, 20870
	ori %r11, %r11, 34691
	stw %r11, 164(%r3)
	lis %r11, -1
	ori %r11, %r11, 65530
	stw %r11, 168(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 172(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 176(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 180(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 184(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 188(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 192(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 196(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 200(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 204(%r3)
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
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 304(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 308(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 312(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 316(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 320(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 324(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 328(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 332(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 336(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 340(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 344(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 348(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 352(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 356(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 360(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 364(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 368(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 372(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 376(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 380(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 384(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 388(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 392(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 396(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 400(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 404(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 408(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 412(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 416(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 420(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 424(%r3)
	lis %r11, 128
	ori %r11, %r11, 0
	stw %r11, 428(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 432(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 436(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 440(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 444(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 448(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 452(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 456(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 460(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 464(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 468(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 472(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 476(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 480(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 484(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 488(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 492(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 496(%r3)
	lis %r11, -385
	ori %r11, %r11, 65535
	stw %r11, 500(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 504(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 508(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 512(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 516(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 520(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 524(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 528(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 532(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 536(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 540(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 544(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 548(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 552(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 556(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 560(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 564(%r3)
	lis %r11, 2825
	ori %r11, %r11, 10901
	stw %r11, 568(%r3)
	lis %r11, -32707
	ori %r11, %r11, 12271
	stw %r11, 572(%r3)
	lis %r11, -16736
	ori %r11, %r11, 63582
	stw %r11, 576(%r3)
	lis %r11, 27366
	ori %r11, %r11, 59311
	stw %r11, 580(%r3)
	lis %r11, 19547
	ori %r11, %r11, 49743
	stw %r11, 584(%r3)
	lis %r11, -30000
	ori %r11, %r11, 11727
	stw %r11, 588(%r3)
	lis %r11, 7129
	ori %r11, %r11, 35486
	stw %r11, 592(%r3)
	lis %r11, 14497
	ori %r11, %r11, 31777
	stw %r11, 596(%r3)
	lis %r11, -1310
	ori %r11, %r11, 48605
	stw %r11, 600(%r3)
	lis %r11, -11775
	ori %r11, %r11, 9685
	stw %r11, 604(%r3)
	lis %r11, 23126
	ori %r11, %r11, 27022
	stw %r11, 608(%r3)
	lis %r11, -4715
	ori %r11, %r11, 3790
	stw %r11, 612(%r3)
	lis %r11, -30362
	ori %r11, %r11, 36000
	stw %r11, 616(%r3)
	lis %r11, 26100
	ori %r11, %r11, 18347
	stw %r11, 620(%r3)
	lis %r11, 28945
	ori %r11, %r11, 51169
	stw %r11, 624(%r3)
	lis %r11, 12123
	ori %r11, %r11, 59186
	stw %r11, 628(%r3)
	lis %r11, 0
	ori %r11, %r11, 231
	stw %r11, 632(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 636(%r3)
	lis %r11, -32339
	ori %r11, %r11, 49409
	stw %r11, 640(%r3)
	lis %r11, -19663
	ori %r11, %r11, 41315
	stw %r11, 644(%r3)
	lis %r11, 6369
	ori %r11, %r11, 29406
	stw %r11, 648(%r3)
	lis %r11, 19964
	ori %r11, %r11, 48959
	stw %r11, 652(%r3)
	lis %r11, -7998
	ori %r11, %r11, 46369
	stw %r11, 656(%r3)
	lis %r11, 28441
	ori %r11, %r11, 42073
	stw %r11, 660(%r3)
	lis %r11, -27695
	ori %r11, %r11, 32724
	stw %r11, 664(%r3)
	lis %r11, -27521
	ori %r11, %r11, 3808
	stw %r11, 668(%r3)
	lis %r11, 15351
	ori %r11, %r11, 62380
	stw %r11, 672(%r3)
	lis %r11, -8880
	ori %r11, %r11, 42415
	stw %r11, 676(%r3)
	lis %r11, -20427
	ori %r11, %r11, 42654
	stw %r11, 680(%r3)
	lis %r11, -28420
	ori %r11, %r11, 5207
	stw %r11, 684(%r3)
	lis %r11, -25470
	ori %r11, %r11, 40922
	stw %r11, 688(%r3)
	lis %r11, 8526
	ori %r11, %r11, 12864
	stw %r11, 692(%r3)
	lis %r11, -19695
	ori %r11, %r11, 51930
	stw %r11, 696(%r3)
	lis %r11, -6449
	ori %r11, %r11, 8037
	stw %r11, 700(%r3)
	lis %r11, 0
	ori %r11, %r11, 116
	stw %r11, 704(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 708(%r3)
	lis %r11, 23198
	ori %r11, %r11, 9870
	stw %r11, 712(%r3)
	lis %r11, 10310
	ori %r11, %r11, 3658
	stw %r11, 716(%r3)
	lis %r11, 15183
	ori %r11, %r11, 59571
	stw %r11, 720(%r3)
	lis %r11, 8260
	ori %r11, %r11, 24394
	stw %r11, 724(%r3)
	lis %r11, 17233
	ori %r11, %r11, 14689
	stw %r11, 728(%r3)
	lis %r11, -20326
	ori %r11, %r11, 40504
	stw %r11, 732(%r3)
	lis %r11, -32609
	ori %r11, %r11, 54915
	stw %r11, 736(%r3)
	lis %r11, 8290
	ori %r11, %r11, 43100
	stw %r11, 740(%r3)
	lis %r11, 19631
	ori %r11, %r11, 31251
	stw %r11, 744(%r3)
	lis %r11, 5707
	ori %r11, %r11, 63289
	stw %r11, 748(%r3)
	lis %r11, -29805
	ori %r11, %r11, 40755
	stw %r11, 752(%r3)
	lis %r11, 13323
	ori %r11, %r11, 55262
	stw %r11, 756(%r3)
	lis %r11, 9387
	ori %r11, %r11, 52642
	stw %r11, 760(%r3)
	lis %r11, -4916
	ori %r11, %r11, 31394
	stw %r11, 764(%r3)
	lis %r11, -9706
	ori %r11, %r11, 16013
	stw %r11, 768(%r3)
	lis %r11, 558
	ori %r11, %r11, 17711
	stw %r11, 772(%r3)
	lis %r11, 0
	ori %r11, %r11, 480
	stw %r11, 776(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 780(%r3)
	lis %r11, -12523
	ori %r11, %r11, 56580
	stw %r11, 784(%r3)
	lis %r11, 4988
	ori %r11, %r11, 53325
	stw %r11, 788(%r3)
	lis %r11, -6828
	ori %r11, %r11, 32419
	stw %r11, 792(%r3)
	lis %r11, -2297
	ori %r11, %r11, 47836
	stw %r11, 796(%r3)
	lis %r11, 31045
	ori %r11, %r11, 29695
	stw %r11, 800(%r3)
	lis %r11, 4775
	ori %r11, %r11, 36152
	stw %r11, 804(%r3)
	lis %r11, 22519
	ori %r11, %r11, 24070
	stw %r11, 808(%r3)
	lis %r11, -11406
	ori %r11, %r11, 7925
	stw %r11, 812(%r3)
	lis %r11, 11849
	ori %r11, %r11, 51163
	stw %r11, 816(%r3)
	lis %r11, -8850
	ori %r11, %r11, 9176
	stw %r11, 820(%r3)
	lis %r11, -18571
	ori %r11, %r11, 28222
	stw %r11, 824(%r3)
	lis %r11, -12301
	ori %r11, %r11, 53570
	stw %r11, 828(%r3)
	lis %r11, -22299
	ori %r11, %r11, 26556
	stw %r11, 832(%r3)
	lis %r11, 23500
	ori %r11, %r11, 28001
	stw %r11, 836(%r3)
	lis %r11, 18733
	ori %r11, %r11, 3397
	stw %r11, 840(%r3)
	lis %r11, 11662
	ori %r11, %r11, 977
	stw %r11, 844(%r3)
	lis %r11, 0
	ori %r11, %r11, 61
	stw %r11, 848(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 852(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 856(%r3)
	lis %r11, -1152
	ori %r11, %r11, 0
	stw %r11, 860(%r3)
	lis %r11, 28855
	ori %r11, %r11, 25549
	stw %r11, 864(%r3)
	lis %r11, 10402
	ori %r11, %r11, 18468
	stw %r11, 868(%r3)
	lis %r11, 9147
	ori %r11, %r11, 12764
	stw %r11, 872(%r3)
	lis %r11, 6114
	ori %r11, %r11, 9499
	stw %r11, 876(%r3)
	lis %r11, 23428
	ori %r11, %r11, 31533
	stw %r11, 880(%r3)
	lis %r11, -13760
	ori %r11, %r11, 6655
	stw %r11, 884(%r3)
	lis %r11, 15904
	ori %r11, %r11, 26676
	stw %r11, 888(%r3)
	lis %r11, 727
	ori %r11, %r11, 15548
	stw %r11, 892(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 896(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 900(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 904(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 908(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 912(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 916(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 920(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 924(%r3)
	lis %r11, -1
	ori %r11, %r11, 65533
	stw %r11, 928(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 932(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 936(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 940(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 944(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 948(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 952(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 956(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 960(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 964(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 968(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 972(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 976(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 980(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 984(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 988(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 992(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 996(%r3)
	lis %r11, -28360
	ori %r11, %r11, 25607
	stw %r11, 1000(%r3)
	lis %r11, -17553
	ori %r11, %r11, 46878
	stw %r11, 1004(%r3)
	lis %r11, -30308
	ori %r11, %r11, 18350
	stw %r11, 1008(%r3)
	lis %r11, 15285
	ori %r11, %r11, 51640
	stw %r11, 1012(%r3)
	lis %r11, -2295
	ori %r11, %r11, 42448
	stw %r11, 1016(%r3)
	lis %r11, 32716
	ori %r11, %r11, 328
	stw %r11, 1020(%r3)
	lis %r11, -16593
	ori %r11, %r11, 38507
	stw %r11, 1024(%r3)
	lis %r11, 20870
	ori %r11, %r11, 34691
	stw %r11, 1028(%r3)
	lis %r11, -1
	ori %r11, %r11, 65530
	stw %r11, 1032(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1036(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1040(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1044(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1048(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1052(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1056(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 1060(%r3)
	lis %r11, 0
	ori %r11, %r11, 511
	stw %r11, 1064(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1068(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1072(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1076(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1080(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1084(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1088(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1092(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1096(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1100(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1104(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1108(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1112(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1116(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1120(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1124(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1128(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1132(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1136(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1140(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1144(%r3)
	lis %r11, 128
	ori %r11, %r11, 0
	stw %r11, 1148(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1152(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1156(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1160(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1164(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1168(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1172(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1176(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1180(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1184(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1188(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1192(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1196(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1200(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1204(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1208(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1212(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1216(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1220(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1224(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1228(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1236(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1240(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1244(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1248(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1252(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1256(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1260(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1264(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1268(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1272(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1276(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1280(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1284(%r3)
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 3232(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2872(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2876(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2880(%r3)
	lis %r11, 0
	ori %r11, %r11, 16384
	stw %r11, 2884(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2888(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2892(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2896(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2900(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2904(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2908(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2912(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2916(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2920(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2924(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2928(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2932(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2936(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 2940(%r3)
	lis %r11, -20904
	ori %r11, %r11, 25479
	stw %r11, 2944(%r3)
	lis %r11, -32748
	ori %r11, %r11, 25935
	stw %r11, 2948(%r3)
	lis %r11, -5579
	ori %r11, %r11, 43039
	stw %r11, 2952(%r3)
	lis %r11, 30967
	ori %r11, %r11, 41615
	stw %r11, 2956(%r3)
	lis %r11, -15330
	ori %r11, %r11, 38426
	stw %r11, 2960(%r3)
	lis %r11, -31846
	ori %r11, %r11, 47599
	stw %r11, 2964(%r3)
	lis %r11, 24221
	ori %r11, %r11, 55519
	stw %r11, 2968(%r3)
	lis %r11, -17013
	ori %r11, %r11, 10592
	stw %r11, 2972(%r3)
	lis %r11, -22282
	ori %r11, %r11, 16201
	stw %r11, 2976(%r3)
	lis %r11, -3925
	ori %r11, %r11, 3228
	stw %r11, 2980(%r3)
	lis %r11, -14137
	ori %r11, %r11, 30852
	stw %r11, 2984(%r3)
	lis %r11, -1572
	ori %r11, %r11, 23108
	stw %r11, 2988(%r3)
	lis %r11, 11724
	ori %r11, %r11, 55690
	stw %r11, 2992(%r3)
	lis %r11, 30545
	ori %r11, %r11, 27961
	stw %r11, 2996(%r3)
	lis %r11, -12197
	ori %r11, %r11, 17056
	stw %r11, 3000(%r3)
	lis %r11, 4041
	ori %r11, %r11, 19728
	stw %r11, 3004(%r3)
	lis %r11, 0
	ori %r11, %r11, 77
	stw %r11, 3008(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 3012(%r3)
	addi %r6, %r12, 1
	li %r9, 58
	ldbrx %r8, %r6, %r9
	std %r8, 2440(%r3)
	li %r9, 50
	ldbrx %r8, %r6, %r9
	std %r8, 2448(%r3)
	li %r9, 42
	ldbrx %r8, %r6, %r9
	std %r8, 2456(%r3)
	li %r9, 34
	ldbrx %r8, %r6, %r9
	std %r8, 2464(%r3)
	li %r9, 26
	ldbrx %r8, %r6, %r9
	std %r8, 2472(%r3)
	li %r9, 18
	ldbrx %r8, %r6, %r9
	std %r8, 2480(%r3)
	li %r9, 10
	ldbrx %r8, %r6, %r9
	std %r8, 2488(%r3)
	li %r9, 2
	ldbrx %r8, %r6, %r9
	std %r8, 2496(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	rldicl %r8, %r8, 16, 48
	std %r8, 2504(%r3)
	lbz %r4, 0(%r12)
	std %r4, 2368(%r3)
	li %r5, 1
	or %r4, %r4, %r5
	li %r5, 3
	xor %r4, %r4, %r5
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2440(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2444(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2448(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2452(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2456(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2460(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2464(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2468(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2472(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2476(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2480(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2484(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2488(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2492(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2496(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2500(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2504(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2508(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	li %r4, 2512
	li %r5, 2440
	li %r6, 2872
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 2512
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 3088
	li %r5, 3016
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 496
	li %r6, 2512
	bl {vg_p521_mul_mod_p}
	li %r4, 2800
	li %r5, 3088
	li %r6, 3016
	bl {vg_p521_add_mod_p}
	li %r4, 3088
	li %r5, 2800
	li %r6, 2944
	bl {vg_p521_add_mod_p}
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 928(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 932(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 936(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 940(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 944(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 948(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 952(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 956(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 960(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 964(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 968(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 972(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 976(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 980(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 984(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 988(%r3)
	lis %r11, 0
	ori %r11, %r11, 128
	stw %r11, 992(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 996(%r3)
	li %r31, 72
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 928(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 5248(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 5249(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 5250(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 5251(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 5252(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 5253(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 5254(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 5255(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 20b
	ld %r4, 424(%r3)
	std %r4, 2152(%r3)
	ld %r4, 432(%r3)
	std %r4, 2160(%r3)
	ld %r4, 440(%r3)
	std %r4, 2168(%r3)
	ld %r4, 448(%r3)
	std %r4, 2176(%r3)
	ld %r4, 456(%r3)
	std %r4, 2184(%r3)
	ld %r4, 464(%r3)
	std %r4, 2192(%r3)
	ld %r4, 472(%r3)
	std %r4, 2200(%r3)
	ld %r4, 480(%r3)
	std %r4, 2208(%r3)
	ld %r4, 488(%r3)
	std %r4, 2216(%r3)
	li %r31, 576
21:
	addi %r31, %r31, -1
	li %r4, 2152
	li %r5, 2152
	li %r6, 2152
	bl {vg_p521_mul_mod_p}
	li %r4, 2224
	li %r5, 2152
	li %r6, 3088
	bl {vg_p521_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 5248(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 2152(%r3)
	ld %r5, 2224(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2152(%r3)
	ld %r4, 2160(%r3)
	ld %r5, 2232(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2160(%r3)
	ld %r4, 2168(%r3)
	ld %r5, 2240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2168(%r3)
	ld %r4, 2176(%r3)
	ld %r5, 2248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2176(%r3)
	ld %r4, 2184(%r3)
	ld %r5, 2256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2184(%r3)
	ld %r4, 2192(%r3)
	ld %r5, 2264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2192(%r3)
	ld %r4, 2200(%r3)
	ld %r5, 2272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2200(%r3)
	ld %r4, 2208(%r3)
	ld %r5, 2280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2208(%r3)
	ld %r4, 2216(%r3)
	ld %r5, 2288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2216(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 2656
	li %r5, 2152
	li %r6, 352
	bl {vg_p521_mul_mod_p}
	li %r4, 2728
	li %r5, 280
	li %r6, 2656
	bl {vg_p521_sub_mod_p}
	ld %r4, 2656(%r3)
	ld %r5, 2368(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	ld %r4, 2656(%r3)
	ld %r5, 2728(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2656(%r3)
	ld %r4, 2664(%r3)
	ld %r5, 2736(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2664(%r3)
	ld %r4, 2672(%r3)
	ld %r5, 2744(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2672(%r3)
	ld %r4, 2680(%r3)
	ld %r5, 2752(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2680(%r3)
	ld %r4, 2688(%r3)
	ld %r5, 2760(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2688(%r3)
	ld %r4, 2696(%r3)
	ld %r5, 2768(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2696(%r3)
	ld %r4, 2704(%r3)
	ld %r5, 2776(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2704(%r3)
	ld %r4, 2712(%r3)
	ld %r5, 2784(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2712(%r3)
	ld %r4, 2720(%r3)
	ld %r5, 2792(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2720(%r3)
	li %r4, 2584
	li %r5, 2656
	li %r6, 2872
	bl {vg_p521_mul_mod_p}
	li %r4, 3016
	li %r5, 2584
	li %r6, 2584
	bl {vg_p521_mul_mod_p}
	li %r4, 2800
	li %r5, 3016
	li %r6, 3088
	bl {vg_p521_sub_mod_p}
	ld %r5, 2800(%r3)
	ld %r4, 2808(%r3)
	or %r5, %r5, %r4
	ld %r4, 2816(%r3)
	or %r5, %r5, %r4
	ld %r4, 2824(%r3)
	or %r5, %r5, %r4
	ld %r4, 2832(%r3)
	or %r5, %r5, %r4
	ld %r4, 2840(%r3)
	or %r5, %r5, %r4
	ld %r4, 2848(%r3)
	or %r5, %r5, %r4
	ld %r4, 2856(%r3)
	or %r5, %r5, %r4
	ld %r4, 2864(%r3)
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
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r4, 2656(%r3)
	ld %r5, 2368(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	addi %r5, %r10, 1
	li %r4, 0
	subf %r5, %r5, %r4
	ld %r4, 3232(%r3)
	and %r4, %r4, %r5
	std %r4, 3232(%r3)
	ld %r10, 3232(%r3)
	li %r4, 4
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 2440(%r3)
	and %r4, %r4, %r10
	li %r6, 59
	stdbrx %r4, %r14, %r6
	ld %r4, 2448(%r3)
	and %r4, %r4, %r10
	li %r6, 51
	stdbrx %r4, %r14, %r6
	ld %r4, 2456(%r3)
	and %r4, %r4, %r10
	li %r6, 43
	stdbrx %r4, %r14, %r6
	ld %r4, 2464(%r3)
	and %r4, %r4, %r10
	li %r6, 35
	stdbrx %r4, %r14, %r6
	ld %r4, 2472(%r3)
	and %r4, %r4, %r10
	li %r6, 27
	stdbrx %r4, %r14, %r6
	ld %r4, 2480(%r3)
	and %r4, %r4, %r10
	li %r6, 19
	stdbrx %r4, %r14, %r6
	ld %r4, 2488(%r3)
	and %r4, %r4, %r10
	li %r6, 11
	stdbrx %r4, %r14, %r6
	ld %r4, 2496(%r3)
	and %r4, %r4, %r10
	li %r6, 3
	stdbrx %r4, %r14, %r6
	ld %r4, 2504(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 1(%r14)
	stb %r4, 2(%r14)
	ld %r4, 2656(%r3)
	and %r4, %r4, %r10
	li %r6, 125
	stdbrx %r4, %r14, %r6
	ld %r4, 2664(%r3)
	and %r4, %r4, %r10
	li %r6, 117
	stdbrx %r4, %r14, %r6
	ld %r4, 2672(%r3)
	and %r4, %r4, %r10
	li %r6, 109
	stdbrx %r4, %r14, %r6
	ld %r4, 2680(%r3)
	and %r4, %r4, %r10
	li %r6, 101
	stdbrx %r4, %r14, %r6
	ld %r4, 2688(%r3)
	and %r4, %r4, %r10
	li %r6, 93
	stdbrx %r4, %r14, %r6
	ld %r4, 2696(%r3)
	and %r4, %r4, %r10
	li %r6, 85
	stdbrx %r4, %r14, %r6
	ld %r4, 2704(%r3)
	and %r4, %r4, %r10
	li %r6, 77
	stdbrx %r4, %r14, %r6
	ld %r4, 2712(%r3)
	and %r4, %r4, %r10
	li %r6, 69
	stdbrx %r4, %r14, %r6
	ld %r4, 2720(%r3)
	and %r4, %r4, %r10
	rldicl %r5, %r4, 56, 8
	stb %r5, 67(%r14)
	stb %r4, 68(%r14)
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
