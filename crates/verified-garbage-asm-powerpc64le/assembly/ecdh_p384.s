// The functions of `src/ecdh_p384.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdh_p384:
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
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 64(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 68(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 72(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 76(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
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
	lis %r11, -13115
	ori %r11, %r11, 10611
	stw %r11, 112(%r3)
	lis %r11, -4884
	ori %r11, %r11, 6506
	stw %r11, 116(%r3)
	lis %r11, 18608
	ori %r11, %r11, 42874
	stw %r11, 120(%r3)
	lis %r11, 22554
	ori %r11, %r11, 3506
	stw %r11, 124(%r3)
	lis %r11, -3017
	ori %r11, %r11, 11743
	stw %r11, 128(%r3)
	lis %r11, -14493
	ori %r11, %r11, 19841
	stw %r11, 132(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 136(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 140(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 144(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 148(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 152(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
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
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 304(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 308(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 312(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 316(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
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
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 352(%r3)
	lis %r11, 0
	ori %r11, %r11, 3
	stw %r11, 356(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 360(%r3)
	lis %r11, -1
	ori %r11, %r11, 65532
	stw %r11, 364(%r3)
	lis %r11, -1
	ori %r11, %r11, 65531
	stw %r11, 368(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 372(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 376(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 380(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 384(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 388(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 392(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 396(%r3)
	lis %r11, -10301
	ori %r11, %r11, 35174
	stw %r11, 400(%r3)
	lis %r11, 6196
	ori %r11, %r11, 39250
	stw %r11, 404(%r3)
	lis %r11, 28388
	ori %r11, %r11, 39108
	stw %r11, 408(%r3)
	lis %r11, -6787
	ori %r11, %r11, 2443
	stw %r11, 412(%r3)
	lis %r11, 19296
	ori %r11, %r11, 1678
	stw %r11, 416(%r3)
	lis %r11, 26582
	ori %r11, %r11, 25041
	stw %r11, 420(%r3)
	lis %r11, -16966
	ori %r11, %r11, 41127
	stw %r11, 424(%r3)
	lis %r11, -22107
	ori %r11, %r11, 58315
	stw %r11, 428(%r3)
	lis %r11, 23814
	ori %r11, %r11, 25022
	stw %r11, 432(%r3)
	lis %r11, 8833
	ori %r11, %r11, 26076
	stw %r11, 436(%r3)
	lis %r11, 8431
	ori %r11, %r11, 16365
	stw %r11, 440(%r3)
	lis %r11, 26392
	ori %r11, %r11, 13282
	stw %r11, 444(%r3)
	lis %r11, 18880
	ori %r11, %r11, 46376
	stw %r11, 448(%r3)
	lis %r11, 15824
	ori %r11, %r11, 30054
	stw %r11, 452(%r3)
	lis %r11, -24362
	ori %r11, %r11, 52792
	stw %r11, 456(%r3)
	lis %r11, 8419
	ori %r11, %r11, 30946
	stw %r11, 460(%r3)
	lis %r11, 21531
	ori %r11, %r11, 19822
	stw %r11, 464(%r3)
	lis %r11, -30820
	ori %r11, %r11, 15100
	stw %r11, 468(%r3)
	lis %r11, 22947
	ori %r11, %r11, 3839
	stw %r11, 472(%r3)
	lis %r11, 25684
	ori %r11, %r11, 34436
	stw %r11, 476(%r3)
	lis %r11, 24910
	ori %r11, %r11, 56875
	stw %r11, 480(%r3)
	lis %r11, -32465
	ori %r11, %r11, 63267
	stw %r11, 484(%r3)
	lis %r11, 10654
	ori %r11, %r11, 5395
	stw %r11, 488(%r3)
	lis %r11, 19770
	ori %r11, %r11, 44482
	stw %r11, 492(%r3)
	lis %r11, 19203
	ori %r11, %r11, 42238
	stw %r11, 496(%r3)
	lis %r11, 8964
	ori %r11, %r11, 15789
	stw %r11, 500(%r3)
	lis %r11, 31668
	ori %r11, %r11, 43436
	stw %r11, 504(%r3)
	lis %r11, -24129
	ori %r11, %r11, 43199
	stw %r11, 508(%r3)
	lis %r11, 11907
	ori %r11, %r11, 45136
	stw %r11, 512(%r3)
	lis %r11, -29779
	ori %r11, %r11, 59222
	stw %r11, 516(%r3)
	lis %r11, 26868
	ori %r11, %r11, 65497
	stw %r11, 520(%r3)
	lis %r11, -14653
	ori %r11, %r11, 21017
	stw %r11, 524(%r3)
	lis %r11, 14697
	ori %r11, %r11, 43072
	stw %r11, 528(%r3)
	lis %r11, -8832
	ori %r11, %r11, 550
	stw %r11, 532(%r3)
	lis %r11, 23061
	ori %r11, %r11, 50665
	stw %r11, 536(%r3)
	lis %r11, 11128
	ori %r11, %r11, 43970
	stw %r11, 540(%r3)
	lis %r11, 6580
	ori %r11, %r11, 2473
	stw %r11, 544(%r3)
	lis %r11, 11569
	ori %r11, %r11, 39716
	stw %r11, 548(%r3)
	lis %r11, -8422
	ori %r11, %r11, 42009
	stw %r11, 552(%r3)
	lis %r11, -195
	ori %r11, %r11, 33253
	stw %r11, 556(%r3)
	lis %r11, -840
	ori %r11, %r11, 10567
	stw %r11, 560(%r3)
	lis %r11, -17346
	ori %r11, %r11, 18490
	stw %r11, 564(%r3)
	lis %r11, 19115
	ori %r11, %r11, 7365
	stw %r11, 568(%r3)
	lis %r11, -11251
	ori %r11, %r11, 18711
	stw %r11, 572(%r3)
	lis %r11, 10278
	ori %r11, %r11, 26773
	stw %r11, 576(%r3)
	lis %r11, 16304
	ori %r11, %r11, 23418
	stw %r11, 580(%r3)
	lis %r11, 11065
	ori %r11, %r11, 48929
	stw %r11, 584(%r3)
	lis %r11, 3204
	ori %r11, %r11, 60929
	stw %r11, 588(%r3)
	lis %r11, 13114
	ori %r11, %r11, 54925
	stw %r11, 592(%r3)
	lis %r11, 4883
	ori %r11, %r11, 59029
	stw %r11, 596(%r3)
	lis %r11, -18609
	ori %r11, %r11, 22661
	stw %r11, 600(%r3)
	lis %r11, -22555
	ori %r11, %r11, 62029
	stw %r11, 604(%r3)
	lis %r11, 3016
	ori %r11, %r11, 53792
	stw %r11, 608(%r3)
	lis %r11, 14492
	ori %r11, %r11, 45694
	stw %r11, 612(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 616(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 620(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 624(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 628(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 632(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 636(%r3)
	lis %r11, -1
	ori %r11, %r11, 65533
	stw %r11, 640(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 644(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 648(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 652(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 656(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 660(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 664(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 668(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 672(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 676(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 680(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 684(%r3)
	lis %r11, -13115
	ori %r11, %r11, 10609
	stw %r11, 688(%r3)
	lis %r11, -4884
	ori %r11, %r11, 6506
	stw %r11, 692(%r3)
	lis %r11, 18608
	ori %r11, %r11, 42874
	stw %r11, 696(%r3)
	lis %r11, 22554
	ori %r11, %r11, 3506
	stw %r11, 700(%r3)
	lis %r11, -3017
	ori %r11, %r11, 11743
	stw %r11, 704(%r3)
	lis %r11, -14493
	ori %r11, %r11, 19841
	stw %r11, 708(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 712(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 716(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 720(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 724(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 728(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
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
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 784(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 788(%r3)
	lis %r11, -1
	ori %r11, %r11, 65535
	stw %r11, 792(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 796(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 800(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 804(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 808(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 812(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 816(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 820(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 824(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1936(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 1940(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1944(%r3)
	lis %r11, 0
	ori %r11, %r11, 2
	stw %r11, 1948(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1952(%r3)
	lis %r11, -1
	ori %r11, %r11, 65534
	stw %r11, 1956(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1960(%r3)
	lis %r11, 0
	ori %r11, %r11, 2
	stw %r11, 1964(%r3)
	lis %r11, 0
	ori %r11, %r11, 1
	stw %r11, 1968(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1972(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1976(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1980(%r3)
	lis %r11, -25279
	ori %r11, %r11, 11724
	stw %r11, 1984(%r3)
	lis %r11, 2065
	ori %r11, %r11, 34929
	stw %r11, 1988(%r3)
	lis %r11, 31308
	ori %r11, %r11, 13036
	stw %r11, 1992(%r3)
	lis %r11, -2263
	ori %r11, %r11, 44504
	stw %r11, 1996(%r3)
	lis %r11, 6432
	ori %r11, %r11, 558
	stw %r11, 2000(%r3)
	lis %r11, 30706
	ori %r11, %r11, 8347
	stw %r11, 2004(%r3)
	lis %r11, -27501
	ori %r11, %r11, 35554
	stw %r11, 2008(%r3)
	lis %r11, -7369
	ori %r11, %r11, 19438
	stw %r11, 2012(%r3)
	lis %r11, 7938
	ori %r11, %r11, 8340
	stw %r11, 2016(%r3)
	lis %r11, -18901
	ori %r11, %r11, 8692
	stw %r11, 2020(%r3)
	lis %r11, 24655
	ori %r11, %r11, 49145
	stw %r11, 2024(%r3)
	lis %r11, -13048
	ori %r11, %r11, 4427
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1744
	li %r5, 1792
	li %r6, 1936
	bl {vg_p384_mul_mod_p}
	li %r4, 1840
	li %r5, 1744
	li %r6, 1744
	bl {vg_p384_mul_mod_p}
	li %r4, 2032
	li %r5, 1696
	li %r6, 1696
	bl {vg_p384_mul_mod_p}
	li %r4, 2080
	li %r5, 2032
	li %r6, 1696
	bl {vg_p384_mul_mod_p}
	li %r4, 2032
	li %r5, 352
	li %r6, 1696
	bl {vg_p384_mul_mod_p}
	li %r4, 1888
	li %r5, 2080
	li %r6, 2032
	bl {vg_p384_add_mod_p}
	li %r4, 2080
	li %r5, 1888
	li %r6, 1984
	bl {vg_p384_add_mod_p}
	li %r4, 2032
	li %r5, 1840
	li %r6, 2080
	bl {vg_p384_sub_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 2128
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 976
	li %r6, 304
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1888
	li %r6, 2128
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 2128
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1888
	li %r6, 304
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1168
	li %r5, 832
	li %r6, 832
	bl {vg_p384_mul_mod_p}
	li %r4, 928
	li %r5, 784
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 976
	li %r5, 832
	li %r6, 208
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 976
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 928
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 880
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1312
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1024
	li %r6, 1312
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1312
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1264
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1312
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1168
	li %r5, 1120
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 1024
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 880
	li %r5, 1024
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 880
	bl {vg_p384_mul_mod_p}
	li %r4, 880
	li %r5, 1312
	li %r6, 1312
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 1312
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 976
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 880
	li %r5, 1312
	li %r6, 1312
	bl {vg_p384_mul_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 928
	li %r5, 1264
	li %r6, 880
	bl {vg_p384_sub_mod_p}
	li %r4, 928
	li %r5, 1312
	li %r6, 928
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1168
	li %r5, 976
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 928
	li %r6, 928
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 880
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 880
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1312
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1024
	li %r6, 1312
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1312
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1264
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1312
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1168
	li %r5, 1120
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 1024
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 880
	li %r5, 1024
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 880
	bl {vg_p384_mul_mod_p}
	li %r4, 880
	li %r5, 1312
	li %r6, 1312
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 880
	li %r6, 1312
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 976
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 880
	li %r5, 1312
	li %r6, 1312
	bl {vg_p384_mul_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 928
	li %r5, 1264
	li %r6, 880
	bl {vg_p384_sub_mod_p}
	li %r4, 928
	li %r5, 1312
	li %r6, 928
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 736
	li %r5, 880
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 1168
	li %r5, 976
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 832
	li %r5, 1168
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 784
	li %r5, 928
	li %r6, 208
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 784
	li %r6, 928
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 832
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 736
	li %r6, 784
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 880
	li %r6, 928
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1168
	li %r6, 1216
	bl {vg_p384_add_mod_p}
	li %r4, 1312
	li %r5, 1312
	li %r6, 1360
	bl {vg_p384_sub_mod_p}
	li %r4, 1360
	li %r5, 784
	li %r6, 832
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 928
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 736
	li %r6, 832
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1072
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1984
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1072
	li %r6, 1120
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1024
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_add_mod_p}
	li %r4, 1120
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_sub_mod_p}
	li %r4, 1024
	li %r5, 1216
	li %r6, 1024
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1984
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1264
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1072
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1072
	li %r5, 1216
	li %r6, 1072
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1216
	li %r5, 1360
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1072
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1024
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1072
	li %r5, 1072
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1024
	li %r5, 1312
	li %r6, 1024
	bl {vg_p384_mul_mod_p}
	li %r4, 1024
	li %r5, 1024
	li %r6, 1216
	bl {vg_p384_sub_mod_p}
	li %r4, 1120
	li %r5, 1360
	li %r6, 1120
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1312
	li %r6, 1168
	bl {vg_p384_mul_mod_p}
	li %r4, 1120
	li %r5, 1120
	li %r6, 1216
	bl {vg_p384_add_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1504
	li %r5, 1456
	li %r6, 832
	bl {vg_p384_mul_mod_p}
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
	bl {vg_p384_mul_mod_p}
	li %r4, 1744
	li %r5, 1696
	li %r6, 256
	bl {vg_p384_mul_mod_p}
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
