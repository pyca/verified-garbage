// The functions of `src/ecdsa_p384.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_p384_verify:
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
	bl {vg_p384_mul_mod_n}
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
	bl {vg_p384_mul_mod_n}
	li %r4, 1504
	li %r5, 1456
	li %r6, 1840
	bl {vg_p384_mul_mod_n}
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
	bl {vg_p384_mul_mod_n}
	li %r4, 1936
	li %r5, 1552
	li %r6, 544
	bl {vg_p384_mul_mod_n}
	li %r4, 2032
	li %r5, 1984
	li %r6, 1456
	bl {vg_p384_mul_mod_n}
	li %r4, 2080
	li %r5, 1936
	li %r6, 1456
	bl {vg_p384_mul_mod_n}
	li %r4, 1696
	li %r5, 2032
	li %r6, 256
	bl {vg_p384_mul_mod_n}
	li %r4, 1744
	li %r5, 2080
	li %r6, 256
	bl {vg_p384_mul_mod_n}
	ld %r4, 1696(%r3)
	std %r4, 1552(%r3)
	ld %r4, 1704(%r3)
	std %r4, 1560(%r3)
	ld %r4, 1712(%r3)
	std %r4, 1568(%r3)
	ld %r4, 1720(%r3)
	std %r4, 1576(%r3)
	ld %r4, 1728(%r3)
	std %r4, 1584(%r3)
	ld %r4, 1736(%r3)
	std %r4, 1592(%r3)
	ld %r4, 448(%r3)
	std %r4, 736(%r3)
	ld %r4, 456(%r3)
	std %r4, 744(%r3)
	ld %r4, 464(%r3)
	std %r4, 752(%r3)
	ld %r4, 472(%r3)
	std %r4, 760(%r3)
	ld %r4, 480(%r3)
	std %r4, 768(%r3)
	ld %r4, 488(%r3)
	std %r4, 776(%r3)
	ld %r4, 496(%r3)
	std %r4, 784(%r3)
	ld %r4, 504(%r3)
	std %r4, 792(%r3)
	ld %r4, 512(%r3)
	std %r4, 800(%r3)
	ld %r4, 520(%r3)
	std %r4, 808(%r3)
	ld %r4, 528(%r3)
	std %r4, 816(%r3)
	ld %r4, 536(%r3)
	std %r4, 824(%r3)
	bl {vg_p384_mul}
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
	ld %r4, 1744(%r3)
	std %r4, 1552(%r3)
	ld %r4, 1752(%r3)
	std %r4, 1560(%r3)
	ld %r4, 1760(%r3)
	std %r4, 1568(%r3)
	ld %r4, 1768(%r3)
	std %r4, 1576(%r3)
	ld %r4, 1776(%r3)
	std %r4, 1584(%r3)
	ld %r4, 1784(%r3)
	std %r4, 1592(%r3)
	ld %r4, 1888(%r3)
	std %r4, 736(%r3)
	ld %r4, 1896(%r3)
	std %r4, 744(%r3)
	ld %r4, 1904(%r3)
	std %r4, 752(%r3)
	ld %r4, 1912(%r3)
	std %r4, 760(%r3)
	ld %r4, 1920(%r3)
	std %r4, 768(%r3)
	ld %r4, 1928(%r3)
	std %r4, 776(%r3)
	ld %r4, 2128(%r3)
	std %r4, 784(%r3)
	ld %r4, 2136(%r3)
	std %r4, 792(%r3)
	ld %r4, 2144(%r3)
	std %r4, 800(%r3)
	ld %r4, 2152(%r3)
	std %r4, 808(%r3)
	ld %r4, 2160(%r3)
	std %r4, 816(%r3)
	ld %r4, 2168(%r3)
	std %r4, 824(%r3)
	bl {vg_p384_mul}
	li %r4, 1168
	li %r5, 2032
	li %r6, 736
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 2080
	li %r6, 784
	bl {vg_p384_mul_mod_p}
	li %r4, 1264
	li %r5, 1840
	li %r6, 832
	bl {vg_p384_mul_mod_p}
	li %r4, 1312
	li %r5, 2032
	li %r6, 2080
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 736
	li %r6, 784
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
	li %r5, 2032
	li %r6, 1840
	bl {vg_p384_add_mod_p}
	li %r4, 1408
	li %r5, 736
	li %r6, 832
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_p384_mul_mod_p}
	li %r4, 1408
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1408
	bl {vg_p384_sub_mod_p}
	li %r4, 1408
	li %r5, 2080
	li %r6, 1840
	bl {vg_p384_add_mod_p}
	li %r4, 880
	li %r5, 784
	li %r6, 832
	bl {vg_p384_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 880
	bl {vg_p384_mul_mod_p}
	li %r4, 880
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 880
	bl {vg_p384_sub_mod_p}
	li %r4, 976
	li %r5, 352
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 880
	li %r5, 400
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 976
	li %r5, 880
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 880
	li %r5, 1216
	li %r6, 976
	bl {vg_p384_sub_mod_p}
	li %r4, 976
	li %r5, 1216
	li %r6, 976
	bl {vg_p384_add_mod_p}
	li %r4, 928
	li %r5, 880
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1168
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 400
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1264
	li %r5, 1168
	li %r6, 1264
	bl {vg_p384_sub_mod_p}
	li %r4, 1264
	li %r5, 352
	li %r6, 1264
	bl {vg_p384_mul_mod_p}
	li %r4, 1360
	li %r5, 1360
	li %r6, 1264
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1216
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 928
	li %r5, 928
	li %r6, 1168
	bl {vg_p384_add_mod_p}
	li %r4, 1168
	li %r5, 1408
	li %r6, 1360
	bl {vg_p384_mul_mod_p}
	li %r4, 880
	li %r5, 1312
	li %r6, 880
	bl {vg_p384_mul_mod_p}
	li %r4, 880
	li %r5, 880
	li %r6, 1168
	bl {vg_p384_sub_mod_p}
	li %r4, 1168
	li %r5, 1312
	li %r6, 1216
	bl {vg_p384_mul_mod_p}
	li %r4, 976
	li %r5, 1408
	li %r6, 976
	bl {vg_p384_mul_mod_p}
	li %r4, 976
	li %r5, 976
	li %r6, 1168
	bl {vg_p384_add_mod_p}
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
	li %r4, 1888
	li %r5, 1744
	li %r6, 544
	bl {vg_p384_mul_mod_n}
	li %r4, 1984
	li %r5, 1888
	li %r6, 1936
	bl {vg_p384_sub_mod_n}
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
