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

vg_ecdsa_p384_sign:
	or %r6, %r7, %r7
	ld %r9, 24(%r8)
	addi %r10, %r9, -0
	cmpldi %cr0, %r10, 0
	beq %cr0, 20f
	addi %r10, %r9, -1
	cmpldi %cr0, %r10, 0
	beq %cr0, 22f
	addi %r10, %r9, -2
	cmpldi %cr0, %r10, 0
	beq %cr0, 24f
	addi %r10, %r9, -3
	cmpldi %cr0, %r10, 0
	beq %cr0, 26f
	addi %r10, %r9, -4
	cmpldi %cr0, %r10, 0
	beq %cr0, 28f
	addi %r10, %r9, -5
	cmpldi %cr0, %r10, 0
	beq %cr0, 210f
	addi %r10, %r9, -6
	cmpldi %cr0, %r10, 0
	beq %cr0, 212f
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -528(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 256(%r11)
	std %r8, 264(%r11)
	std %r8, 272(%r11)
	std %r8, 280(%r11)
	std %r8, 288(%r11)
	std %r8, 296(%r11)
	std %r8, 304(%r11)
	std %r8, 312(%r11)
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 272(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 276(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 280(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 284(%r11)
	lwz %r8, 16(%r9)
	stw %r8, 288(%r11)
	lwz %r8, 20(%r9)
	stw %r8, 292(%r11)
	lwz %r8, 24(%r9)
	stw %r8, 296(%r11)
	lwz %r8, 28(%r9)
	stw %r8, 300(%r11)
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 0
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2377(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2381(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 129
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 257
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 1
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2377(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2381(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 129
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 257
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
214:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 400(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 404(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 408(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 412(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 416(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 420(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 424(%r11)
	lwz %r8, 124(%r11)
	stw %r8, 428(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 432(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 436(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 440(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 444(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 448(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 452(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 456(%r11)
	lwz %r8, 124(%r11)
	stw %r8, 460(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 400
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p384_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 215f
	li %r12, 0
	b 216f
215:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 0
	stb %r8, 2288(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 33
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 161
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 160
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	li %r12, 1
216:
	cmpldi %cr0, %r12, 0
	bne %cr0, 214b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
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
	addi %r1, %r1, 528
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	b 213f
212:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -528(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 256(%r11)
	std %r8, 264(%r11)
	std %r8, 272(%r11)
	std %r8, 280(%r11)
	std %r8, 288(%r11)
	std %r8, 296(%r11)
	std %r8, 304(%r11)
	std %r8, 312(%r11)
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 276(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 280(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 284(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 288(%r11)
	lwz %r8, 16(%r9)
	stw %r8, 292(%r11)
	lwz %r8, 20(%r9)
	stw %r8, 296(%r11)
	lwz %r8, 24(%r9)
	stw %r8, 300(%r11)
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2377(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 125
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 253
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 1
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2377(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 125
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 253
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
217:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 400(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 404(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 408(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 412(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 416(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 420(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 424(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 428(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 432(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 436(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 440(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 444(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 448(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 452(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 400
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p384_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 218f
	li %r12, 0
	b 219f
218:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 29
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 157
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 156
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r12, 1
219:
	cmpldi %cr0, %r12, 0
	bne %cr0, 217b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
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
	addi %r1, %r1, 528
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
213:
	b 211f
210:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 44
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -13115
	ori %r12, %r12, 10611
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 40
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, -4884
	ori %r12, %r12, 6506
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 36
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, 18608
	ori %r12, %r12, 42874
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 32
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, 22554
	ori %r12, %r12, 3506
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 28
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -3017
	ori %r12, %r12, 11743
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 24
	lwbrx %r7, %r9, %r8
	stw %r7, 116(%r11)
	lis %r12, -14493
	ori %r12, %r12, 19841
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 52(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 120(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 56(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 124(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 60(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 128(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 64(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 132(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 68(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 136(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 72(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
	lwbrx %r7, %r9, %r8
	stw %r7, 140(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
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
	li %r12, 204
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 200
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 196
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 192
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 188
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 184
	stwbrx %r7, %r11, %r12
	lwz %r7, 120(%r11)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 180
	stwbrx %r7, %r11, %r12
	lwz %r7, 124(%r11)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 176
	stwbrx %r7, %r11, %r12
	lwz %r7, 128(%r11)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 172
	stwbrx %r7, %r11, %r12
	lwz %r7, 132(%r11)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 168
	stwbrx %r7, %r11, %r12
	lwz %r7, 136(%r11)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 164
	stwbrx %r7, %r11, %r12
	lwz %r7, 140(%r11)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 160
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	lwz %r8, 144(%r11)
	stw %r8, 2304(%r9)
	lwz %r8, 148(%r11)
	stw %r8, 2308(%r9)
	lwz %r8, 152(%r11)
	stw %r8, 2312(%r9)
	lwz %r8, 156(%r11)
	stw %r8, 2316(%r9)
	li %r8, 0
	stb %r8, 2320(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2337(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2341(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2345(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2349(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2353(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2357(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2361(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2365(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2377(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2381(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2385(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2389(%r9)
	lwz %r8, 184(%r11)
	stw %r8, 2393(%r9)
	lwz %r8, 188(%r11)
	stw %r8, 2397(%r9)
	lwz %r8, 192(%r11)
	stw %r8, 2401(%r9)
	lwz %r8, 196(%r11)
	stw %r8, 2405(%r9)
	lwz %r8, 200(%r11)
	stw %r8, 2409(%r9)
	lwz %r8, 204(%r11)
	stw %r8, 2413(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 161
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 289
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 80(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 84(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 88(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 92(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 144(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 148(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 152(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 156(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	lwz %r8, 144(%r11)
	stw %r8, 2304(%r9)
	lwz %r8, 148(%r11)
	stw %r8, 2308(%r9)
	lwz %r8, 152(%r11)
	stw %r8, 2312(%r9)
	lwz %r8, 156(%r11)
	stw %r8, 2316(%r9)
	li %r8, 1
	stb %r8, 2320(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2337(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2341(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2345(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2349(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2353(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2357(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2361(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2365(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2377(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2381(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2385(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2389(%r9)
	lwz %r8, 184(%r11)
	stw %r8, 2393(%r9)
	lwz %r8, 188(%r11)
	stw %r8, 2397(%r9)
	lwz %r8, 192(%r11)
	stw %r8, 2401(%r9)
	lwz %r8, 196(%r11)
	stw %r8, 2405(%r9)
	lwz %r8, 200(%r11)
	stw %r8, 2409(%r9)
	lwz %r8, 204(%r11)
	stw %r8, 2413(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 161
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 289
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 80(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 84(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 88(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 92(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 144(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 148(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 152(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 156(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
220:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 144(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 148(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 152(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 156(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p384_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 221f
	li %r12, 0
	b 222f
221:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	lwz %r8, 144(%r11)
	stw %r8, 2304(%r9)
	lwz %r8, 148(%r11)
	stw %r8, 2308(%r9)
	lwz %r8, 152(%r11)
	stw %r8, 2312(%r9)
	lwz %r8, 156(%r11)
	stw %r8, 2316(%r9)
	li %r8, 0
	stb %r8, 2320(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 65
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 193
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 80(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 84(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 88(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 92(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	lwz %r8, 80(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1840(%r12)
	lwz %r8, 84(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1844(%r12)
	lwz %r8, 88(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1848(%r12)
	lwz %r8, 92(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 192
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	lwz %r8, 1968(%r12)
	stw %r8, 144(%r11)
	lwz %r8, 1972(%r12)
	stw %r8, 148(%r11)
	lwz %r8, 1976(%r12)
	stw %r8, 152(%r11)
	lwz %r8, 1980(%r12)
	stw %r8, 156(%r11)
	li %r12, 1
222:
	cmpldi %cr0, %r12, 0
	bne %cr0, 220b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	addi %r1, %r1, 256
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
211:
	b 29f
28:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -256(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r10, 1
	li %r8, 44
	lwbrx %r7, %r9, %r8
	stw %r7, 96(%r11)
	lis %r12, -13115
	ori %r12, %r12, 10611
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 32(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 40
	lwbrx %r7, %r9, %r8
	stw %r7, 100(%r11)
	lis %r12, -4884
	ori %r12, %r12, 6506
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 36(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 36
	lwbrx %r7, %r9, %r8
	stw %r7, 104(%r11)
	lis %r12, 18608
	ori %r12, %r12, 42874
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 40(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 32
	lwbrx %r7, %r9, %r8
	stw %r7, 108(%r11)
	lis %r12, 22554
	ori %r12, %r12, 3506
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 44(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 28
	lwbrx %r7, %r9, %r8
	stw %r7, 112(%r11)
	lis %r12, -3017
	ori %r12, %r12, 11743
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 48(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 24
	lwbrx %r7, %r9, %r8
	stw %r7, 116(%r11)
	lis %r12, -14493
	ori %r12, %r12, 19841
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 52(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 20
	lwbrx %r7, %r9, %r8
	stw %r7, 120(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 56(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 16
	lwbrx %r7, %r9, %r8
	stw %r7, 124(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 60(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 12
	lwbrx %r7, %r9, %r8
	stw %r7, 128(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 64(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 8
	lwbrx %r7, %r9, %r8
	stw %r7, 132(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 68(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 4
	lwbrx %r7, %r9, %r8
	stw %r7, 136(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
	and %r12, %r12, %r0
	add %r7, %r7, %r0
	subf %r7, %r12, %r7
	add %r7, %r7, %r10
	stw %r7, 72(%r11)
	rldicl %r10, %r7, 32, 32
	li %r8, 0
	lwbrx %r7, %r9, %r8
	stw %r7, 140(%r11)
	lis %r12, -1
	ori %r12, %r12, 65535
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
	li %r12, 204
	stwbrx %r7, %r11, %r12
	lwz %r7, 100(%r11)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 200
	stwbrx %r7, %r11, %r12
	lwz %r7, 104(%r11)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 196
	stwbrx %r7, %r11, %r12
	lwz %r7, 108(%r11)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 192
	stwbrx %r7, %r11, %r12
	lwz %r7, 112(%r11)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 188
	stwbrx %r7, %r11, %r12
	lwz %r7, 116(%r11)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 184
	stwbrx %r7, %r11, %r12
	lwz %r7, 120(%r11)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 180
	stwbrx %r7, %r11, %r12
	lwz %r7, 124(%r11)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 176
	stwbrx %r7, %r11, %r12
	lwz %r7, 128(%r11)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 172
	stwbrx %r7, %r11, %r12
	lwz %r7, 132(%r11)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 168
	stwbrx %r7, %r11, %r12
	lwz %r7, 136(%r11)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 164
	stwbrx %r7, %r11, %r12
	lwz %r7, 140(%r11)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r7
	and %r8, %r8, %r10
	xor %r7, %r7, %r8
	li %r12, 160
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	li %r8, 0
	stb %r8, 2304(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2337(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2341(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2345(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2349(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 184(%r11)
	stw %r8, 2377(%r9)
	lwz %r8, 188(%r11)
	stw %r8, 2381(%r9)
	lwz %r8, 192(%r11)
	stw %r8, 2385(%r9)
	lwz %r8, 196(%r11)
	stw %r8, 2389(%r9)
	lwz %r8, 200(%r11)
	stw %r8, 2393(%r9)
	lwz %r8, 204(%r11)
	stw %r8, 2397(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 145
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 273
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	li %r8, 1
	stb %r8, 2304(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2337(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2341(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2345(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2349(%r9)
	lwz %r8, 160(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 164(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 168(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 172(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 176(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 180(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 184(%r11)
	stw %r8, 2377(%r9)
	lwz %r8, 188(%r11)
	stw %r8, 2381(%r9)
	lwz %r8, 192(%r11)
	stw %r8, 2385(%r9)
	lwz %r8, 196(%r11)
	stw %r8, 2389(%r9)
	lwz %r8, 200(%r11)
	stw %r8, 2393(%r9)
	lwz %r8, 204(%r11)
	stw %r8, 2397(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 145
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 273
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
223:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	ld %r5, 224(%r11)
	addi %r6, %r1, 96
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p384_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 224f
	li %r12, 0
	b 225f
224:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	lwz %r8, 128(%r11)
	stw %r8, 2288(%r9)
	lwz %r8, 132(%r11)
	stw %r8, 2292(%r9)
	lwz %r8, 136(%r11)
	stw %r8, 2296(%r9)
	lwz %r8, 140(%r11)
	stw %r8, 2300(%r9)
	li %r8, 0
	stb %r8, 2304(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r12, 2256
	li %r6, 49
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 177
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 64(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 68(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 72(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 76(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	lwz %r8, 64(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1824(%r12)
	lwz %r8, 68(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1828(%r12)
	lwz %r8, 72(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1832(%r12)
	lwz %r8, 76(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	stw %r9, 1856(%r12)
	stw %r9, 1860(%r12)
	stw %r9, 1864(%r12)
	stw %r9, 1868(%r12)
	stw %r9, 1872(%r12)
	stw %r9, 1876(%r12)
	stw %r9, 1880(%r12)
	stw %r9, 1884(%r12)
	stw %r9, 1888(%r12)
	stw %r9, 1892(%r12)
	stw %r9, 1896(%r12)
	stw %r9, 1900(%r12)
	stw %r9, 1904(%r12)
	stw %r9, 1908(%r12)
	stw %r9, 1912(%r12)
	stw %r9, 1916(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 128
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 128
	addi %r5, %r1, 96
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 128
	addi %r5, %r12, 1920
	li %r6, 48
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 176
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	lwz %r8, 1952(%r12)
	stw %r8, 128(%r11)
	lwz %r8, 1956(%r12)
	stw %r8, 132(%r11)
	lwz %r8, 1960(%r12)
	stw %r8, 136(%r11)
	lwz %r8, 1964(%r12)
	stw %r8, 140(%r11)
	li %r12, 1
225:
	cmpldi %cr0, %r12, 0
	bne %cr0, 223b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
	addi %r1, %r1, 256
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
29:
	b 27f
26:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -528(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 256(%r11)
	std %r8, 264(%r11)
	std %r8, 272(%r11)
	std %r8, 280(%r11)
	std %r8, 288(%r11)
	std %r8, 296(%r11)
	std %r8, 304(%r11)
	std %r8, 312(%r11)
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 272(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 276(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 280(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 284(%r11)
	lwz %r8, 16(%r9)
	stw %r8, 288(%r11)
	lwz %r8, 20(%r9)
	stw %r8, 292(%r11)
	lwz %r8, 24(%r9)
	stw %r8, 296(%r11)
	lwz %r8, 28(%r9)
	stw %r8, 300(%r11)
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 0
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2377(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2381(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 129
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 193
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 1
	stb %r8, 2288(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2333(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2377(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2381(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 129
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 193
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
226:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 400(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 404(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 408(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 412(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 416(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 420(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 424(%r11)
	lwz %r8, 124(%r11)
	stw %r8, 428(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 432(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 436(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 440(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 444(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 448(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 452(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 456(%r11)
	lwz %r8, 124(%r11)
	stw %r8, 460(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 400
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p384_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 227f
	li %r12, 0
	b 228f
227:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	lwz %r8, 124(%r11)
	stw %r8, 2284(%r9)
	li %r8, 0
	stb %r8, 2288(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 33
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 97
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 60(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	lwz %r8, 60(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 32
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 96
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	lwz %r8, 1948(%r12)
	stw %r8, 124(%r11)
	li %r12, 1
228:
	cmpldi %cr0, %r12, 0
	bne %cr0, 226b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
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
	addi %r1, %r1, 528
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
27:
	b 25f
24:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -528(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 256(%r11)
	std %r8, 264(%r11)
	std %r8, 272(%r11)
	std %r8, 280(%r11)
	std %r8, 288(%r11)
	std %r8, 296(%r11)
	std %r8, 304(%r11)
	std %r8, 312(%r11)
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 276(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 280(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 284(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 288(%r11)
	lwz %r8, 16(%r9)
	stw %r8, 292(%r11)
	lwz %r8, 20(%r9)
	stw %r8, 296(%r11)
	lwz %r8, 24(%r9)
	stw %r8, 300(%r11)
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2377(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 125
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 189
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 1
	stb %r8, 2284(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2325(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2329(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2369(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2373(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2377(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 125
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 189
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
229:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 400(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 404(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 408(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 412(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 416(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 420(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 424(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 428(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 432(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 436(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 440(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 444(%r11)
	lwz %r8, 116(%r11)
	stw %r8, 448(%r11)
	lwz %r8, 120(%r11)
	stw %r8, 452(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 400
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p384_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 230f
	li %r12, 0
	b 231f
230:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	lwz %r8, 116(%r11)
	stw %r8, 2276(%r9)
	lwz %r8, 120(%r11)
	stw %r8, 2280(%r9)
	li %r8, 0
	stb %r8, 2284(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 29
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 93
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 52(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 56(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	lwz %r8, 52(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1812(%r12)
	lwz %r8, 56(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 28
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 92
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	lwz %r8, 1940(%r12)
	stw %r8, 116(%r11)
	lwz %r8, 1944(%r12)
	stw %r8, 120(%r11)
	li %r12, 1
231:
	cmpldi %cr0, %r12, 0
	bne %cr0, 229b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
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
	addi %r1, %r1, 528
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
25:
	b 23f
22:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -528(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 256(%r11)
	std %r8, 264(%r11)
	std %r8, 272(%r11)
	std %r8, 280(%r11)
	std %r8, 288(%r11)
	std %r8, 296(%r11)
	std %r8, 304(%r11)
	std %r8, 312(%r11)
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 284(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 288(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 292(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 296(%r11)
	lwz %r8, 16(%r9)
	stw %r8, 300(%r11)
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	li %r8, 0
	stb %r8, 2276(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2369(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 117
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 181
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	li %r8, 1
	stb %r8, 2276(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2321(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2365(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2369(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 117
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 181
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
232:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 400(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 404(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 408(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 412(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 416(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 420(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 424(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 428(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 432(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 436(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 440(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 444(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 448(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 452(%r11)
	lwz %r8, 112(%r11)
	stw %r8, 456(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 400
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p384_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 233f
	li %r12, 0
	b 234f
233:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	lwz %r8, 112(%r11)
	stw %r8, 2272(%r9)
	li %r8, 0
	stb %r8, 2276(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 21
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 85
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 48(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	lwz %r8, 48(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 20
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 84
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	lwz %r8, 1936(%r12)
	stw %r8, 112(%r11)
	li %r12, 1
234:
	cmpldi %cr0, %r12, 0
	bne %cr0, 232b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
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
	addi %r1, %r1, 528
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
23:
	b 21f
20:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -528(%r1)
	addi %r11, %r1, 0
	std %r3, 240(%r11)
	std %r4, 232(%r11)
	std %r5, 224(%r11)
	std %r6, 216(%r11)
	std %r8, 248(%r11)
	addi %r11, %r1, 0
	ld %r9, 224(%r11)
	li %r8, 0
	std %r8, 256(%r11)
	std %r8, 264(%r11)
	std %r8, 272(%r11)
	std %r8, 280(%r11)
	std %r8, 288(%r11)
	std %r8, 296(%r11)
	std %r8, 304(%r11)
	std %r8, 312(%r11)
	std %r8, 320(%r11)
	lwz %r8, 0(%r9)
	stw %r8, 288(%r11)
	lwz %r8, 4(%r9)
	stw %r8, 292(%r11)
	lwz %r8, 8(%r9)
	stw %r8, 296(%r11)
	lwz %r8, 12(%r9)
	stw %r8, 300(%r11)
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
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	li %r8, 0
	stb %r8, 2272(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2273(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2365(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 113
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 177
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	li %r8, 1
	stb %r8, 2272(%r9)
	lwz %r8, 0(%r10)
	stw %r8, 2273(%r9)
	lwz %r8, 4(%r10)
	stw %r8, 2277(%r9)
	lwz %r8, 8(%r10)
	stw %r8, 2281(%r9)
	lwz %r8, 12(%r10)
	stw %r8, 2285(%r9)
	lwz %r8, 16(%r10)
	stw %r8, 2289(%r9)
	lwz %r8, 20(%r10)
	stw %r8, 2293(%r9)
	lwz %r8, 24(%r10)
	stw %r8, 2297(%r9)
	lwz %r8, 28(%r10)
	stw %r8, 2301(%r9)
	lwz %r8, 32(%r10)
	stw %r8, 2305(%r9)
	lwz %r8, 36(%r10)
	stw %r8, 2309(%r9)
	lwz %r8, 40(%r10)
	stw %r8, 2313(%r9)
	lwz %r8, 44(%r10)
	stw %r8, 2317(%r9)
	lwz %r8, 256(%r11)
	stw %r8, 2321(%r9)
	lwz %r8, 260(%r11)
	stw %r8, 2325(%r9)
	lwz %r8, 264(%r11)
	stw %r8, 2329(%r9)
	lwz %r8, 268(%r11)
	stw %r8, 2333(%r9)
	lwz %r8, 272(%r11)
	stw %r8, 2337(%r9)
	lwz %r8, 276(%r11)
	stw %r8, 2341(%r9)
	lwz %r8, 280(%r11)
	stw %r8, 2345(%r9)
	lwz %r8, 284(%r11)
	stw %r8, 2349(%r9)
	lwz %r8, 288(%r11)
	stw %r8, 2353(%r9)
	lwz %r8, 292(%r11)
	stw %r8, 2357(%r9)
	lwz %r8, 296(%r11)
	stw %r8, 2361(%r9)
	lwz %r8, 300(%r11)
	stw %r8, 2365(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 113
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 177
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	li %r9, 8
	addi %r11, %r1, 0
	std %r9, 208(%r11)
235:
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 400(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 404(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 408(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 412(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 416(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 420(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 424(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 428(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	addi %r11, %r1, 0
	lwz %r8, 96(%r11)
	stw %r8, 432(%r11)
	lwz %r8, 100(%r11)
	stw %r8, 436(%r11)
	lwz %r8, 104(%r11)
	stw %r8, 440(%r11)
	lwz %r8, 108(%r11)
	stw %r8, 444(%r11)
	addi %r11, %r1, 0
	ld %r3, 240(%r11)
	ld %r4, 232(%r11)
	addi %r5, %r1, 256
	addi %r6, %r1, 400
	ld %r7, 216(%r11)
	bl {vg_ecdsa_p384_sign_k}
	addi %r11, %r1, 0
	ld %r9, 208(%r11)
	addi %r9, %r9, -1
	std %r9, 208(%r11)
	li %r10, 1
	and %r8, %r3, %r10
	subf %r8, %r10, %r8
	and %r12, %r8, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 236f
	li %r12, 0
	b 237f
236:
	addi %r11, %r1, 0
	ld %r9, 216(%r11)
	ld %r10, 232(%r11)
	lwz %r8, 96(%r11)
	stw %r8, 2256(%r9)
	lwz %r8, 100(%r11)
	stw %r8, 2260(%r9)
	lwz %r8, 104(%r11)
	stw %r8, 2264(%r9)
	lwz %r8, 108(%r11)
	stw %r8, 2268(%r9)
	li %r8, 0
	stb %r8, 2272(%r9)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r12, 2256
	li %r6, 17
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 81
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 32(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 36(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 40(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 44(%r11)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 13878
	ori %r9, %r9, 13878
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lis %r9, 23644
	ori %r9, %r9, 23644
	lwz %r8, 32(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1792(%r12)
	lwz %r8, 36(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1796(%r12)
	lwz %r8, 40(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1800(%r12)
	lwz %r8, 44(%r11)
	xor %r8, %r8, %r9
	stw %r8, 1804(%r12)
	stw %r9, 1808(%r12)
	stw %r9, 1812(%r12)
	stw %r9, 1816(%r12)
	stw %r9, 1820(%r12)
	stw %r9, 1824(%r12)
	stw %r9, 1828(%r12)
	stw %r9, 1832(%r12)
	stw %r9, 1836(%r12)
	stw %r9, 1840(%r12)
	stw %r9, 1844(%r12)
	stw %r9, 1848(%r12)
	stw %r9, 1852(%r12)
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 0
	addi %r5, %r12, 1792
	li %r6, 64
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 64
	addi %r5, %r1, 96
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 0
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 64
	addi %r5, %r12, 1920
	li %r6, 16
	addi %r7, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	addi %r3, %r12, 192
	li %r4, 80
	addi %r5, %r12, 1920
	addi %r6, %r12, 384
	addi %r12, %r1, 0
	ld %r12, 248(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r11, %r1, 0
	ld %r12, 216(%r11)
	lwz %r8, 1920(%r12)
	stw %r8, 96(%r11)
	lwz %r8, 1924(%r12)
	stw %r8, 100(%r11)
	lwz %r8, 1928(%r12)
	stw %r8, 104(%r11)
	lwz %r8, 1932(%r12)
	stw %r8, 108(%r11)
	li %r12, 1
237:
	cmpldi %cr0, %r12, 0
	bne %cr0, 235b
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
	std %r12, 160(%r11)
	std %r12, 168(%r11)
	std %r12, 176(%r11)
	std %r12, 184(%r11)
	std %r12, 192(%r11)
	std %r12, 200(%r11)
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
	addi %r1, %r1, 528
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
21:
	blr
