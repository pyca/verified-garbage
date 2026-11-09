// The functions of `src/internal/vg_ecdsa_brainpoolp512r1_sign_k.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_sign_k:
	std %r14, 0(%r7)
	std %r31, 8(%r7)
	mflr %r0
	std %r0, 16(%r7)
	or %r14, %r3, %r3
	or %r3, %r7, %r7
	li %r9, 56
	ldbrx %r8, %r6, %r9
	std %r8, 2048(%r3)
	li %r9, 48
	ldbrx %r8, %r6, %r9
	std %r8, 2056(%r3)
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 2064(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 2072(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 2080(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 2088(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 2096(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 2104(%r3)
	li %r9, 56
	ldbrx %r8, %r4, %r9
	std %r8, 2112(%r3)
	li %r9, 48
	ldbrx %r8, %r4, %r9
	std %r8, 2120(%r3)
	li %r9, 40
	ldbrx %r8, %r4, %r9
	std %r8, 2128(%r3)
	li %r9, 32
	ldbrx %r8, %r4, %r9
	std %r8, 2136(%r3)
	li %r9, 24
	ldbrx %r8, %r4, %r9
	std %r8, 2144(%r3)
	li %r9, 16
	ldbrx %r8, %r4, %r9
	std %r8, 2152(%r3)
	li %r9, 8
	ldbrx %r8, %r4, %r9
	std %r8, 2160(%r3)
	li %r9, 0
	ldbrx %r8, %r4, %r9
	std %r8, 2168(%r3)
	li %r9, 56
	ldbrx %r8, %r5, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r5, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r5, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r5, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r5, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r5, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r5, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r5, %r9
	std %r8, 2232(%r3)
	lis %r11, 22586
	ori %r11, %r11, 18675
	stw %r11, 64(%r3)
	lis %r11, 10410
	ori %r11, %r11, 24662
	stw %r11, 68(%r3)
	lis %r11, 11650
	ori %r11, %r11, 50821
	stw %r11, 72(%r3)
	lis %r11, 10369
	ori %r11, %r11, 65327
	stw %r11, 76(%r3)
	lis %r11, -6493
	ori %r11, %r11, 32998
	stw %r11, 80(%r3)
	lis %r11, -20787
	ori %r11, %r11, 41258
	stw %r11, 84(%r3)
	lis %r11, -25658
	ori %r11, %r11, 26690
	stw %r11, 88(%r3)
	lis %r11, 32077
	ori %r11, %r11, 39680
	stw %r11, 92(%r3)
	lis %r11, 28723
	ori %r11, %r11, 2161
	stw %r11, 96(%r3)
	lis %r11, -10653
	ori %r11, %r11, 40138
	stw %r11, 100(%r3)
	lis %r11, -19511
	ori %r11, %r11, 53774
	stw %r11, 104(%r3)
	lis %r11, -13520
	ori %r11, %r11, 36275
	stw %r11, 108(%r3)
	lis %r11, 13257
	ori %r11, %r11, 64519
	stw %r11, 112(%r3)
	lis %r11, 16340
	ori %r11, %r11, 59054
	stw %r11, 116(%r3)
	lis %r11, -9239
	ori %r11, %r11, 50315
	stw %r11, 120(%r3)
	lis %r11, -21795
	ori %r11, %r11, 40376
	stw %r11, 124(%r3)
	lis %r11, -25431
	ori %r11, %r11, 105
	stw %r11, 128(%r3)
	lis %r11, -19065
	ori %r11, %r11, 38530
	stw %r11, 132(%r3)
	lis %r11, 2141
	ori %r11, %r11, 56029
	stw %r11, 136(%r3)
	lis %r11, 7601
	ori %r11, %r11, 54145
	stw %r11, 140(%r3)
	lis %r11, 32684
	ori %r11, %r11, 4167
	stw %r11, 144(%r3)
	lis %r11, 16774
	ori %r11, %r11, 24857
	stw %r11, 148(%r3)
	lis %r11, 19625
	ori %r11, %r11, 9753
	stw %r11, 152(%r3)
	lis %r11, 21822
	ori %r11, %r11, 23617
	stw %r11, 156(%r3)
	lis %r11, 28723
	ori %r11, %r11, 2160
	stw %r11, 160(%r3)
	lis %r11, -10653
	ori %r11, %r11, 40138
	stw %r11, 164(%r3)
	lis %r11, -19511
	ori %r11, %r11, 53774
	stw %r11, 168(%r3)
	lis %r11, -13520
	ori %r11, %r11, 36275
	stw %r11, 172(%r3)
	lis %r11, 13257
	ori %r11, %r11, 64519
	stw %r11, 176(%r3)
	lis %r11, 16340
	ori %r11, %r11, 59054
	stw %r11, 180(%r3)
	lis %r11, -9239
	ori %r11, %r11, 50315
	stw %r11, 184(%r3)
	lis %r11, -21795
	ori %r11, %r11, 40376
	stw %r11, 188(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
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
	lis %r11, 0
	ori %r11, %r11, 0
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
	lis %r11, -22587
	ori %r11, %r11, 46861
	stw %r11, 384(%r3)
	lis %r11, -10411
	ori %r11, %r11, 40873
	stw %r11, 388(%r3)
	lis %r11, -11651
	ori %r11, %r11, 14714
	stw %r11, 392(%r3)
	lis %r11, -10370
	ori %r11, %r11, 208
	stw %r11, 396(%r3)
	lis %r11, 6492
	ori %r11, %r11, 32537
	stw %r11, 400(%r3)
	lis %r11, 20786
	ori %r11, %r11, 24277
	stw %r11, 404(%r3)
	lis %r11, 25657
	ori %r11, %r11, 38845
	stw %r11, 408(%r3)
	lis %r11, -32078
	ori %r11, %r11, 25855
	stw %r11, 412(%r3)
	lis %r11, -28724
	ori %r11, %r11, 63374
	stw %r11, 416(%r3)
	lis %r11, 10652
	ori %r11, %r11, 25397
	stw %r11, 420(%r3)
	lis %r11, 19510
	ori %r11, %r11, 11761
	stw %r11, 424(%r3)
	lis %r11, 13519
	ori %r11, %r11, 29260
	stw %r11, 428(%r3)
	lis %r11, -13258
	ori %r11, %r11, 1016
	stw %r11, 432(%r3)
	lis %r11, -16341
	ori %r11, %r11, 6481
	stw %r11, 436(%r3)
	lis %r11, 9238
	ori %r11, %r11, 15220
	stw %r11, 440(%r3)
	lis %r11, 21794
	ori %r11, %r11, 25159
	stw %r11, 444(%r3)
	lis %r11, -5616
	ori %r11, %r11, 50246
	stw %r11, 448(%r3)
	lis %r11, -9697
	ori %r11, %r11, 35380
	stw %r11, 452(%r3)
	lis %r11, -20569
	ori %r11, %r11, 53891
	stw %r11, 456(%r3)
	lis %r11, 5348
	ori %r11, %r11, 38269
	stw %r11, 460(%r3)
	lis %r11, 18037
	ori %r11, %r11, 48043
	stw %r11, 464(%r3)
	lis %r11, 16560
	ori %r11, %r11, 19314
	stw %r11, 468(%r3)
	lis %r11, -24978
	ori %r11, %r11, 34815
	stw %r11, 472(%r3)
	lis %r11, -12401
	ori %r11, %r11, 273
	stw %r11, 476(%r3)
	lis %r11, 16256
	ori %r11, %r11, 53703
	stw %r11, 480(%r3)
	lis %r11, -23060
	ori %r11, %r11, 12488
	stw %r11, 484(%r3)
	lis %r11, -3042
	ori %r11, %r11, 34680
	stw %r11, 488(%r3)
	lis %r11, 6189
	ori %r11, %r11, 3929
	stw %r11, 492(%r3)
	lis %r11, -7472
	ori %r11, %r11, 34060
	stw %r11, 496(%r3)
	lis %r11, -18373
	ori %r11, %r11, 34042
	stw %r11, 500(%r3)
	lis %r11, 8829
	ori %r11, %r11, 10883
	stw %r11, 504(%r3)
	lis %r11, 24260
	ori %r11, %r11, 61831
	stw %r11, 508(%r3)
	lis %r11, 2689
	ori %r11, %r11, 13737
	stw %r11, 512(%r3)
	lis %r11, -14127
	ori %r11, %r11, 10860
	stw %r11, 516(%r3)
	lis %r11, -31960
	ori %r11, %r11, 18455
	stw %r11, 520(%r3)
	lis %r11, -9904
	ori %r11, %r11, 11304
	stw %r11, 524(%r3)
	lis %r11, -24079
	ori %r11, %r11, 60695
	stw %r11, 528(%r3)
	lis %r11, -2699
	ori %r11, %r11, 19415
	stw %r11, 532(%r3)
	lis %r11, 11680
	ori %r11, %r11, 53701
	stw %r11, 536(%r3)
	lis %r11, -10132
	ori %r11, %r11, 63417
	stw %r11, 540(%r3)
	lis %r11, -30157
	ori %r11, %r11, 25641
	stw %r11, 544(%r3)
	lis %r11, -3780
	ori %r11, %r11, 34913
	stw %r11, 548(%r3)
	lis %r11, -27779
	ori %r11, %r11, 46665
	stw %r11, 552(%r3)
	lis %r11, -26530
	ori %r11, %r11, 31057
	stw %r11, 556(%r3)
	lis %r11, -4265
	ori %r11, %r11, 992
	stw %r11, 560(%r3)
	lis %r11, -4972
	ori %r11, %r11, 20800
	stw %r11, 564(%r3)
	lis %r11, -1679
	ori %r11, %r11, 59242
	stw %r11, 568(%r3)
	lis %r11, -27646
	ori %r11, %r11, 25955
	stw %r11, 572(%r3)
	lis %r11, 20833
	ori %r11, %r11, 55763
	stw %r11, 576(%r3)
	lis %r11, -15154
	ori %r11, %r11, 38409
	stw %r11, 580(%r3)
	lis %r11, 10028
	ori %r11, %r11, 676
	stw %r11, 584(%r3)
	lis %r11, 26686
	ori %r11, %r11, 19812
	stw %r11, 588(%r3)
	lis %r11, 28149
	ori %r11, %r11, 24207
	stw %r11, 592(%r3)
	lis %r11, 13483
	ori %r11, %r11, 1044
	stw %r11, 596(%r3)
	lis %r11, 5312
	ori %r11, %r11, 8136
	stw %r11, 600(%r3)
	lis %r11, -31408
	ori %r11, %r11, 21397
	stw %r11, 604(%r3)
	lis %r11, -28580
	ori %r11, %r11, 34615
	stw %r11, 608(%r3)
	lis %r11, 9267
	ori %r11, %r11, 55151
	stw %r11, 612(%r3)
	lis %r11, -3219
	ori %r11, %r11, 15607
	stw %r11, 616(%r3)
	lis %r11, -19786
	ori %r11, %r11, 59959
	stw %r11, 620(%r3)
	lis %r11, 109
	ori %r11, %r11, 17779
	stw %r11, 624(%r3)
	lis %r11, -30948
	ori %r11, %r11, 46538
	stw %r11, 628(%r3)
	lis %r11, 2452
	ori %r11, %r11, 59777
	stw %r11, 632(%r3)
	lis %r11, 23083
	ori %r11, %r11, 41292
	stw %r11, 636(%r3)
	lis %r11, 9476
	ori %r11, %r11, 10861
	stw %r11, 640(%r3)
	lis %r11, 12176
	ori %r11, %r11, 26153
	stw %r11, 644(%r3)
	lis %r11, 18242
	ori %r11, %r11, 62245
	stw %r11, 648(%r3)
	lis %r11, 29976
	ori %r11, %r11, 57199
	stw %r11, 652(%r3)
	lis %r11, 19589
	ori %r11, %r11, 38032
	stw %r11, 656(%r3)
	lis %r11, -16508
	ori %r11, %r11, 21843
	stw %r11, 660(%r3)
	lis %r11, 22926
	ori %r11, %r11, 52286
	stw %r11, 664(%r3)
	lis %r11, 13838
	ori %r11, %r11, 51061
	stw %r11, 668(%r3)
	lis %r11, -28698
	ori %r11, %r11, 12252
	stw %r11, 672(%r3)
	lis %r11, 31767
	ori %r11, %r11, 2952
	stw %r11, 676(%r3)
	lis %r11, -12899
	ori %r11, %r11, 16268
	stw %r11, 680(%r3)
	lis %r11, 22621
	ori %r11, %r11, 11127
	stw %r11, 684(%r3)
	lis %r11, -30961
	ori %r11, %r11, 16283
	stw %r11, 688(%r3)
	lis %r11, -26018
	ori %r11, %r11, 55258
	stw %r11, 692(%r3)
	lis %r11, 10955
	ori %r11, %r11, 29313
	stw %r11, 696(%r3)
	lis %r11, -29616
	ori %r11, %r11, 51665
	stw %r11, 700(%r3)
	lis %r11, -12888
	ori %r11, %r11, 5745
	stw %r11, 704(%r3)
	lis %r11, -11613
	ori %r11, %r11, 26654
	stw %r11, 708(%r3)
	lis %r11, -27352
	ori %r11, %r11, 15837
	stw %r11, 712(%r3)
	lis %r11, 2182
	ori %r11, %r11, 46936
	stw %r11, 716(%r3)
	lis %r11, 13239
	ori %r11, %r11, 25215
	stw %r11, 720(%r3)
	lis %r11, 16070
	ori %r11, %r11, 19408
	stw %r11, 724(%r3)
	lis %r11, 12034
	ori %r11, %r11, 2024
	stw %r11, 728(%r3)
	lis %r11, -22798
	ori %r11, %r11, 12487
	stw %r11, 732(%r3)
	lis %r11, 15225
	ori %r11, %r11, 3555
	stw %r11, 736(%r3)
	lis %r11, -10247
	ori %r11, %r11, 52262
	stw %r11, 740(%r3)
	lis %r11, 12054
	ori %r11, %r11, 48095
	stw %r11, 744(%r3)
	lis %r11, 29244
	ori %r11, %r11, 14242
	stw %r11, 748(%r3)
	lis %r11, 6475
	ori %r11, %r11, 11862
	stw %r11, 752(%r3)
	lis %r11, -27169
	ori %r11, %r11, 6988
	stw %r11, 756(%r3)
	lis %r11, 29060
	ori %r11, %r11, 1968
	stw %r11, 760(%r3)
	lis %r11, -22636
	ori %r11, %r11, 22634
	stw %r11, 764(%r3)
	lis %r11, 25430
	ori %r11, %r11, 65431
	stw %r11, 768(%r3)
	lis %r11, 19064
	ori %r11, %r11, 27005
	stw %r11, 772(%r3)
	lis %r11, -2142
	ori %r11, %r11, 9506
	stw %r11, 776(%r3)
	lis %r11, -7602
	ori %r11, %r11, 11390
	stw %r11, 780(%r3)
	lis %r11, -32685
	ori %r11, %r11, 61368
	stw %r11, 784(%r3)
	lis %r11, -16775
	ori %r11, %r11, 40678
	stw %r11, 788(%r3)
	lis %r11, -19626
	ori %r11, %r11, 55782
	stw %r11, 792(%r3)
	lis %r11, -21823
	ori %r11, %r11, 41918
	stw %r11, 796(%r3)
	lis %r11, -28724
	ori %r11, %r11, 63375
	stw %r11, 800(%r3)
	lis %r11, 10652
	ori %r11, %r11, 25397
	stw %r11, 804(%r3)
	lis %r11, 19510
	ori %r11, %r11, 11761
	stw %r11, 808(%r3)
	lis %r11, 13519
	ori %r11, %r11, 29260
	stw %r11, 812(%r3)
	lis %r11, -13258
	ori %r11, %r11, 1016
	stw %r11, 816(%r3)
	lis %r11, -16341
	ori %r11, %r11, 6481
	stw %r11, 820(%r3)
	lis %r11, 9238
	ori %r11, %r11, 15220
	stw %r11, 824(%r3)
	lis %r11, 21794
	ori %r11, %r11, 25159
	stw %r11, 828(%r3)
	lis %r11, 22586
	ori %r11, %r11, 18673
	stw %r11, 832(%r3)
	lis %r11, 10410
	ori %r11, %r11, 24662
	stw %r11, 836(%r3)
	lis %r11, 11650
	ori %r11, %r11, 50821
	stw %r11, 840(%r3)
	lis %r11, 10369
	ori %r11, %r11, 65327
	stw %r11, 844(%r3)
	lis %r11, -6493
	ori %r11, %r11, 32998
	stw %r11, 848(%r3)
	lis %r11, -20787
	ori %r11, %r11, 41258
	stw %r11, 852(%r3)
	lis %r11, -25658
	ori %r11, %r11, 26690
	stw %r11, 856(%r3)
	lis %r11, 32077
	ori %r11, %r11, 39680
	stw %r11, 860(%r3)
	lis %r11, 28723
	ori %r11, %r11, 2161
	stw %r11, 864(%r3)
	lis %r11, -10653
	ori %r11, %r11, 40138
	stw %r11, 868(%r3)
	lis %r11, -19511
	ori %r11, %r11, 53774
	stw %r11, 872(%r3)
	lis %r11, -13520
	ori %r11, %r11, 36275
	stw %r11, 876(%r3)
	lis %r11, 13257
	ori %r11, %r11, 64519
	stw %r11, 880(%r3)
	lis %r11, 16340
	ori %r11, %r11, 59054
	stw %r11, 884(%r3)
	lis %r11, -9239
	ori %r11, %r11, 50315
	stw %r11, 888(%r3)
	lis %r11, -21795
	ori %r11, %r11, 40376
	stw %r11, 892(%r3)
	lis %r11, -25431
	ori %r11, %r11, 103
	stw %r11, 896(%r3)
	lis %r11, -19065
	ori %r11, %r11, 38530
	stw %r11, 900(%r3)
	lis %r11, 2141
	ori %r11, %r11, 56029
	stw %r11, 904(%r3)
	lis %r11, 7601
	ori %r11, %r11, 54145
	stw %r11, 908(%r3)
	lis %r11, 32684
	ori %r11, %r11, 4167
	stw %r11, 912(%r3)
	lis %r11, 16774
	ori %r11, %r11, 24857
	stw %r11, 916(%r3)
	lis %r11, 19625
	ori %r11, %r11, 9753
	stw %r11, 920(%r3)
	lis %r11, 21822
	ori %r11, %r11, 23617
	stw %r11, 924(%r3)
	lis %r11, 28723
	ori %r11, %r11, 2160
	stw %r11, 928(%r3)
	lis %r11, -10653
	ori %r11, %r11, 40138
	stw %r11, 932(%r3)
	lis %r11, -19511
	ori %r11, %r11, 53774
	stw %r11, 936(%r3)
	lis %r11, -13520
	ori %r11, %r11, 36275
	stw %r11, 940(%r3)
	lis %r11, 13257
	ori %r11, %r11, 64519
	stw %r11, 944(%r3)
	lis %r11, 16340
	ori %r11, %r11, 59054
	stw %r11, 948(%r3)
	lis %r11, -9239
	ori %r11, %r11, 50315
	stw %r11, 952(%r3)
	lis %r11, -21795
	ori %r11, %r11, 40376
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
	ori %r11, %r11, 0
	stw %r11, 992(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 996(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1000(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1004(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1008(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1012(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1016(%r3)
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1020(%r3)
	lis %r11, -22587
	ori %r11, %r11, 46861
	stw %r11, 1024(%r3)
	lis %r11, -10411
	ori %r11, %r11, 40873
	stw %r11, 1028(%r3)
	lis %r11, -11651
	ori %r11, %r11, 14714
	stw %r11, 1032(%r3)
	lis %r11, -10370
	ori %r11, %r11, 208
	stw %r11, 1036(%r3)
	lis %r11, 6492
	ori %r11, %r11, 32537
	stw %r11, 1040(%r3)
	lis %r11, 20786
	ori %r11, %r11, 24277
	stw %r11, 1044(%r3)
	lis %r11, 25657
	ori %r11, %r11, 38845
	stw %r11, 1048(%r3)
	lis %r11, -32078
	ori %r11, %r11, 25855
	stw %r11, 1052(%r3)
	lis %r11, -28724
	ori %r11, %r11, 63374
	stw %r11, 1056(%r3)
	lis %r11, 10652
	ori %r11, %r11, 25397
	stw %r11, 1060(%r3)
	lis %r11, 19510
	ori %r11, %r11, 11761
	stw %r11, 1064(%r3)
	lis %r11, 13519
	ori %r11, %r11, 29260
	stw %r11, 1068(%r3)
	lis %r11, -13258
	ori %r11, %r11, 1016
	stw %r11, 1072(%r3)
	lis %r11, -16341
	ori %r11, %r11, 6481
	stw %r11, 1076(%r3)
	lis %r11, 9238
	ori %r11, %r11, 15220
	stw %r11, 1080(%r3)
	lis %r11, 21794
	ori %r11, %r11, 25159
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
	lis %r11, 0
	ori %r11, %r11, 0
	stw %r11, 1148(%r3)
	li %r4, 0
	addi %r4, %r4, -1
	std %r4, 2880(%r3)
	li %r31, 64
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 2048(%r4)
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
	li %r31, 64
21:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 832(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 4608(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 4609(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 4610(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 4611(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 4612(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 4613(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 4614(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 4615(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r31, 64
22:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 896(%r4)
	rldicr %r5, %r31, 3, 60
	add %r5, %r3, %r5
	li %r7, 1
	and %r6, %r4, %r7
	stb %r6, 5120(%r5)
	rldicl %r6, %r4, 63, 1
	and %r6, %r6, %r7
	stb %r6, 5121(%r5)
	rldicl %r6, %r4, 62, 2
	and %r6, %r6, %r7
	stb %r6, 5122(%r5)
	rldicl %r6, %r4, 61, 3
	and %r6, %r6, %r7
	stb %r6, 5123(%r5)
	rldicl %r6, %r4, 60, 4
	and %r6, %r6, %r7
	stb %r6, 5124(%r5)
	rldicl %r6, %r4, 59, 5
	and %r6, %r6, %r7
	stb %r6, 5125(%r5)
	rldicl %r6, %r4, 58, 6
	and %r6, %r6, %r7
	stb %r6, 5126(%r5)
	rldicl %r6, %r4, 57, 7
	and %r6, %r6, %r7
	stb %r6, 5127(%r5)
	cmpldi %cr0, %r31, 0
	bne %cr0, 22b
	li %r31, 512
23:
	addi %r31, %r31, -1
	li %r4, 1536
	li %r5, 960
	li %r6, 960
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1024
	li %r6, 1024
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1664
	li %r5, 1088
	li %r6, 1088
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1728
	li %r5, 960
	li %r6, 1024
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1792
	li %r5, 960
	li %r6, 1024
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1728
	li %r5, 1728
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1792
	li %r5, 1536
	li %r6, 1600
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1728
	li %r5, 1728
	li %r6, 1792
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1792
	li %r5, 960
	li %r6, 1088
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1856
	li %r5, 960
	li %r6, 1088
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1856
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1856
	li %r5, 1536
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1856
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1856
	li %r5, 1024
	li %r6, 1088
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1152
	li %r5, 1024
	li %r6, 1088
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1856
	li %r5, 1856
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1152
	li %r5, 1600
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1856
	li %r5, 1856
	li %r6, 1152
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1280
	li %r5, 448
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1152
	li %r5, 512
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1280
	li %r5, 1152
	li %r6, 1280
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1152
	li %r5, 1600
	li %r6, 1280
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1280
	li %r5, 1600
	li %r6, 1280
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1216
	li %r5, 1152
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1536
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1600
	li %r5, 1600
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1664
	li %r5, 448
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1792
	li %r5, 512
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1600
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1664
	li %r5, 1536
	li %r6, 1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1664
	li %r5, 448
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1536
	li %r5, 1600
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1216
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1536
	li %r5, 1856
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1152
	li %r5, 1728
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1152
	li %r5, 1152
	li %r6, 1536
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1536
	li %r5, 1728
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1280
	li %r5, 1856
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1280
	li %r5, 1280
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1536
	li %r5, 1152
	li %r6, 576
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1216
	li %r6, 640
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1664
	li %r5, 1280
	li %r6, 384
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1728
	li %r5, 1152
	li %r6, 1216
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1792
	li %r5, 576
	li %r6, 640
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1728
	li %r5, 1728
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1792
	li %r5, 1536
	li %r6, 1600
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1728
	li %r5, 1728
	li %r6, 1792
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1792
	li %r5, 1152
	li %r6, 1280
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1856
	li %r5, 576
	li %r6, 384
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1856
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1856
	li %r5, 1536
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1856
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1856
	li %r5, 1216
	li %r6, 1280
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1344
	li %r5, 640
	li %r6, 384
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1856
	li %r5, 1856
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1344
	li %r5, 1600
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1856
	li %r5, 1856
	li %r6, 1344
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1472
	li %r5, 448
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1344
	li %r5, 512
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1472
	li %r5, 1344
	li %r6, 1472
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1344
	li %r5, 1600
	li %r6, 1472
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1472
	li %r5, 1600
	li %r6, 1472
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1408
	li %r5, 1344
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1536
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1600
	li %r5, 1600
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1664
	li %r5, 448
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1792
	li %r5, 512
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1600
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1664
	li %r5, 1536
	li %r6, 1664
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1664
	li %r5, 448
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1792
	li %r5, 1792
	li %r6, 1664
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1536
	li %r5, 1600
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1408
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 1536
	li %r5, 1856
	li %r6, 1792
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1344
	li %r5, 1728
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1344
	li %r5, 1344
	li %r6, 1536
	bl {vg_brainpoolp512r1_sub_mod_p}
	li %r4, 1536
	li %r5, 1728
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1472
	li %r5, 1856
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1472
	li %r5, 1472
	li %r6, 1536
	bl {vg_brainpoolp512r1_add_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 4096(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 1152(%r3)
	ld %r5, 1344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 960(%r3)
	ld %r4, 1160(%r3)
	ld %r5, 1352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 968(%r3)
	ld %r4, 1168(%r3)
	ld %r5, 1360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 976(%r3)
	ld %r4, 1176(%r3)
	ld %r5, 1368(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 984(%r3)
	ld %r4, 1184(%r3)
	ld %r5, 1376(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 992(%r3)
	ld %r4, 1192(%r3)
	ld %r5, 1384(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1000(%r3)
	ld %r4, 1200(%r3)
	ld %r5, 1392(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1008(%r3)
	ld %r4, 1208(%r3)
	ld %r5, 1400(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1016(%r3)
	ld %r4, 1216(%r3)
	ld %r5, 1408(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1024(%r3)
	ld %r4, 1224(%r3)
	ld %r5, 1416(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1032(%r3)
	ld %r4, 1232(%r3)
	ld %r5, 1424(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1040(%r3)
	ld %r4, 1240(%r3)
	ld %r5, 1432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1048(%r3)
	ld %r4, 1248(%r3)
	ld %r5, 1440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1056(%r3)
	ld %r4, 1256(%r3)
	ld %r5, 1448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1064(%r3)
	ld %r4, 1264(%r3)
	ld %r5, 1456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1072(%r3)
	ld %r4, 1272(%r3)
	ld %r5, 1464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1080(%r3)
	ld %r4, 1280(%r3)
	ld %r5, 1472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1088(%r3)
	ld %r4, 1288(%r3)
	ld %r5, 1480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1096(%r3)
	ld %r4, 1296(%r3)
	ld %r5, 1488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1104(%r3)
	ld %r4, 1304(%r3)
	ld %r5, 1496(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1112(%r3)
	ld %r4, 1312(%r3)
	ld %r5, 1504(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1120(%r3)
	ld %r4, 1320(%r3)
	ld %r5, 1512(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1128(%r3)
	ld %r4, 1328(%r3)
	ld %r5, 1520(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1136(%r3)
	ld %r4, 1336(%r3)
	ld %r5, 1528(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1144(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 23b
	ld %r4, 1088(%r3)
	std %r4, 1152(%r3)
	ld %r4, 1096(%r3)
	std %r4, 1160(%r3)
	ld %r4, 1104(%r3)
	std %r4, 1168(%r3)
	ld %r4, 1112(%r3)
	std %r4, 1176(%r3)
	ld %r4, 1120(%r3)
	std %r4, 1184(%r3)
	ld %r4, 1128(%r3)
	std %r4, 1192(%r3)
	ld %r4, 1136(%r3)
	std %r4, 1200(%r3)
	ld %r4, 1144(%r3)
	std %r4, 1208(%r3)
	li %r4, 1664
	li %r5, 1088
	li %r6, 1088
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1216
	li %r5, 1152
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1280
	li %r5, 1216
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1344
	li %r5, 1280
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1408
	li %r5, 1344
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1472
	li %r5, 1408
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1536
	li %r5, 1472
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1600
	li %r5, 1536
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_p}
	ld %r4, 1280(%r3)
	std %r4, 1920(%r3)
	ld %r4, 1288(%r3)
	std %r4, 1928(%r3)
	ld %r4, 1296(%r3)
	std %r4, 1936(%r3)
	ld %r4, 1304(%r3)
	std %r4, 1944(%r3)
	ld %r4, 1312(%r3)
	std %r4, 1952(%r3)
	ld %r4, 1320(%r3)
	std %r4, 1960(%r3)
	ld %r4, 1328(%r3)
	std %r4, 1968(%r3)
	ld %r4, 1336(%r3)
	std %r4, 1976(%r3)
	li %r31, 4
24:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 24b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
25:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 25b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
26:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 26b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
27:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 27b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
28:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 28b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
29:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 29b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 1
210:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 210b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
211:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 211b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
212:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 212b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
213:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 213b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
214:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 214b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 2
215:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 215b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
216:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 216b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
217:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 217b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
218:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 218b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
219:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 219b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
220:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 220b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
221:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 221b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
222:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 222b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
223:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 223b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 1
224:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 224b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
225:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 225b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
226:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 226b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
227:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 227b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
228:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 228b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 2
229:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 11
230:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 230b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
231:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 231b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
232:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 232b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
233:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 233b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
234:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
235:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 235b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
236:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 236b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
237:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 237b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
238:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 238b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
239:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 239b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
240:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 240b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
241:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 241b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
242:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 242b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 8
243:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 243b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
244:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 244b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
245:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 245b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
246:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 246b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
247:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 247b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
248:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 248b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
249:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 249b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
250:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 250b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
251:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 251b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 8
252:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 252b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
253:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 253b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
254:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 254b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
255:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 255b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
256:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 256b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
257:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 257b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
258:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 258b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
259:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 259b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
260:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 260b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
261:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 261b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 12
262:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 262b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
263:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 263b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 2
264:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 264b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
265:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 265b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
266:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 266b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
267:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 267b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
268:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 268b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
269:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 269b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
270:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 270b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
271:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 271b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
272:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 272b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 8
273:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 273b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
274:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 274b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
275:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 275b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
276:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 276b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 2
277:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 277b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
278:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 278b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 10
279:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 279b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
280:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 280b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
281:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 281b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
282:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 282b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 10
283:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 283b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
284:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 284b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
285:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 285b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
286:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 286b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
287:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 287b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
288:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 288b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 9
289:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 289b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
290:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 290b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
291:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 291b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
292:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 292b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
293:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 293b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
294:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 294b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
295:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 295b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 9
296:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 296b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
297:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 297b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 6
298:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 298b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 8
299:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 299b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 5
2100:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2100b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 3
2101:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2101b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 7
2102:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2102b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r31, 4
2103:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2103b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2240
	li %r5, 960
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2304
	li %r5, 2240
	li %r6, 320
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2368
	li %r5, 2304
	li %r6, 256
	bl {vg_brainpoolp512r1_add_mod_n}
	li %r4, 2432
	li %r5, 2048
	li %r6, 704
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2112(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2116(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2120(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2124(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2128(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2132(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2136(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2140(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2144(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2148(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2152(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2156(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2160(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2164(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2168(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2172(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 2112(%r3)
	ld %r4, 2120(%r3)
	or %r5, %r5, %r4
	ld %r4, 2128(%r3)
	or %r5, %r5, %r4
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
	and %r5, %r5, %r9
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2048(%r3)
	lwz %r8, 128(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2052(%r3)
	lwz %r8, 132(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2056(%r3)
	lwz %r8, 136(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2060(%r3)
	lwz %r8, 140(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2064(%r3)
	lwz %r8, 144(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2068(%r3)
	lwz %r8, 148(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2072(%r3)
	lwz %r8, 152(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2076(%r3)
	lwz %r8, 156(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2080(%r3)
	lwz %r8, 160(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2084(%r3)
	lwz %r8, 164(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2088(%r3)
	lwz %r8, 168(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2092(%r3)
	lwz %r8, 172(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2096(%r3)
	lwz %r8, 176(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2100(%r3)
	lwz %r8, 180(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2104(%r3)
	lwz %r8, 184(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2108(%r3)
	lwz %r8, 188(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	or %r9, %r5, %r5
	ld %r5, 2048(%r3)
	ld %r4, 2056(%r3)
	or %r5, %r5, %r4
	ld %r4, 2064(%r3)
	or %r5, %r5, %r4
	ld %r4, 2072(%r3)
	or %r5, %r5, %r4
	ld %r4, 2080(%r3)
	or %r5, %r5, %r4
	ld %r4, 2088(%r3)
	or %r5, %r5, %r4
	ld %r4, 2096(%r3)
	or %r5, %r5, %r4
	ld %r4, 2104(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	and %r5, %r5, %r9
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r5, 2368(%r3)
	ld %r4, 2376(%r3)
	or %r5, %r5, %r4
	ld %r4, 2384(%r3)
	or %r5, %r5, %r4
	ld %r4, 2392(%r3)
	or %r5, %r5, %r4
	ld %r4, 2400(%r3)
	or %r5, %r5, %r4
	ld %r4, 2408(%r3)
	or %r5, %r5, %r4
	ld %r4, 2416(%r3)
	or %r5, %r5, %r4
	ld %r4, 2424(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r4, 2432(%r3)
	std %r4, 1152(%r3)
	ld %r4, 2440(%r3)
	std %r4, 1160(%r3)
	ld %r4, 2448(%r3)
	std %r4, 1168(%r3)
	ld %r4, 2456(%r3)
	std %r4, 1176(%r3)
	ld %r4, 2464(%r3)
	std %r4, 1184(%r3)
	ld %r4, 2472(%r3)
	std %r4, 1192(%r3)
	ld %r4, 2480(%r3)
	std %r4, 1200(%r3)
	ld %r4, 2488(%r3)
	std %r4, 1208(%r3)
	li %r4, 1664
	li %r5, 2432
	li %r6, 2432
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1216
	li %r5, 1152
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1280
	li %r5, 1216
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1344
	li %r5, 1280
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1408
	li %r5, 1344
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1472
	li %r5, 1408
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1536
	li %r5, 1472
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 1600
	li %r5, 1536
	li %r6, 1664
	bl {vg_brainpoolp512r1_mul_mod_n}
	ld %r4, 1280(%r3)
	std %r4, 1920(%r3)
	ld %r4, 1288(%r3)
	std %r4, 1928(%r3)
	ld %r4, 1296(%r3)
	std %r4, 1936(%r3)
	ld %r4, 1304(%r3)
	std %r4, 1944(%r3)
	ld %r4, 1312(%r3)
	std %r4, 1952(%r3)
	ld %r4, 1320(%r3)
	std %r4, 1960(%r3)
	ld %r4, 1328(%r3)
	std %r4, 1968(%r3)
	ld %r4, 1336(%r3)
	std %r4, 1976(%r3)
	li %r31, 4
2104:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2104b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2105:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2105b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2106:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2106b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2107:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2107b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2108:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2108b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2109:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2109b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 1
2110:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2110b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
2111:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2111b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2112:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2112b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
2113:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2113b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2114:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2114b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 2
2115:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2115b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
2116:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2116b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
2117:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2117b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2118:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2118b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2119:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2119b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2120:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2120b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2121:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2121b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2122:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2122b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2123:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2123b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 1
2124:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2124b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2125:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2125b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2126:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2126b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2127:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2127b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2128:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2128b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 2
2129:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2129b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 11
2130:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2130b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2131:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2131b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
2132:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2132b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2133:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2133b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2134:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2134b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
2135:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2135b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2136:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2136b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2137:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2137b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
2138:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2138b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2139:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2139b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2140:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2140b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2141:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2141b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
2142:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2142b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
2143:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2143b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2144:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2144b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
2145:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2145b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2146:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2146b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2147:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2147b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2148:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2148b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2149:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2149b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2150:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2150b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2151:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2151b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
2152:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2152b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2153:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2153b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2154:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2154b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
2155:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2155b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
2156:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2156b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2157:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2157b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2158:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2158b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2159:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2159b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2160:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2160b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2161:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2161b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
2162:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2162b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2163:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2163b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2164:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2164b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2165:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2165b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2166:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2166b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 1
2167:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2167b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2168:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2168b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2169:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2169b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
2170:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2170b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2171:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2171b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2172:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2172b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2173:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2173b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2174:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2174b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2175:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2175b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2176:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2176b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2177:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2177b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
2178:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2178b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2179:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2179b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2180:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2180b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2181:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2181b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2182:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2182b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2183:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2183b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 1
2184:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2184b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2185:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2185b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2186:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2186b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 2
2187:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2187b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 7
2188:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2188b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2189:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2189b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
2190:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2190b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2191:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2191b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2192:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2192b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2193:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2193b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 4
2194:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2194b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2195:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2195b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1536
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
2196:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2196b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 3
2197:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2197b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
2198:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2198b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1600
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 6
2199:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2199b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1472
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 2
2200:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2200b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1152
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 8
2201:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2201b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2202:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2202b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2203:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2203b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1280
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2204:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2204b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1408
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 11
2205:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2205b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1216
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r31, 5
2206:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_n}
	cmpldi %cr0, %r31, 0
	bne %cr0, 2206b
	li %r4, 1920
	li %r5, 1920
	li %r6, 1344
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2496
	li %r5, 2368
	li %r6, 704
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2560
	li %r5, 2112
	li %r6, 704
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2624
	li %r5, 2176
	li %r6, 704
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2688
	li %r5, 2496
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2688
	li %r5, 2688
	li %r6, 2624
	bl {vg_brainpoolp512r1_add_mod_n}
	li %r4, 2752
	li %r5, 1920
	li %r6, 2688
	bl {vg_brainpoolp512r1_mul_mod_n}
	li %r4, 2816
	li %r5, 2752
	li %r6, 320
	bl {vg_brainpoolp512r1_mul_mod_n}
	ld %r5, 2816(%r3)
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
	ld %r4, 2872(%r3)
	or %r5, %r5, %r4
	li %r4, 0
	subf %r4, %r5, %r4
	or %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r10, 2880(%r3)
	ld %r4, 2368(%r3)
	and %r4, %r4, %r10
	li %r6, 56
	stdbrx %r4, %r14, %r6
	ld %r4, 2376(%r3)
	and %r4, %r4, %r10
	li %r6, 48
	stdbrx %r4, %r14, %r6
	ld %r4, 2384(%r3)
	and %r4, %r4, %r10
	li %r6, 40
	stdbrx %r4, %r14, %r6
	ld %r4, 2392(%r3)
	and %r4, %r4, %r10
	li %r6, 32
	stdbrx %r4, %r14, %r6
	ld %r4, 2400(%r3)
	and %r4, %r4, %r10
	li %r6, 24
	stdbrx %r4, %r14, %r6
	ld %r4, 2408(%r3)
	and %r4, %r4, %r10
	li %r6, 16
	stdbrx %r4, %r14, %r6
	ld %r4, 2416(%r3)
	and %r4, %r4, %r10
	li %r6, 8
	stdbrx %r4, %r14, %r6
	ld %r4, 2424(%r3)
	and %r4, %r4, %r10
	li %r6, 0
	stdbrx %r4, %r14, %r6
	ld %r4, 2816(%r3)
	and %r4, %r4, %r10
	li %r6, 120
	stdbrx %r4, %r14, %r6
	ld %r4, 2824(%r3)
	and %r4, %r4, %r10
	li %r6, 112
	stdbrx %r4, %r14, %r6
	ld %r4, 2832(%r3)
	and %r4, %r4, %r10
	li %r6, 104
	stdbrx %r4, %r14, %r6
	ld %r4, 2840(%r3)
	and %r4, %r4, %r10
	li %r6, 96
	stdbrx %r4, %r14, %r6
	ld %r4, 2848(%r3)
	and %r4, %r4, %r10
	li %r6, 88
	stdbrx %r4, %r14, %r6
	ld %r4, 2856(%r3)
	and %r4, %r4, %r10
	li %r6, 80
	stdbrx %r4, %r14, %r6
	ld %r4, 2864(%r3)
	and %r4, %r4, %r10
	li %r6, 72
	stdbrx %r4, %r14, %r6
	ld %r4, 2872(%r3)
	and %r4, %r4, %r10
	li %r6, 64
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
