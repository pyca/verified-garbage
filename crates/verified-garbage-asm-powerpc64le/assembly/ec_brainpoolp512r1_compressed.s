// The functions of `src/ec_brainpoolp512r1_compressed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp512r1_compress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2048(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2056(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2064(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2072(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2080(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2088(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2096(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2104(%r3)
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2112(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2120(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2128(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2136(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2144(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2152(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2160(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2168(%r3)
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
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
	lis %r11, 24920
	ori %r11, %r11, 61957
	stw %r11, 2560(%r3)
	lis %r11, 18861
	ori %r11, %r11, 5194
	stw %r11, 2564(%r3)
	lis %r11, 10005
	ori %r11, %r11, 30981
	stw %r11, 2568(%r3)
	lis %r11, 31039
	ori %r11, %r11, 45360
	stw %r11, 2572(%r3)
	lis %r11, -28582
	ori %r11, %r11, 65491
	stw %r11, 2576(%r3)
	lis %r11, 21431
	ori %r11, %r11, 63932
	stw %r11, 2580(%r3)
	lis %r11, -31919
	ori %r11, %r11, 18981
	stw %r11, 2584(%r3)
	lis %r11, -7999
	ori %r11, %r11, 39543
	stw %r11, 2588(%r3)
	lis %r11, -10871
	ori %r11, %r11, 32855
	stw %r11, 2592(%r3)
	lis %r11, 6472
	ori %r11, %r11, 28632
	stw %r11, 2596(%r3)
	lis %r11, -11221
	ori %r11, %r11, 65411
	stw %r11, 2600(%r3)
	lis %r11, -24211
	ori %r11, %r11, 43615
	stw %r11, 2604(%r3)
	lis %r11, 8278
	ori %r11, %r11, 61132
	stw %r11, 2608(%r3)
	lis %r11, 8238
	ori %r11, %r11, 6464
	stw %r11, 2612(%r3)
	lis %r11, -22017
	ori %r11, %r11, 25680
	stw %r11, 2616(%r3)
	lis %r11, 15436
	ori %r11, %r11, 40197
	stw %r11, 2620(%r3)
	lis %r11, 8425
	ori %r11, %r11, 10804
	stw %r11, 2624(%r3)
	lis %r11, 20606
	ori %r11, %r11, 33686
	stw %r11, 2628(%r3)
	lis %r11, -6770
	ori %r11, %r11, 23092
	stw %r11, 2632(%r3)
	lis %r11, 155
	ori %r11, %r11, 25543
	stw %r11, 2636(%r3)
	lis %r11, 11655
	ori %r11, %r11, 9386
	stw %r11, 2640(%r3)
	lis %r11, -7829
	ori %r11, %r11, 42070
	stw %r11, 2644(%r3)
	lis %r11, -26505
	ori %r11, %r11, 48642
	stw %r11, 2648(%r3)
	lis %r11, -14530
	ori %r11, %r11, 12520
	stw %r11, 2652(%r3)
	lis %r11, -478
	ori %r11, %r11, 9267
	stw %r11, 2656(%r3)
	lis %r11, -26656
	ori %r11, %r11, 3171
	stw %r11, 2660(%r3)
	lis %r11, 27927
	ori %r11, %r11, 55325
	stw %r11, 2664(%r3)
	lis %r11, -13350
	ori %r11, %r11, 22444
	stw %r11, 2668(%r3)
	lis %r11, 2997
	ori %r11, %r11, 43682
	stw %r11, 2672(%r3)
	lis %r11, 25635
	ori %r11, %r11, 4773
	stw %r11, 2676(%r3)
	lis %r11, 18206
	ori %r11, %r11, 36519
	stw %r11, 2680(%r3)
	lis %r11, 27210
	ori %r11, %r11, 43956
	stw %r11, 2684(%r3)
	addi %r6, %r12, 1
	li %r9, 56
	ldbrx %r8, %r6, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r6, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 2232(%r3)
	addi %r6, %r6, 64
	li %r9, 56
	ldbrx %r8, %r6, %r9
	std %r8, 2368(%r3)
	li %r9, 48
	ldbrx %r8, %r6, %r9
	std %r8, 2376(%r3)
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 2384(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 2392(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 2400(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 2408(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 2416(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 2424(%r3)
	lbz %r4, 0(%r12)
	li %r7, 4
	xor %r4, %r4, %r7
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2176(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2180(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2184(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2188(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2192(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2196(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2200(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2204(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2208(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2212(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2216(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2220(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2224(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2228(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2232(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2236(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2368(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2372(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2376(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2380(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2384(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2388(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2392(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2396(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2400(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2404(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2408(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2412(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2416(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2420(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2424(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2428(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r4, 2240
	li %r5, 2176
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2304
	li %r5, 2368
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2432
	li %r5, 2304
	li %r6, 2304
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 2240
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2752
	li %r5, 2688
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 448
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2496
	li %r5, 2752
	li %r6, 2688
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 2752
	li %r5, 2496
	li %r6, 2624
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 2688
	li %r5, 2432
	li %r6, 2752
	bl {vg_brainpoolp512r1_sub_mod_p}
	ld %r5, 2688(%r3)
	ld %r4, 2696(%r3)
	or %r5, %r5, %r4
	ld %r4, 2704(%r3)
	or %r5, %r5, %r4
	ld %r4, 2712(%r3)
	or %r5, %r5, %r4
	ld %r4, 2720(%r3)
	or %r5, %r5, %r4
	ld %r4, 2728(%r3)
	or %r5, %r5, %r4
	ld %r4, 2736(%r3)
	or %r5, %r5, %r4
	ld %r4, 2744(%r3)
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
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r10, 2880(%r3)
	ld %r4, 576(%r3)
	ld %r5, 2240(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2496(%r3)
	ld %r4, 584(%r3)
	ld %r5, 2248(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2504(%r3)
	ld %r4, 592(%r3)
	ld %r5, 2256(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2512(%r3)
	ld %r4, 600(%r3)
	ld %r5, 2264(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2520(%r3)
	ld %r4, 608(%r3)
	ld %r5, 2272(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2528(%r3)
	ld %r4, 616(%r3)
	ld %r5, 2280(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2536(%r3)
	ld %r4, 624(%r3)
	ld %r5, 2288(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2544(%r3)
	ld %r4, 632(%r3)
	ld %r5, 2296(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2552(%r3)
	ld %r4, 640(%r3)
	ld %r5, 2304(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2816(%r3)
	ld %r4, 648(%r3)
	ld %r5, 2312(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2824(%r3)
	ld %r4, 656(%r3)
	ld %r5, 2320(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2832(%r3)
	ld %r4, 664(%r3)
	ld %r5, 2328(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2840(%r3)
	ld %r4, 672(%r3)
	ld %r5, 2336(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2848(%r3)
	ld %r4, 680(%r3)
	ld %r5, 2344(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2856(%r3)
	ld %r4, 688(%r3)
	ld %r5, 2352(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2864(%r3)
	ld %r4, 696(%r3)
	ld %r5, 2360(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2872(%r3)
	ld %r10, 2880(%r3)
	ld %r4, 2368(%r3)
	li %r5, 1
	and %r4, %r4, %r5
	addi %r4, %r4, 2
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 2176(%r3)
	and %r4, %r4, %r10
	li %r6, 57
	stdbrx %r4, %r14, %r6
	ld %r4, 2184(%r3)
	and %r4, %r4, %r10
	li %r6, 49
	stdbrx %r4, %r14, %r6
	ld %r4, 2192(%r3)
	and %r4, %r4, %r10
	li %r6, 41
	stdbrx %r4, %r14, %r6
	ld %r4, 2200(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 2208(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 2216(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 2224(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 2232(%r3)
	and %r4, %r4, %r10
	li %r6, 1
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr

vg_ec_brainpoolp512r1_decompress_public_key:
	or %r12, %r4, %r4
	std %r14, 0(%r5)
	std %r31, 8(%r5)
	mflr %r0
	std %r0, 16(%r5)
	or %r14, %r3, %r3
	or %r3, %r5, %r5
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2048(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2056(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2064(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2072(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2080(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2088(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2096(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2104(%r3)
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2112(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2120(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2128(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2136(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2144(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2152(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2160(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
	std %r8, 2168(%r3)
	li %r9, 56
	ldbrx %r8, %r12, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r12, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r12, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r12, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r12, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r12, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r12, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r12, %r9
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
	lis %r11, 24920
	ori %r11, %r11, 61957
	stw %r11, 2560(%r3)
	lis %r11, 18861
	ori %r11, %r11, 5194
	stw %r11, 2564(%r3)
	lis %r11, 10005
	ori %r11, %r11, 30981
	stw %r11, 2568(%r3)
	lis %r11, 31039
	ori %r11, %r11, 45360
	stw %r11, 2572(%r3)
	lis %r11, -28582
	ori %r11, %r11, 65491
	stw %r11, 2576(%r3)
	lis %r11, 21431
	ori %r11, %r11, 63932
	stw %r11, 2580(%r3)
	lis %r11, -31919
	ori %r11, %r11, 18981
	stw %r11, 2584(%r3)
	lis %r11, -7999
	ori %r11, %r11, 39543
	stw %r11, 2588(%r3)
	lis %r11, -10871
	ori %r11, %r11, 32855
	stw %r11, 2592(%r3)
	lis %r11, 6472
	ori %r11, %r11, 28632
	stw %r11, 2596(%r3)
	lis %r11, -11221
	ori %r11, %r11, 65411
	stw %r11, 2600(%r3)
	lis %r11, -24211
	ori %r11, %r11, 43615
	stw %r11, 2604(%r3)
	lis %r11, 8278
	ori %r11, %r11, 61132
	stw %r11, 2608(%r3)
	lis %r11, 8238
	ori %r11, %r11, 6464
	stw %r11, 2612(%r3)
	lis %r11, -22017
	ori %r11, %r11, 25680
	stw %r11, 2616(%r3)
	lis %r11, 15436
	ori %r11, %r11, 40197
	stw %r11, 2620(%r3)
	lis %r11, 8425
	ori %r11, %r11, 10804
	stw %r11, 2624(%r3)
	lis %r11, 20606
	ori %r11, %r11, 33686
	stw %r11, 2628(%r3)
	lis %r11, -6770
	ori %r11, %r11, 23092
	stw %r11, 2632(%r3)
	lis %r11, 155
	ori %r11, %r11, 25543
	stw %r11, 2636(%r3)
	lis %r11, 11655
	ori %r11, %r11, 9386
	stw %r11, 2640(%r3)
	lis %r11, -7829
	ori %r11, %r11, 42070
	stw %r11, 2644(%r3)
	lis %r11, -26505
	ori %r11, %r11, 48642
	stw %r11, 2648(%r3)
	lis %r11, -14530
	ori %r11, %r11, 12520
	stw %r11, 2652(%r3)
	lis %r11, -478
	ori %r11, %r11, 9267
	stw %r11, 2656(%r3)
	lis %r11, -26656
	ori %r11, %r11, 3171
	stw %r11, 2660(%r3)
	lis %r11, 27927
	ori %r11, %r11, 55325
	stw %r11, 2664(%r3)
	lis %r11, -13350
	ori %r11, %r11, 22444
	stw %r11, 2668(%r3)
	lis %r11, 2997
	ori %r11, %r11, 43682
	stw %r11, 2672(%r3)
	lis %r11, 25635
	ori %r11, %r11, 4773
	stw %r11, 2676(%r3)
	lis %r11, 18206
	ori %r11, %r11, 36519
	stw %r11, 2680(%r3)
	lis %r11, 27210
	ori %r11, %r11, 43956
	stw %r11, 2684(%r3)
	addi %r6, %r12, 1
	li %r9, 56
	ldbrx %r8, %r6, %r9
	std %r8, 2176(%r3)
	li %r9, 48
	ldbrx %r8, %r6, %r9
	std %r8, 2184(%r3)
	li %r9, 40
	ldbrx %r8, %r6, %r9
	std %r8, 2192(%r3)
	li %r9, 32
	ldbrx %r8, %r6, %r9
	std %r8, 2200(%r3)
	li %r9, 24
	ldbrx %r8, %r6, %r9
	std %r8, 2208(%r3)
	li %r9, 16
	ldbrx %r8, %r6, %r9
	std %r8, 2216(%r3)
	li %r9, 8
	ldbrx %r8, %r6, %r9
	std %r8, 2224(%r3)
	li %r9, 0
	ldbrx %r8, %r6, %r9
	std %r8, 2232(%r3)
	lbz %r4, 0(%r12)
	std %r4, 2112(%r3)
	li %r5, 1
	or %r4, %r4, %r5
	li %r5, 3
	xor %r4, %r4, %r5
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r4, %r5
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r0, 0
	ori %r0, %r0, 65535
	oris %r0, %r0, 65535
	li %r6, 1
	lwz %r7, 2176(%r3)
	lwz %r8, 64(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2180(%r3)
	lwz %r8, 68(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2184(%r3)
	lwz %r8, 72(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2188(%r3)
	lwz %r8, 76(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2192(%r3)
	lwz %r8, 80(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2196(%r3)
	lwz %r8, 84(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2200(%r3)
	lwz %r8, 88(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2204(%r3)
	lwz %r8, 92(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2208(%r3)
	lwz %r8, 96(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2212(%r3)
	lwz %r8, 100(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2216(%r3)
	lwz %r8, 104(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2220(%r3)
	lwz %r8, 108(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2224(%r3)
	lwz %r8, 112(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2228(%r3)
	lwz %r8, 116(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2232(%r3)
	lwz %r8, 120(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	lwz %r7, 2236(%r3)
	lwz %r8, 124(%r3)
	add %r7, %r7, %r0
	subf %r7, %r8, %r7
	add %r7, %r7, %r6
	rldicl %r6, %r7, 32, 32
	addi %r5, %r6, -1
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	li %r4, 2240
	li %r5, 2176
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 2240
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2752
	li %r5, 2688
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 448
	li %r6, 2240
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2496
	li %r5, 2752
	li %r6, 2688
	bl {vg_brainpoolp512r1_add_mod_p}
	li %r4, 2752
	li %r5, 2496
	li %r6, 2624
	bl {vg_brainpoolp512r1_add_mod_p}
	lis %r11, -27122
	ori %r11, %r11, 37437
	stw %r11, 832(%r3)
	lis %r11, 18986
	ori %r11, %r11, 38933
	stw %r11, 836(%r3)
	lis %r11, -13472
	ori %r11, %r11, 45473
	stw %r11, 840(%r3)
	lis %r11, -30176
	ori %r11, %r11, 32715
	stw %r11, 844(%r3)
	lis %r11, -18008
	ori %r11, %r11, 57401
	stw %r11, 848(%r3)
	lis %r11, -21581
	ori %r11, %r11, 26698
	stw %r11, 852(%r3)
	lis %r11, 9969
	ori %r11, %r11, 39440
	stw %r11, 856(%r3)
	lis %r11, 24403
	ori %r11, %r11, 26304
	stw %r11, 860(%r3)
	lis %r11, -25588
	ori %r11, %r11, 49692
	stw %r11, 864(%r3)
	lis %r11, -19048
	ori %r11, %r11, 59186
	stw %r11, 868(%r3)
	lis %r11, -4878
	ori %r11, %r11, 29827
	stw %r11, 872(%r3)
	lis %r11, -3380
	ori %r11, %r11, 9068
	stw %r11, 876(%r3)
	lis %r11, -29454
	ori %r11, %r11, 32513
	stw %r11, 880(%r3)
	lis %r11, -12299
	ori %r11, %r11, 14763
	stw %r11, 884(%r3)
	lis %r11, 14074
	ori %r11, %r11, 28962
	stw %r11, 888(%r3)
	lis %r11, 10935
	ori %r11, %r11, 26478
	stw %r11, 892(%r3)
	li %r31, 64
20:
	addi %r31, %r31, -1
	add %r4, %r3, %r31
	lbz %r4, 832(%r4)
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
	bne %cr0, 20b
	ld %r4, 384(%r3)
	std %r4, 1920(%r3)
	ld %r4, 392(%r3)
	std %r4, 1928(%r3)
	ld %r4, 400(%r3)
	std %r4, 1936(%r3)
	ld %r4, 408(%r3)
	std %r4, 1944(%r3)
	ld %r4, 416(%r3)
	std %r4, 1952(%r3)
	ld %r4, 424(%r3)
	std %r4, 1960(%r3)
	ld %r4, 432(%r3)
	std %r4, 1968(%r3)
	ld %r4, 440(%r3)
	std %r4, 1976(%r3)
	li %r31, 512
21:
	addi %r31, %r31, -1
	li %r4, 1920
	li %r5, 1920
	li %r6, 1920
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 1984
	li %r5, 1920
	li %r6, 2752
	bl {vg_brainpoolp512r1_mul_mod_p}
	add %r4, %r3, %r31
	lbz %r4, 5120(%r4)
	li %r5, 0
	subf %r10, %r4, %r5
	ld %r4, 1920(%r3)
	ld %r5, 1984(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1920(%r3)
	ld %r4, 1928(%r3)
	ld %r5, 1992(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1928(%r3)
	ld %r4, 1936(%r3)
	ld %r5, 2000(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1936(%r3)
	ld %r4, 1944(%r3)
	ld %r5, 2008(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1944(%r3)
	ld %r4, 1952(%r3)
	ld %r5, 2016(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1952(%r3)
	ld %r4, 1960(%r3)
	ld %r5, 2024(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1960(%r3)
	ld %r4, 1968(%r3)
	ld %r5, 2032(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1968(%r3)
	ld %r4, 1976(%r3)
	ld %r5, 2040(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 1976(%r3)
	cmpldi %cr0, %r31, 0
	bne %cr0, 21b
	li %r4, 2368
	li %r5, 1920
	li %r6, 320
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2432
	li %r5, 256
	li %r6, 2368
	bl {vg_brainpoolp512r1_sub_mod_p}
	ld %r4, 2368(%r3)
	ld %r5, 2112(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	ld %r4, 2368(%r3)
	ld %r5, 2432(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2368(%r3)
	ld %r4, 2376(%r3)
	ld %r5, 2440(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2376(%r3)
	ld %r4, 2384(%r3)
	ld %r5, 2448(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2384(%r3)
	ld %r4, 2392(%r3)
	ld %r5, 2456(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2392(%r3)
	ld %r4, 2400(%r3)
	ld %r5, 2464(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2400(%r3)
	ld %r4, 2408(%r3)
	ld %r5, 2472(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2408(%r3)
	ld %r4, 2416(%r3)
	ld %r5, 2480(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2416(%r3)
	ld %r4, 2424(%r3)
	ld %r5, 2488(%r3)
	xor %r5, %r5, %r4
	and %r5, %r5, %r10
	xor %r4, %r4, %r5
	std %r4, 2424(%r3)
	li %r4, 2304
	li %r5, 2368
	li %r6, 2560
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2688
	li %r5, 2304
	li %r6, 2304
	bl {vg_brainpoolp512r1_mul_mod_p}
	li %r4, 2496
	li %r5, 2688
	li %r6, 2752
	bl {vg_brainpoolp512r1_sub_mod_p}
	ld %r5, 2496(%r3)
	ld %r4, 2504(%r3)
	or %r5, %r5, %r4
	ld %r4, 2512(%r3)
	or %r5, %r5, %r4
	ld %r4, 2520(%r3)
	or %r5, %r5, %r4
	ld %r4, 2528(%r3)
	or %r5, %r5, %r4
	ld %r4, 2536(%r3)
	or %r5, %r5, %r4
	ld %r4, 2544(%r3)
	or %r5, %r5, %r4
	ld %r4, 2552(%r3)
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
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r4, 2368(%r3)
	ld %r5, 2112(%r3)
	xor %r5, %r5, %r4
	li %r4, 1
	and %r5, %r5, %r4
	li %r4, 0
	subf %r10, %r5, %r4
	addi %r5, %r10, 1
	li %r4, 0
	subf %r5, %r5, %r4
	ld %r4, 2880(%r3)
	and %r4, %r4, %r5
	std %r4, 2880(%r3)
	ld %r10, 2880(%r3)
	li %r4, 4
	and %r4, %r4, %r10
	stb %r4, 0(%r14)
	ld %r4, 2176(%r3)
	and %r4, %r4, %r10
	li %r6, 57
	stdbrx %r4, %r14, %r6
	ld %r4, 2184(%r3)
	and %r4, %r4, %r10
	li %r6, 49
	stdbrx %r4, %r14, %r6
	ld %r4, 2192(%r3)
	and %r4, %r4, %r10
	li %r6, 41
	stdbrx %r4, %r14, %r6
	ld %r4, 2200(%r3)
	and %r4, %r4, %r10
	li %r6, 33
	stdbrx %r4, %r14, %r6
	ld %r4, 2208(%r3)
	and %r4, %r4, %r10
	li %r6, 25
	stdbrx %r4, %r14, %r6
	ld %r4, 2216(%r3)
	and %r4, %r4, %r10
	li %r6, 17
	stdbrx %r4, %r14, %r6
	ld %r4, 2224(%r3)
	and %r4, %r4, %r10
	li %r6, 9
	stdbrx %r4, %r14, %r6
	ld %r4, 2232(%r3)
	and %r4, %r4, %r10
	li %r6, 1
	stdbrx %r4, %r14, %r6
	ld %r4, 2368(%r3)
	and %r4, %r4, %r10
	li %r6, 121
	stdbrx %r4, %r14, %r6
	ld %r4, 2376(%r3)
	and %r4, %r4, %r10
	li %r6, 113
	stdbrx %r4, %r14, %r6
	ld %r4, 2384(%r3)
	and %r4, %r4, %r10
	li %r6, 105
	stdbrx %r4, %r14, %r6
	ld %r4, 2392(%r3)
	and %r4, %r4, %r10
	li %r6, 97
	stdbrx %r4, %r14, %r6
	ld %r4, 2400(%r3)
	and %r4, %r4, %r10
	li %r6, 89
	stdbrx %r4, %r14, %r6
	ld %r4, 2408(%r3)
	and %r4, %r4, %r10
	li %r6, 81
	stdbrx %r4, %r14, %r6
	ld %r4, 2416(%r3)
	and %r4, %r4, %r10
	li %r6, 73
	stdbrx %r4, %r14, %r6
	ld %r4, 2424(%r3)
	and %r4, %r4, %r10
	li %r6, 65
	stdbrx %r4, %r14, %r6
	li %r4, 1
	and %r4, %r10, %r4
	ld %r0, 16(%r3)
	mtlr %r0
	ld %r14, 0(%r3)
	ld %r31, 8(%r3)
	or %r3, %r4, %r4
	blr
