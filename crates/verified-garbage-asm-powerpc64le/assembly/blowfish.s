// The functions of `src/blowfish.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_expand_key:
	stdu %r1, -64(%r1)
	addi %r6, %r1, 32
	std %r14, 0(%r6)
	std %r15, 8(%r6)
	std %r16, 16(%r6)
	std %r17, 24(%r6)
	lis %r12, -26299
	ori %r12, %r12, 38637
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47067
	ori %r12, %r12, 44198
	std %r12, 0(%r5)
	lis %r12, 32419
	ori %r12, %r12, 27096
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5858
	ori %r12, %r12, 63303
	std %r12, 8(%r5)
	lis %r12, 4921
	ori %r12, %r12, 46365
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61016
	ori %r12, %r12, 22671
	std %r12, 16(%r5)
	lis %r12, 16011
	ori %r12, %r12, 3760
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61208
	ori %r12, %r12, 61475
	std %r12, 24(%r5)
	lis %r12, 16482
	ori %r12, %r12, 38131
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24794
	ori %r12, %r12, 10177
	std %r12, 32(%r5)
	lis %r12, 10769
	ori %r12, %r12, 37807
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52788
	ori %r12, %r12, 46698
	std %r12, 40(%r5)
	lis %r12, 30593
	ori %r12, %r12, 23603
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7702
	ori %r12, %r12, 63069
	std %r12, 48(%r5)
	lis %r12, 12896
	ori %r12, %r12, 37324
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37659
	ori %r12, %r12, 44952
	std %r12, 56(%r5)
	lis %r12, 14835
	ori %r12, %r12, 50561
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34818
	ori %r12, %r12, 45405
	std %r12, 64(%r5)
	lis %r12, -3999
	ori %r12, %r12, 39490
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24138
	ori %r12, %r12, 1154
	std %r12, 72(%r5)
	lis %r12, -26544
	ori %r12, %r12, 58476
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 41768
	ori %r12, %r12, 26834
	std %r12, 80(%r5)
	lis %r12, -16701
	ori %r12, %r12, 46105
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34878
	ori %r12, %r12, 30237
	std %r12, 88(%r5)
	lis %r12, 15730
	ori %r12, %r12, 1634
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 42655
	ori %r12, %r12, 29656
	std %r12, 96(%r5)
	lis %r12, -2088
	ori %r12, %r12, 31689
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39891
	ori %r12, %r12, 18468
	std %r12, 104(%r5)
	lis %r12, 25538
	ori %r12, %r12, 50358
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47805
	ori %r12, %r12, 15130
	std %r12, 112(%r5)
	lis %r12, 2372
	ori %r12, %r12, 11295
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28651
	ori %r12, %r12, 46511
	std %r12, 120(%r5)
	lis %r12, -9415
	ori %r12, %r12, 3927
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 45831
	ori %r12, %r12, 64772
	std %r12, 128(%r5)
	lis %r12, -1800
	ori %r12, %r12, 52478
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 31174
	ori %r12, %r12, 2749
	std %r12, 136(%r5)
	lis %r12, -32184
	ori %r12, %r12, 24826
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43976
	ori %r12, %r12, 5599
	std %r12, 144(%r5)
	lis %r12, 29638
	ori %r12, %r12, 50166
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 56110
	ori %r12, %r12, 41147
	std %r12, 152(%r5)
	lis %r12, 23404
	ori %r12, %r12, 47256
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 41053
	ori %r12, %r12, 51376
	std %r12, 160(%r5)
	lis %r12, -6079
	ori %r12, %r12, 13274
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37052
	ori %r12, %r12, 25977
	std %r12, 168(%r5)
	lis %r12, -24463
	ori %r12, %r12, 38989
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 46334
	ori %r12, %r12, 474
	std %r12, 176(%r5)
	lis %r12, 7186
	ori %r12, %r12, 25851
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 46895
	ori %r12, %r12, 57552
	std %r12, 184(%r5)
	lis %r12, -24066
	ori %r12, %r12, 30488
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44433
	ori %r12, %r12, 7328
	std %r12, 192(%r5)
	lis %r12, -9855
	ori %r12, %r12, 47072
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39382
	ori %r12, %r12, 59407
	std %r12, 200(%r5)
	lis %r12, -12299
	ori %r12, %r12, 34405
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 30484
	ori %r12, %r12, 1382
	std %r12, 208(%r5)
	lis %r12, -20549
	ori %r12, %r12, 24109
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 18899
	ori %r12, %r12, 40972
	std %r12, 216(%r5)
	lis %r12, -14942
	ori %r12, %r12, 32649
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43549
	ori %r12, %r12, 7835
	std %r12, 224(%r5)
	lis %r12, 5458
	ori %r12, %r12, 19146
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16744
	ori %r12, %r12, 43382
	std %r12, 232(%r5)
	lis %r12, 5483
	ori %r12, %r12, 8117
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 118
	ori %r12, %r12, 58431
	std %r12, 240(%r5)
	lis %r12, 27289
	ori %r12, %r12, 41309
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25646
	ori %r12, %r12, 46625
	std %r12, 248(%r5)
	lis %r12, 32656
	ori %r12, %r12, 32431
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 57202
	ori %r12, %r12, 46347
	std %r12, 256(%r5)
	lis %r12, 15870
	ori %r12, %r12, 20000
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 64754
	ori %r12, %r12, 27801
	std %r12, 264(%r5)
	lis %r12, 24789
	ori %r12, %r12, 22948
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 19149
	ori %r12, %r12, 46708
	std %r12, 272(%r5)
	lis %r12, -30194
	ori %r12, %r12, 6364
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 14457
	ori %r12, %r12, 34224
	std %r12, 280(%r5)
	lis %r12, 5272
	ori %r12, %r12, 43813
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 23599
	ori %r12, %r12, 19319
	std %r12, 288(%r5)
	lis %r12, -17388
	ori %r12, %r12, 59782
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 59484
	ori %r12, %r12, 4153
	std %r12, 296(%r5)
	lis %r12, -31149
	ori %r12, %r12, 53178
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37694
	ori %r12, %r12, 12741
	std %r12, 304(%r5)
	lis %r12, -32596
	ori %r12, %r12, 43273
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8680
	ori %r12, %r12, 47432
	std %r12, 312(%r5)
	lis %r12, 17007
	ori %r12, %r12, 44094
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6947
	ori %r12, %r12, 30045
	std %r12, 320(%r5)
	lis %r12, -30564
	ori %r12, %r12, 27752
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39920
	ori %r12, %r12, 8260
	std %r12, 328(%r5)
	lis %r12, 10992
	ori %r12, %r12, 15115
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 13223
	ori %r12, %r12, 12192
	std %r12, 336(%r5)
	lis %r12, 24229
	ori %r12, %r12, 40838
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 3673
	ori %r12, %r12, 357
	std %r12, 344(%r5)
	lis %r12, 735
	ori %r12, %r12, 30634
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 27204
	ori %r12, %r12, 8309
	std %r12, 352(%r5)
	lis %r12, -8583
	ori %r12, %r12, 7026
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49386
	ori %r12, %r12, 4823
	std %r12, 360(%r5)
	lis %r12, 9374
	ori %r12, %r12, 24655
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1760
	ori %r12, %r12, 19536
	std %r12, 368(%r5)
	lis %r12, -17083
	ori %r12, %r12, 38225
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 60594
	ori %r12, %r12, 21359
	std %r12, 376(%r5)
	lis %r12, -1185
	ori %r12, %r12, 29864
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 19240
	ori %r12, %r12, 19152
	std %r12, 384(%r5)
	lis %r12, 8937
	ori %r12, %r12, 41765
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 29184
	ori %r12, %r12, 12992
	std %r12, 392(%r5)
	lis %r12, -8325
	ori %r12, %r12, 34741
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 21022
	ori %r12, %r12, 27414
	std %r12, 400(%r5)
	lis %r12, 21810
	ori %r12, %r12, 65448
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26966
	ori %r12, %r12, 35927
	std %r12, 408(%r5)
	lis %r12, -11339
	ori %r12, %r12, 33597
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4515
	ori %r12, %r12, 22567
	std %r12, 416(%r5)
	lis %r12, -14829
	ori %r12, %r12, 32498
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 38729
	ori %r12, %r12, 17892
	std %r12, 424(%r5)
	lis %r12, -10866
	ori %r12, %r12, 37338
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8094
	ori %r12, %r12, 19658
	std %r12, 432(%r5)
	lis %r12, -3912
	ori %r12, %r12, 11234
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37979
	ori %r12, %r12, 9681
	std %r12, 440(%r5)
	lis %r12, 7981
	ori %r12, %r12, 5922
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49649
	ori %r12, %r12, 50014
	std %r12, 448(%r5)
	lis %r12, -22469
	ori %r12, %r12, 57423
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 58099
	ori %r12, %r12, 29900
	std %r12, 456(%r5)
	lis %r12, 13634
	ori %r12, %r12, 64032
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5235
	ori %r12, %r12, 30626
	std %r12, 464(%r5)
	lis %r12, -8192
	ori %r12, %r12, 45838
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 32283
	ori %r12, %r12, 35247
	std %r12, 472(%r5)
	lis %r12, -18085
	ori %r12, %r12, 21315
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 42641
	ori %r12, %r12, 47414
	std %r12, 480(%r5)
	lis %r12, 10496
	ori %r12, %r12, 43309
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 18969
	ori %r12, %r12, 52995
	std %r12, 488(%r5)
	lis %r12, -9748
	ori %r12, %r12, 59759
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 29860
	ori %r12, %r12, 50775
	std %r12, 496(%r5)
	lis %r12, 1863
	ori %r12, %r12, 36653
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 22021
	ori %r12, %r12, 63845
	std %r12, 504(%r5)
	lis %r12, 11388
	ori %r12, %r12, 9953
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6909
	ori %r12, %r12, 57137
	std %r12, 512(%r5)
	lis %r12, -27816
	ori %r12, %r12, 22377
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 36353
	ori %r12, %r12, 37281
	std %r12, 520(%r5)
	lis %r12, -3536
	ori %r12, %r12, 23124
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5515
	ori %r12, %r12, 36501
	std %r12, 528(%r5)
	lis %r12, 7838
	ori %r12, %r12, 14969
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 56129
	ori %r12, %r12, 24785
	std %r12, 536(%r5)
	lis %r12, -6072
	ori %r12, %r12, 21845
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24751
	ori %r12, %r12, 12565
	std %r12, 544(%r5)
	lis %r12, 28654
	ori %r12, %r12, 29268
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16844
	ori %r12, %r12, 43978
	std %r12, 552(%r5)
	lis %r12, -27342
	ori %r12, %r12, 9430
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34652
	ori %r12, %r12, 6313
	std %r12, 560(%r5)
	lis %r12, -4996
	ori %r12, %r12, 8664
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10431
	ori %r12, %r12, 19343
	std %r12, 568(%r5)
	lis %r12, -2963
	ori %r12, %r12, 38537
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25894
	ori %r12, %r12, 34180
	std %r12, 576(%r5)
	lis %r12, -11508
	ori %r12, %r12, 59846
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8136
	ori %r12, %r12, 33803
	std %r12, 584(%r5)
	lis %r12, -1221
	ori %r12, %r12, 31471
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 20751
	ori %r12, %r12, 21585
	std %r12, 592(%r5)
	lis %r12, -29820
	ori %r12, %r12, 28654
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 17354
	ori %r12, %r12, 45041
	std %r12, 600(%r5)
	lis %r12, -25602
	ori %r12, %r12, 16339
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49434
	ori %r12, %r12, 49519
	std %r12, 608(%r5)
	lis %r12, -5932
	ori %r12, %r12, 39251
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61711
	ori %r12, %r12, 2768
	std %r12, 616(%r5)
	lis %r12, 27228
	ori %r12, %r12, 40873
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49260
	ori %r12, %r12, 31230
	std %r12, 624(%r5)
	lis %r12, 24193
	ori %r12, %r12, 12540
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 21049
	ori %r12, %r12, 27899
	std %r12, 632(%r5)
	lis %r12, -11509
	ori %r12, %r12, 51403
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11791
	ori %r12, %r12, 13283
	std %r12, 640(%r5)
	lis %r12, 12965
	ori %r12, %r12, 8095
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11425
	ori %r12, %r12, 24697
	std %r12, 648(%r5)
	lis %r12, 49
	ori %r12, %r12, 9021
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1360
	ori %r12, %r12, 24949
	std %r12, 656(%r5)
	lis %r12, 20327
	ori %r12, %r12, 32322
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6023
	ori %r12, %r12, 28508
	std %r12, 664(%r5)
	lis %r12, -11780
	ori %r12, %r12, 8698
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61695
	ori %r12, %r12, 51803
	std %r12, 672(%r5)
	lis %r12, -6917
	ori %r12, %r12, 52189
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 64398
	ori %r12, %r12, 63571
	std %r12, 680(%r5)
	lis %r12, -27731
	ori %r12, %r12, 37083
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61822
	ori %r12, %r12, 30496
	std %r12, 688(%r5)
	lis %r12, 3464
	ori %r12, %r12, 4854
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 30012
	ori %r12, %r12, 51086
	std %r12, 696(%r5)
	lis %r12, 629
	ori %r12, %r12, 3631
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43215
	ori %r12, %r12, 36781
	std %r12, 704(%r5)
	lis %r12, -21052
	ori %r12, %r12, 5032
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 35244
	ori %r12, %r12, 28576
	std %r12, 712(%r5)
	lis %r12, -25260
	ori %r12, %r12, 46509
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6860
	ori %r12, %r12, 38239
	std %r12, 720(%r5)
	lis %r12, -18328
	ori %r12, %r12, 28965
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7745
	ori %r12, %r12, 16077
	std %r12, 728(%r5)
	lis %r12, -6787
	ori %r12, %r12, 23233
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 57187
	ori %r12, %r12, 2404
	std %r12, 736(%r5)
	lis %r12, 21329
	ori %r12, %r12, 5191
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 29640
	ori %r12, %r12, 38182
	std %r12, 744(%r5)
	lis %r12, 3478
	ori %r12, %r12, 7098
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 58976
	ori %r12, %r12, 39695
	std %r12, 752(%r5)
	lis %r12, -31302
	ori %r12, %r12, 40880
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34100
	ori %r12, %r12, 47459
	std %r12, 760(%r5)
	lis %r12, -3654
	ori %r12, %r12, 27320
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 53295
	ori %r12, %r12, 39121
	std %r12, 768(%r5)
	lis %r12, -2908
	ori %r12, %r12, 29027
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34056
	ori %r12, %r12, 45860
	std %r12, 776(%r5)
	lis %r12, 10908
	ori %r12, %r12, 49787
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 33393
	ori %r12, %r12, 29197
	std %r12, 784(%r5)
	lis %r12, -20372
	ori %r12, %r12, 24718
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47306
	ori %r12, %r12, 10437
	std %r12, 792(%r5)
	lis %r12, 25431
	ori %r12, %r12, 43750
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 21880
	ori %r12, %r12, 48599
	std %r12, 800(%r5)
	lis %r12, 25523
	ori %r12, %r12, 31905
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4532
	ori %r12, %r12, 10837
	std %r12, 808(%r5)
	lis %r12, 10362
	ori %r12, %r12, 27823
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39886
	ori %r12, %r12, 29739
	std %r12, 816(%r5)
	lis %r12, 23880
	ori %r12, %r12, 64353
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26308
	ori %r12, %r12, 27451
	std %r12, 824(%r5)
	lis %r12, -31985
	ori %r12, %r12, 54051
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 60380
	ori %r12, %r12, 59887
	std %r12, 832(%r5)
	lis %r12, -21657
	ori %r12, %r12, 63009
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 40553
	ori %r12, %r12, 42030
	std %r12, 840(%r5)
	lis %r12, 32442
	ori %r12, %r12, 4974
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43926
	ori %r12, %r12, 55402
	std %r12, 848(%r5)
	lis %r12, 15229
	ori %r12, %r12, 17804
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 33382
	ori %r12, %r12, 14753
	std %r12, 856(%r5)
	lis %r12, 16923
	ori %r12, %r12, 13902
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 22080
	ori %r12, %r12, 34272
	std %r12, 864(%r5)
	lis %r12, -2523
	ori %r12, %r12, 32775
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 18907
	ori %r12, %r12, 53303
	std %r12, 872(%r5)
	lis %r12, 6494
	ori %r12, %r12, 16577
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1175
	ori %r12, %r12, 46819
	std %r12, 880(%r5)
	lis %r12, -20532
	ori %r12, %r12, 39789
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15123
	ori %r12, %r12, 15976
	std %r12, 888(%r5)
	lis %r12, -17966
	ori %r12, %r12, 17856
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6502
	ori %r12, %r12, 57022
	std %r12, 896(%r5)
	lis %r12, -9330
	ori %r12, %r12, 64359
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16598
	ori %r12, %r12, 6741
	std %r12, 904(%r5)
	lis %r12, 15955
	ori %r12, %r12, 64818
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44335
	ori %r12, %r12, 64828
	std %r12, 912(%r5)
	lis %r12, -29524
	ori %r12, %r12, 10453
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 57114
	ori %r12, %r12, 51870
	std %r12, 920(%r5)
	lis %r12, 11594
	ori %r12, %r12, 64784
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47329
	ori %r12, %r12, 47977
	std %r12, 928(%r5)
	lis %r12, -12702
	ori %r12, %r12, 42209
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 19410
	ori %r12, %r12, 46746
	std %r12, 936(%r5)
	lis %r12, 27626
	ori %r12, %r12, 44693
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11216
	ori %r12, %r12, 14063
	std %r12, 944(%r5)
	lis %r12, -28536
	ori %r12, %r12, 62095
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 36494
	ori %r12, %r12, 45008
	std %r12, 952(%r5)
	lis %r12, -29718
	ori %r12, %r12, 48687
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 46033
	ori %r12, %r12, 26703
	std %r12, 960(%r5)
	lis %r12, -11652
	ori %r12, %r12, 64948
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52760
	ori %r12, %r12, 46565
	std %r12, 968(%r5)
	lis %r12, -1081
	ori %r12, %r12, 30694
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8595
	ori %r12, %r12, 32790
	std %r12, 976(%r5)
	lis %r12, 22306
	ori %r12, %r12, 8192
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44758
	ori %r12, %r12, 31723
	std %r12, 984(%r5)
	lis %r12, 544
	ori %r12, %r12, 55672
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 22869
	ori %r12, %r12, 61476
	std %r12, 992(%r5)
	lis %r12, -26085
	ori %r12, %r12, 31667
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 19985
	ori %r12, %r12, 25219
	std %r12, 1000(%r5)
	lis %r12, 10994
	ori %r12, %r12, 22280
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 33067
	ori %r12, %r12, 48342
	std %r12, 1008(%r5)
	lis %r12, 28168
	ori %r12, %r12, 43347
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50687
	ori %r12, %r12, 59318
	std %r12, 1016(%r5)
	lis %r12, 26296
	ori %r12, %r12, 32176
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 9006
	ori %r12, %r12, 17641
	std %r12, 1024(%r5)
	lis %r12, 15936
	ori %r12, %r12, 10661
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 57708
	ori %r12, %r12, 65393
	std %r12, 1032(%r5)
	lis %r12, -15898
	ori %r12, %r12, 62727
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 54998
	ori %r12, %r12, 26010
	std %r12, 1040(%r5)
	lis %r12, -24300
	ori %r12, %r12, 51519
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24262
	ori %r12, %r12, 9862
	std %r12, 1048(%r5)
	lis %r12, -18196
	ori %r12, %r12, 23580
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 14085
	ori %r12, %r12, 34436
	std %r12, 1056(%r5)
	lis %r12, -17064
	ori %r12, %r12, 45594
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 65284
	ori %r12, %r12, 3383
	std %r12, 1064(%r5)
	lis %r12, -22732
	ori %r12, %r12, 56449
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 371
	ori %r12, %r12, 63225
	std %r12, 1072(%r5)
	lis %r12, 12705
	ori %r12, %r12, 12185
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16702
	ori %r12, %r12, 3654
	std %r12, 1080(%r5)
	lis %r12, -20622
	ori %r12, %r12, 31120
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 48899
	ori %r12, %r12, 2104
	std %r12, 1088(%r5)
	lis %r12, -30746
	ori %r12, %r12, 9247
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11794
	ori %r12, %r12, 4127
	std %r12, 1096(%r5)
	lis %r12, -11674
	ori %r12, %r12, 64058
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 36028
	ori %r12, %r12, 5912
	std %r12, 1104(%r5)
	lis %r12, -8958
	ori %r12, %r12, 20803
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5687
	ori %r12, %r12, 2119
	std %r12, 1112(%r5)
	lis %r12, 2363
	ori %r12, %r12, 27633
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39894
	ori %r12, %r12, 21918
	std %r12, 1120(%r5)
	lis %r12, -19702
	ori %r12, %r12, 45424
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28204
	ori %r12, %r12, 64237
	std %r12, 1128(%r5)
	lis %r12, 27256
	ori %r12, %r12, 9686
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4025
	ori %r12, %r12, 64028
	std %r12, 1136(%r5)
	lis %r12, 24591
	ori %r12, %r12, 15783
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 62547
	ori %r12, %r12, 30906
	std %r12, 1144(%r5)
	lis %r12, 10449
	ori %r12, %r12, 33685
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26222
	ori %r12, %r12, 46600
	std %r12, 1152(%r5)
	lis %r12, -31571
	ori %r12, %r12, 15119
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 645
	ori %r12, %r12, 42479
	std %r12, 1160(%r5)
	lis %r12, -12514
	ori %r12, %r12, 38448
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4213
	ori %r12, %r12, 28712
	std %r12, 1168(%r5)
	lis %r12, 28331
	ori %r12, %r12, 42940
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5131
	ori %r12, %r12, 14736
	std %r12, 1176(%r5)
	lis %r12, -2091
	ori %r12, %r12, 45874
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 20665
	ori %r12, %r12, 51887
	std %r12, 1184(%r5)
	lis %r12, -32417
	ori %r12, %r12, 30618
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43134
	ori %r12, %r12, 39193
	std %r12, 1192(%r5)
	lis %r12, -26881
	ori %r12, %r12, 25509
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39329
	ori %r12, %r12, 54825
	std %r12, 1200(%r5)
	lis %r12, 29537
	ori %r12, %r12, 60143
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10468
	ori %r12, %r12, 21739
	std %r12, 1208(%r5)
	lis %r12, -12267
	ori %r12, %r12, 60086
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 57364
	ori %r12, %r12, 58329
	std %r12, 1216(%r5)
	lis %r12, 20586
	ori %r12, %r12, 51102
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1309
	ori %r12, %r12, 46402
	std %r12, 1224(%r5)
	lis %r12, -31477
	ori %r12, %r12, 37571
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 41888
	ori %r12, %r12, 18162
	std %r12, 1232(%r5)
	lis %r12, 24894
	ori %r12, %r12, 59946
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 116
	ori %r12, %r12, 40192
	std %r12, 1240(%r5)
	lis %r12, 28327
	ori %r12, %r12, 24665
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 56305
	ori %r12, %r12, 16786
	std %r12, 1248(%r5)
	lis %r12, -8964
	ori %r12, %r12, 49834
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 13653
	ori %r12, %r12, 40580
	std %r12, 1256(%r5)
	lis %r12, 16505
	ori %r12, %r12, 52691
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 51461
	ori %r12, %r12, 33838
	std %r12, 1264(%r5)
	lis %r12, -2261
	ori %r12, %r12, 19175
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8350
	ori %r12, %r12, 55397
	std %r12, 1272(%r5)
	lis %r12, -19872
	ori %r12, %r12, 57254
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 9737
	ori %r12, %r12, 10608
	std %r12, 1280(%r5)
	lis %r12, 14867
	ori %r12, %r12, 19458
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 40530
	ori %r12, %r12, 6028
	std %r12, 1288(%r5)
	lis %r12, 23864
	ori %r12, %r12, 12444
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16356
	ori %r12, %r12, 40344
	std %r12, 1296(%r5)
	lis %r12, 28696
	ori %r12, %r12, 61291
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52457
	ori %r12, %r12, 60192
	std %r12, 1304(%r5)
	lis %r12, -3516
	ori %r12, %r12, 44676
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1875
	ori %r12, %r12, 57909
	std %r12, 1312(%r5)
	lis %r12, 8570
	ori %r12, %r12, 29941
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 45855
	ori %r12, %r12, 3290
	std %r12, 1320(%r5)
	lis %r12, -8842
	ori %r12, %r12, 56037
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 18247
	ori %r12, %r12, 12051
	std %r12, 1328(%r5)
	lis %r12, -19525
	ori %r12, %r12, 3789
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7879
	ori %r12, %r12, 865
	std %r12, 1336(%r5)
	lis %r12, -30288
	ori %r12, %r12, 31762
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1037
	ori %r12, %r12, 47499
	std %r12, 1344(%r5)
	lis %r12, -12835
	ori %r12, %r12, 29042
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16302
	ori %r12, %r12, 2167
	std %r12, 1352(%r5)
	lis %r12, -15549
	ori %r12, %r12, 7660
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 32154
	ori %r12, %r12, 55879
	std %r12, 1360(%r5)
	lis %r12, -7168
	ori %r12, %r12, 50253
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47675
	ori %r12, %r12, 55576
	std %r12, 1368(%r5)
	lis %r12, -23272
	ori %r12, %r12, 51030
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6519
	ori %r12, %r12, 20216
	std %r12, 1376(%r5)
	lis %r12, 10846
	ori %r12, %r12, 28485
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15551
	ori %r12, %r12, 64486
	std %r12, 1384(%r5)
	lis %r12, -19511
	ori %r12, %r12, 51337
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7644
	ori %r12, %r12, 1767
	std %r12, 1392(%r5)
	lis %r12, 31014
	ori %r12, %r12, 11086
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11580
	ori %r12, %r12, 59918
	std %r12, 1400(%r5)
	lis %r12, -201
	ori %r12, %r12, 51269
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8190
	ori %r12, %r12, 4775
	std %r12, 1408(%r5)
	lis %r12, 12157
	ori %r12, %r12, 38309
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 38945
	ori %r12, %r12, 23261
	std %r12, 1416(%r5)
	lis %r12, 25598
	ori %r12, %r12, 48552
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5447
	ori %r12, %r12, 25014
	std %r12, 1424(%r5)
	lis %r12, -31652
	ori %r12, %r12, 11398
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 56990
	ori %r12, %r12, 41564
	std %r12, 1432(%r5)
	lis %r12, -18199
	ori %r12, %r12, 46170
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47977
	ori %r12, %r12, 61470
	std %r12, 1440(%r5)
	lis %r12, 4755
	ori %r12, %r12, 11656
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 32153
	ori %r12, %r12, 40971
	std %r12, 1448(%r5)
	lis %r12, 18115
	ori %r12, %r12, 29316
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47839
	ori %r12, %r12, 8072
	std %r12, 1456(%r5)
	lis %r12, 15597
	ori %r12, %r12, 65522
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 12616
	ori %r12, %r12, 12298
	std %r12, 1464(%r5)
	lis %r12, 20303
	ori %r12, %r12, 44002
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4957
	ori %r12, %r12, 46868
	std %r12, 1472(%r5)
	lis %r12, 25159
	ori %r12, %r12, 19833
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8507
	ori %r12, %r12, 48116
	std %r12, 1480(%r5)
	lis %r12, -19830
	ori %r12, %r12, 29732
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 46723
	ori %r12, %r12, 9889
	std %r12, 1488(%r5)
	lis %r12, 28916
	ori %r12, %r12, 62861
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 3761
	ori %r12, %r12, 18623
	std %r12, 1496(%r5)
	lis %r12, 13042
	ori %r12, %r12, 29751
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15340
	ori %r12, %r12, 32496
	std %r12, 1504(%r5)
	lis %r12, -13653
	ori %r12, %r12, 1703
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 38872
	ori %r12, %r12, 20608
	std %r12, 1512(%r5)
	lis %r12, 17370
	ori %r12, %r12, 35035
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 40551
	ori %r12, %r12, 13434
	std %r12, 1520(%r5)
	lis %r12, -21089
	ori %r12, %r12, 15649
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 65528
	ori %r12, %r12, 14388
	std %r12, 1528(%r5)
	lis %r12, -4626
	ori %r12, %r12, 42862
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6517
	ori %r12, %r12, 45946
	std %r12, 1536(%r5)
	lis %r12, 6233
	ori %r12, %r12, 2358
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 45412
	ori %r12, %r12, 39594
	std %r12, 1544(%r5)
	lis %r12, 9517
	ori %r12, %r12, 59602
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63375
	ori %r12, %r12, 16980
	std %r12, 1552(%r5)
	lis %r12, 27287
	ori %r12, %r12, 47720
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7810
	ori %r12, %r12, 28893
	std %r12, 1560(%r5)
	lis %r12, 5757
	ori %r12, %r12, 56839
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 20636
	ori %r12, %r12, 41087
	std %r12, 1568(%r5)
	lis %r12, 2435
	ori %r12, %r12, 46348
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28
	ori %r12, %r12, 20538
	std %r12, 1576(%r5)
	lis %r12, -3147
	ori %r12, %r12, 49893
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 62770
	ori %r12, %r12, 43409
	std %r12, 1584(%r5)
	lis %r12, 16000
	ori %r12, %r12, 59960
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 30152
	ori %r12, %r12, 53316
	std %r12, 1592(%r5)
	lis %r12, -20615
	ori %r12, %r12, 38840
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 2626
	ori %r12, %r12, 27988
	std %r12, 1600(%r5)
	lis %r12, -31718
	ori %r12, %r12, 27410
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 53131
	ori %r12, %r12, 37786
	std %r12, 1608(%r5)
	lis %r12, 25609
	ori %r12, %r12, 34170
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 19359
	ori %r12, %r12, 2136
	std %r12, 1616(%r5)
	lis %r12, 14996
	ori %r12, %r12, 26017
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49731
	ori %r12, %r12, 5404
	std %r12, 1624(%r5)
	lis %r12, 9233
	ori %r12, %r12, 41781
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4524
	ori %r12, %r12, 12767
	std %r12, 1632(%r5)
	lis %r12, 15886
	ori %r12, %r12, 59875
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5562
	ori %r12, %r12, 61839
	std %r12, 1640(%r5)
	lis %r12, 4172
	ori %r12, %r12, 26174
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 59237
	ori %r12, %r12, 15647
	std %r12, 1648(%r5)
	lis %r12, -15815
	ori %r12, %r12, 7671
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 2812
	ori %r12, %r12, 57877
	std %r12, 1656(%r5)
	lis %r12, -29569
	ori %r12, %r12, 31676
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50093
	ori %r12, %r12, 4899
	std %r12, 1664(%r5)
	lis %r12, 28399
	ori %r12, %r12, 12238
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43864
	ori %r12, %r12, 27698
	std %r12, 1672(%r5)
	lis %r12, 820
	ori %r12, %r12, 25036
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 40925
	ori %r12, %r12, 1825
	std %r12, 1680(%r5)
	lis %r12, -3157
	ori %r12, %r12, 25292
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43678
	ori %r12, %r12, 28787
	std %r12, 1688(%r5)
	lis %r12, 8606
	ori %r12, %r12, 10856
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 23075
	ori %r12, %r12, 48523
	std %r12, 1696(%r5)
	lis %r12, 26861
	ori %r12, %r12, 58167
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15863
	ori %r12, %r12, 24404
	std %r12, 1704(%r5)
	lis %r12, -15741
	ori %r12, %r12, 8949
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 22750
	ori %r12, %r12, 58933
	std %r12, 1712(%r5)
	lis %r12, 31784
	ori %r12, %r12, 50923
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 48345
	ori %r12, %r12, 11955
	std %r12, 1720(%r5)
	lis %r12, -13460
	ori %r12, %r12, 43758
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15888
	ori %r12, %r12, 25674
	std %r12, 1728(%r5)
	lis %r12, -32437
	ori %r12, %r12, 34078
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52559
	ori %r12, %r12, 27202
	std %r12, 1736(%r5)
	lis %r12, -28028
	ori %r12, %r12, 51989
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 51080
	ori %r12, %r12, 36194
	std %r12, 1744(%r5)
	lis %r12, 16301
	ori %r12, %r12, 21826
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 33378
	ori %r12, %r12, 6491
	std %r12, 1752(%r5)
	lis %r12, 30597
	ori %r12, %r12, 61150
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8799
	ori %r12, %r12, 37746
	std %r12, 1760(%r5)
	lis %r12, 2820
	ori %r12, %r12, 3177
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 55791
	ori %r12, %r12, 63495
	std %r12, 1768(%r5)
	lis %r12, 26463
	ori %r12, %r12, 21875
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7893
	ori %r12, %r12, 17732
	std %r12, 1776(%r5)
	lis %r12, -31773
	ori %r12, %r12, 45118
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 27944
	ori %r12, %r12, 16068
	std %r12, 1784(%r5)
	lis %r12, -28772
	ori %r12, %r12, 18861
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50395
	ori %r12, %r12, 46411
	std %r12, 1792(%r5)
	lis %r12, -7008
	ori %r12, %r12, 29977
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49750
	ori %r12, %r12, 27116
	std %r12, 1800(%r5)
	lis %r12, -4019
	ori %r12, %r12, 61345
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39275
	ori %r12, %r12, 23359
	std %r12, 1808(%r5)
	lis %r12, 27452
	ori %r12, %r12, 15881
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 611
	ori %r12, %r12, 33868
	std %r12, 1816(%r5)
	lis %r12, 22414
	ori %r12, %r12, 32574
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43703
	ori %r12, %r12, 21096
	std %r12, 1824(%r5)
	lis %r12, -9179
	ori %r12, %r12, 15534
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 752
	ori %r12, %r12, 61616
	std %r12, 1832(%r5)
	lis %r12, -25912
	ori %r12, %r12, 14138
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8852
	ori %r12, %r12, 31953
	std %r12, 1840(%r5)
	lis %r12, 6194
	ori %r12, %r12, 15330
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 42220
	ori %r12, %r12, 4009
	std %r12, 1848(%r5)
	lis %r12, -17322
	ori %r12, %r12, 9260
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63087
	ori %r12, %r12, 20302
	std %r12, 1856(%r5)
	lis %r12, -24752
	ori %r12, %r12, 11861
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 56499
	ori %r12, %r12, 55774
	std %r12, 1864(%r5)
	lis %r12, -15261
	ori %r12, %r12, 56300
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 59836
	ori %r12, %r12, 29818
	std %r12, 1872(%r5)
	lis %r12, 4944
	ori %r12, %r12, 10770
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 9437
	ori %r12, %r12, 13039
	std %r12, 1880(%r5)
	lis %r12, 22844
	ori %r12, %r12, 55044
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24449
	ori %r12, %r12, 4209
	std %r12, 1888(%r5)
	lis %r12, 23174
	ori %r12, %r12, 60038
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7838
	ori %r12, %r12, 38898
	std %r12, 1896(%r5)
	lis %r12, -25554
	ori %r12, %r12, 21120
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39209
	ori %r12, %r12, 20087
	std %r12, 1904(%r5)
	lis %r12, 6425
	ori %r12, %r12, 14066
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7845
	ori %r12, %r12, 38086
	std %r12, 1912(%r5)
	lis %r12, 433
	ori %r12, %r12, 42723
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 60139
	ori %r12, %r12, 63314
	std %r12, 1920(%r5)
	lis %r12, 23338
	ori %r12, %r12, 56302
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26725
	ori %r12, %r12, 48835
	std %r12, 1928(%r5)
	lis %r12, -22013
	ori %r12, %r12, 60179
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25068
	ori %r12, %r12, 10517
	std %r12, 1936(%r5)
	lis %r12, -19812
	ori %r12, %r12, 24814
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52181
	ori %r12, %r12, 19637
	std %r12, 1944(%r5)
	lis %r12, -16335
	ori %r12, %r12, 15424
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26016
	ori %r12, %r12, 6500
	std %r12, 1952(%r5)
	lis %r12, 5649
	ori %r12, %r12, 38904
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25237
	ori %r12, %r12, 34715
	std %r12, 1960(%r5)
	lis %r12, 6811
	ori %r12, %r12, 6999
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 30870
	ori %r12, %r12, 50958
	std %r12, 1968(%r5)
	lis %r12, -4354
	ori %r12, %r12, 13400
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28047
	ori %r12, %r12, 21453
	std %r12, 1976(%r5)
	lis %r12, -1317
	ori %r12, %r12, 41797
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8258
	ori %r12, %r12, 59485
	std %r12, 1984(%r5)
	lis %r12, 15844
	ori %r12, %r12, 34520
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16741
	ori %r12, %r12, 61383
	std %r12, 1992(%r5)
	lis %r12, 22087
	ori %r12, %r12, 27007
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49660
	ori %r12, %r12, 23503
	std %r12, 2000(%r5)
	lis %r12, 8989
	ori %r12, %r12, 3160
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8980
	ori %r12, %r12, 44297
	std %r12, 2008(%r5)
	lis %r12, -12736
	ori %r12, %r12, 52092
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 27862
	ori %r12, %r12, 36147
	std %r12, 2016(%r5)
	lis %r12, -32678
	ori %r12, %r12, 50601
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25064
	ori %r12, %r12, 6566
	std %r12, 2024(%r5)
	lis %r12, -7321
	ori %r12, %r12, 4315
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 3837
	ori %r12, %r12, 50078
	std %r12, 2032(%r5)
	lis %r12, -9242
	ori %r12, %r12, 36629
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61757
	ori %r12, %r12, 29125
	std %r12, 2040(%r5)
	lis %r12, 26670
	ori %r12, %r12, 63479
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 13340
	ori %r12, %r12, 63336
	std %r12, 2048(%r5)
	lis %r12, 16500
	ori %r12, %r12, 17966
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44983
	ori %r12, %r12, 27249
	std %r12, 2056(%r5)
	lis %r12, 1232
	ori %r12, %r12, 34284
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 17875
	ori %r12, %r12, 44829
	std %r12, 2064(%r5)
	lis %r12, -1062
	ori %r12, %r12, 62501
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39654
	ori %r12, %r12, 16819
	std %r12, 2072(%r5)
	lis %r12, -18938
	ori %r12, %r12, 36002
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61092
	ori %r12, %r12, 98
	std %r12, 2080(%r5)
	lis %r12, -29781
	ori %r12, %r12, 47413
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 17049
	ori %r12, %r12, 60540
	std %r12, 2088(%r5)
	lis %r12, -1033
	ori %r12, %r12, 12916
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 45617
	ori %r12, %r12, 22263
	std %r12, 2096(%r5)
	lis %r12, 19383
	ori %r12, %r12, 34618
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10156
	ori %r12, %r12, 38734
	std %r12, 2104(%r5)
	lis %r12, 31772
	ori %r12, %r12, 63830
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 13155
	ori %r12, %r12, 22716
	std %r12, 2112(%r5)
	lis %r12, -9153
	ori %r12, %r12, 8776
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 58204
	ori %r12, %r12, 28674
	std %r12, 2120(%r5)
	lis %r12, 25743
	ori %r12, %r12, 53739
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6052
	ori %r12, %r12, 4078
	std %r12, 2128(%r5)
	lis %r12, 5585
	ori %r12, %r12, 40642
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7075
	ori %r12, %r12, 24628
	std %r12, 2136(%r5)
	lis %r12, 10380
	ori %r12, %r12, 39182
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8802
	ori %r12, %r12, 57824
	std %r12, 2144(%r5)
	lis %r12, 7719
	ori %r12, %r12, 64111
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61538
	ori %r12, %r12, 64837
	std %r12, 2152(%r5)
	lis %r12, 3404
	ori %r12, %r12, 63584
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 14251
	ori %r12, %r12, 29761
	std %r12, 2160(%r5)
	lis %r12, 2962
	ori %r12, %r12, 41927
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1083
	ori %r12, %r12, 14096
	std %r12, 2168(%r5)
	lis %r12, -5185
	ori %r12, %r12, 9352
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 41739
	ori %r12, %r12, 40187
	std %r12, 2176(%r5)
	lis %r12, 7372
	ori %r12, %r12, 15271
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11671
	ori %r12, %r12, 31155
	std %r12, 2184(%r5)
	lis %r12, -13864
	ori %r12, %r12, 64024
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 20710
	ori %r12, %r12, 59191
	std %r12, 2192(%r5)
	lis %r12, -376
	ori %r12, %r12, 24398
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10862
	ori %r12, %r12, 34393
	std %r12, 2200(%r5)
	lis %r12, -13308
	ori %r12, %r12, 45126
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 19960
	ori %r12, %r12, 34391
	std %r12, 2208(%r5)
	lis %r12, 24985
	ori %r12, %r12, 9406
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24455
	ori %r12, %r12, 28979
	std %r12, 2216(%r5)
	lis %r12, -18091
	ori %r12, %r12, 29891
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49720
	ori %r12, %r12, 41615
	std %r12, 2224(%r5)
	lis %r12, 19601
	ori %r12, %r12, 28814
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 57977
	ori %r12, %r12, 33889
	std %r12, 2232(%r5)
	lis %r12, 13217
	ori %r12, %r12, 2486
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 40520
	ori %r12, %r12, 53473
	std %r12, 2240(%r5)
	lis %r12, 26895
	ori %r12, %r12, 57117
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4133
	ori %r12, %r12, 35842
	std %r12, 2248(%r5)
	lis %r12, 10180
	ori %r12, %r12, 64001
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 21147
	ori %r12, %r12, 65155
	std %r12, 2256(%r5)
	lis %r12, 25258
	ori %r12, %r12, 57384
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 46342
	ori %r12, %r12, 16679
	std %r12, 2264(%r5)
	lis %r12, 30369
	ori %r12, %r12, 56918
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 13460
	ori %r12, %r12, 25559
	std %r12, 2272(%r5)
	lis %r12, -844
	ori %r12, %r12, 47455
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 9277
	ori %r12, %r12, 34825
	std %r12, 2280(%r5)
	lis %r12, 15577
	ori %r12, %r12, 63582
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50387
	ori %r12, %r12, 46456
	std %r12, 2288(%r5)
	lis %r12, -8050
	ori %r12, %r12, 4660
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 14286
	ori %r12, %r12, 50407
	std %r12, 2296(%r5)
	lis %r12, 107
	ori %r12, %r12, 54304
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10534
	ori %r12, %r12, 16474
	std %r12, 2304(%r5)
	lis %r12, -30641
	ori %r12, %r12, 17910
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25044
	ori %r12, %r12, 62500
	std %r12, 2312(%r5)
	lis %r12, -31379
	ori %r12, %r12, 38665
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 12253
	ori %r12, %r12, 37372
	std %r12, 2320(%r5)
	lis %r12, 28038
	ori %r12, %r12, 10616
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 2631
	ori %r12, %r12, 14631
	std %r12, 2328(%r5)
	lis %r12, -10528
	ori %r12, %r12, 44542
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 36288
	ori %r12, %r12, 26900
	std %r12, 2336(%r5)
	lis %r12, 20183
	ori %r12, %r12, 34206
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10915
	ori %r12, %r12, 24350
	std %r12, 2344(%r5)
	lis %r12, 8423
	ori %r12, %r12, 17402
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 38758
	ori %r12, %r12, 6394
	std %r12, 2352(%r5)
	lis %r12, -27223
	ori %r12, %r12, 36154
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 38230
	ori %r12, %r12, 46069
	std %r12, 2360(%r5)
	lis %r12, 12670
	ori %r12, %r12, 9546
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 56105
	ori %r12, %r12, 39527
	std %r12, 2368(%r5)
	lis %r12, -31213
	ori %r12, %r12, 27925
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11285
	ori %r12, %r12, 12264
	std %r12, 2376(%r5)
	lis %r12, 13761
	ori %r12, %r12, 49233
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28281
	ori %r12, %r12, 8137
	std %r12, 2384(%r5)
	lis %r12, -32433
	ori %r12, %r12, 12980
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 27880
	ori %r12, %r12, 40056
	std %r12, 2392(%r5)
	lis %r12, -2292
	ori %r12, %r12, 3490
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47371
	ori %r12, %r12, 37525
	std %r12, 2400(%r5)
	lis %r12, -29187
	ori %r12, %r12, 18595
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 62728
	ori %r12, %r12, 38008
	std %r12, 2408(%r5)
	lis %r12, 27617
	ori %r12, %r12, 56796
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 64878
	ori %r12, %r12, 65379
	std %r12, 2416(%r5)
	lis %r12, -4849
	ori %r12, %r12, 65293
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 59604
	ori %r12, %r12, 11349
	std %r12, 2424(%r5)
	lis %r12, -10631
	ori %r12, %r12, 44335
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24271
	ori %r12, %r12, 32159
	std %r12, 2432(%r5)
	lis %r12, -3764
	ori %r12, %r12, 11181
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 12770
	ori %r12, %r12, 22830
	std %r12, 2440(%r5)
	lis %r12, -15427
	ori %r12, %r12, 60688
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25531
	ori %r12, %r12, 20802
	std %r12, 2448(%r5)
	lis %r12, -15383
	ori %r12, %r12, 43111
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 60140
	ori %r12, %r12, 4886
	std %r12, 2456(%r5)
	lis %r12, -850
	ori %r12, %r12, 8067
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24699
	ori %r12, %r12, 49280
	std %r12, 2464(%r5)
	lis %r12, 11842
	ori %r12, %r12, 44631
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24129
	ori %r12, %r12, 43883
	std %r12, 2472(%r5)
	lis %r12, -9742
	ori %r12, %r12, 36601
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 48623
	ori %r12, %r12, 65012
	std %r12, 2480(%r5)
	lis %r12, -8619
	ori %r12, %r12, 22361
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 38158
	ori %r12, %r12, 57126
	std %r12, 2488(%r5)
	lis %r12, 17929
	ori %r12, %r12, 56345
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43362
	ori %r12, %r12, 1452
	std %r12, 2496(%r5)
	lis %r12, -3598
	ori %r12, %r12, 42045
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 65184
	ori %r12, %r12, 48671
	std %r12, 2504(%r5)
	lis %r12, -12107
	ori %r12, %r12, 33630
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 32718
	ori %r12, %r12, 1754
	std %r12, 2512(%r5)
	lis %r12, 32088
	ori %r12, %r12, 34426
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1612
	ori %r12, %r12, 34444
	std %r12, 2520(%r5)
	lis %r12, 7549
	ori %r12, %r12, 46830
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5853
	ori %r12, %r12, 60062
	std %r12, 2528(%r5)
	lis %r12, -18341
	ori %r12, %r12, 40306
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 31754
	ori %r12, %r12, 484
	std %r12, 2536(%r5)
	lis %r12, 4884
	ori %r12, %r12, 59119
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 3964
	ori %r12, %r12, 42325
	std %r12, 2544(%r5)
	lis %r12, 250
	ori %r12, %r12, 33330
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 51391
	ori %r12, %r12, 20167
	std %r12, 2552(%r5)
	lis %r12, -23820
	ori %r12, %r12, 533
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26956
	ori %r12, %r12, 33085
	std %r12, 2560(%r5)
	lis %r12, -29919
	ori %r12, %r12, 9273
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 183
	ori %r12, %r12, 8200
	std %r12, 2568(%r5)
	lis %r12, -13396
	ori %r12, %r12, 48572
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 41204
	ori %r12, %r12, 46485
	std %r12, 2576(%r5)
	lis %r12, -18900
	ori %r12, %r12, 1104
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 51749
	ori %r12, %r12, 65003
	std %r12, 2584(%r5)
	lis %r12, -2932
	ori %r12, %r12, 34623
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 41230
	ori %r12, %r12, 18652
	std %r12, 2592(%r5)
	lis %r12, 4665
	ori %r12, %r12, 62462
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 27512
	ori %r12, %r12, 14286
	std %r12, 2600(%r5)
	lis %r12, 30785
	ori %r12, %r12, 23406
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 58275
	ori %r12, %r12, 28105
	std %r12, 2608(%r5)
	lis %r12, -27029
	ori %r12, %r12, 33619
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 18496
	ori %r12, %r12, 65034
	std %r12, 2616(%r5)
	lis %r12, 10740
	ori %r12, %r12, 12586
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 57769
	ori %r12, %r12, 5544
	std %r12, 2624(%r5)
	lis %r12, 4033
	ori %r12, %r12, 50881
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10427
	ori %r12, %r12, 10232
	std %r12, 2632(%r5)
	lis %r12, 4540
	ori %r12, %r12, 39775
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34887
	ori %r12, %r12, 1273
	std %r12, 2640(%r5)
	lis %r12, -11930
	ori %r12, %r12, 57618
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25592
	ori %r12, %r12, 10875
	std %r12, 2648(%r5)
	lis %r12, -23950
	ori %r12, %r12, 47794
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 48676
	ori %r12, %r12, 15907
	std %r12, 2656(%r5)
	lis %r12, 16029
	ori %r12, %r12, 32073
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52349
	ori %r12, %r12, 46866
	std %r12, 2664(%r5)
	lis %r12, 28187
	ori %r12, %r12, 60178
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63599
	ori %r12, %r12, 11847
	std %r12, 2672(%r5)
	lis %r12, 3897
	ori %r12, %r12, 41
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 53349
	ori %r12, %r12, 26491
	std %r12, 2680(%r5)
	lis %r12, 15252
	ori %r12, %r12, 23315
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5521
	ori %r12, %r12, 56187
	std %r12, 2688(%r5)
	lis %r12, 11893
	ori %r12, %r12, 27202
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11814
	ori %r12, %r12, 4409
	std %r12, 2696(%r5)
	lis %r12, -7899
	ori %r12, %r12, 51819
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 64417
	ori %r12, %r12, 37394
	std %r12, 2704(%r5)
	lis %r12, -6977
	ori %r12, %r12, 34479
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43788
	ori %r12, %r12, 4674
	std %r12, 2712(%r5)
	lis %r12, 13893
	ori %r12, %r12, 14589
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 888
	ori %r12, %r12, 63420
	std %r12, 2720(%r5)
	lis %r12, 22598
	ori %r12, %r12, 59552
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 128
	ori %r12, %r12, 7746
	std %r12, 2728(%r5)
	lis %r12, -907
	ori %r12, %r12, 45926
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 35188
	ori %r12, %r12, 56664
	std %r12, 2736(%r5)
	lis %r12, 725
	ori %r12, %r12, 46190
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24426
	ori %r12, %r12, 7659
	std %r12, 2744(%r5)
	lis %r12, 12845
	ori %r12, %r12, 43391
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 29864
	ori %r12, %r12, 33291
	std %r12, 2752(%r5)
	lis %r12, 26758
	ori %r12, %r12, 42425
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28313
	ori %r12, %r12, 61530
	std %r12, 2760(%r5)
	lis %r12, -6654
	ori %r12, %r12, 1553
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52706
	ori %r12, %r12, 14775
	std %r12, 2768(%r5)
	lis %r12, -9120
	ori %r12, %r12, 62743
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43104
	ori %r12, %r12, 16376
	std %r12, 2776(%r5)
	lis %r12, 23036
	ori %r12, %r12, 48331
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49858
	ori %r12, %r12, 14566
	std %r12, 2784(%r5)
	lis %r12, -24895
	ori %r12, %r12, 19939
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37490
	ori %r12, %r12, 31749
	std %r12, 2792(%r5)
	lis %r12, 20869
	ori %r12, %r12, 24912
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44349
	ori %r12, %r12, 64596
	std %r12, 2800(%r5)
	lis %r12, 24590
	ori %r12, %r12, 25498
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50730
	ori %r12, %r12, 57813
	std %r12, 2808(%r5)
	lis %r12, -11076
	ori %r12, %r12, 30273
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 38134
	ori %r12, %r12, 38121
	std %r12, 2816(%r5)
	lis %r12, -16620
	ori %r12, %r12, 38686
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 20547
	ori %r12, %r12, 13268
	std %r12, 2824(%r5)
	lis %r12, 12671
	ori %r12, %r12, 959
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26224
	ori %r12, %r12, 38477
	std %r12, 2832(%r5)
	lis %r12, -5878
	ori %r12, %r12, 21288
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43994
	ori %r12, %r12, 21910
	std %r12, 2840(%r5)
	lis %r12, 31413
	ori %r12, %r12, 59471
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10088
	ori %r12, %r12, 55144
	std %r12, 2848(%r5)
	lis %r12, 15342
	ori %r12, %r12, 55584
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16590
	ori %r12, %r12, 54186
	std %r12, 2856(%r5)
	lis %r12, -13720
	ori %r12, %r12, 56634
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 59942
	ori %r12, %r12, 19229
	std %r12, 2864(%r5)
	lis %r12, -12034
	ori %r12, %r12, 8277
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47685
	ori %r12, %r12, 55547
	std %r12, 2872(%r5)
	lis %r12, -28578
	ori %r12, %r12, 16294
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39372
	ori %r12, %r12, 41301
	std %r12, 2880(%r5)
	lis %r12, -14520
	ori %r12, %r12, 58517
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1408
	ori %r12, %r12, 1277
	std %r12, 2888(%r5)
	lis %r12, 16882
	ori %r12, %r12, 54578
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 23872
	ori %r12, %r12, 16647
	std %r12, 2896(%r5)
	lis %r12, -13649
	ori %r12, %r12, 526
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8159
	ori %r12, %r12, 24613
	std %r12, 2904(%r5)
	lis %r12, 11742
	ori %r12, %r12, 59013
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 60987
	ori %r12, %r12, 13163
	std %r12, 2912(%r5)
	lis %r12, -3133
	ori %r12, %r12, 34644
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 59236
	ori %r12, %r12, 38352
	std %r12, 2920(%r5)
	lis %r12, -9319
	ori %r12, %r12, 41384
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 62522
	ori %r12, %r12, 39178
	std %r12, 2928(%r5)
	lis %r12, 27061
	ori %r12, %r12, 52465
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 56359
	ori %r12, %r12, 28102
	std %r12, 2936(%r5)
	lis %r12, 30331
	ori %r12, %r12, 20923
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 55712
	ori %r12, %r12, 52838
	std %r12, 2944(%r5)
	lis %r12, 30738
	ori %r12, %r12, 50792
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 62592
	ori %r12, %r12, 52279
	std %r12, 2952(%r5)
	lis %r12, -7619
	ori %r12, %r12, 4378
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 19206
	ori %r12, %r12, 46954
	std %r12, 2960(%r5)
	lis %r12, 25790
	ori %r12, %r12, 55908
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 54745
	ori %r12, %r12, 2628
	std %r12, 2968(%r5)
	lis %r12, -10377
	ori %r12, %r12, 63185
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24672
	ori %r12, %r12, 61597
	std %r12, 2976(%r5)
	lis %r12, -16555
	ori %r12, %r12, 48503
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15536
	ori %r12, %r12, 61571
	std %r12, 2984(%r5)
	lis %r12, 18100
	ori %r12, %r12, 51283
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 34804
	ori %r12, %r12, 62030
	std %r12, 2992(%r5)
	lis %r12, -13940
	ori %r12, %r12, 8262
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37252
	ori %r12, %r12, 35706
	std %r12, 3000(%r5)
	lis %r12, -15258
	ori %r12, %r12, 57527
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 29969
	ori %r12, %r12, 48057
	std %r12, 3008(%r5)
	lis %r12, 10401
	ori %r12, %r12, 2842
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7498
	ori %r12, %r12, 2536
	std %r12, 3016(%r5)
	lis %r12, 3488
	ori %r12, %r12, 42832
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 20385
	ori %r12, %r12, 22492
	std %r12, 3024(%r5)
	lis %r12, 12288
	ori %r12, %r12, 49392
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25027
	ori %r12, %r12, 30618
	std %r12, 3032(%r5)
	lis %r12, -12565
	ori %r12, %r12, 37051
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49747
	ori %r12, %r12, 8977
	std %r12, 3040(%r5)
	lis %r12, -11494
	ori %r12, %r12, 29318
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 31801
	ori %r12, %r12, 19311
	std %r12, 3048(%r5)
	lis %r12, 27810
	ori %r12, %r12, 45342
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 19928
	ori %r12, %r12, 2285
	std %r12, 3056(%r5)
	lis %r12, 16487
	ori %r12, %r12, 37591
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 56630
	ori %r12, %r12, 22127
	std %r12, 3064(%r5)
	lis %r12, -16832
	ori %r12, %r12, 17054
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 6967
	ori %r12, %r12, 53047
	std %r12, 3072(%r5)
	lis %r12, -19266
	ori %r12, %r12, 17771
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 31614
	ori %r12, %r12, 5533
	std %r12, 3080(%r5)
	lis %r12, -14819
	ori %r12, %r12, 32238
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 51410
	ori %r12, %r12, 31023
	std %r12, 3088(%r5)
	lis %r12, 8930
	ori %r12, %r12, 39664
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1256
	ori %r12, %r12, 20699
	std %r12, 3096(%r5)
	lis %r12, -10672
	ori %r12, %r12, 19898
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 42154
	ori %r12, %r12, 63160
	std %r12, 3104(%r5)
	lis %r12, 22889
	ori %r12, %r12, 56019
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 59782
	ori %r12, %r12, 57849
	std %r12, 3112(%r5)
	lis %r12, 20953
	ori %r12, %r12, 38746
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37805
	ori %r12, %r12, 277
	std %r12, 3120(%r5)
	lis %r12, 19570
	ori %r12, %r12, 39887
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10454
	ori %r12, %r12, 32058
	std %r12, 3128(%r5)
	lis %r12, 10281
	ori %r12, %r12, 52365
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 39933
	ori %r12, %r12, 58993
	std %r12, 3136(%r5)
	lis %r12, -17115
	ori %r12, %r12, 47828
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 35908
	ori %r12, %r12, 21905
	std %r12, 3144(%r5)
	lis %r12, 6651
	ori %r12, %r12, 62875
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10988
	ori %r12, %r12, 41493
	std %r12, 3152(%r5)
	lis %r12, 24423
	ori %r12, %r12, 63505
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 48002
	ori %r12, %r12, 62760
	std %r12, 3160(%r5)
	lis %r12, 12900
	ori %r12, %r12, 52930
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37218
	ori %r12, %r12, 36433
	std %r12, 3168(%r5)
	lis %r12, 26365
	ori %r12, %r12, 9232
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 32873
	ori %r12, %r12, 18046
	std %r12, 3176(%r5)
	lis %r12, -17537
	ori %r12, %r12, 16605
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44751
	ori %r12, %r12, 56586
	std %r12, 3184(%r5)
	lis %r12, 18350
	ori %r12, %r12, 48040
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 54596
	ori %r12, %r12, 17790
	std %r12, 3192(%r5)
	lis %r12, 23921
	ori %r12, %r12, 22413
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28699
	ori %r12, %r12, 40547
	std %r12, 3200(%r5)
	lis %r12, 18612
	ori %r12, %r12, 7464
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 33898
	ori %r12, %r12, 52232
	std %r12, 3208(%r5)
	lis %r12, -17109
	ori %r12, %r12, 56497
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63563
	ori %r12, %r12, 33410
	std %r12, 3216(%r5)
	lis %r12, -14397
	ori %r12, %r12, 63102
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 51639
	ori %r12, %r12, 19425
	std %r12, 3224(%r5)
	lis %r12, 20348
	ori %r12, %r12, 26410
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 14539
	ori %r12, %r12, 39497
	std %r12, 3232(%r5)
	lis %r12, 9585
	ori %r12, %r12, 10796
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 40191
	ori %r12, %r12, 15031
	std %r12, 3240(%r5)
	lis %r12, 16997
	ori %r12, %r12, 3166
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 53593
	ori %r12, %r12, 60257
	std %r12, 3248(%r5)
	lis %r12, 7723
	ori %r12, %r12, 57138
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25790
	ori %r12, %r12, 15118
	std %r12, 3256(%r5)
	lis %r12, 7495
	ori %r12, %r12, 11917
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 55328
	ori %r12, %r12, 35905
	std %r12, 3264(%r5)
	lis %r12, -26171
	ori %r12, %r12, 1382
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 28623
	ori %r12, %r12, 37204
	std %r12, 3272(%r5)
	lis %r12, -13161
	ori %r12, %r12, 46434
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 561
	ori %r12, %r12, 9047
	std %r12, 3280(%r5)
	lis %r12, -26106
	ori %r12, %r12, 2749
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5147
	ori %r12, %r12, 53394
	std %r12, 3288(%r5)
	lis %r12, 11132
	ori %r12, %r12, 8709
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63202
	ori %r12, %r12, 253
	std %r12, 3296(%r5)
	lis %r12, 24773
	ori %r12, %r12, 30364
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61536
	ori %r12, %r12, 54208
	std %r12, 3304(%r5)
	lis %r12, -1564
	ori %r12, %r12, 35932
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 32432
	ori %r12, %r12, 55374
	std %r12, 3312(%r5)
	lis %r12, -6429
	ori %r12, %r12, 23346
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 40749
	ori %r12, %r12, 41065
	std %r12, 3320(%r5)
	lis %r12, -25817
	ori %r12, %r12, 14183
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11639
	ori %r12, %r12, 62926
	std %r12, 3328(%r5)
	lis %r12, 28337
	ori %r12, %r12, 36891
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50204
	ori %r12, %r12, 29582
	std %r12, 3336(%r5)
	lis %r12, 19722
	ori %r12, %r12, 57080
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49782
	ori %r12, %r12, 28331
	std %r12, 3344(%r5)
	lis %r12, -4468
	ori %r12, %r12, 20949
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 58150
	ori %r12, %r12, 18107
	std %r12, 3352(%r5)
	lis %r12, 23317
	ori %r12, %r12, 27233
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 53251
	ori %r12, %r12, 11970
	std %r12, 3360(%r5)
	lis %r12, 2671
	ori %r12, %r12, 63471
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25237
	ori %r12, %r12, 15010
	std %r12, 3368(%r5)
	lis %r12, -29769
	ori %r12, %r12, 55293
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 58854
	ori %r12, %r12, 34473
	std %r12, 3376(%r5)
	lis %r12, -2636
	ori %r12, %r12, 47141
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 11582
	ori %r12, %r12, 42668
	std %r12, 3384(%r5)
	lis %r12, 11878
	ori %r12, %r12, 22468
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 64172
	ori %r12, %r12, 42412
	std %r12, 3392(%r5)
	lis %r12, -3999
	ori %r12, %r12, 28013
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24078
	ori %r12, %r12, 24577
	std %r12, 3400(%r5)
	lis %r12, -3226
	ori %r12, %r12, 8557
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 1818
	ori %r12, %r12, 22430
	std %r12, 3408(%r5)
	lis %r12, -28079
	ori %r12, %r12, 55671
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15412
	ori %r12, %r12, 64985
	std %r12, 3416(%r5)
	lis %r12, -16690
	ori %r12, %r12, 31632
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63832
	ori %r12, %r12, 56343
	std %r12, 3424(%r5)
	lis %r12, 8493
	ori %r12, %r12, 45576
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 58963
	ori %r12, %r12, 15843
	std %r12, 3432(%r5)
	lis %r12, -7423
	ori %r12, %r12, 36343
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 51422
	ori %r12, %r12, 49222
	std %r12, 3440(%r5)
	lis %r12, 28434
	ori %r12, %r12, 33998
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52490
	ori %r12, %r12, 65386
	std %r12, 3448(%r5)
	lis %r12, 32022
	ori %r12, %r12, 4877
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25463
	ori %r12, %r12, 24036
	std %r12, 3456(%r5)
	lis %r12, -24417
	ori %r12, %r12, 14852
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44870
	ori %r12, %r12, 58059
	std %r12, 3464(%r5)
	lis %r12, 9593
	ori %r12, %r12, 16224
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10013
	ori %r12, %r12, 43835
	std %r12, 3472(%r5)
	lis %r12, -21999
	ori %r12, %r12, 53704
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47817
	ori %r12, %r12, 31033
	std %r12, 3480(%r5)
	lis %r12, 11057
	ori %r12, %r12, 14019
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 56030
	ori %r12, %r12, 48519
	std %r12, 3488(%r5)
	lis %r12, 5628
	ori %r12, %r12, 64546
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 17689
	ori %r12, %r12, 47961
	std %r12, 3496(%r5)
	lis %r12, -23472
	ori %r12, %r12, 27143
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43108
	ori %r12, %r12, 40083
	std %r12, 3504(%r5)
	lis %r12, -3532
	ori %r12, %r12, 37525
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 59808
	ori %r12, %r12, 56174
	std %r12, 3512(%r5)
	lis %r12, -3729
	ori %r12, %r12, 12191
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 12913
	ori %r12, %r12, 13428
	std %r12, 3520(%r5)
	lis %r12, 8914
	ori %r12, %r12, 7601
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 32377
	ori %r12, %r12, 55514
	std %r12, 3528(%r5)
	lis %r12, 29494
	ori %r12, %r12, 60289
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52533
	ori %r12, %r12, 30451
	std %r12, 3536(%r5)
	lis %r12, 31696
	ori %r12, %r12, 5319
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 22160
	ori %r12, %r12, 18786
	std %r12, 3544(%r5)
	lis %r12, -25393
	ori %r12, %r12, 617
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 53951
	ori %r12, %r12, 3923
	std %r12, 3552(%r5)
	lis %r12, 24737
	ori %r12, %r12, 52768
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 44477
	ori %r12, %r12, 58174
	std %r12, 3560(%r5)
	lis %r12, -7830
	ori %r12, %r12, 35522
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43769
	ori %r12, %r12, 36350
	std %r12, 3568(%r5)
	lis %r12, 29407
	ori %r12, %r12, 57953
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 58917
	ori %r12, %r12, 57080
	std %r12, 3576(%r5)
	lis %r12, -17278
	ori %r12, %r12, 41904
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50626
	ori %r12, %r12, 64057
	std %r12, 3584(%r5)
	lis %r12, 13934
	ori %r12, %r12, 41356
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 45
	ori %r12, %r12, 3857
	std %r12, 3592(%r5)
	lis %r12, -12173
	ori %r12, %r12, 36111
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 18851
	ori %r12, %r12, 37960
	std %r12, 3600(%r5)
	lis %r12, -30993
	ori %r12, %r12, 11770
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 24213
	ori %r12, %r12, 47673
	std %r12, 3608(%r5)
	lis %r12, 25829
	ori %r12, %r12, 59840
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61982
	ori %r12, %r12, 9353
	std %r12, 3616(%r5)
	lis %r12, -1532
	ori %r12, %r12, 21039
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 21929
	ori %r12, %r12, 14886
	std %r12, 3624(%r5)
	lis %r12, 11248
	ori %r12, %r12, 13456
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15881
	ori %r12, %r12, 45284
	std %r12, 3632(%r5)
	lis %r12, -30506
	ori %r12, %r12, 62111
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 32207
	ori %r12, %r12, 32213
	std %r12, 3640(%r5)
	lis %r12, 5077
	ori %r12, %r12, 15315
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37808
	ori %r12, %r12, 6441
	std %r12, 3648(%r5)
	lis %r12, 25761
	ori %r12, %r12, 62469
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 54166
	ori %r12, %r12, 30047
	std %r12, 3656(%r5)
	lis %r12, -9060
	ori %r12, %r12, 25407
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 14887
	ori %r12, %r12, 37099
	std %r12, 3664(%r5)
	lis %r12, -21044
	ori %r12, %r12, 2641
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47702
	ori %r12, %r12, 21811
	std %r12, 3672(%r5)
	lis %r12, 20257
	ori %r12, %r12, 15994
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8349
	ori %r12, %r12, 12520
	std %r12, 3680(%r5)
	lis %r12, 1925
	ori %r12, %r12, 28078
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5086
	ori %r12, %r12, 10678
	std %r12, 3688(%r5)
	lis %r12, -19246
	ori %r12, %r12, 22718
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 8300
	ori %r12, %r12, 17818
	std %r12, 3696(%r5)
	lis %r12, 15462
	ori %r12, %r12, 25834
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 46133
	ori %r12, %r12, 22946
	std %r12, 3704(%r5)
	lis %r12, 21362
	ori %r12, %r12, 23310
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 20162
	ori %r12, %r12, 12187
	std %r12, 3712(%r5)
	lis %r12, 28344
	ori %r12, %r12, 39088
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 5586
	ori %r12, %r12, 46144
	std %r12, 3720(%r5)
	lis %r12, 17722
	ori %r12, %r12, 37653
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 29210
	ori %r12, %r12, 8255
	std %r12, 3728(%r5)
	lis %r12, -6143
	ori %r12, %r12, 50972
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7986
	ori %r12, %r12, 52872
	std %r12, 3736(%r5)
	lis %r12, -19975
	ori %r12, %r12, 37177
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 2778
	ori %r12, %r12, 20368
	std %r12, 3744(%r5)
	lis %r12, -27503
	ori %r12, %r12, 59031
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 55765
	ori %r12, %r12, 62878
	std %r12, 3752(%r5)
	lis %r12, 978
	ori %r12, %r12, 1473
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 47784
	ori %r12, %r12, 46821
	std %r12, 3760(%r5)
	lis %r12, 29088
	ori %r12, %r12, 54047
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 30872
	ori %r12, %r12, 39148
	std %r12, 3768(%r5)
	lis %r12, -7413
	ori %r12, %r12, 39221
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 30398
	ori %r12, %r12, 41738
	std %r12, 3776(%r5)
	lis %r12, -1137
	ori %r12, %r12, 11288
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15970
	ori %r12, %r12, 55884
	std %r12, 3784(%r5)
	lis %r12, -11754
	ori %r12, %r12, 30192
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52392
	ori %r12, %r12, 12835
	std %r12, 3792(%r5)
	lis %r12, -3359
	ori %r12, %r12, 31430
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50768
	ori %r12, %r12, 47510
	std %r12, 3800(%r5)
	lis %r12, 30411
	ori %r12, %r12, 1042
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 48421
	ori %r12, %r12, 43178
	std %r12, 3808(%r5)
	lis %r12, 30127
	ori %r12, %r12, 17976
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 18347
	ori %r12, %r12, 16401
	std %r12, 3816(%r5)
	lis %r12, -5181
	ori %r12, %r12, 64328
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63914
	ori %r12, %r12, 59595
	std %r12, 3824(%r5)
	lis %r12, -15473
	ori %r12, %r12, 30542
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 2057
	ori %r12, %r12, 23764
	std %r12, 3832(%r5)
	lis %r12, -26157
	ori %r12, %r12, 20316
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 23211
	ori %r12, %r12, 54074
	std %r12, 3840(%r5)
	lis %r12, 27314
	ori %r12, %r12, 8631
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 51158
	ori %r12, %r12, 49109
	std %r12, 3848(%r5)
	lis %r12, 19669
	ori %r12, %r12, 18003
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 26054
	ori %r12, %r12, 48215
	std %r12, 3856(%r5)
	lis %r12, -26013
	ori %r12, %r12, 27297
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 48812
	ori %r12, %r12, 43305
	std %r12, 3864(%r5)
	lis %r12, -17777
	ori %r12, %r12, 39811
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 40101
	ori %r12, %r12, 17344
	std %r12, 3872(%r5)
	lis %r12, 30527
	ori %r12, %r12, 63431
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 61259
	ori %r12, %r12, 42792
	std %r12, 3880(%r5)
	lis %r12, 556
	ori %r12, %r12, 40681
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 15259
	ori %r12, %r12, 34688
	std %r12, 3888(%r5)
	lis %r12, 23130
	ori %r12, %r12, 44319
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 31953
	ori %r12, %r12, 406
	std %r12, 3896(%r5)
	lis %r12, 31224
	ori %r12, %r12, 10472
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 60743
	ori %r12, %r12, 57568
	std %r12, 3904(%r5)
	lis %r12, 1283
	ori %r12, %r12, 34837
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 58359
	ori %r12, %r12, 60792
	std %r12, 3912(%r5)
	lis %r12, 9973
	ori %r12, %r12, 7707
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 43415
	ori %r12, %r12, 15555
	std %r12, 3920(%r5)
	lis %r12, -13141
	ori %r12, %r12, 49704
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 35331
	ori %r12, %r12, 45429
	std %r12, 3928(%r5)
	lis %r12, 30545
	ori %r12, %r12, 64490
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37687
	ori %r12, %r12, 14413
	std %r12, 3936(%r5)
	lis %r12, 2409
	ori %r12, %r12, 56738
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 25672
	ori %r12, %r12, 50088
	std %r12, 3944(%r5)
	lis %r12, 27596
	ori %r12, %r12, 7003
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 7256
	ori %r12, %r12, 25779
	std %r12, 3952(%r5)
	lis %r12, -16499
	ori %r12, %r12, 64114
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 48190
	ori %r12, %r12, 15069
	std %r12, 3960(%r5)
	lis %r12, -20488
	ori %r12, %r12, 59252
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 63150
	ori %r12, %r12, 21714
	std %r12, 3968(%r5)
	lis %r12, -12794
	ori %r12, %r12, 38369
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 308
	ori %r12, %r12, 20032
	std %r12, 3976(%r5)
	lis %r12, 13499
	ori %r12, %r12, 59233
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 9985
	ori %r12, %r12, 13679
	std %r12, 3984(%r5)
	lis %r12, -24113
	ori %r12, %r12, 48352
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 41007
	ori %r12, %r12, 20896
	std %r12, 3992(%r5)
	lis %r12, -8051
	ori %r12, %r12, 50691
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 54736
	ori %r12, %r12, 54298
	std %r12, 4000(%r5)
	lis %r12, -25841
	ori %r12, %r12, 5567
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 10226
	ori %r12, %r12, 17399
	std %r12, 4008(%r5)
	lis %r12, -13552
	ori %r12, %r12, 58294
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4802
	ori %r12, %r12, 52986
	std %r12, 4016(%r5)
	lis %r12, -30253
	ori %r12, %r12, 57503
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 12876
	ori %r12, %r12, 5856
	std %r12, 4024(%r5)
	lis %r12, 4070
	ori %r12, %r12, 39903
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 50117
	ori %r12, %r12, 19227
	std %r12, 4032(%r5)
	lis %r12, -2428
	ori %r12, %r12, 64790
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 52686
	ori %r12, %r12, 7909
	std %r12, 4040(%r5)
	lis %r12, -30610
	ori %r12, %r12, 23212
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 22163
	ori %r12, %r12, 42741
	std %r12, 4048(%r5)
	lis %r12, -15547
	ori %r12, %r12, 13030
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 29004
	ori %r12, %r12, 33246
	std %r12, 4056(%r5)
	lis %r12, -12874
	ori %r12, %r12, 45681
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 13755
	ori %r12, %r12, 25289
	std %r12, 4064(%r5)
	lis %r12, 8311
	ori %r12, %r12, 63418
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 9528
	ori %r12, %r12, 5715
	std %r12, 4072(%r5)
	lis %r12, -10751
	ori %r12, %r12, 537
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 19578
	ori %r12, %r12, 35461
	std %r12, 4080(%r5)
	lis %r12, 14935
	ori %r12, %r12, 52919
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49727
	ori %r12, %r12, 42640
	std %r12, 4088(%r5)
	lis %r12, -31325
	ori %r12, %r12, 2259
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 9279
	ori %r12, %r12, 27272
	std %r12, 4096(%r5)
	lis %r12, 880
	ori %r12, %r12, 29508
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 4889
	ori %r12, %r12, 35374
	std %r12, 4104(%r5)
	lis %r12, 10655
	ori %r12, %r12, 12752
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 41993
	ori %r12, %r12, 14370
	std %r12, 4112(%r5)
	lis %r12, -5042
	ori %r12, %r12, 27785
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 2094
	ori %r12, %r12, 64152
	std %r12, 4120(%r5)
	lis %r12, 14544
	ori %r12, %r12, 4983
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 17704
	ori %r12, %r12, 8678
	std %r12, 4128(%r5)
	lis %r12, 13545
	ori %r12, %r12, 3180
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 48724
	ori %r12, %r12, 26319
	std %r12, 4136(%r5)
	lis %r12, -13956
	ori %r12, %r12, 20701
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 49324
	ori %r12, %r12, 10679
	std %r12, 4144(%r5)
	lis %r12, -19129
	ori %r12, %r12, 2327
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 16260
	ori %r12, %r12, 54709
	std %r12, 4152(%r5)
	lis %r12, -30343
	ori %r12, %r12, 64283
	rldicr %r12, %r12, 32, 31
	oris %r12, %r12, 37398
	ori %r12, %r12, 54745
	std %r12, 4160(%r5)
	li %r9, 0
	addi %r8, %r5, 4096
	li %r17, 18
20:
	li %r10, 0
	add %r12, %r3, %r9
	lbz %r11, 0(%r12)
	rldicr %r10, %r10, 8, 55
	or %r10, %r10, %r11
	addi %r9, %r9, 1
	subf %r12, %r4, %r9
	cmpldi %cr0, %r12, 0
	beq %cr0, 21f
	b 22f
21:
	li %r9, 0
22:
	add %r12, %r3, %r9
	lbz %r11, 0(%r12)
	rldicr %r10, %r10, 8, 55
	or %r10, %r10, %r11
	addi %r9, %r9, 1
	subf %r12, %r4, %r9
	cmpldi %cr0, %r12, 0
	beq %cr0, 23f
	b 24f
23:
	li %r9, 0
24:
	add %r12, %r3, %r9
	lbz %r11, 0(%r12)
	rldicr %r10, %r10, 8, 55
	or %r10, %r10, %r11
	addi %r9, %r9, 1
	subf %r12, %r4, %r9
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
	b 26f
25:
	li %r9, 0
26:
	add %r12, %r3, %r9
	lbz %r11, 0(%r12)
	rldicr %r10, %r10, 8, 55
	or %r10, %r10, %r11
	addi %r9, %r9, 1
	subf %r12, %r4, %r9
	cmpldi %cr0, %r12, 0
	beq %cr0, 27f
	b 28f
27:
	li %r9, 0
28:
	lwz %r11, 0(%r8)
	xor %r11, %r11, %r10
	stw %r11, 0(%r8)
	addi %r8, %r8, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	li %r0, 0
	or %r3, %r5, %r5
	li %r4, 0
	li %r5, 0
	addi %r16, %r3, 4096
	li %r17, 9
29:
	addi %r8, %r3, 4096
210:
	lwz %r12, 0(%r8)
	xor %r4, %r4, %r12
	rldicr %r9, %r4, 32, 31
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
211:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 0(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 256(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 512(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 768(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 211b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	or %r7, %r10, %r10
	rldicr %r9, %r4, 40, 23
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
212:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 1024(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 1280(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1536(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1792(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	rldicr %r9, %r4, 48, 15
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
213:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 2048(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 2304(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2560(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2816(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 213b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	xor %r7, %r7, %r10
	rldicr %r9, %r4, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
214:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 3072(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 3328(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3584(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3840(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 214b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	xor %r5, %r5, %r7
	or %r12, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r12, %r12
	addi %r8, %r8, 4
	subf %r12, %r3, %r8
	addi %r12, %r12, -4160
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
	lwz %r12, 0(%r8)
	xor %r12, %r4, %r12
	lwz %r4, 4(%r8)
	xor %r4, %r4, %r5
	or %r5, %r12, %r12
	stw %r4, 0(%r16)
	stw %r5, 4(%r16)
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 29b
	or %r16, %r3, %r3
	li %r17, 512
215:
	addi %r8, %r3, 4096
216:
	lwz %r12, 0(%r8)
	xor %r4, %r4, %r12
	rldicr %r9, %r4, 32, 31
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
217:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 0(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 256(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 512(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 768(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 217b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	or %r7, %r10, %r10
	rldicr %r9, %r4, 40, 23
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
218:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 1024(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 1280(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1536(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1792(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 218b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	rldicr %r9, %r4, 48, 15
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
219:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 2048(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 2304(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2560(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2816(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 219b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	xor %r7, %r7, %r10
	rldicr %r9, %r4, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
220:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 3072(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 3328(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3584(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3840(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 220b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	xor %r5, %r5, %r7
	or %r12, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r12, %r12
	addi %r8, %r8, 4
	subf %r12, %r3, %r8
	addi %r12, %r12, -4160
	cmpldi %cr0, %r12, 0
	bne %cr0, 216b
	lwz %r12, 0(%r8)
	xor %r12, %r4, %r12
	lwz %r4, 4(%r8)
	xor %r4, %r4, %r5
	or %r5, %r12, %r12
	stb %r4, 0(%r16)
	rlwinm %r12, %r4, 24, 8, 31
	stb %r12, 256(%r16)
	rlwinm %r12, %r4, 16, 16, 31
	stb %r12, 512(%r16)
	rlwinm %r12, %r4, 8, 24, 31
	stb %r12, 768(%r16)
	stb %r5, 1(%r16)
	rlwinm %r12, %r5, 24, 8, 31
	stb %r12, 257(%r16)
	rlwinm %r12, %r5, 16, 16, 31
	stb %r12, 513(%r16)
	rlwinm %r12, %r5, 8, 24, 31
	stb %r12, 769(%r16)
	addi %r16, %r16, 2
	subf %r12, %r3, %r16
	rldicr %r12, %r12, 56, 7
	cmpldi %cr0, %r12, 0
	beq %cr0, 221f
	b 222f
221:
	addi %r16, %r16, 768
222:
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 215b
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	addi %r1, %r1, 64
	blr

vg_blowfish_ecb_encrypt:
	stdu %r1, -288(%r1)
	addi %r6, %r1, 32
	std %r14, 0(%r6)
	std %r15, 8(%r6)
	std %r16, 16(%r6)
	std %r17, 24(%r6)
	li %r0, 0
	or %r16, %r4, %r4
	or %r17, %r5, %r5
	cmpldi %cr0, %r17, 0
	beq %cr0, 20f
22:
	lwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	lwbrx %r5, %r12, %r0
	addi %r8, %r3, 4096
23:
	lwz %r12, 0(%r8)
	xor %r4, %r4, %r12
	rldicr %r9, %r4, 32, 31
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
24:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 0(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 256(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 512(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 768(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	or %r7, %r10, %r10
	rldicr %r9, %r4, 40, 23
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
25:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 1024(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 1280(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1536(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1792(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	rldicr %r9, %r4, 48, 15
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
26:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 2048(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 2304(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2560(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2816(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	xor %r7, %r7, %r10
	rldicr %r9, %r4, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
27:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 3072(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 3328(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3584(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3840(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	xor %r5, %r5, %r7
	or %r12, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r12, %r12
	addi %r8, %r8, 4
	subf %r12, %r3, %r8
	addi %r12, %r12, -4160
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	lwz %r12, 0(%r8)
	xor %r12, %r4, %r12
	lwz %r4, 4(%r8)
	xor %r4, %r4, %r5
	or %r5, %r12, %r12
	stwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	stwbrx %r5, %r12, %r0
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	addi %r1, %r1, 288
	blr

vg_blowfish_ecb_decrypt:
	stdu %r1, -288(%r1)
	addi %r6, %r1, 32
	std %r14, 0(%r6)
	std %r15, 8(%r6)
	std %r16, 16(%r6)
	std %r17, 24(%r6)
	li %r0, 0
	or %r16, %r4, %r4
	or %r17, %r5, %r5
	cmpldi %cr0, %r17, 0
	beq %cr0, 20f
22:
	lwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	lwbrx %r5, %r12, %r0
	addi %r8, %r3, 4160
23:
	lwz %r12, 4(%r8)
	xor %r4, %r4, %r12
	rldicr %r9, %r4, 32, 31
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
24:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 0(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 256(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 512(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 768(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	or %r7, %r10, %r10
	rldicr %r9, %r4, 40, 23
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
25:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 1024(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 1280(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1536(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 1792(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 25b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	rldicr %r9, %r4, 48, 15
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
26:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 2048(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 2304(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2560(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 2816(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 26b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	xor %r7, %r7, %r10
	rldicr %r9, %r4, 56, 7
	rldicl %r9, %r9, 8, 56
	li %r14, 255
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 8, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r14, 16, 0, 31
	xor %r12, %r12, %r14
	and %r12, %r12, %r11
	xor %r14, %r14, %r12
	li %r10, 0
	or %r15, %r3, %r3
27:
	rldicl %r11, %r9, 62, 2
	addi %r11, %r11, -1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	and %r11, %r11, %r14
	addi %r9, %r9, -4
	lwz %r12, 3072(%r15)
	and %r12, %r12, %r11
	or %r10, %r10, %r12
	lwz %r12, 3328(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 8, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3584(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 16, 0, 31
	or %r10, %r10, %r12
	lwz %r12, 3840(%r15)
	and %r12, %r12, %r11
	rlwinm %r12, %r12, 24, 0, 31
	or %r10, %r10, %r12
	addi %r15, %r15, 4
	subf %r12, %r3, %r15
	addi %r12, %r12, -256
	cmpldi %cr0, %r12, 0
	bne %cr0, 27b
	rldicr %r11, %r9, 63, 0
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 24, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	rldicr %r11, %r9, 62, 1
	rldicl %r11, %r11, 1, 63
	subf %r11, %r11, %r0
	rlwinm %r12, %r10, 16, 0, 31
	xor %r12, %r12, %r10
	and %r12, %r12, %r11
	xor %r10, %r10, %r12
	add %r7, %r7, %r10
	xor %r5, %r5, %r7
	or %r12, %r4, %r4
	or %r4, %r5, %r5
	or %r5, %r12, %r12
	addi %r8, %r8, -4
	subf %r12, %r3, %r8
	addi %r12, %r12, -4096
	cmpldi %cr0, %r12, 0
	bne %cr0, 23b
	lwz %r12, 4(%r8)
	xor %r12, %r4, %r12
	lwz %r4, 0(%r8)
	xor %r4, %r4, %r5
	or %r5, %r12, %r12
	stwbrx %r4, %r16, %r0
	addi %r12, %r16, 4
	stwbrx %r5, %r12, %r0
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r14, 0(%r6)
	ld %r15, 8(%r6)
	ld %r16, 16(%r6)
	ld %r17, 24(%r6)
	addi %r12, %r1, 32
	li %r11, 0
	std %r11, 0(%r12)
	std %r11, 8(%r12)
	std %r11, 16(%r12)
	std %r11, 24(%r12)
	addi %r1, %r1, 288
	blr
