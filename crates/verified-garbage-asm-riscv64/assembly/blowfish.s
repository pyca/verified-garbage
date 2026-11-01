// The functions of `src/blowfish.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_expand_key:
	.option push
	.option arch, +m, +c
	addi sp, sp, -2032
	addi sp, sp, -2032
	addi sp, sp, -112
	addi a7, sp, 0
	addi t0, a7, 0
	lui t4, 753083
	addiw t4, t4, -858
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 627801
	addiw t4, t4, 1773
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 93743
	addiw t4, t4, 1863
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 518711
	addiw t4, t4, -1576
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 976262
	addiw t4, t4, -1905
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 78747
	addiw t4, t4, 1309
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 979343
	addiw t4, t4, 35
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 256177
	addiw t4, t4, -336
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 396706
	addiw t4, t4, 1985
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 263721
	addiw t4, t4, 1267
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 844619
	addiw t4, t4, 1642
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 172313
	addiw t4, t4, 943
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 123247
	addiw t4, t4, 1629
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 489494
	addiw t4, t4, -973
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 602555
	addiw t4, t4, -104
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 206345
	addiw t4, t4, 460
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 557099
	addiw t4, t4, 349
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 237372
	addiw t4, t4, 1409
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 386208
	addiw t4, t4, 1154
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 984602
	addiw t4, t4, -1470
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 668295
	addiw t4, t4, -1838
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 623886
	addiw t4, t4, 1132
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 558055
	addiw t4, t4, 1565
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 781371
	addiw t4, t4, 1049
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 682487
	addiw t4, t4, 984
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 251680
	addiw t4, t4, 1634
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 638261
	addiw t4, t4, -2012
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1015176
	addiw t4, t4, -1079
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 764884
	addiw t4, t4, -1254
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 408620
	addiw t4, t4, 1206
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 458427
	addiw t4, t4, 1455
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 37955
	addiw t4, t4, -993
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 733312
	addiw t4, t4, -764
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 897937
	addiw t4, t4, -169
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 498785
	addiw t4, t4, -1347
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1019789
	addiw t4, t4, -770
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 703617
	addiw t4, t4, 1503
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 533638
	addiw t4, t4, 250
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 897770
	addiw t4, t4, 187
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 474220
	addiw t4, t4, 1014
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 656861
	addiw t4, t4, -1872
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 374476
	addiw t4, t4, -1896
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 592838
	addiw t4, t4, 1401
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 951315
	addiw t4, t4, 986
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 741344
	addiw t4, t4, 474
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 657178
	addiw t4, t4, -1971
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 750334
	addiw t4, t4, 208
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 114982
	addiw t4, t4, 1275
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 710930
	addiw t4, t4, -864
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 663527
	addiw t4, t4, 1816
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 630127
	addiw t4, t4, -2033
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 890907
	addiw t4, t4, 2016
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 487744
	addiw t4, t4, 1382
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 851800
	addiw t4, t4, 1637
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 302394
	addiw t4, t4, 12
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 719798
	addiw t4, t4, -467
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 696786
	addiw t4, t4, -357
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 809512
	addiw t4, t4, -119
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 267915
	addiw t4, t4, -1674
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 87333
	addiw t4, t4, -1334
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1902
	addiw t4, t4, 1087
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 87730
	addiw t4, t4, -75
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 410347
	addiw t4, t4, 1569
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 436634
	addiw t4, t4, 349
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 915243
	addiw t4, t4, 1291
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 522504
	addiw t4, t4, -337
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1036071
	addiw t4, t4, -871
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 253925
	addiw t4, t4, -480
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 306395
	addiw t4, t4, 1652
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 396630
	addiw t4, t4, -1628
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 231320
	addiw t4, t4, 1456
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 565474
	addiw t4, t4, -1828
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 377589
	addiw t4, t4, -1161
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 84363
	addiw t4, t4, -1243
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 951745
	addiw t4, t4, 57
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 770383
	addiw t4, t4, -1658
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 603107
	addiw t4, t4, 453
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 550205
	addiw t4, t4, -70
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 138892
	addiw t4, t4, -1720
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 527051
	addiw t4, t4, -1783
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 111159
	addiw t4, t4, 1373
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 272123
	addiw t4, t4, -962
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 638722
	addiw t4, t4, 68
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 559559
	addiw t4, t4, -920
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 211571
	addiw t4, t4, -96
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 175876
	addiw t4, t4, -1269
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 58768
	addiw t4, t4, 357
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 387674
	addiw t4, t4, -122
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 435266
	addiw t4, t4, 117
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 11767
	addiw t4, t4, 1962
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 790177
	addiw t4, t4, 727
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 911250
	addiw t4, t4, -1166
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 28165
	addiw t4, t4, -944
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 149990
	addiw t4, t4, 79
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 969509
	addiw t4, t4, 879
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 775257
	addiw t4, t4, 1361
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 307845
	addiw t4, t4, -1328
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1029623
	addiw t4, t4, 1192
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 466947
	addiw t4, t4, 704
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 143002
	addiw t4, t4, 805
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 336359
	addiw t4, t4, -1258
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 915384
	addiw t4, t4, 1973
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 431465
	addiw t4, t4, -937
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 348976
	addiw t4, t4, -88
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 72246
	addiw t4, t4, -2009
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 867160
	addiw t4, t4, 829
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 619668
	addiw t4, t4, 1508
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 811320
	addiw t4, t4, -270
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 129509
	addiw t4, t4, -822
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 874729
	addiw t4, t4, 474
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 607666
	addiw t4, t4, 1489
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 985987
	addiw t4, t4, -1054
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 794396
	addiw t4, t4, 862
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 127697
	addiw t4, t4, 1826
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 929591
	addiw t4, t4, 1228
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 689086
	addiw t4, t4, 79
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 83767
	addiw t4, t4, 1954
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 218160
	addiw t4, t4, -1504
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 516537
	addiw t4, t4, -1617
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 917515
	addiw t4, t4, 782
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 682268
	addiw t4, t4, -1738
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 759221
	addiw t4, t4, 835
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 303517
	addiw t4, t4, -253
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 167947
	addiw t4, t4, -1747
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 477772
	addiw t4, t4, 1623
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 892623
	addiw t4, t4, -1681
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 352352
	addiw t4, t4, -1691
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 29817
	addiw t4, t4, -211
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 110558
	addiw t4, t4, -207
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 182210
	addiw t4, t4, 1761
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 581657
	addiw t4, t4, 417
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 603525
	addiw t4, t4, 1897
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 88249
	addiw t4, t4, -363
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 992006
	addiw t4, t4, -1452
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 898070
	addiw t4, t4, 209
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 125412
	addiw t4, t4, -1415
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 396019
	addiw t4, t4, 277
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 951429
	addiw t4, t4, 1365
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 269515
	addiw t4, t4, -1078
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 458471
	addiw t4, t4, 596
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 554434
	addiw t4, t4, -1879
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 611106
	addiw t4, t4, 1238
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 166901
	addiw t4, t4, -1137
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 968642
	addiw t4, t4, 472
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 414312
	addiw t4, t4, 1412
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1001177
	addiw t4, t4, 1673
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 130184
	addiw t4, t4, 1035
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 864463
	addiw t4, t4, -1594
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 332021
	addiw t4, t4, 1105
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1029048
	addiw t4, t4, -1297
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 277675
	addiw t4, t4, -15
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 571463
	addiw t4, t4, -18
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 790956
	addiw t4, t4, 367
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 638948
	addiw t4, t4, -45
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 987377
	addiw t4, t4, -1328
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 953674
	addiw t4, t4, -1709
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 788168
	addiw t4, t4, -1538
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 435658
	addiw t4, t4, -87
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 336791
	addiw t4, t4, -773
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 387091
	addiw t4, t4, 252
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 188659
	addiw t4, t4, 995
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 864445
	addiw t4, t4, -1845
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 182806
	addiw t4, t4, 121
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 207442
	addiw t4, t4, -97
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 21766
	addiw t4, t4, 373
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 786
	addiw t4, t4, 829
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 96375
	addiw t4, t4, -164
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 325240
	addiw t4, t4, -446
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 987133
	addiw t4, t4, -1445
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 860098
	addiw t4, t4, 506
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1030384
	addiw t4, t4, -1965
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 937917
	addiw t4, t4, -1059
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 989159
	addiw t4, t4, 1824
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 604889
	addiw t4, t4, 219
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 480204
	addiw t4, t4, 1934
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 55425
	addiw t4, t4, 758
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 691449
	addiw t4, t4, -83
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 10065
	addiw t4, t4, -465
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 563911
	addiw t4, t4, -96
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 711745
	addiw t4, t4, 936
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 109769
	addiw t4, t4, 1375
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 644427
	addiw t4, t4, 1453
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 123924
	addiw t4, t4, -307
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 755335
	addiw t4, t4, 293
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 914993
	addiw t4, t4, -1692
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 939990
	addiw t4, t4, -1343
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 474249
	addiw t4, t4, 1318
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 341265
	addiw t4, t4, 1095
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 943626
	addiw t4, t4, -1265
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 55650
	addiw t4, t4, -1094
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 545612
	addiw t4, t4, -1693
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 547754
	addiw t4, t4, -80
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 852730
	addiw t4, t4, -1839
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 990119
	addiw t4, t4, -1352
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 544907
	addiw t4, t4, 804
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1002055
	addiw t4, t4, 355
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 534295
	addiw t4, t4, 525
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 174540
	addiw t4, t4, 635
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 756899
	addiw t4, t4, -1851
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 722630
	addiw t4, t4, 142
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 350092
	addiw t4, t4, -553
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 406907
	addiw t4, t4, -1306
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 72515
	addiw t4, t4, -1451
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 408376
	addiw t4, t4, -863
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 638183
	addiw t4, t4, 1067
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 165799
	addiw t4, t4, -849
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 420935
	addiw t4, t4, -1221
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 382096
	addiw t4, t4, -1183
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 966095
	addiw t4, t4, -1553
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 536829
	addiw t4, t4, 803
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 648858
	addiw t4, t4, 1070
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 702079
	addiw t4, t4, 1569
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 702830
	addiw t4, t4, -1942
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 519073
	addiw t4, t4, 878
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 534116
	addiw t4, t4, -1631
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 243668
	addiw t4, t4, 1420
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 353288
	addiw t4, t4, 1504
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 270771
	addiw t4, t4, 1614
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 302525
	addiw t4, t4, 55
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1008216
	addiw t4, t4, 7
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 18811
	addiw t4, t4, 1763
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 103908
	addiw t4, t4, 193
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 241972
	addiw t4, t4, -408
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 720074
	addiw t4, t4, -1171
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 104046
	addiw t4, t4, -322
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 761124
	addiw t4, t4, 1472
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 265570
	addiw t4, t4, -1451
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 899312
	addiw t4, t4, -1177
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 709376
	addiw t4, t4, -708
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 255296
	addiw t4, t4, -718
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 913837
	addiw t4, t4, -1378
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 576195
	addiw t4, t4, -1835
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 757276
	addiw t4, t4, -1175
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 185520
	addiw t4, t4, -752
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 310571
	addiw t4, t4, 1690
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 845354
	addiw t4, t4, 1249
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 179459
	addiw t4, t4, 1775
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 442027
	addiw t4, t4, -363
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 583915
	addiw t4, t4, -48
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 592015
	addiw t4, t4, 655
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 736535
	addiw t4, t4, -1969
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 573100
	addiw t4, t4, -465
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 844171
	addiw t4, t4, 1509
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 862160
	addiw t4, t4, -588
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 137528
	addiw t4, t4, 22
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1031287
	addiw t4, t4, 2022
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 716136
	addiw t4, t4, -1045
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 356898
	addiw t4, t4, 0
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 365919
	addiw t4, t4, 36
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 8718
	addiw t4, t4, -1672
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 319766
	addiw t4, t4, 643
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 631224
	addiw t4, t4, -1101
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 529084
	addiw t4, t4, -810
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 175909
	addiw t4, t4, 1800
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 811006
	addiw t4, t4, 1974
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 450699
	addiw t4, t4, -1709
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 144100
	addiw t4, t4, 1257
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 420744
	addiw t4, t4, -592
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 923344
	addiw t4, t4, -143
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 254979
	addiw t4, t4, -1627
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 879974
	addiw t4, t4, 1434
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 794223
	addiw t4, t4, 1287
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 388194
	addiw t4, t4, 1670
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 659789
	addiw t4, t4, -1729
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 225368
	addiw t4, t4, 1668
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 757446
	addiw t4, t4, -996
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1044545
	addiw t4, t4, -713
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 775563
	addiw t4, t4, 538
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 5951
	addiw t4, t4, 1785
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 684878
	addiw t4, t4, -895
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 267233
	addiw t4, t4, -442
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 203283
	addiw t4, t4, -103
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 782385
	addiw t4, t4, -1992
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 718632
	addiw t4, t4, -1648
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 188705
	addiw t4, t4, 31
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 556642
	addiw t4, t4, 1055
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 576449
	addiw t4, t4, 1816
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 861808
	addiw t4, t4, -1478
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 90993
	addiw t4, t4, -1977
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 905253
	addiw t4, t4, 323
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 638309
	addiw t4, t4, 1438
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 37815
	addiw t4, t4, -1039
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 451280
	addiw t4, t4, -1299
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 733355
	addiw t4, t4, 368
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 64416
	addiw t4, t4, -1508
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 436098
	addiw t4, t4, 1494
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1000760
	addiw t4, t4, -1862
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 393460
	addiw t4, t4, -601
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 419563
	addiw t4, t4, 1544
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 167192
	addiw t4, t4, 917
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 10330
	addiw t4, t4, 1519
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 543444
	addiw t4, t4, -1265
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 67415
	addiw t4, t4, 40
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 848361
	addiw t4, t4, 1584
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 82100
	addiw t4, t4, -1648
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 453306
	addiw t4, t4, 1980
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 330653
	addiw t4, t4, -1361
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1015131
	addiw t4, t4, 818
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 690154
	addiw t4, t4, -1767
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 529911
	addiw t4, t4, 1946
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 629277
	addiw t4, t4, 1577
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 618486
	addiw t4, t4, 933
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 167493
	addiw t4, t4, 1259
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 472607
	addiw t4, t4, -1297
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 917838
	addiw t4, t4, 985
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 852319
	addiw t4, t4, -1354
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 20955
	addiw t4, t4, 1346
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 329388
	addiw t4, t4, 1950
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 670212
	addiw t4, t4, 1778
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 544953
	addiw t4, t4, 707
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1866
	addiw t4, t4, -768
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 398319
	addiw t4, t4, -1494
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 900884
	addiw t4, t4, 402
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 453238
	addiw t4, t4, 89
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 218458
	addiw t4, t4, -380
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 905164
	addiw t4, t4, 682
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 823384
	addiw t4, t4, 1070
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 264093
	addiw t4, t4, -557
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 133614
	addiw t4, t4, -1947
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1012405
	addiw t4, t4, -1305
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 155795
	addiw t4, t4, -1680
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 730638
	addiw t4, t4, -90
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 648481
	addiw t4, t4, 1932
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 237877
	addiw t4, t4, -1022
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 261706
	addiw t4, t4, -616
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 381827
	addiw t4, t4, 156
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 839327
	addiw t4, t4, -1248
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 459151
	addiw t4, t4, -149
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 30014
	addiw t4, t4, 565
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 992331
	addiw t4, t4, -380
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 733681
	addiw t4, t4, -806
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 137127
	addiw t4, t4, 1269
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 291955
	addiw t4, t4, -237
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 907118
	addiw t4, t4, -1307
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 126064
	addiw t4, t4, 865
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 736177
	addiw t4, t4, -307
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 16604
	addiw t4, t4, -1653
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 563976
	addiw t4, t4, -1006
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 260833
	addiw t4, t4, -1929
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 843223
	addiw t4, t4, 370
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 514478
	addiw t4, t4, -1465
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 799794
	addiw t4, t4, -532
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 762814
	addiw t4, t4, -1768
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 933900
	addiw t4, t4, 1101
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 104309
	addiw t4, t4, -264
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 676236
	addiw t4, t4, 1878
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 248832
	addiw t4, t4, -1050
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 173543
	addiw t4, t4, -187
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 122304
	addiw t4, t4, 1767
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 736413
	addiw t4, t4, -1911
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 185295
	addiw t4, t4, -1522
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 496227
	addiw t4, t4, -1202
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 131041
	addiw t4, t4, 679
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1045373
	addiw t4, t4, -1979
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 623126
	addiw t4, t4, -1315
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 194521
	addiw t4, t4, 1445
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 87158
	addiw t4, t4, 438
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 409580
	addiw t4, t4, -600
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 911850
	addiw t4, t4, 604
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 542147
	addiw t4, t4, -890
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 767647
	addiw t4, t4, 30
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 757403
	addiw t4, t4, 1114
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 514458
	addiw t4, t4, 11
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 76083
	addiw t4, t4, -632
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 765426
	addiw t4, t4, -120
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 289847
	addiw t4, t4, 644
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 201859
	addiw t4, t4, 10
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 249568
	addiw t4, t4, -14
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 79323
	addiw t4, t4, 1812
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 324859
	addiw t4, t4, -1054
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 136124
	addiw t4, t4, -1036
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 402549
	addiw t4, t4, -647
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 747570
	addiw t4, t4, 1697
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 731303
	addiw t4, t4, 1060
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 60181
	addiw t4, t4, -1857
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 462671
	addiw t4, t4, 1421
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 245448
	addiw t4, t4, -272
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 208679
	addiw t4, t4, 1079
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 621957
	addiw t4, t4, 128
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 830128
	addiw t4, t4, 1703
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 648819
	addiw t4, t4, 1146
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 277929
	addiw t4, t4, -1829
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1048452
	addiw t4, t4, -1996
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 711156
	addiw t4, t4, -735
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 104283
	addiw t4, t4, 890
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 974570
	addiw t4, t4, 1902
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 726602
	addiw t4, t4, -1366
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 99729
	addiw t4, t4, -1738
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1014004
	addiw t4, t4, 596
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 152287
	addiw t4, t4, -1838
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 124967
	addiw t4, t4, 221
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 436604
	addiw t4, t4, -1432
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 330186
	addiw t4, t4, 127
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 92126
	addiw t4, t4, -505
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 453
	addiw t4, t4, 58
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 38971
	addiw t4, t4, 1292
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1004331
	addiw t4, t4, -1647
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 998236
	addiw t4, t4, 741
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 482445
	addiw t4, t4, 68
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 256015
	addiw t4, t4, -1480
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 42023
	addiw t4, t4, -684
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 718745
	addiw t4, t4, 1976
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 850105
	addiw t4, t4, 922
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 541095
	addiw t4, t4, -1262
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 309745
	addiw t4, t4, -1960
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 409752
	addiw t4, t4, 1402
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 795697
	addiw t4, t4, 1308
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 239942
	addiw t4, t4, 1441
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 72387
	addiw t4, t4, 479
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 147738
	addiw t4, t4, 821
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 89007
	addiw t4, t4, 399
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 254191
	addiw t4, t4, -1565
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 947796
	addiw t4, t4, -737
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 66758
	addiw t4, t4, 1598
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 45006
	addiw t4, t4, 533
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 795538
	addiw t4, t4, -521
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 801489
	addiw t4, t4, 803
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 575480
	addiw t4, t4, -1092
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 701831
	addiw t4, t4, -974
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 454387
	addiw t4, t4, -50
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 654800
	addiw t4, t4, 1825
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 13126
	addiw t4, t4, 460
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 698855
	addiw t4, t4, 115
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 998070
	addiw t4, t4, 716
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 369212
	addiw t4, t4, -629
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 137699
	addiw t4, t4, -1432
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 253814
	addiw t4, t4, -172
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 429790
	addiw t4, t4, 823
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 364014
	addiw t4, t4, 1589
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 796722
	addiw t4, t4, 757
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 773523
	addiw t4, t4, -333
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 508556
	addiw t4, t4, 1771
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 254214
	addiw t4, t4, 1098
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 833227
	addiw t4, t4, -1298
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 840951
	addiw t4, t4, -1470
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 529592
	addiw t4, t4, 1310
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 817289
	addiw t4, t4, -670
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 600141
	addiw t4, t4, -1259
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 534050
	addiw t4, t4, -1701
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 260821
	addiw t4, t4, 1346
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 140793
	addiw t4, t4, 882
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 489567
	addiw t4, t4, -290
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 892672
	addiw t4, t4, -2041
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 45121
	addiw t4, t4, -919
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 126292
	addiw t4, t4, 1348
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 423413
	addiw t4, t4, 1395
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 447108
	addiw t4, t4, -316
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 540219
	addiw t4, t4, 62
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 806331
	addiw t4, t4, 1355
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 588229
	addiw t4, t4, -1619
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 796007
	addiw t4, t4, -1556
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 936455
	addiw t4, t4, 1305
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 628406
	addiw t4, t4, -1217
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 984287
	addiw t4, t4, -95
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 9784
	addiw t4, t4, 1100
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 439236
	addiw t4, t4, -503
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 699253
	addiw t4, t4, 616
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 358632
	addiw t4, t4, -194
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 12047
	addiw t4, t4, 176
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 901716
	addiw t4, t4, -850
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 141640
	addiw t4, t4, -815
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 633987
	addiw t4, t4, 1850
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 675521
	addiw t4, t4, -87
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 99108
	addiw t4, t4, -1054
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1009397
	addiw t4, t4, -178
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 771426
	addiw t4, t4, 1068
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 903998
	addiw t4, t4, -1570
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 652547
	addiw t4, t4, -427
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 957383
	addiw t4, t4, 1146
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 804414
	addiw t4, t4, -1044
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 150995
	addiw t4, t4, 751
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 79107
	addiw t4, t4, -1518
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 391185
	addiw t4, t4, 113
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 365517
	addiw t4, t4, 1796
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 125417
	addiw t4, t4, 2034
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 370799
	addiw t4, t4, -1402
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 627349
	addiw t4, t4, -393
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 639717
	addiw t4, t4, 640
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 125529
	addiw t4, t4, 1222
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 102803
	addiw t4, t4, 1778
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 962239
	addiw t4, t4, 1874
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 6938
	addiw t4, t4, 1763
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 427612
	addiw t4, t4, -317
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 373422
	addiw t4, t4, -1042
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 401091
	addiw t4, t4, -1771
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 696383
	addiw t4, t4, -1261
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 834901
	addiw t4, t4, -843
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 731590
	addiw t4, t4, 238
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 416258
	addiw t4, t4, -1692
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 787220
	addiw t4, t4, -960
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 403800
	addiw t4, t4, 1947
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 90393
	addiw t4, t4, 2040
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 493932
	addiw t4, t4, 1806
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 108978
	addiw t4, t4, -1193
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 448757
	addiw t4, t4, 973
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 978915
	addiw t4, t4, 1112
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 132143
	addiw t4, t4, -1955
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1027514
	addiw t4, t4, 837
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 267871
	addiw t4, t4, -57
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 253512
	addiw t4, t4, 1752
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 794566
	addiw t4, t4, -1073
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 353399
	addiw t4, t4, -1665
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 143691
	addiw t4, t4, -759
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 143825
	addiw t4, t4, -936
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 445801
	addiw t4, t4, -717
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 844813
	addiw t4, t4, -1156
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 401026
	addiw t4, t4, -1626
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 525740
	addiw t4, t4, 1449
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 61404
	addiw t4, t4, 926
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 931441
	addiw t4, t4, 219
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 988119
	addiw t4, t4, 453
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 900713
	addiw t4, t4, -235
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 213455
	addiw t4, t4, 1896
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 426735
	addiw t4, t4, 2039
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 719735
	addiw t4, t4, -1423
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 264004
	addiw t4, t4, 1582
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 286011
	addiw t4, t4, -227
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 19720
	addiw t4, t4, 1516
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 634468
	addiw t4, t4, 435
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1031599
	addiw t4, t4, 1061
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 977472
	addiw t4, t4, 98
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 745577
	addiw t4, t4, -862
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 272799
	addiw t4, t4, -900
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 572092
	addiw t4, t4, -1739
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 729877
	addiw t4, t4, 1783
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1032051
	addiw t4, t4, 628
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 162505
	addiw t4, t4, 1870
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 310136
	addiw t4, t4, 1850
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 210486
	addiw t4, t4, -1860
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 508368
	addiw t4, t4, -1706
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 931271
	addiw t4, t4, 2
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 902130
	addiw t4, t4, 584
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 96833
	addiw t4, t4, -18
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 411901
	addiw t4, t4, 491
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 113206
	addiw t4, t4, 52
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 89370
	addiw t4, t4, -318
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 140846
	addiw t4, t4, 480
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 166090
	addiw t4, t4, -1778
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 984624
	addiw t4, t4, -699
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 123520
	addiw t4, t4, -1425
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 228023
	addiw t4, t4, 1089
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 54480
	addiw t4, t4, -1952
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 17331
	addiw t4, t4, 1808
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 47402
	addiw t4, t4, 967
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 667834
	addiw t4, t4, -773
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 965618
	addiw t4, t4, 1160
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 186744
	addiw t4, t4, -1613
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 117956
	addiw t4, t4, -1113
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 331374
	addiw t4, t4, 1847
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 826768
	addiw t4, t4, -1512
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 173800
	addiw t4, t4, 1625
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1042566
	addiw t4, t4, -178
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 319368
	addiw t4, t4, 1623
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 835659
	addiw t4, t4, 70
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 391287
	addiw t4, t4, 307
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 399762
	addiw t4, t4, 1214
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 795530
	addiw t4, t4, 655
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 759127
	addiw t4, t4, 1219
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 927640
	addiw t4, t4, 1121
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 313623
	addiw t4, t4, 142
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 648333
	addiw t4, t4, 225
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 211473
	addiw t4, t4, -1610
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 66137
	addiw t4, t4, -1022
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 430334
	addiw t4, t4, -227
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 338368
	addiw t4, t4, -381
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 162896
	addiw t4, t4, -1535
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 741476
	addiw t4, t4, 295
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 404142
	addiw t4, t4, 40
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 215366
	addiw t4, t4, 983
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 485918
	addiw t4, t4, -426
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 148441
	addiw t4, t4, -2039
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1035084
	addiw t4, t4, -1697
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 806203
	addiw t4, t4, 1400
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 249248
	addiw t4, t4, -1954
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 228588
	addiw t4, t4, 1255
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 919777
	addiw t4, t4, 564
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 168548
	addiw t4, t4, 90
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1725
	addiw t4, t4, 1056
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 400719
	addiw t4, t4, 1060
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 558324
	addiw t4, t4, 1526
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 196057
	addiw t4, t4, 508
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 546521
	addiw t4, t4, 1801
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 42100
	addiw t4, t4, -1753
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 448611
	addiw t4, t4, -1672
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 580615
	addiw t4, t4, -1772
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 880139
	addiw t4, t4, -514
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 174646
	addiw t4, t4, -226
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 322936
	addiw t4, t4, 1438
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 620130
	addiw t4, t4, -1798
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 134772
	addiw t4, t4, 1018
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 611691
	addiw t4, t4, 1013
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 613017
	addiw t4, t4, -710
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 897690
	addiw t4, t4, -1433
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 202722
	addiw t4, t4, 1354
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 180563
	addiw t4, t4, -24
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 549175
	addiw t4, t4, -747
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 452498
	addiw t4, t4, -55
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 220188
	addiw t4, t4, 81
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 446090
	addiw t4, t4, -904
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 529651
	addiw t4, t4, 692
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 757945
	addiw t4, t4, 661
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1011905
	addiw t4, t4, -606
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1003657
	addiw t4, t4, 1144
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 581589
	addiw t4, t4, -1885
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1038064
	addiw t4, t4, -157
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 441886
	addiw t4, t4, -548
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 953667
	addiw t4, t4, -939
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 971008
	addiw t4, t4, -243
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 388344
	addiw t4, t4, -609
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 878491
	addiw t4, t4, -721
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 204326
	addiw t4, t4, -1746
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 988355
	addiw t4, t4, -1107
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 408501
	addiw t4, t4, 322
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 801759
	addiw t4, t4, -752
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 962241
	addiw t4, t4, 790
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 802459
	addiw t4, t4, -1945
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 395196
	addiw t4, t4, 128
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1034978
	addiw t4, t4, -125
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 386075
	addiw t4, t4, -1173
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 189483
	addiw t4, t4, -425
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 777984
	addiw t4, t4, -524
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 892713
	addiw t4, t4, -263
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 610542
	addiw t4, t4, -218
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 910677
	addiw t4, t4, 1881
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 693792
	addiw t4, t4, 1452
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 286878
	addiw t4, t4, -999
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1042956
	addiw t4, t4, -481
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 991018
	addiw t4, t4, 1085
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 523488
	addiw t4, t4, 1754
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 854872
	addiw t4, t4, 862
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 25800
	addiw t4, t4, 1676
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 513416
	addiw t4, t4, 1658
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 93663
	addiw t4, t4, -1378
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 120795
	addiw t4, t4, 1774
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 508064
	addiw t4, t4, 484
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 755130
	addiw t4, t4, -654
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 63434
	addiw t4, t4, 1365
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 78158
	addiw t4, t4, 1775
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 822261
	addiw t4, t4, -313
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 4008
	addiw t4, t4, 562
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 431304
	addiw t4, t4, 317
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 667456
	addiw t4, t4, 533
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 2930
	addiw t4, t4, 8
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 569874
	addiw t4, t4, 1081
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 659275
	addiw t4, t4, 1429
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 834252
	addiw t4, t4, -580
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 828000
	addiw t4, t4, -533
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 746176
	addiw t4, t4, 1104
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 659685
	addiw t4, t4, -1828
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1001672
	addiw t4, t4, 1855
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 440195
	addiw t4, t4, 1998
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 74655
	addiw t4, t4, 1022
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 932407
	addiw t4, t4, -567
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 492566
	addiw t4, t4, -1170
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 295952
	addiw t4, t4, -502
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 616120
	addiw t4, t4, 851
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 924305
	addiw t4, t4, 1448
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 171843
	addiw t4, t4, 298
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 166834
	addiw t4, t4, 2040
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 64540
	addiw t4, t4, 1729
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 558192
	addiw t4, t4, 1273
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 72650
	addiw t4, t4, -1185
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 409475
	addiw t4, t4, -1413
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 857710
	addiw t4, t4, 274
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 778820
	addiw t4, t4, -477
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 665388
	addiw t4, t4, -1358
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 837595
	addiw t4, t4, 1810
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 256472
	addiw t4, t4, -695
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1017587
	addiw t4, t4, -441
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 451007
	addiw t4, t4, -1262
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 853590
	addiw t4, t4, 1915
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 62352
	addiw t4, t4, 41
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 88350
	addiw t4, t4, -1157
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 244038
	addiw t4, t4, -1261
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 189025
	addiw t4, t4, 313
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 190295
	addiw t4, t4, -1470
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1030681
	addiw t4, t4, 530
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 922205
	addiw t4, t4, -1429
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 700609
	addiw t4, t4, 578
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 936952
	addiw t4, t4, 1711
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 14223
	addiw t4, t4, 1980
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 222292
	addiw t4, t4, -1795
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 2050
	addiw t4, t4, -446
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 361583
	addiw t4, t4, -1888
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 563022
	addiw t4, t4, -680
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1034075
	addiw t4, t4, 870
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 390818
	addiw t4, t4, -533
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 11611
	addiw t4, t4, 1134
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 477832
	addiw t4, t4, 523
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 205531
	addiw t4, t4, -1665
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 453023
	addiw t4, t4, 90
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 428138
	addiw t4, t4, 1465
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 843300
	addiw t4, t4, -1609
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 942112
	addiw t4, t4, 1553
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 689668
	addiw t4, t4, -8
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 902671
	addiw t4, t4, 1303
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 797732
	addiw t4, t4, -1818
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 368588
	addiw t4, t4, -821
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 599848
	addiw t4, t4, -1019
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 650261
	addiw t4, t4, -541
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 709600
	addiw t4, t4, -940
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 333910
	addiw t4, t4, 336
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 811694
	addiw t4, t4, 469
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 393446
	addiw t4, t4, 922
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 610153
	addiw t4, t4, 1257
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 871367
	addiw t4, t4, 1601
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 328755
	addiw t4, t4, 980
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 782665
	addiw t4, t4, 1822
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 419593
	addiw t4, t4, 1613
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 202736
	addiw t4, t4, 959
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 703909
	addiw t4, t4, 1430
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 954533
	addiw t4, t4, 808
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 161421
	addiw t4, t4, 1896
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 502623
	addiw t4, t4, -1969
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 265453
	addiw t4, t4, 938
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 245486
	addiw t4, t4, -1760
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 959077
	addiw t4, t4, -1251
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 829070
	addiw t4, t4, -710
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 762974
	addiw t4, t4, -1797
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 856034
	addiw t4, t4, 85
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 629962
	addiw t4, t4, 341
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 591332
	addiw t4, t4, -90
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 22528
	addiw t4, t4, 1277
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 816270
	addiw t4, t4, 1173
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 381956
	addiw t4, t4, 263
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 270125
	addiw t4, t4, 1330
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 130550
	addiw t4, t4, 37
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 830192
	addiw t4, t4, 526
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 975795
	addiw t4, t4, 875
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 187886
	addiw t4, t4, 1669
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 947785
	addiw t4, t4, 1488
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 998456
	addiw t4, t4, 1876
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1000362
	addiw t4, t4, -1782
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 899482
	addiw t4, t4, 424
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 901751
	addiw t4, t4, -570
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 432989
	addiw t4, t4, -783
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 891405
	addiw t4, t4, -410
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 485301
	addiw t4, t4, 443
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1001485
	addiw t4, t4, -969
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 491820
	addiw t4, t4, 1640
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 307307
	addiw t4, t4, 1898
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 926673
	addiw t4, t4, 282
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 875921
	addiw t4, t4, -1468
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 412654
	addiw t4, t4, -1436
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 394767
	addiw t4, t4, 157
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 882559
	addiw t4, t4, 1745
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 248591
	addiw t4, t4, 131
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 783708
	addiw t4, t4, -649
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 556879
	addiw t4, t4, 590
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 289613
	addiw t4, t4, -1965
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 596041
	addiw t4, t4, -1158
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 825538
	addiw t4, t4, 70
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 479516
	addiw t4, t4, -1095
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 804462
	addiw t4, t4, 183
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 119969
	addiw t4, t4, -1560
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 166417
	addiw t4, t4, -1254
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 326165
	addiw t4, t4, 2012
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 55818
	addiw t4, t4, 1872
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 400439
	addiw t4, t4, 1946
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 196620
	addiw t4, t4, 240
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 795954
	addiw t4, t4, 785
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 847545
	addiw t4, t4, 187
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 508821
	addiw t4, t4, -1169
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 864679
	addiw t4, t4, 646
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 318849
	addiw t4, t4, -1811
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 444971
	addiw t4, t4, 286
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 906085
	addiw t4, t4, 1647
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 263801
	addiw t4, t4, 727
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 111485
	addiw t4, t4, -201
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 779268
	addiw t4, t4, 670
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 505825
	addiw t4, t4, 1437
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 740324
	addiw t4, t4, 1387
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 822568
	addiw t4, t4, -1745
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 811480
	addiw t4, t4, -530
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 20101
	addiw t4, t4, 219
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 142890
	addiw t4, t4, -1296
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 674479
	addiw t4, t4, 1720
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 877829
	addiw t4, t4, -582
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 956526
	addiw t4, t4, 505
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 366238
	addiw t4, t4, -1325
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 604880
	addiw t4, t4, 277
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 335257
	addiw t4, t4, 1882
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 167272
	addiw t4, t4, -710
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 313130
	addiw t4, t4, -1073
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 638942
	addiw t4, t4, 1649
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 164509
	addiw t4, t4, -883
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 574533
	addiw t4, t4, 1425
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 774748
	addiw t4, t4, -1324
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 175818
	addiw t4, t4, 533
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 106431
	addiw t4, t4, 1435
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 768047
	addiw t4, t4, 1320
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 390784
	addiw t4, t4, -2031
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 595497
	addiw t4, t4, -431
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 206413
	addiw t4, t4, -318
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 525972
	addiw t4, t4, 1662
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 421842
	addiw t4, t4, 1040
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 716030
	addiw t4, t4, -758
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 767988
	addiw t4, t4, 221
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 873540
	addiw t4, t4, 1406
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 293612
	addiw t4, t4, -1112
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 459194
	addiw t4, t4, -413
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 382741
	addiw t4, t4, 1933
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 542381
	addiw t4, t4, -1016
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 297794
	addiw t4, t4, -728
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1017016
	addiw t4, t4, 642
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 774846
	addiw t4, t4, -847
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 826229
	addiw t4, t4, -1055
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 818239
	addiw t4, t4, 1662
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 232634
	addiw t4, t4, -1463
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 325574
	addiw t4, t4, 1834
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 643060
	addiw t4, t4, -1353
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 153363
	addiw t4, t4, -1492
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 857503
	addiw t4, t4, -1183
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 271953
	addiw t4, t4, -930
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 412644
	addiw t4, t4, -1266
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 123582
	addiw t4, t4, -206
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 885257
	addiw t4, t4, -959
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 119923
	addiw t4, t4, -371
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 457977
	addiw t4, t4, 340
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 629840
	addiw t4, t4, 1382
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 8978
	addiw t4, t4, 855
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 838011
	addiw t4, t4, 1378
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 82365
	addiw t4, t4, 146
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 630881
	addiw t4, t4, -1347
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1011232
	addiw t4, t4, 253
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 178114
	addiw t4, t4, 517
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 984589
	addiw t4, t4, 960
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 396375
	addiw t4, t4, 1692
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 518926
	addiw t4, t4, -1970
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1023561
	addiw t4, t4, -932
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 651994
	addiw t4, t4, 105
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 945718
	addiw t4, t4, -1230
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 186239
	addiw t4, t4, 1486
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 635507
	addiw t4, t4, 1895
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 803271
	addiw t4, t4, 910
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 453401
	addiw t4, t4, 27
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 796519
	addiw t4, t4, -341
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 315566
	addiw t4, t4, -264
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 930404
	addiw t4, t4, 1723
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 977093
	addiw t4, t4, 469
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 852019
	addiw t4, t4, -318
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 373079
	addiw t4, t4, -1439
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 403796
	addiw t4, t4, -1374
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 42751
	addiw t4, t4, 2031
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 941672
	addiw t4, t4, 1705
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 572285
	addiw t4, t4, 2045
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 185322
	addiw t4, t4, 1708
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1006412
	addiw t4, t4, -2011
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1026762
	addiw t4, t4, 1452
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 190053
	addiw t4, t4, 1988
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 385254
	addiw t4, t4, 1
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 984599
	addiw t4, t4, -659
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 29093
	addiw t4, t4, 1950
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 996962
	addiw t4, t4, 365
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 246608
	addiw t4, t4, -551
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 599326
	addiw t4, t4, -1673
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1021326
	addiw t4, t4, -1001
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 781544
	addiw t4, t4, -1136
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 943412
	addiw t4, t4, -541
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 135899
	addiw t4, t4, 520
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 822764
	addiw t4, t4, 70
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 929817
	addiw t4, t4, -521
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 839856
	addiw t4, t4, -150
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 454952
	addiw t4, t4, 1230
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 407414
	addiw t4, t4, -540
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 512353
	addiw t4, t4, 781
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 717934
	addiw t4, t4, 715
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 657908
	addiw t4, t4, -1532
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 160219
	addiw t4, t4, -1221
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 153492
	addiw t4, t4, -160
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 765080
	addiw t4, t4, -1735
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 696605
	addiw t4, t4, 456
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 896492
	addiw t4, t4, -633
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 176915
	addiw t4, t4, 1731
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 283036
	addiw t4, t4, -1191
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 90064
	addiw t4, t4, -990
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 689738
	addiw t4, t4, -877
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 673031
	addiw t4, t4, -1529
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 956942
	addiw t4, t4, -1170
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 992073
	addiw t4, t4, 661
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 206611
	addiw t4, t4, 1140
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 988915
	addiw t4, t4, -97
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 518046
	addiw t4, t4, -1830
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 142626
	addiw t4, t4, -591
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 840535
	addiw t4, t4, 1779
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 471919
	addiw t4, t4, -1151
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 354565
	addiw t4, t4, -1694
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 507137
	addiw t4, t4, 1223
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 863217
	addiw t4, t4, -173
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 642288
	addiw t4, t4, 617
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 711646
	addiw t4, t4, 830
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 395805
	addiw t4, t4, -480
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 700313
	addiw t4, t4, -514
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 923305
	addiw t4, t4, -1342
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 942686
	addiw t4, t4, -264
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 470526
	addiw t4, t4, 609
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 810032
	addiw t4, t4, -1479
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 772138
	addiw t4, t4, 944
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 721
	addiw t4, t4, -239
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 222954
	addiw t4, t4, 396
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 301625
	addiw t4, t4, 1096
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 853817
	addiw t4, t4, -753
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 387420
	addiw t4, t4, -1479
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 552691
	addiw t4, t4, -518
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 991714
	addiw t4, t4, 1161
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 413279
	addiw t4, t4, -1600
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 350868
	addiw t4, t4, -1498
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1024069
	addiw t4, t4, 559
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 254107
	addiw t4, t4, 228
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 179971
	addiw t4, t4, 1168
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 515320
	addiw t4, t4, -555
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 560495
	addiw t4, t4, 671
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 604930
	addiw t4, t4, -1751
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 81236
	addiw t4, t4, -1069
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 866663
	addiw t4, t4, 1375
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 412191
	addiw t4, t4, 1029
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 238201
	addiw t4, t4, 235
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 903622
	addiw t4, t4, 831
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 763237
	addiw t4, t4, 1331
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 711873
	addiw t4, t4, -1455
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 133587
	addiw t4, t4, 232
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 324116
	addiw t4, t4, -390
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 81379
	addiw t4, t4, -1610
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 30807
	addiw t4, t4, -594
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 132804
	addiw t4, t4, 1434
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 740646
	addiw t4, t4, -1858
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 738134
	addiw t4, t4, -1630
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 247398
	addiw t4, t4, 1258
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 322595
	addiw t4, t4, -101
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 341798
	addiw t4, t4, -1266
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 89387
	addiw t4, t4, 1088
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 453514
	addiw t4, t4, -1872
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 467362
	addiw t4, t4, 63
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 283561
	addiw t4, t4, 789
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 127789
	addiw t4, t4, -376
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 950300
	addiw t4, t4, 1820
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 44453
	addiw t4, t4, -112
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 728985
	addiw t4, t4, 313
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 892255
	addiw t4, t4, 1438
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 608542
	addiw t4, t4, 1687
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 764555
	addiw t4, t4, 1765
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 15648
	addiw t4, t4, 1473
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 493962
	addiw t4, t4, -1812
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 465421
	addiw t4, t4, 799
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 486378
	addiw t4, t4, 778
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 929978
	addiw t4, t4, -1739
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 255534
	addiw t4, t4, -1460
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1030387
	addiw t4, t4, -1000
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 838275
	addiw t4, t4, 547
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 860519
	addiw t4, t4, 1520
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 812300
	addiw t4, t4, -1642
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 994840
	addiw t4, t4, -1338
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 774747
	addiw t4, t4, -1878
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 486576
	addiw t4, t4, 1042
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 293556
	addiw t4, t4, 17
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 482036
	addiw t4, t4, 1592
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1022639
	addiw t4, t4, -1845
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 965696
	addiw t4, t4, -1208
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 32918
	addiw t4, t4, -812
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 801015
	addiw t4, t4, 1870
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 371389
	addiw t4, t4, 826
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 630069
	addiw t4, t4, -164
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 818540
	addiw t4, t4, -43
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 437026
	addiw t4, t4, 439
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 416876
	addiw t4, t4, -937
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 314708
	addiw t4, t4, 1619
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 781003
	addiw t4, t4, -1751
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 632375
	addiw t4, t4, -1375
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 641620
	addiw t4, t4, 960
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 764154
	addiw t4, t4, -1149
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 980154
	addiw t4, t4, 1832
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 488447
	addiw t4, t4, 1991
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 244152
	addiw t4, t4, 1920
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 8906
	addiw t4, t4, -279
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 511248
	addiw t4, t4, 406
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 370091
	addiw t4, t4, -737
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 971902
	addiw t4, t4, 224
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 499587
	addiw t4, t4, -1816
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 933759
	addiw t4, t4, -648
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 20537
	addiw t4, t4, -2027
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 694644
	addiw t4, t4, -829
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 159570
	addiw t4, t4, -485
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 565307
	addiw t4, t4, 373
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 838332
	addiw t4, t4, 552
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 602996
	addiw t4, t4, -1971
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 488736
	addiw t4, t4, -1046
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 410764
	addiw t4, t4, 936
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 38558
	addiw t4, t4, -606
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 116102
	addiw t4, t4, 1203
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 441538
	addiw t4, t4, -1189
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 771044
	addiw t4, t4, -1315
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 784608
	addiw t4, t4, -1422
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1010405
	addiw t4, t4, 1234
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 720782
	addiw t4, t4, 1908
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 4933
	addiw t4, t4, -448
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 843881
	addiw t4, t4, 1505
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 159763
	addiw t4, t4, 1391
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 215998
	addiw t4, t4, 1889
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 656117
	addiw t4, t4, 416
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 662780
	addiw t4, t4, -800
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 875789
	addiw t4, t4, 1050
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 919772
	addiw t4, t4, 1539
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 163620
	addiw t4, t4, 1015
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 635121
	addiw t4, t4, 1471
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 76845
	addiw t4, t4, -262
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 831758
	addiw t4, t4, 950
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 206017
	addiw t4, t4, 1760
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 564542
	addiw t4, t4, 159
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 801877
	addiw t4, t4, -1253
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 65130
	addiw t4, t4, -1057
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 842978
	addiw t4, t4, -283
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 1009744
	addiw t4, t4, -746
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 354618
	addiw t4, t4, 1781
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 558822
	addiw t4, t4, -1364
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 464072
	addiw t4, t4, 478
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 799827
	addiw t4, t4, 742
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 220086
	addiw t4, t4, 713
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 842603
	addiw t4, t4, 625
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 152449
	addiw t4, t4, 1619
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 132991
	addiw t4, t4, 1978
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 313257
	addiw t4, t4, -1403
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 876560
	addiw t4, t4, 537
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 795642
	addiw t4, t4, 1680
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 238973
	addiw t4, t4, -329
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 148471
	addiw t4, t4, -1400
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 547377
	addiw t4, t4, -1837
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 78233
	addiw t4, t4, -1490
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 14087
	addiw t4, t4, 836
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 671892
	addiw t4, t4, -2014
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 170483
	addiw t4, t4, 464
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 33520
	addiw t4, t4, -1384
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 967911
	addiw t4, t4, -887
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 283266
	addiw t4, t4, 486
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 232705
	addiw t4, t4, 887
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 779590
	addiw t4, t4, 1743
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 216721
	addiw t4, t4, -916
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 789187
	addiw t4, t4, -1609
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 825285
	addiw t4, t4, 221
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 260173
	addiw t4, t4, 1461
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 742513
	addiw t4, t4, -1769
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 598381
	addiw t4, t4, 1497
	sw t4, 0(t0)
	addi t0, t0, 4
	lui t4, 563104
	addiw t4, t4, -1253
	sw t4, 0(t0)
	addi t0, t0, 4
	addi t1, zero, 0
	addi a6, a7, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
	addi t5, zero, 18
20:
	addi t2, zero, 0
	add t4, a0, t1
	lbu t3, 0(t4)
	slli t2, t2, 8
	or t2, t2, t3
	addi t1, t1, 1
	sub t4, t1, a1
	beqz t4, 21f
	j 22f
21:
	addi t1, zero, 0
22:
	add t4, a0, t1
	lbu t3, 0(t4)
	slli t2, t2, 8
	or t2, t2, t3
	addi t1, t1, 1
	sub t4, t1, a1
	beqz t4, 23f
	j 24f
23:
	addi t1, zero, 0
24:
	add t4, a0, t1
	lbu t3, 0(t4)
	slli t2, t2, 8
	or t2, t2, t3
	addi t1, t1, 1
	sub t4, t1, a1
	beqz t4, 25f
	j 26f
25:
	addi t1, zero, 0
26:
	add t4, a0, t1
	lbu t3, 0(t4)
	slli t2, t2, 8
	or t2, t2, t3
	addi t1, t1, 1
	sub t4, t1, a1
	beqz t4, 27f
	j 28f
27:
	addi t1, zero, 0
28:
	lwu t3, 0(a6)
	xor t3, t3, t2
	sw t3, 0(a6)
	addi a6, a6, 4
	addi t5, t5, -1
	bnez t5, 20b
	addi a3, zero, 0
	addi a4, zero, 0
	addi a1, a7, 2047
	addi a1, a1, 2047
	addi a1, a1, 2
	addi a0, zero, 9
29:
	addi a6, a7, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
210:
	lwu t4, 0(a6)
	xor a3, a3, t4
	slli t1, a3, 32
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 24
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	or a5, t2, t2
	addi a7, a7, 1024
	slli t1, a3, 40
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 16
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	add a5, a5, t2
	addi a7, a7, 1024
	slli t1, a3, 48
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 8
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	xor a5, a5, t2
	addi a7, a7, 1024
	slli t1, a3, 56
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 0
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	add a5, a5, t2
	addi a7, a7, -2048
	addi a7, a7, -1024
	xor a4, a4, a5
	or t4, a3, a3
	or a3, a4, a4
	or a4, t4, t4
	addi a6, a6, 4
	sub t4, a6, a7
	addi t4, t4, -2047
	addi t4, t4, -2047
	addi t4, t4, -66
	bnez t4, 210b
	lwu t4, 0(a6)
	xor t4, a3, t4
	lwu a3, 4(a6)
	xor a3, a3, a4
	or a4, t4, t4
	sw a3, 0(a1)
	sw a4, 4(a1)
	addi a1, a1, 8
	addi a0, a0, -1
	bnez a0, 29b
	addi a1, a7, 0
	addi a0, zero, 512
211:
	addi a6, a7, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
212:
	lwu t4, 0(a6)
	xor a3, a3, t4
	slli t1, a3, 32
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 24
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	or a5, t2, t2
	addi a7, a7, 1024
	slli t1, a3, 40
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 16
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	add a5, a5, t2
	addi a7, a7, 1024
	slli t1, a3, 48
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 8
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	xor a5, a5, t2
	addi a7, a7, 1024
	slli t1, a3, 56
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 0
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	add a5, a5, t2
	addi a7, a7, -2048
	addi a7, a7, -1024
	xor a4, a4, a5
	or t4, a3, a3
	or a3, a4, a4
	or a4, t4, t4
	addi a6, a6, 4
	sub t4, a6, a7
	addi t4, t4, -2047
	addi t4, t4, -2047
	addi t4, t4, -66
	bnez t4, 212b
	lwu t4, 0(a6)
	xor t4, a3, t4
	lwu a3, 4(a6)
	xor a3, a3, a4
	or a4, t4, t4
	sb a3, 0(a1)
	srliw t4, a3, 8
	sb t4, 256(a1)
	srliw t4, a3, 16
	sb t4, 512(a1)
	srliw t4, a3, 24
	sb t4, 768(a1)
	sb a4, 1(a1)
	srliw t4, a4, 8
	sb t4, 257(a1)
	srliw t4, a4, 16
	sb t4, 513(a1)
	srliw t4, a4, 24
	sb t4, 769(a1)
	addi a1, a1, 2
	sub t4, a1, a7
	slli t4, t4, 56
	beqz t4, 213f
	j 214f
213:
	addi a1, a1, 768
214:
	addi a0, a0, -1
	bnez a0, 211b
	addi t0, a7, 0
	addi t4, zero, 1042
	slli t4, t4, 2
215:
	lbu t1, 0(t0)
	sb t1, 0(a2)
	addi t0, t0, 1
	addi a2, a2, 1
	addi t4, t4, -1
	bnez t4, 215b
	addi t1, zero, 0
	addi t0, a7, 0
	addi t4, zero, 522
216:
	sd t1, 0(t0)
	addi t0, t0, 8
	addi t4, t4, -1
	bnez t4, 216b
	addi sp, sp, 112
	addi sp, sp, 2032
	addi sp, sp, 2032
	ret
	.option pop

vg_blowfish_ecb_encrypt:
	.option push
	.option arch, +m, +c
	beqz a2, 20f
	addi sp, sp, -2032
	addi sp, sp, -2032
	addi sp, sp, -112
	addi a7, sp, 0
	addi t0, a7, 0
	addi t4, zero, 1042
	slli t4, t4, 2
22:
	lbu t1, 0(a0)
	sb t1, 0(t0)
	addi a0, a0, 1
	addi t0, t0, 1
	addi t4, t4, -1
	bnez t4, 22b
23:
	lbu a3, 0(a1)
	slli a3, a3, 24
	lbu t4, 1(a1)
	slli t4, t4, 16
	or a3, a3, t4
	lbu t4, 2(a1)
	slli t4, t4, 8
	or a3, a3, t4
	lbu t4, 3(a1)
	or a3, a3, t4
	lbu a4, 4(a1)
	slli a4, a4, 24
	lbu t4, 5(a1)
	slli t4, t4, 16
	or a4, a4, t4
	lbu t4, 6(a1)
	slli t4, t4, 8
	or a4, a4, t4
	lbu t4, 7(a1)
	or a4, a4, t4
	addi a6, a7, 2047
	addi a6, a6, 2047
	addi a6, a6, 2
24:
	lwu t4, 0(a6)
	xor a3, a3, t4
	slli t1, a3, 32
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 24
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	or a5, t2, t2
	addi a7, a7, 1024
	slli t1, a3, 40
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 16
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	add a5, a5, t2
	addi a7, a7, 1024
	slli t1, a3, 48
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 8
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	xor a5, a5, t2
	addi a7, a7, 1024
	slli t1, a3, 56
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 0
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	add a5, a5, t2
	addi a7, a7, -2048
	addi a7, a7, -1024
	xor a4, a4, a5
	or t4, a3, a3
	or a3, a4, a4
	or a4, t4, t4
	addi a6, a6, 4
	sub t4, a6, a7
	addi t4, t4, -2047
	addi t4, t4, -2047
	addi t4, t4, -66
	bnez t4, 24b
	lwu t4, 0(a6)
	xor t4, a3, t4
	lwu a3, 4(a6)
	xor a3, a3, a4
	or a4, t4, t4
	srli t4, a3, 24
	sb t4, 0(a1)
	srli t4, a3, 16
	sb t4, 1(a1)
	srli t4, a3, 8
	sb t4, 2(a1)
	srli t4, a3, 0
	sb t4, 3(a1)
	srli t4, a4, 24
	sb t4, 4(a1)
	srli t4, a4, 16
	sb t4, 5(a1)
	srli t4, a4, 8
	sb t4, 6(a1)
	srli t4, a4, 0
	sb t4, 7(a1)
	addi a1, a1, 8
	addi a2, a2, -1
	bnez a2, 23b
	addi t1, zero, 0
	addi t0, a7, 0
	addi t4, zero, 522
25:
	sd t1, 0(t0)
	addi t0, t0, 8
	addi t4, t4, -1
	bnez t4, 25b
	addi sp, sp, 112
	addi sp, sp, 2032
	addi sp, sp, 2032
	j 21f
20:
21:
	ret
	.option pop

vg_blowfish_ecb_decrypt:
	.option push
	.option arch, +m, +c
	beqz a2, 20f
	addi sp, sp, -2032
	addi sp, sp, -2032
	addi sp, sp, -112
	addi a7, sp, 0
	addi t0, a7, 0
	addi t4, zero, 1042
	slli t4, t4, 2
22:
	lbu t1, 0(a0)
	sb t1, 0(t0)
	addi a0, a0, 1
	addi t0, t0, 1
	addi t4, t4, -1
	bnez t4, 22b
23:
	lbu a3, 0(a1)
	slli a3, a3, 24
	lbu t4, 1(a1)
	slli t4, t4, 16
	or a3, a3, t4
	lbu t4, 2(a1)
	slli t4, t4, 8
	or a3, a3, t4
	lbu t4, 3(a1)
	or a3, a3, t4
	lbu a4, 4(a1)
	slli a4, a4, 24
	lbu t4, 5(a1)
	slli t4, t4, 16
	or a4, a4, t4
	lbu t4, 6(a1)
	slli t4, t4, 8
	or a4, a4, t4
	lbu t4, 7(a1)
	or a4, a4, t4
	addi a6, a7, 2047
	addi a6, a6, 2047
	addi a6, a6, 66
24:
	lwu t4, 4(a6)
	xor a3, a3, t4
	slli t1, a3, 32
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 24
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	or a5, t2, t2
	addi a7, a7, 1024
	slli t1, a3, 40
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 16
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	add a5, a5, t2
	addi a7, a7, 1024
	slli t1, a3, 48
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 8
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	xor a5, a5, t2
	addi a7, a7, 1024
	slli t1, a3, 56
	srli t1, t1, 59
	addi t3, zero, 1
	sll t1, t3, t1
	slli t3, t1, 63
	srai t3, t3, 63
	ld t2, 0(a7)
	and t2, t2, t3
	ld t5, 256(a7)
	and t5, t5, t3
	ld t6, 512(a7)
	and t6, t6, t3
	ld t0, 768(a7)
	and t0, t0, t3
	slli t3, t1, 62
	srai t3, t3, 63
	ld t4, 8(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 264(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 520(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 776(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 61
	srai t3, t3, 63
	ld t4, 16(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 272(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 528(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 784(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 60
	srai t3, t3, 63
	ld t4, 24(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 280(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 536(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 792(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 59
	srai t3, t3, 63
	ld t4, 32(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 288(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 544(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 800(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 58
	srai t3, t3, 63
	ld t4, 40(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 296(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 552(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 808(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 57
	srai t3, t3, 63
	ld t4, 48(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 304(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 560(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 816(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 56
	srai t3, t3, 63
	ld t4, 56(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 312(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 568(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 824(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 55
	srai t3, t3, 63
	ld t4, 64(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 320(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 576(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 832(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 54
	srai t3, t3, 63
	ld t4, 72(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 328(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 584(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 840(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 53
	srai t3, t3, 63
	ld t4, 80(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 336(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 592(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 848(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 52
	srai t3, t3, 63
	ld t4, 88(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 344(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 600(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 856(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 51
	srai t3, t3, 63
	ld t4, 96(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 352(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 608(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 864(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 50
	srai t3, t3, 63
	ld t4, 104(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 360(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 616(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 872(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 49
	srai t3, t3, 63
	ld t4, 112(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 368(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 624(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 880(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 48
	srai t3, t3, 63
	ld t4, 120(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 376(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 632(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 888(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 47
	srai t3, t3, 63
	ld t4, 128(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 384(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 640(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 896(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 46
	srai t3, t3, 63
	ld t4, 136(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 392(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 648(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 904(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 45
	srai t3, t3, 63
	ld t4, 144(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 400(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 656(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 912(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 44
	srai t3, t3, 63
	ld t4, 152(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 408(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 664(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 920(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 43
	srai t3, t3, 63
	ld t4, 160(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 416(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 672(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 928(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 42
	srai t3, t3, 63
	ld t4, 168(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 424(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 680(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 936(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 41
	srai t3, t3, 63
	ld t4, 176(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 432(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 688(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 944(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 40
	srai t3, t3, 63
	ld t4, 184(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 440(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 696(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 952(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 39
	srai t3, t3, 63
	ld t4, 192(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 448(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 704(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 960(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 38
	srai t3, t3, 63
	ld t4, 200(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 456(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 712(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 968(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 37
	srai t3, t3, 63
	ld t4, 208(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 464(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 720(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 976(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 36
	srai t3, t3, 63
	ld t4, 216(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 472(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 728(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 984(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 35
	srai t3, t3, 63
	ld t4, 224(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 480(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 736(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 992(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 34
	srai t3, t3, 63
	ld t4, 232(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 488(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 744(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1000(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 33
	srai t3, t3, 63
	ld t4, 240(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 496(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 752(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1008(a7)
	and t4, t4, t3
	or t0, t0, t4
	slli t3, t1, 32
	srai t3, t3, 63
	ld t4, 248(a7)
	and t4, t4, t3
	or t2, t2, t4
	ld t4, 504(a7)
	and t4, t4, t3
	or t5, t5, t4
	ld t4, 760(a7)
	and t4, t4, t3
	or t6, t6, t4
	ld t4, 1016(a7)
	and t4, t4, t3
	or t0, t0, t4
	srli t3, a3, 0
	andi t3, t3, 7
	slli t3, t3, 3
	srl t2, t2, t3
	andi t2, t2, 255
	srl t5, t5, t3
	andi t5, t5, 255
	slli t5, t5, 8
	srl t6, t6, t3
	andi t6, t6, 255
	slli t6, t6, 16
	srl t0, t0, t3
	andi t0, t0, 255
	slli t0, t0, 24
	or t2, t2, t5
	or t6, t6, t0
	or t2, t2, t6
	add a5, a5, t2
	addi a7, a7, -2048
	addi a7, a7, -1024
	xor a4, a4, a5
	or t4, a3, a3
	or a3, a4, a4
	or a4, t4, t4
	addi a6, a6, -4
	sub t4, a6, a7
	addi t4, t4, -2047
	addi t4, t4, -2047
	addi t4, t4, -2
	bnez t4, 24b
	lwu t4, 4(a6)
	xor t4, a3, t4
	lwu a3, 0(a6)
	xor a3, a3, a4
	or a4, t4, t4
	srli t4, a3, 24
	sb t4, 0(a1)
	srli t4, a3, 16
	sb t4, 1(a1)
	srli t4, a3, 8
	sb t4, 2(a1)
	srli t4, a3, 0
	sb t4, 3(a1)
	srli t4, a4, 24
	sb t4, 4(a1)
	srli t4, a4, 16
	sb t4, 5(a1)
	srli t4, a4, 8
	sb t4, 6(a1)
	srli t4, a4, 0
	sb t4, 7(a1)
	addi a1, a1, 8
	addi a2, a2, -1
	bnez a2, 23b
	addi t1, zero, 0
	addi t0, a7, 0
	addi t4, zero, 522
25:
	sd t1, 0(t0)
	addi t0, t0, 8
	addi t4, t4, -1
	bnez t4, 25b
	addi sp, sp, 112
	addi sp, sp, 2032
	addi sp, sp, 2032
	j 21f
20:
21:
	ret
	.option pop
