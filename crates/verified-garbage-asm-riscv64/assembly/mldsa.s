// The functions of `src/mldsa.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_ntt:
	.option push
	.option arch, +m, +c
	lui t2, 0
	addi t2, t2, 1
	sw t2, 0(a1)
	lui t2, 1174
	addi t2, t2, -510
	sw t2, 4(a1)
	lui t2, 919
	addi t2, t2, 1383
	sw t2, 8(a1)
	lui t2, 918
	addi t2, t2, 1385
	sw t2, 12(a1)
	lui t2, 1264
	addi t2, t2, 1579
	sw t2, 16(a1)
	lui t2, 1342
	addi t2, t2, -141
	sw t2, 20(a1)
	lui t2, 1278
	addi t2, t2, 51
	sw t2, 24(a1)
	lui t2, 1264
	addi t2, t2, 1643
	sw t2, 28(a1)
	lui t2, 1899
	addi t2, t2, 430
	sw t2, 32(a1)
	lui t2, 865
	addi t2, t2, -555
	sw t2, 36(a1)
	lui t2, 655
	addi t2, t2, -592
	sw t2, 40(a1)
	lui t2, 520
	addi t2, t2, -28
	sw t2, 44(a1)
	lui t2, 919
	addi t2, t2, 643
	sw t2, 48(a1)
	lui t2, 1801
	addi t2, t2, -1718
	sw t2, 52(a1)
	lui t2, 136
	addi t2, t2, 402
	sw t2, 56(a1)
	lui t2, 1748
	addi t2, t2, -568
	sw t2, 60(a1)
	lui t2, 1223
	addi t2, t2, 660
	sw t2, 64(a1)
	lui t2, 1054
	addi t2, t2, 180
	sw t2, 68(a1)
	lui t2, 650
	addi t2, t2, 978
	sw t2, 72(a1)
	lui t2, 1637
	addi t2, t2, 650
	sw t2, 76(a1)
	lui t2, 1186
	addi t2, t2, -1881
	sw t2, 80(a1)
	lui t2, 1940
	addi t2, t2, 52
	sw t2, 84(a1)
	lui t2, 165
	addi t2, t2, 750
	sw t2, 88(a1)
	lui t2, 1720
	addi t2, t2, -639
	sw t2, 92(a1)
	lui t2, 1258
	addi t2, t2, -227
	sw t2, 96(a1)
	lui t2, 419
	addi t2, t2, -1929
	sw t2, 100(a1)
	lui t2, 599
	addi t2, t2, 479
	sw t2, 104(a1)
	lui t2, 357
	addi t2, t2, -1554
	sw t2, 108(a1)
	lui t2, 1889
	addi t2, t2, 445
	sw t2, 112(a1)
	lui t2, 1171
	addi t2, t2, -1097
	sw t2, 116(a1)
	lui t2, 687
	addi t2, t2, 1687
	sw t2, 120(a1)
	lui t2, 558
	addi t2, t2, -1835
	sw t2, 124(a1)
	lui t2, 879
	addi t2, t2, 1834
	sw t2, 128(a1)
	lui t2, 777
	addi t2, t2, 286
	sw t2, 132(a1)
	lui t2, 669
	addi t2, t2, 319
	sw t2, 136(a1)
	lui t2, 1170
	addi t2, t2, 1651
	sw t2, 140(a1)
	lui t2, 1287
	addi t2, t2, -1953
	sw t2, 144(a1)
	lui t2, 513
	addi t2, t2, 162
	sw t2, 148(a1)
	lui t2, 904
	addi t2, t2, 2039
	sw t2, 152(a1)
	lui t2, 283
	addi t2, t2, 707
	sw t2, 156(a1)
	lui t2, 96
	addi t2, t2, 932
	sw t2, 160(a1)
	lui t2, 227
	addi t2, t2, -1043
	sw t2, 164(a1)
	lui t2, 267
	addi t2, t2, 1836
	sw t2, 168(a1)
	lui t2, 1190
	addi t2, t2, -203
	sw t2, 172(a1)
	lui t2, 506
	addi t2, t2, -747
	sw t2, 176(a1)
	lui t2, 1065
	addi t2, t2, -812
	sw t2, 180(a1)
	lui t2, 791
	addi t2, t2, 2036
	sw t2, 184(a1)
	lui t2, 526
	addi t2, t2, 1554
	sw t2, 188(a1)
	lui t2, 834
	addi t2, t2, -995
	sw t2, 192(a1)
	lui t2, 430
	addi t2, t2, -1933
	sw t2, 196(a1)
	lui t2, 1846
	addi t2, t2, 1665
	sw t2, 200(a1)
	lui t2, 1173
	addi t2, t2, 1343
	sw t2, 204(a1)
	lui t2, 917
	addi t2, t2, 758
	sw t2, 208(a1)
	lui t2, 1573
	addi t2, t2, 1610
	sw t2, 212(a1)
	lui t2, 1627
	addi t2, t2, -763
	sw t2, 216(a1)
	lui t2, 1082
	addi t2, t2, -1508
	sw t2, 220(a1)
	lui t2, 1339
	addi t2, t2, -1441
	sw t2, 224(a1)
	lui t2, 779
	addi t2, t2, 1570
	sw t2, 228(a1)
	lui t2, 136
	addi t2, t2, -200
	sw t2, 232(a1)
	lui t2, 945
	addi t2, t2, -403
	sw t2, 236(a1)
	lui t2, 712
	addi t2, t2, 986
	sw t2, 240(a1)
	lui t2, 453
	addi t2, t2, -1682
	sw t2, 244(a1)
	lui t2, 817
	addi t2, t2, -469
	sw t2, 248(a1)
	lui t2, 454
	addi t2, t2, -1168
	sw t2, 252(a1)
	lui t2, 750
	addi t2, t2, 1009
	sw t2, 256(a1)
	lui t2, 312
	addi t2, t2, -327
	sw t2, 260(a1)
	lui t2, 1403
	addi t2, t2, -1744
	sw t2, 264(a1)
	lui t2, 940
	addi t2, t2, 1775
	sw t2, 268(a1)
	lui t2, 1021
	addi t2, t2, 1356
	sw t2, 272(a1)
	lui t2, 1259
	addi t2, t2, 746
	sw t2, 276(a1)
	lui t2, 1284
	addi t2, t2, -287
	sw t2, 280(a1)
	lui t2, 1979
	addi t2, t2, 373
	sw t2, 284(a1)
	lui t2, 613
	addi t2, t2, -1868
	sw t2, 288(a1)
	lui t2, 495
	addi t2, t2, 598
	sw t2, 292(a1)
	lui t2, 473
	addi t2, t2, 162
	sw t2, 296(a1)
	lui t2, 1114
	addi t2, t2, 1748
	sw t2, 300(a1)
	lui t2, 686
	addi t2, t2, 1435
	sw t2, 304(a1)
	lui t2, 1318
	addi t2, t2, -1892
	sw t2, 308(a1)
	lui t2, 1775
	addi t2, t2, 501
	sw t2, 312(a1)
	lui t2, 1015
	addi t2, t2, 648
	sw t2, 316(a1)
	lui t2, 373
	addi t2, t2, 258
	sw t2, 320(a1)
	lui t2, 118
	addi t2, t2, -679
	sw t2, 324(a1)
	lui t2, 280
	addi t2, t2, 1978
	sw t2, 328(a1)
	lui t2, 1323
	addi t2, t2, -855
	sw t2, 332(a1)
	lui t2, 1908
	addi t2, t2, -354
	sw t2, 336(a1)
	lui t2, 41
	addi t2, t2, 1752
	sw t2, 340(a1)
	lui t2, 601
	addi t2, t2, 748
	sw t2, 344(a1)
	lui t2, 1232
	addi t2, t2, -238
	sw t2, 348(a1)
	lui t2, 1029
	addi t2, t2, -792
	sw t2, 352(a1)
	lui t2, 1194
	addi t2, t2, 1410
	sw t2, 356(a1)
	lui t2, 485
	addi t2, t2, 1254
	sw t2, 360(a1)
	lui t2, 1265
	addi t2, t2, 1729
	sw t2, 364(a1)
	lui t2, 424
	addi t2, t2, -391
	sw t2, 368(a1)
	lui t2, 57
	addi t2, t2, 1935
	sw t2, 372(a1)
	lui t2, 1253
	addi t2, t2, -2025
	sw t2, 376(a1)
	lui t2, 796
	addi t2, t2, -1959
	sw t2, 380(a1)
	lui t2, 1416
	addi t2, t2, 1228
	sw t2, 384(a1)
	lui t2, 437
	addi t2, t2, -2009
	sw t2, 388(a1)
	lui t2, 1462
	addi t2, t2, 976
	sw t2, 392(a1)
	lui t2, 1496
	addi t2, t2, -1926
	sw t2, 396(a1)
	lui t2, 850
	addi t2, t2, 606
	sw t2, 400(a1)
	lui t2, 1025
	addi t2, t2, -898
	sw t2, 404(a1)
	lui t2, 1729
	addi t2, t2, -1583
	sw t2, 408(a1)
	lui t2, 1469
	addi t2, t2, 1330
	sw t2, 412(a1)
	lui t2, 1724
	addi t2, t2, 1235
	sw t2, 416(a1)
	lui t2, 601
	addi t2, t2, -309
	sw t2, 420(a1)
	lui t2, 741
	addi t2, t2, 844
	sw t2, 424(a1)
	lui t2, 152
	addi t2, t2, -1428
	sw t2, 428(a1)
	lui t2, 953
	addi t2, t2, -2016
	sw t2, 432(a1)
	lui t2, 1747
	addi t2, t2, -1956
	sw t2, 436(a1)
	lui t2, 714
	addi t2, t2, 1272
	sw t2, 440(a1)
	lui t2, 824
	addi t2, t2, -854
	sw t2, 444(a1)
	lui t2, 331
	addi t2, t2, 672
	sw t2, 448(a1)
	lui t2, 1368
	addi t2, t2, 1334
	sw t2, 452(a1)
	lui t2, 655
	addi t2, t2, 390
	sw t2, 456(a1)
	lui t2, 1368
	addi t2, t2, -1699
	sw t2, 460(a1)
	lui t2, 1199
	addi t2, t2, 1648
	sw t2, 464(a1)
	lui t2, 565
	addi t2, t2, -1402
	sw t2, 468(a1)
	lui t2, 1887
	addi t2, t2, -2010
	sw t2, 472(a1)
	lui t2, 1934
	addi t2, t2, -410
	sw t2, 476(a1)
	lui t2, 85
	addi t2, t2, 652
	sw t2, 480(a1)
	lui t2, 1966
	addi t2, t2, -167
	sw t2, 484(a1)
	lui t2, 247
	addi t2, t2, -489
	sw t2, 488(a1)
	lui t2, 1471
	addi t2, t2, 986
	sw t2, 492(a1)
	lui t2, 1114
	addi t2, t2, -1154
	sw t2, 496(a1)
	lui t2, 1577
	addi t2, t2, -1228
	sw t2, 500(a1)
	lui t2, 1500
	addi t2, t2, -309
	sw t2, 504(a1)
	lui t2, 426
	addi t2, t2, -389
	sw t2, 508(a1)
	lui t2, 0
	addi t2, t2, 1753
	sw t2, 512(a1)
	lui t2, 1573
	addi t2, t2, 1989
	sw t2, 516(a1)
	lui t2, 1397
	addi t2, t2, -1220
	sw t2, 520(a1)
	lui t2, 1691
	addi t2, t2, -1809
	sw t2, 524(a1)
	lui t2, 650
	addi t2, t2, -1992
	sw t2, 528(a1)
	lui t2, 1611
	addi t2, t2, 1534
	sw t2, 532(a1)
	lui t2, 2032
	addi t2, t2, -1803
	sw t2, 536(a1)
	lui t2, 677
	addi t2, t2, -392
	sw t2, 540(a1)
	lui t2, 289
	addi t2, t2, -1501
	sw t2, 544(a1)
	lui t2, 21
	addi t2, t2, 1192
	sw t2, 548(a1)
	lui t2, 155
	addi t2, t2, 2047
	sw t2, 552(a1)
	lui t2, 1078
	addi t2, t2, -377
	sw t2, 556(a1)
	lui t2, 1080
	addi t2, t2, -8
	sw t2, 560(a1)
	lui t2, 1485
	addi t2, t2, 1460
	sw t2, 564(a1)
	lui t2, 1244
	addi t2, t2, 78
	sw t2, 568(a1)
	lui t2, 1139
	addi t2, t2, -1873
	sw t2, 572(a1)
	lui t2, 2039
	addi t2, t2, 861
	sw t2, 576(a1)
	lui t2, 201
	addi t2, t2, -755
	sw t2, 580(a1)
	lui t2, 246
	addi t2, t2, 1749
	sw t2, 584(a1)
	lui t2, 1447
	addi t2, t2, -640
	sw t2, 588(a1)
	lui t2, 1563
	addi t2, t2, -1128
	sw t2, 592(a1)
	lui t2, 390
	addi t2, t2, -618
	sw t2, 596(a1)
	lui t2, 1080
	addi t2, t2, -207
	sw t2, 600(a1)
	lui t2, 1128
	addi t2, t2, 664
	sw t2, 604(a1)
	lui t2, 1635
	addi t2, t2, -1696
	sw t2, 608(a1)
	lui t2, 1213
	addi t2, t2, 1401
	sw t2, 612(a1)
	lui t2, 654
	addi t2, t2, -506
	sw t2, 616(a1)
	lui t2, 1126
	addi t2, t2, -627
	sw t2, 620(a1)
	lui t2, 1179
	addi t2, t2, 227
	sw t2, 624(a1)
	lui t2, 155
	addi t2, t2, 1076
	sw t2, 628(a1)
	lui t2, 1985
	addi t2, t2, -589
	sw t2, 632(a1)
	lui t2, 1447
	addi t2, t2, -1872
	sw t2, 636(a1)
	lui t2, 1034
	addi t2, t2, -1111
	sw t2, 640(a1)
	lui t2, 1613
	addi t2, t2, 981
	sw t2, 644(a1)
	lui t2, 535
	addi t2, t2, 1578
	sw t2, 648(a1)
	lui t2, 1624
	addi t2, t2, 1425
	sw t2, 652(a1)
	lui t2, 583
	addi t2, t2, -455
	sw t2, 656(a1)
	lui t2, 1164
	addi t2, t2, 923
	sw t2, 660(a1)
	lui t2, 1980
	addi t2, t2, 1881
	sw t2, 664(a1)
	lui t2, 1270
	addi t2, t2, -1959
	sw t2, 668(a1)
	lui t2, 915
	addi t2, t2, -590
	sw t2, 672(a1)
	lui t2, 561
	addi t2, t2, -1757
	sw t2, 676(a1)
	lui t2, 303
	addi t2, t2, -1177
	sw t2, 680(a1)
	lui t2, 1109
	addi t2, t2, -526
	sw t2, 684(a1)
	lui t2, 780
	addi t2, t2, 796
	sw t2, 688(a1)
	lui t2, 645
	addi t2, t2, 1060
	sw t2, 692(a1)
	lui t2, 306
	addi t2, t2, 814
	sw t2, 696(a1)
	lui t2, 2043
	addi t2, t2, -128
	sw t2, 700(a1)
	lui t2, 732
	addi t2, t2, -53
	sw t2, 704(a1)
	lui t2, 35
	addi t2, t2, -1525
	sw t2, 708(a1)
	lui t2, 2024
	addi t2, t2, 812
	sw t2, 712(a1)
	lui t2, 614
	addi t2, t2, -1926
	sw t2, 716(a1)
	lui t2, 1715
	addi t2, t2, 885
	sw t2, 720(a1)
	lui t2, 150
	addi t2, t2, -1162
	sw t2, 724(a1)
	lui t2, 1726
	addi t2, t2, 460
	sw t2, 728(a1)
	lui t2, 1504
	addi t2, t2, 1566
	sw t2, 732(a1)
	lui t2, 1934
	addi t2, t2, 13
	sw t2, 736(a1)
	lui t2, 1577
	addi t2, t2, -969
	sw t2, 740(a1)
	lui t2, 986
	addi t2, t2, 1540
	sw t2, 744(a1)
	lui t2, 1198
	addi t2, t2, 1340
	sw t2, 748(a1)
	lui t2, 498
	addi t2, t2, -664
	sw t2, 752(a1)
	lui t2, 1587
	addi t2, t2, 187
	sw t2, 756(a1)
	lui t2, 1846
	addi t2, t2, 440
	sw t2, 760(a1)
	lui t2, 1514
	addi t2, t2, 108
	sw t2, 764(a1)
	lui t2, 1650
	addi t2, t2, -1337
	sw t2, 768(a1)
	lui t2, 514
	addi t2, t2, -58
	sw t2, 772(a1)
	lui t2, 1466
	addi t2, t2, 1279
	sw t2, 776(a1)
	lui t2, 1549
	addi t2, t2, 1906
	sw t2, 780(a1)
	lui t2, 143
	addi t2, t2, 513
	sw t2, 784(a1)
	lui t2, 1758
	addi t2, t2, 36
	sw t2, 788(a1)
	lui t2, 129
	addi t2, t2, -403
	sw t2, 792(a1)
	lui t2, 1376
	addi t2, t2, 910
	sw t2, 796(a1)
	lui t2, 1685
	addi t2, t2, 1672
	sw t2, 800(a1)
	lui t2, 487
	addi t2, t2, -706
	sw t2, 804(a1)
	lui t2, 608
	addi t2, t2, 957
	sw t2, 808(a1)
	lui t2, 1706
	addi t2, t2, -518
	sw t2, 812(a1)
	lui t2, 124
	addi t2, t2, 23
	sw t2, 816(a1)
	lui t2, 1756
	addi t2, t2, -44
	sw t2, 820(a1)
	lui t2, 1869
	addi t2, t2, 189
	sw t2, 824(a1)
	lui t2, 1598
	addi t2, t2, 483
	sw t2, 828(a1)
	lui t2, 1305
	addi t2, t2, 1395
	sw t2, 832(a1)
	lui t2, 1963
	addi t2, t2, 1549
	sw t2, 836(a1)
	lui t2, 646
	addi t2, t2, 1978
	sw t2, 840(a1)
	lui t2, 735
	addi t2, t2, -812
	sw t2, 844(a1)
	lui t2, 1408
	addi t2, t2, 396
	sw t2, 848(a1)
	lui t2, 1013
	addi t2, t2, -779
	sw t2, 852(a1)
	lui t2, 183
	addi t2, t2, 9
	sw t2, 856(a1)
	lui t2, 1064
	addi t2, t2, -477
	sw t2, 860(a1)
	lui t2, 972
	addi t2, t2, -713
	sw t2, 864(a1)
	lui t2, 627
	addi t2, t2, 819
	sw t2, 868(a1)
	lui t2, 1652
	addi t2, t2, -1705
	sw t2, 872(a1)
	lui t2, 421
	addi t2, t2, -1187
	sw t2, 876(a1)
	lui t2, 407
	addi t2, t2, -1754
	sw t2, 880(a1)
	lui t2, 495
	addi t2, t2, 518
	sw t2, 884(a1)
	lui t2, 284
	addi t2, t2, 334
	sw t2, 888(a1)
	lui t2, 1223
	addi t2, t2, 1736
	sw t2, 892(a1)
	lui t2, 975
	addi t2, t2, 1071
	sw t2, 896(a1)
	lui t2, 2043
	addi t2, t2, 410
	sw t2, 900(a1)
	lui t2, 1711
	addi t2, t2, 1644
	sw t2, 904(a1)
	lui t2, 737
	addi t2, t2, 1641
	sw t2, 908(a1)
	lui t2, 821
	addi t2, t2, 726
	sw t2, 912(a1)
	lui t2, 52
	addi t2, t2, 1888
	sw t2, 916(a1)
	lui t2, 133
	addi t2, t2, 608
	sw t2, 920(a1)
	lui t2, 1858
	addi t2, t2, -392
	sw t2, 924(a1)
	lui t2, 758
	addi t2, t2, 790
	sw t2, 928(a1)
	lui t2, 1777
	addi t2, t2, -1519
	sw t2, 932(a1)
	lui t2, 124
	addi t2, t2, 241
	sw t2, 936(a1)
	lui t2, 1911
	addi t2, t2, -757
	sw t2, 940(a1)
	lui t2, 210
	addi t2, t2, -16
	sw t2, 944(a1)
	lui t2, 838
	addi t2, t2, -2012
	sw t2, 948(a1)
	lui t2, 34
	addi t2, t2, 980
	sw t2, 952(a1)
	lui t2, 1676
	addi t2, t2, 1369
	sw t2, 956(a1)
	lui t2, 1513
	addi t2, t2, -1915
	sw t2, 960(a1)
	lui t2, 763
	addi t2, t2, -1486
	sw t2, 964(a1)
	lui t2, 576
	addi t2, t2, -923
	sw t2, 968(a1)
	lui t2, 1511
	addi t2, t2, -1726
	sw t2, 972(a1)
	lui t2, 1310
	addi t2, t2, 237
	sw t2, 976(a1)
	lui t2, 1627
	addi t2, t2, -589
	sw t2, 980(a1)
	lui t2, 714
	addi t2, t2, 1510
	sw t2, 984(a1)
	lui t2, 1950
	addi t2, t2, 510
	sw t2, 988(a1)
	lui t2, 1972
	addi t2, t2, 100
	sw t2, 992(a1)
	lui t2, 862
	addi t2, t2, 477
	sw t2, 996(a1)
	lui t2, 1076
	addi t2, t2, -1364
	sw t2, 1000(a1)
	lui t2, 1125
	addi t2, t2, -1314
	sw t2, 1004(a1)
	lui t2, 464
	addi t2, t2, -492
	sw t2, 1008(a1)
	lui t2, 1855
	addi t2, t2, 462
	sw t2, 1012(a1)
	lui t2, 257
	addi t2, t2, 1806
	sw t2, 1016(a1)
	lui t2, 1867
	addi t2, t2, 1751
	sw t2, 1020(a1)
	lui a5, 131200
	addi a5, a5, 448
	slli a5, a5, 12
	addi a5, a5, 1537
	lui a6, 2046
	addi a6, a6, 1
	addi a0, a0, 1024
	addi a1, a1, 4
	addi a7, zero, 512
20:
	addi a2, a0, -1024
21:
	lwu a4, 0(a1)
	addi a1, a1, 4
	add a3, a2, a7
	srli t1, a7, 2
22:
	lwu t2, 0(a2)
	lwu t0, 0(a3)
	mul t0, a4, t0
	mulhu t3, t0, a5
	sub t0, t0, t3
	slli t3, t3, 13
	add t0, t0, t3
	slli t3, t3, 10
	sub t0, t0, t3
	sub t0, t0, a6
	srai t3, t0, 63
	and t3, t3, a6
	add t0, t0, t3
	sub t3, t2, t0
	srai t4, t3, 63
	and t4, t4, a6
	add t3, t3, t4
	sw t3, 0(a3)
	add t2, t2, t0
	sub t2, t2, a6
	srai t4, t2, 63
	and t4, t4, a6
	add t2, t2, t4
	sw t2, 0(a2)
	addi a2, a2, 4
	addi a3, a3, 4
	addi t1, t1, -1
	bnez t1, 22b
	addi a2, a3, 0
	sub t0, a2, a0
	bnez t0, 21b
	srli a7, a7, 1
	addi t0, a7, -2
	bnez t0, 20b
	ret
	.option pop

vg_mldsa_inv_ntt:
	.option push
	.option arch, +m, +c
	lui t2, 2046
	addi t2, t2, 0
	sw t2, 0(a1)
	lui t2, 872
	addi t2, t2, 511
	sw t2, 4(a1)
	lui t2, 1127
	addi t2, t2, -1382
	sw t2, 8(a1)
	lui t2, 1128
	addi t2, t2, -1384
	sw t2, 12(a1)
	lui t2, 782
	addi t2, t2, -1578
	sw t2, 16(a1)
	lui t2, 704
	addi t2, t2, 142
	sw t2, 20(a1)
	lui t2, 768
	addi t2, t2, -50
	sw t2, 24(a1)
	lui t2, 782
	addi t2, t2, -1642
	sw t2, 28(a1)
	lui t2, 147
	addi t2, t2, -429
	sw t2, 32(a1)
	lui t2, 1181
	addi t2, t2, 556
	sw t2, 36(a1)
	lui t2, 1391
	addi t2, t2, 593
	sw t2, 40(a1)
	lui t2, 1526
	addi t2, t2, 29
	sw t2, 44(a1)
	lui t2, 1127
	addi t2, t2, -642
	sw t2, 48(a1)
	lui t2, 245
	addi t2, t2, 1719
	sw t2, 52(a1)
	lui t2, 1910
	addi t2, t2, -401
	sw t2, 56(a1)
	lui t2, 298
	addi t2, t2, 569
	sw t2, 60(a1)
	lui t2, 823
	addi t2, t2, -659
	sw t2, 64(a1)
	lui t2, 992
	addi t2, t2, -179
	sw t2, 68(a1)
	lui t2, 1396
	addi t2, t2, -977
	sw t2, 72(a1)
	lui t2, 409
	addi t2, t2, -649
	sw t2, 76(a1)
	lui t2, 860
	addi t2, t2, 1882
	sw t2, 80(a1)
	lui t2, 106
	addi t2, t2, -51
	sw t2, 84(a1)
	lui t2, 1881
	addi t2, t2, -749
	sw t2, 88(a1)
	lui t2, 326
	addi t2, t2, 640
	sw t2, 92(a1)
	lui t2, 788
	addi t2, t2, 228
	sw t2, 96(a1)
	lui t2, 1627
	addi t2, t2, 1930
	sw t2, 100(a1)
	lui t2, 1447
	addi t2, t2, -478
	sw t2, 104(a1)
	lui t2, 1689
	addi t2, t2, 1555
	sw t2, 108(a1)
	lui t2, 157
	addi t2, t2, -444
	sw t2, 112(a1)
	lui t2, 875
	addi t2, t2, 1098
	sw t2, 116(a1)
	lui t2, 1359
	addi t2, t2, -1686
	sw t2, 120(a1)
	lui t2, 1488
	addi t2, t2, 1836
	sw t2, 124(a1)
	lui t2, 1167
	addi t2, t2, -1833
	sw t2, 128(a1)
	lui t2, 1269
	addi t2, t2, -285
	sw t2, 132(a1)
	lui t2, 1377
	addi t2, t2, -318
	sw t2, 136(a1)
	lui t2, 876
	addi t2, t2, -1650
	sw t2, 140(a1)
	lui t2, 759
	addi t2, t2, 1954
	sw t2, 144(a1)
	lui t2, 1533
	addi t2, t2, -161
	sw t2, 148(a1)
	lui t2, 1142
	addi t2, t2, -2038
	sw t2, 152(a1)
	lui t2, 1763
	addi t2, t2, -706
	sw t2, 156(a1)
	lui t2, 1950
	addi t2, t2, -931
	sw t2, 160(a1)
	lui t2, 1819
	addi t2, t2, 1044
	sw t2, 164(a1)
	lui t2, 1779
	addi t2, t2, -1835
	sw t2, 168(a1)
	lui t2, 856
	addi t2, t2, 204
	sw t2, 172(a1)
	lui t2, 1540
	addi t2, t2, 748
	sw t2, 176(a1)
	lui t2, 981
	addi t2, t2, 813
	sw t2, 180(a1)
	lui t2, 1255
	addi t2, t2, -2035
	sw t2, 184(a1)
	lui t2, 1520
	addi t2, t2, -1553
	sw t2, 188(a1)
	lui t2, 1212
	addi t2, t2, 996
	sw t2, 192(a1)
	lui t2, 1616
	addi t2, t2, 1934
	sw t2, 196(a1)
	lui t2, 200
	addi t2, t2, -1664
	sw t2, 200(a1)
	lui t2, 873
	addi t2, t2, -1342
	sw t2, 204(a1)
	lui t2, 1129
	addi t2, t2, -757
	sw t2, 208(a1)
	lui t2, 473
	addi t2, t2, -1609
	sw t2, 212(a1)
	lui t2, 419
	addi t2, t2, 764
	sw t2, 216(a1)
	lui t2, 964
	addi t2, t2, 1509
	sw t2, 220(a1)
	lui t2, 707
	addi t2, t2, 1442
	sw t2, 224(a1)
	lui t2, 1267
	addi t2, t2, -1569
	sw t2, 228(a1)
	lui t2, 1910
	addi t2, t2, 201
	sw t2, 232(a1)
	lui t2, 1101
	addi t2, t2, 404
	sw t2, 236(a1)
	lui t2, 1334
	addi t2, t2, -985
	sw t2, 240(a1)
	lui t2, 1593
	addi t2, t2, 1683
	sw t2, 244(a1)
	lui t2, 1229
	addi t2, t2, 470
	sw t2, 248(a1)
	lui t2, 1592
	addi t2, t2, 1169
	sw t2, 252(a1)
	lui t2, 1296
	addi t2, t2, -1008
	sw t2, 256(a1)
	lui t2, 1734
	addi t2, t2, 328
	sw t2, 260(a1)
	lui t2, 643
	addi t2, t2, 1745
	sw t2, 264(a1)
	lui t2, 1106
	addi t2, t2, -1774
	sw t2, 268(a1)
	lui t2, 1025
	addi t2, t2, -1355
	sw t2, 272(a1)
	lui t2, 787
	addi t2, t2, -745
	sw t2, 276(a1)
	lui t2, 762
	addi t2, t2, 288
	sw t2, 280(a1)
	lui t2, 67
	addi t2, t2, -372
	sw t2, 284(a1)
	lui t2, 1433
	addi t2, t2, 1869
	sw t2, 288(a1)
	lui t2, 1551
	addi t2, t2, -597
	sw t2, 292(a1)
	lui t2, 1573
	addi t2, t2, -161
	sw t2, 296(a1)
	lui t2, 932
	addi t2, t2, -1747
	sw t2, 300(a1)
	lui t2, 1360
	addi t2, t2, -1434
	sw t2, 304(a1)
	lui t2, 728
	addi t2, t2, 1893
	sw t2, 308(a1)
	lui t2, 271
	addi t2, t2, -500
	sw t2, 312(a1)
	lui t2, 1031
	addi t2, t2, -647
	sw t2, 316(a1)
	lui t2, 1673
	addi t2, t2, -257
	sw t2, 320(a1)
	lui t2, 1928
	addi t2, t2, 680
	sw t2, 324(a1)
	lui t2, 1766
	addi t2, t2, -1977
	sw t2, 328(a1)
	lui t2, 723
	addi t2, t2, 856
	sw t2, 332(a1)
	lui t2, 138
	addi t2, t2, 355
	sw t2, 336(a1)
	lui t2, 2005
	addi t2, t2, -1751
	sw t2, 340(a1)
	lui t2, 1445
	addi t2, t2, -747
	sw t2, 344(a1)
	lui t2, 814
	addi t2, t2, 239
	sw t2, 348(a1)
	lui t2, 1017
	addi t2, t2, 793
	sw t2, 352(a1)
	lui t2, 852
	addi t2, t2, -1409
	sw t2, 356(a1)
	lui t2, 1561
	addi t2, t2, -1253
	sw t2, 360(a1)
	lui t2, 781
	addi t2, t2, -1728
	sw t2, 364(a1)
	lui t2, 1622
	addi t2, t2, 392
	sw t2, 368(a1)
	lui t2, 1989
	addi t2, t2, -1934
	sw t2, 372(a1)
	lui t2, 793
	addi t2, t2, 2026
	sw t2, 376(a1)
	lui t2, 1250
	addi t2, t2, 1960
	sw t2, 380(a1)
	lui t2, 630
	addi t2, t2, -1227
	sw t2, 384(a1)
	lui t2, 1609
	addi t2, t2, 2010
	sw t2, 388(a1)
	lui t2, 584
	addi t2, t2, -975
	sw t2, 392(a1)
	lui t2, 550
	addi t2, t2, 1927
	sw t2, 396(a1)
	lui t2, 1196
	addi t2, t2, -605
	sw t2, 400(a1)
	lui t2, 1021
	addi t2, t2, 899
	sw t2, 404(a1)
	lui t2, 317
	addi t2, t2, 1584
	sw t2, 408(a1)
	lui t2, 577
	addi t2, t2, -1329
	sw t2, 412(a1)
	lui t2, 322
	addi t2, t2, -1234
	sw t2, 416(a1)
	lui t2, 1445
	addi t2, t2, 310
	sw t2, 420(a1)
	lui t2, 1305
	addi t2, t2, -843
	sw t2, 424(a1)
	lui t2, 1894
	addi t2, t2, 1429
	sw t2, 428(a1)
	lui t2, 1093
	addi t2, t2, 2017
	sw t2, 432(a1)
	lui t2, 299
	addi t2, t2, 1957
	sw t2, 436(a1)
	lui t2, 1332
	addi t2, t2, -1271
	sw t2, 440(a1)
	lui t2, 1222
	addi t2, t2, 855
	sw t2, 444(a1)
	lui t2, 1715
	addi t2, t2, -671
	sw t2, 448(a1)
	lui t2, 678
	addi t2, t2, -1333
	sw t2, 452(a1)
	lui t2, 1391
	addi t2, t2, -389
	sw t2, 456(a1)
	lui t2, 678
	addi t2, t2, 1700
	sw t2, 460(a1)
	lui t2, 847
	addi t2, t2, -1647
	sw t2, 464(a1)
	lui t2, 1481
	addi t2, t2, 1403
	sw t2, 468(a1)
	lui t2, 159
	addi t2, t2, 2011
	sw t2, 472(a1)
	lui t2, 112
	addi t2, t2, 411
	sw t2, 476(a1)
	lui t2, 1961
	addi t2, t2, -651
	sw t2, 480(a1)
	lui t2, 80
	addi t2, t2, 168
	sw t2, 484(a1)
	lui t2, 1799
	addi t2, t2, 490
	sw t2, 488(a1)
	lui t2, 575
	addi t2, t2, -985
	sw t2, 492(a1)
	lui t2, 932
	addi t2, t2, 1155
	sw t2, 496(a1)
	lui t2, 469
	addi t2, t2, 1229
	sw t2, 500(a1)
	lui t2, 546
	addi t2, t2, 310
	sw t2, 504(a1)
	lui t2, 1620
	addi t2, t2, 390
	sw t2, 508(a1)
	lui t2, 2046
	addi t2, t2, -1752
	sw t2, 512(a1)
	lui t2, 473
	addi t2, t2, -1988
	sw t2, 516(a1)
	lui t2, 649
	addi t2, t2, 1221
	sw t2, 520(a1)
	lui t2, 355
	addi t2, t2, 1810
	sw t2, 524(a1)
	lui t2, 1396
	addi t2, t2, 1993
	sw t2, 528(a1)
	lui t2, 435
	addi t2, t2, -1533
	sw t2, 532(a1)
	lui t2, 14
	addi t2, t2, 1804
	sw t2, 536(a1)
	lui t2, 1369
	addi t2, t2, 393
	sw t2, 540(a1)
	lui t2, 1757
	addi t2, t2, 1502
	sw t2, 544(a1)
	lui t2, 2025
	addi t2, t2, -1191
	sw t2, 548(a1)
	lui t2, 1891
	addi t2, t2, -2046
	sw t2, 552(a1)
	lui t2, 968
	addi t2, t2, 378
	sw t2, 556(a1)
	lui t2, 966
	addi t2, t2, 9
	sw t2, 560(a1)
	lui t2, 561
	addi t2, t2, -1459
	sw t2, 564(a1)
	lui t2, 802
	addi t2, t2, -77
	sw t2, 568(a1)
	lui t2, 907
	addi t2, t2, 1874
	sw t2, 572(a1)
	lui t2, 7
	addi t2, t2, -860
	sw t2, 576(a1)
	lui t2, 1845
	addi t2, t2, 756
	sw t2, 580(a1)
	lui t2, 1800
	addi t2, t2, -1748
	sw t2, 584(a1)
	lui t2, 599
	addi t2, t2, 641
	sw t2, 588(a1)
	lui t2, 483
	addi t2, t2, 1129
	sw t2, 592(a1)
	lui t2, 1656
	addi t2, t2, 619
	sw t2, 596(a1)
	lui t2, 966
	addi t2, t2, 208
	sw t2, 600(a1)
	lui t2, 918
	addi t2, t2, -663
	sw t2, 604(a1)
	lui t2, 411
	addi t2, t2, 1697
	sw t2, 608(a1)
	lui t2, 833
	addi t2, t2, -1400
	sw t2, 612(a1)
	lui t2, 1392
	addi t2, t2, 507
	sw t2, 616(a1)
	lui t2, 920
	addi t2, t2, 628
	sw t2, 620(a1)
	lui t2, 867
	addi t2, t2, -226
	sw t2, 624(a1)
	lui t2, 1891
	addi t2, t2, -1075
	sw t2, 628(a1)
	lui t2, 61
	addi t2, t2, 590
	sw t2, 632(a1)
	lui t2, 599
	addi t2, t2, 1873
	sw t2, 636(a1)
	lui t2, 1012
	addi t2, t2, 1112
	sw t2, 640(a1)
	lui t2, 433
	addi t2, t2, -980
	sw t2, 644(a1)
	lui t2, 1511
	addi t2, t2, -1577
	sw t2, 648(a1)
	lui t2, 422
	addi t2, t2, -1424
	sw t2, 652(a1)
	lui t2, 1463
	addi t2, t2, 456
	sw t2, 656(a1)
	lui t2, 882
	addi t2, t2, -922
	sw t2, 660(a1)
	lui t2, 66
	addi t2, t2, -1880
	sw t2, 664(a1)
	lui t2, 776
	addi t2, t2, 1960
	sw t2, 668(a1)
	lui t2, 1131
	addi t2, t2, 591
	sw t2, 672(a1)
	lui t2, 1485
	addi t2, t2, 1758
	sw t2, 676(a1)
	lui t2, 1743
	addi t2, t2, 1178
	sw t2, 680(a1)
	lui t2, 937
	addi t2, t2, 527
	sw t2, 684(a1)
	lui t2, 1266
	addi t2, t2, -795
	sw t2, 688(a1)
	lui t2, 1401
	addi t2, t2, -1059
	sw t2, 692(a1)
	lui t2, 1740
	addi t2, t2, -813
	sw t2, 696(a1)
	lui t2, 3
	addi t2, t2, 129
	sw t2, 700(a1)
	lui t2, 1314
	addi t2, t2, 54
	sw t2, 704(a1)
	lui t2, 2011
	addi t2, t2, 1526
	sw t2, 708(a1)
	lui t2, 22
	addi t2, t2, -811
	sw t2, 712(a1)
	lui t2, 1432
	addi t2, t2, 1927
	sw t2, 716(a1)
	lui t2, 331
	addi t2, t2, -884
	sw t2, 720(a1)
	lui t2, 1896
	addi t2, t2, 1163
	sw t2, 724(a1)
	lui t2, 320
	addi t2, t2, -459
	sw t2, 728(a1)
	lui t2, 542
	addi t2, t2, -1565
	sw t2, 732(a1)
	lui t2, 112
	addi t2, t2, -12
	sw t2, 736(a1)
	lui t2, 469
	addi t2, t2, 970
	sw t2, 740(a1)
	lui t2, 1060
	addi t2, t2, -1539
	sw t2, 744(a1)
	lui t2, 848
	addi t2, t2, -1339
	sw t2, 748(a1)
	lui t2, 1548
	addi t2, t2, 665
	sw t2, 752(a1)
	lui t2, 459
	addi t2, t2, -186
	sw t2, 756(a1)
	lui t2, 200
	addi t2, t2, -439
	sw t2, 760(a1)
	lui t2, 532
	addi t2, t2, -107
	sw t2, 764(a1)
	lui t2, 396
	addi t2, t2, 1338
	sw t2, 768(a1)
	lui t2, 1532
	addi t2, t2, 59
	sw t2, 772(a1)
	lui t2, 580
	addi t2, t2, -1278
	sw t2, 776(a1)
	lui t2, 497
	addi t2, t2, -1905
	sw t2, 780(a1)
	lui t2, 1903
	addi t2, t2, -512
	sw t2, 784(a1)
	lui t2, 288
	addi t2, t2, -35
	sw t2, 788(a1)
	lui t2, 1917
	addi t2, t2, 404
	sw t2, 792(a1)
	lui t2, 670
	addi t2, t2, -909
	sw t2, 796(a1)
	lui t2, 361
	addi t2, t2, -1671
	sw t2, 800(a1)
	lui t2, 1559
	addi t2, t2, 707
	sw t2, 804(a1)
	lui t2, 1438
	addi t2, t2, -956
	sw t2, 808(a1)
	lui t2, 340
	addi t2, t2, 519
	sw t2, 812(a1)
	lui t2, 1922
	addi t2, t2, -22
	sw t2, 816(a1)
	lui t2, 290
	addi t2, t2, 45
	sw t2, 820(a1)
	lui t2, 177
	addi t2, t2, -188
	sw t2, 824(a1)
	lui t2, 448
	addi t2, t2, -482
	sw t2, 828(a1)
	lui t2, 741
	addi t2, t2, -1394
	sw t2, 832(a1)
	lui t2, 83
	addi t2, t2, -1548
	sw t2, 836(a1)
	lui t2, 1400
	addi t2, t2, -1977
	sw t2, 840(a1)
	lui t2, 1311
	addi t2, t2, 813
	sw t2, 844(a1)
	lui t2, 638
	addi t2, t2, -395
	sw t2, 848(a1)
	lui t2, 1033
	addi t2, t2, 780
	sw t2, 852(a1)
	lui t2, 1863
	addi t2, t2, -8
	sw t2, 856(a1)
	lui t2, 982
	addi t2, t2, 478
	sw t2, 860(a1)
	lui t2, 1074
	addi t2, t2, 714
	sw t2, 864(a1)
	lui t2, 1419
	addi t2, t2, -818
	sw t2, 868(a1)
	lui t2, 394
	addi t2, t2, 1706
	sw t2, 872(a1)
	lui t2, 1625
	addi t2, t2, 1188
	sw t2, 876(a1)
	lui t2, 1639
	addi t2, t2, 1755
	sw t2, 880(a1)
	lui t2, 1551
	addi t2, t2, -517
	sw t2, 884(a1)
	lui t2, 1762
	addi t2, t2, -333
	sw t2, 888(a1)
	lui t2, 823
	addi t2, t2, -1735
	sw t2, 892(a1)
	lui t2, 1071
	addi t2, t2, -1070
	sw t2, 896(a1)
	lui t2, 3
	addi t2, t2, -409
	sw t2, 900(a1)
	lui t2, 335
	addi t2, t2, -1643
	sw t2, 904(a1)
	lui t2, 1309
	addi t2, t2, -1640
	sw t2, 908(a1)
	lui t2, 1225
	addi t2, t2, -725
	sw t2, 912(a1)
	lui t2, 1994
	addi t2, t2, -1887
	sw t2, 916(a1)
	lui t2, 1913
	addi t2, t2, -607
	sw t2, 920(a1)
	lui t2, 188
	addi t2, t2, 393
	sw t2, 924(a1)
	lui t2, 1288
	addi t2, t2, -789
	sw t2, 928(a1)
	lui t2, 269
	addi t2, t2, 1520
	sw t2, 932(a1)
	lui t2, 1922
	addi t2, t2, -240
	sw t2, 936(a1)
	lui t2, 135
	addi t2, t2, 758
	sw t2, 940(a1)
	lui t2, 1836
	addi t2, t2, 17
	sw t2, 944(a1)
	lui t2, 1208
	addi t2, t2, 2013
	sw t2, 948(a1)
	lui t2, 2012
	addi t2, t2, -979
	sw t2, 952(a1)
	lui t2, 370
	addi t2, t2, -1368
	sw t2, 956(a1)
	lui t2, 533
	addi t2, t2, 1916
	sw t2, 960(a1)
	lui t2, 1283
	addi t2, t2, 1487
	sw t2, 964(a1)
	lui t2, 1470
	addi t2, t2, 924
	sw t2, 968(a1)
	lui t2, 535
	addi t2, t2, 1727
	sw t2, 972(a1)
	lui t2, 736
	addi t2, t2, -236
	sw t2, 976(a1)
	lui t2, 419
	addi t2, t2, 590
	sw t2, 980(a1)
	lui t2, 1332
	addi t2, t2, -1509
	sw t2, 984(a1)
	lui t2, 96
	addi t2, t2, -509
	sw t2, 988(a1)
	lui t2, 74
	addi t2, t2, -99
	sw t2, 992(a1)
	lui t2, 1184
	addi t2, t2, -476
	sw t2, 996(a1)
	lui t2, 970
	addi t2, t2, 1365
	sw t2, 1000(a1)
	lui t2, 921
	addi t2, t2, 1315
	sw t2, 1004(a1)
	lui t2, 1582
	addi t2, t2, 493
	sw t2, 1008(a1)
	lui t2, 191
	addi t2, t2, -461
	sw t2, 1012(a1)
	lui t2, 1789
	addi t2, t2, -1805
	sw t2, 1016(a1)
	lui t2, 179
	addi t2, t2, -1750
	sw t2, 1020(a1)
	lui a5, 131200
	addi a5, a5, 448
	slli a5, a5, 12
	addi a5, a5, 1537
	lui a6, 2046
	addi a6, a6, 1
	addi a0, a0, 1024
	addi a1, a1, 1020
	addi a7, zero, 4
20:
	addi a2, a0, -1024
21:
	lwu a4, 0(a1)
	addi a1, a1, -4
	add a3, a2, a7
	srli t1, a7, 2
22:
	lwu t2, 0(a2)
	lwu t0, 0(a3)
	add t3, t2, t0
	sub t3, t3, a6
	srai t4, t3, 63
	and t4, t4, a6
	add t3, t3, t4
	sw t3, 0(a2)
	sub t0, t2, t0
	srai t4, t0, 63
	and t4, t4, a6
	add t0, t0, t4
	mul t0, a4, t0
	mulhu t3, t0, a5
	sub t0, t0, t3
	slli t3, t3, 13
	add t0, t0, t3
	slli t3, t3, 10
	sub t0, t0, t3
	sub t0, t0, a6
	srai t3, t0, 63
	and t3, t3, a6
	add t0, t0, t3
	sw t0, 0(a3)
	addi a2, a2, 4
	addi a3, a3, 4
	addi t1, t1, -1
	bnez t1, 22b
	addi a2, a3, 0
	sub t0, a2, a0
	bnez t0, 21b
	slli a7, a7, 1
	addi t0, a7, -1024
	bnez t0, 20b
	lui a4, 2038
	addi a4, a4, 33
	addi a2, a0, -1024
	addi t1, zero, 256
23:
	lwu t2, 0(a2)
	mul t2, t2, a4
	mulhu t3, t2, a5
	sub t2, t2, t3
	slli t3, t3, 13
	add t2, t2, t3
	slli t3, t3, 10
	sub t2, t2, t3
	sub t2, t2, a6
	srai t3, t2, 63
	and t3, t3, a6
	add t2, t2, t3
	sw t2, 0(a2)
	addi a2, a2, 4
	addi t1, t1, -1
	bnez t1, 23b
	ret
	.option pop

vg_mldsa_multiply_ntt:
	.option push
	.option arch, +m, +c
	lui a5, 131200
	addi a5, a5, 448
	slli a5, a5, 12
	addi a5, a5, 1537
	lui a6, 2046
	addi a6, a6, 1
	addi t1, zero, 256
20:
	lwu t0, 0(a1)
	lwu t2, 0(a2)
	mul t0, t0, t2
	mulhu t2, t0, a5
	sub t0, t0, t2
	slli t2, t2, 13
	add t0, t0, t2
	slli t2, t2, 10
	sub t0, t0, t2
	sub t0, t0, a6
	srai t2, t0, 63
	and t2, t2, a6
	add t0, t0, t2
	sw t0, 0(a0)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a2, a2, 4
	addi t1, t1, -1
	bnez t1, 20b
	ret
	.option pop

vg_mldsa_multiply_add_ntt:
	.option push
	.option arch, +m, +c
	lui a5, 131200
	addi a5, a5, 448
	slli a5, a5, 12
	addi a5, a5, 1537
	lui a6, 2046
	addi a6, a6, 1
	addi t1, zero, 256
20:
	lwu t0, 0(a1)
	lwu t2, 0(a2)
	mul t0, t0, t2
	lwu t2, 0(a0)
	add t0, t0, t2
	mulhu t2, t0, a5
	sub t0, t0, t2
	slli t2, t2, 13
	add t0, t0, t2
	slli t2, t2, 10
	sub t0, t0, t2
	sub t0, t0, a6
	srai t2, t0, 63
	and t2, t2, a6
	add t0, t0, t2
	sw t0, 0(a0)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a2, a2, 4
	addi t1, t1, -1
	bnez t1, 20b
	ret
	.option pop

vg_mldsa_add:
	.option push
	.option arch, +m, +c
	addi a2, zero, 256
	lui a5, 2046
	addi a5, a5, 1
20:
	lwu a3, 0(a0)
	lwu a4, 0(a1)
	add a3, a3, a4
	sub a3, a3, a5
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 0(a0)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop

vg_mldsa_sub:
	.option push
	.option arch, +m, +c
	addi a2, zero, 256
	lui a5, 2046
	addi a5, a5, 1
20:
	lwu a3, 0(a0)
	lwu a4, 0(a1)
	sub a3, a3, a4
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 0(a0)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop
