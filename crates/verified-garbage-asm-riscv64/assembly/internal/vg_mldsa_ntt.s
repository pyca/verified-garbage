// The functions of `src/internal/vg_mldsa_ntt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
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
	add t5, a6, a6
	addi a0, a0, 1024
	addi a1, a1, 4
	addi a2, a0, -1024
20:
	lwu a4, 0(a1)
	addi a1, a1, 4
	addi a3, a2, 512
21:
	lwu t2, 0(a2)
	lwu t0, 512(a2)
	mul t0, a4, t0
	mulhu t3, t0, a5
	mul t3, t3, a6
	sub t0, t0, t3
	sub t3, t2, t0
	add t3, t3, t5
	sw t3, 512(a2)
	add t2, t2, t0
	sw t2, 0(a2)
	addi a2, a2, 4
	bne a2, a3, 21b
	addi a2, a2, 512
	bne a2, a0, 20b
	addi a2, a0, -1024
22:
	lwu a4, 0(a1)
	addi a1, a1, 4
	addi a3, a2, 256
23:
	lwu t2, 0(a2)
	lwu t0, 256(a2)
	mul t0, a4, t0
	mulhu t3, t0, a5
	mul t3, t3, a6
	sub t0, t0, t3
	sub t3, t2, t0
	add t3, t3, t5
	sw t3, 256(a2)
	add t2, t2, t0
	sw t2, 0(a2)
	addi a2, a2, 4
	bne a2, a3, 23b
	addi a2, a2, 256
	bne a2, a0, 22b
	addi a2, a0, -1024
24:
	lwu a4, 0(a1)
	addi a1, a1, 4
	addi a3, a2, 128
25:
	lwu t2, 0(a2)
	lwu t0, 128(a2)
	mul t0, a4, t0
	mulhu t3, t0, a5
	mul t3, t3, a6
	sub t0, t0, t3
	sub t3, t2, t0
	add t3, t3, t5
	sw t3, 128(a2)
	add t2, t2, t0
	sw t2, 0(a2)
	addi a2, a2, 4
	bne a2, a3, 25b
	addi a2, a2, 128
	bne a2, a0, 24b
	addi a2, a0, -1024
26:
	lwu a4, 0(a1)
	addi a1, a1, 4
	addi a3, a2, 64
27:
	lwu t2, 0(a2)
	lwu t0, 64(a2)
	mul t0, a4, t0
	mulhu t3, t0, a5
	mul t3, t3, a6
	sub t0, t0, t3
	sub t3, t2, t0
	add t3, t3, t5
	sw t3, 64(a2)
	add t2, t2, t0
	sw t2, 0(a2)
	addi a2, a2, 4
	bne a2, a3, 27b
	addi a2, a2, 64
	bne a2, a0, 26b
	addi a2, a0, -1024
28:
	lwu a4, 0(a1)
	addi a1, a1, 4
	addi a3, a2, 32
29:
	lwu t2, 0(a2)
	lwu t0, 32(a2)
	mul t0, a4, t0
	mulhu t3, t0, a5
	mul t3, t3, a6
	sub t0, t0, t3
	sub t3, t2, t0
	add t3, t3, t5
	sw t3, 32(a2)
	add t2, t2, t0
	sw t2, 0(a2)
	addi a2, a2, 4
	bne a2, a3, 29b
	addi a2, a2, 32
	bne a2, a0, 28b
	addi a2, a0, -1024
210:
	lwu a4, 0(a1)
	addi a1, a1, 4
	addi a3, a2, 16
211:
	lwu t2, 0(a2)
	lwu t0, 16(a2)
	mul t0, a4, t0
	mulhu t3, t0, a5
	mul t3, t3, a6
	sub t0, t0, t3
	sub t3, t2, t0
	add t3, t3, t5
	sw t3, 16(a2)
	add t2, t2, t0
	sw t2, 0(a2)
	addi a2, a2, 4
	bne a2, a3, 211b
	addi a2, a2, 16
	bne a2, a0, 210b
	addi a2, a0, -1024
212:
	lwu a4, 0(a1)
	addi a1, a1, 4
	addi a3, a2, 8
213:
	lwu t2, 0(a2)
	lwu t0, 8(a2)
	mul t0, a4, t0
	mulhu t3, t0, a5
	mul t3, t3, a6
	sub t0, t0, t3
	sub t3, t2, t0
	add t3, t3, t5
	sw t3, 8(a2)
	add t2, t2, t0
	sw t2, 0(a2)
	addi a2, a2, 4
	bne a2, a3, 213b
	addi a2, a2, 8
	bne a2, a0, 212b
	addi a2, a0, -1024
214:
	lwu a4, 0(a1)
	addi a1, a1, 4
	addi a3, a2, 4
215:
	lwu t2, 0(a2)
	lwu t0, 4(a2)
	mul t0, a4, t0
	mulhu t3, t0, a5
	mul t3, t3, a6
	sub t0, t0, t3
	sub t3, t2, t0
	add t3, t3, t5
	sw t3, 4(a2)
	add t2, t2, t0
	sw t2, 0(a2)
	addi a2, a2, 4
	bne a2, a3, 215b
	addi a2, a2, 4
	bne a2, a0, 214b
	addi a2, a0, -1024
	addi t1, zero, 256
216:
	lwu t2, 0(a2)
	mulhu t3, t2, a5
	mul t3, t3, a6
	sub t2, t2, t3
	sub t2, t2, a6
	srai t3, t2, 63
	and t3, t3, a6
	add t2, t2, t3
	sw t2, 0(a2)
	addi a2, a2, 4
	addi t1, t1, -1
	bnez t1, 216b
	ret
	.option pop
