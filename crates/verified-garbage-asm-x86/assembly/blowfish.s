// The functions of `src/blowfish.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_expand_key:
	lea esp, [esp-84]
	mov eax, DWORD PTR [esp+88]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+92]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+96]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov ebp, eax
	mov ebx, DWORD PTR [esp+12]
	add ebx, 0
	mov ecx, -1210340186
	mov DWORD PTR [ebx], ecx
	mov ecx, -1723492627
	mov DWORD PTR [ebx+4], ecx
	mov ecx, 383973191
	mov DWORD PTR [ebx+8], ecx
	mov ecx, 2124638680
	mov DWORD PTR [ebx+12], ecx
	mov ecx, -296200049
	mov DWORD PTR [ebx+16], ecx
	mov ecx, 322549021
	mov DWORD PTR [ebx+20], ecx
	mov ecx, -283578333
	mov DWORD PTR [ebx+24], ecx
	mov ecx, 1049300656
	mov DWORD PTR [ebx+28], ecx
	mov ecx, 1624909761
	mov DWORD PTR [ebx+32], ecx
	mov ecx, 1080202483
	mov DWORD PTR [ebx+36], ecx
	mov ecx, -835406230
	mov DWORD PTR [ebx+40], ecx
	mov ecx, 705794991
	mov DWORD PTR [ebx+44], ecx
	mov ecx, 504821341
	mov DWORD PTR [ebx+48], ecx
	mov ecx, 2004966451
	mov DWORD PTR [ebx+52], ecx
	mov ecx, -1826902120
	mov DWORD PTR [ebx+56], ecx
	mov ecx, 845189580
	mov DWORD PTR [ebx+60], ecx
	mov ecx, -2013089443
	mov DWORD PTR [ebx+64], ecx
	mov ecx, 972277121
	mov DWORD PTR [ebx+68], ecx
	mov ecx, 1581909122
	mov DWORD PTR [ebx+72], ecx
	mov ecx, -262038974
	mov DWORD PTR [ebx+76], ecx
	mov ecx, -1557632814
	mov DWORD PTR [ebx+80], ecx
	mov ecx, -1739529108
	mov DWORD PTR [ebx+84], ecx
	mov ecx, -2009172451
	mov DWORD PTR [ebx+88], ecx
	mov ecx, -1094470631
	mov DWORD PTR [ebx+92], ecx
	mov ecx, -1499499560
	mov DWORD PTR [ebx+96], ecx
	mov ecx, 1030882914
	mov DWORD PTR [ebx+100], ecx
	mov ecx, -1680652252
	mov DWORD PTR [ebx+104], ecx
	mov ecx, -136807479
	mov DWORD PTR [ebx+108], ecx
	mov ecx, -1162003686
	mov DWORD PTR [ebx+112], ecx
	mov ecx, 1673708726
	mov DWORD PTR [ebx+116], ecx
	mov ecx, 1877718447
	mov DWORD PTR [ebx+120], ecx
	mov ecx, 155462687
	mov DWORD PTR [ebx+124], ecx
	mov ecx, -1291322108
	mov DWORD PTR [ebx+128], ecx
	mov ecx, -617017513
	mov DWORD PTR [ebx+132], ecx
	mov ecx, 2043022013
	mov DWORD PTR [ebx+136], ecx
	mov ecx, -117912322
	mov DWORD PTR [ebx+140], ecx
	mov ecx, -1412950561
	mov DWORD PTR [ebx+144], ecx
	mov ecx, -2109185798
	mov DWORD PTR [ebx+148], ecx
	mov ecx, -617701189
	mov DWORD PTR [ebx+152], ecx
	mov ecx, 1942406134
	mov DWORD PTR [ebx+156], ecx
	mov ecx, -1604466512
	mov DWORD PTR [ebx+160], ecx
	mov ecx, 1533851800
	mov DWORD PTR [ebx+164], ecx
	mov ecx, -1866701447
	mov DWORD PTR [ebx+168], ecx
	mov ecx, -398380070
	mov DWORD PTR [ebx+172], ecx
	mov ecx, -1258421798
	mov DWORD PTR [ebx+176], ecx
	mov ecx, -1603168179
	mov DWORD PTR [ebx+180], ecx
	mov ecx, -1221599024
	mov DWORD PTR [ebx+184], ecx
	mov ecx, 470967547
	mov DWORD PTR [ebx+188], ecx
	mov ecx, -1382998880
	mov DWORD PTR [ebx+192], ecx
	mov ecx, -1577158888
	mov DWORD PTR [ebx+196], ecx
	mov ecx, -1713969137
	mov DWORD PTR [ebx+200], ecx
	mov ecx, -645810208
	mov DWORD PTR [ebx+204], ecx
	mov ecx, 1997800806
	mov DWORD PTR [ebx+208], ecx
	mov ecx, -805992859
	mov DWORD PTR [ebx+212], ecx
	mov ecx, 1238605836
	mov DWORD PTR [ebx+216], ecx
	mov ecx, -1346675155
	mov DWORD PTR [ebx+220], ecx
	mov ecx, -1440932197
	mov DWORD PTR [ebx+224], ecx
	mov ecx, -979206263
	mov DWORD PTR [ebx+228], ecx
	mov ecx, 1097378166
	mov DWORD PTR [ebx+232], ecx
	mov ecx, 357714634
	mov DWORD PTR [ebx+236], ecx
	mov ecx, 7791679
	mov DWORD PTR [ebx+240], ecx
	mov ecx, 359342005
	mov DWORD PTR [ebx+244], ecx
	mov ecx, 1680782881
	mov DWORD PTR [ebx+248], ecx
	mov ecx, 1788453213
	mov DWORD PTR [ebx+252], ecx
	mov ecx, -546130677
	mov DWORD PTR [ebx+256], ecx
	mov ecx, 2140176047
	mov DWORD PTR [ebx+260], ecx
	mov ecx, -51221351
	mov DWORD PTR [ebx+264], ecx
	mov ecx, 1040076320
	mov DWORD PTR [ebx+268], ecx
	mov ecx, 1254995572
	mov DWORD PTR [ebx+272], ecx
	mov ecx, 1624594852
	mov DWORD PTR [ebx+276], ecx
	mov ecx, 947488176
	mov DWORD PTR [ebx+280], ecx
	mov ecx, -1978787620
	mov DWORD PTR [ebx+284], ecx
	mov ecx, 1546603383
	mov DWORD PTR [ebx+288], ecx
	mov ecx, 345549605
	mov DWORD PTR [ebx+292], ecx
	mov ecx, -396619719
	mov DWORD PTR [ebx+296], ecx
	mov ecx, -1139480186
	mov DWORD PTR [ebx+300], ecx
	mov ecx, -1824640571
	mov DWORD PTR [ebx+304], ecx
	mov ecx, -2041327686
	mov DWORD PTR [ebx+308], ecx
	mov ecx, 568899912
	mov DWORD PTR [ebx+312], ecx
	mov ecx, -2136168183
	mov DWORD PTR [ebx+316], ecx
	mov ecx, 455308637
	mov DWORD PTR [ebx+320], ecx
	mov ecx, 1114614846
	mov DWORD PTR [ebx+324], ecx
	mov ecx, -1678761916
	mov DWORD PTR [ebx+328], ecx
	mov ecx, -2003014552
	mov DWORD PTR [ebx+332], ecx
	mov ecx, 866594720
	mov DWORD PTR [ebx+336], ecx
	mov ecx, 720386827
	mov DWORD PTR [ebx+340], ecx
	mov ecx, 240714085
	mov DWORD PTR [ebx+344], ecx
	mov ecx, 1587912582
	mov DWORD PTR [ebx+348], ecx
	mov ecx, 1782849653
	mov DWORD PTR [ebx+352], ecx
	mov ecx, 48199594
	mov DWORD PTR [ebx+356], ecx
	mov ecx, -1058401577
	mov DWORD PTR [ebx+360], ecx
	mov ecx, -562488462
	mov DWORD PTR [ebx+364], ecx
	mov ecx, 115362896
	mov DWORD PTR [ebx+368], ecx
	mov ecx, 614359119
	mov DWORD PTR [ebx+372], ecx
	mov ecx, -323857553
	mov DWORD PTR [ebx+376], ecx
	mov ecx, -1119513263
	mov DWORD PTR [ebx+380], ecx
	mov ecx, 1260931792
	mov DWORD PTR [ebx+384], ecx
	mov ecx, -77630296
	mov DWORD PTR [ebx+388], ecx
	mov ecx, 1912615616
	mov DWORD PTR [ebx+392], ecx
	mov ecx, 585736997
	mov DWORD PTR [ebx+396], ecx
	mov ecx, 1377725206
	mov DWORD PTR [ebx+400], ecx
	mov ecx, -545552459
	mov DWORD PTR [ebx+404], ecx
	mov ecx, 1767279703
	mov DWORD PTR [ebx+408], ecx
	mov ecx, 1429405608
	mov DWORD PTR [ebx+412], ecx
	mov ecx, 295917607
	mov DWORD PTR [ebx+416], ecx
	mov ecx, -743079107
	mov DWORD PTR [ebx+420], ecx
	mov ecx, -1756805660
	mov DWORD PTR [ebx+424], ecx
	mov ecx, -971800846
	mov DWORD PTR [ebx+428], ecx
	mov ecx, 530468042
	mov DWORD PTR [ebx+432], ecx
	mov ecx, -712076838
	mov DWORD PTR [ebx+436], ecx
	mov ecx, -1805965871
	mov DWORD PTR [ebx+440], ecx
	mov ecx, -256365598
	mov DWORD PTR [ebx+444], ecx
	mov ecx, -1041120418
	mov DWORD PTR [ebx+448], ecx
	mov ecx, 523048738
	mov DWORD PTR [ebx+452], ecx
	mov ecx, -487361332
	mov DWORD PTR [ebx+456], ecx
	mov ecx, -1472470961
	mov DWORD PTR [ebx+460], ecx
	mov ecx, 343111586
	mov DWORD PTR [ebx+464], ecx
	mov ecx, 893581856
	mov DWORD PTR [ebx+468], ecx
	mov ecx, 2115733935
	mov DWORD PTR [ebx+472], ecx
	mov ecx, -536825074
	mov DWORD PTR [ebx+476], ecx
	mov ecx, -1500399306
	mov DWORD PTR [ebx+480], ecx
	mov ecx, -1185197245
	mov DWORD PTR [ebx+484], ecx
	mov ecx, 1243205379
	mov DWORD PTR [ebx+488], ecx
	mov ecx, 687909165
	mov DWORD PTR [ebx+492], ecx
	mov ecx, 1956955735
	mov DWORD PTR [ebx+496], ecx
	mov ecx, -638785169
	mov DWORD PTR [ebx+500], ecx
	mov ecx, 1443232101
	mov DWORD PTR [ebx+504], ecx
	mov ecx, 122130221
	mov DWORD PTR [ebx+508], ecx
	mov ecx, 452845361
	mov DWORD PTR [ebx+512], ecx
	mov ecx, 746333921
	mov DWORD PTR [ebx+516], ecx
	mov ecx, -1912499807
	mov DWORD PTR [ebx+520], ecx
	mov ecx, -1822926999
	mov DWORD PTR [ebx+524], ecx
	mov ecx, 361467541
	mov DWORD PTR [ebx+528], ecx
	mov ecx, -231712172
	mov DWORD PTR [ebx+532], ecx
	mov ecx, -616472367
	mov DWORD PTR [ebx+536], ecx
	mov ecx, 513686137
	mov DWORD PTR [ebx+540], ecx
	mov ecx, 1622094101
	mov DWORD PTR [ebx+544], ecx
	mov ecx, -397912747
	mov DWORD PTR [ebx+548], ecx
	mov ecx, 1103932362
	mov DWORD PTR [ebx+552], ecx
	mov ecx, 1877897812
	mov DWORD PTR [ebx+556], ecx
	mov ecx, -2024007511
	mov DWORD PTR [ebx+560], ecx
	mov ecx, -1791875882
	mov DWORD PTR [ebx+564], ecx
	mov ecx, 683625359
	mov DWORD PTR [ebx+568], ecx
	mov ecx, -327409192
	mov DWORD PTR [ebx+572], ecx
	mov ecx, 1697023364
	mov DWORD PTR [ebx+576], ecx
	mov ecx, -194144631
	mov DWORD PTR [ebx+580], ecx
	mov ecx, 533234699
	mov DWORD PTR [ebx+584], ecx
	mov ecx, -754128442
	mov DWORD PTR [ebx+588], ecx
	mov ecx, 1359959121
	mov DWORD PTR [ebx+592], ecx
	mov ecx, -79987985
	mov DWORD PTR [ebx+596], ecx
	mov ecx, 1137356785
	mov DWORD PTR [ebx+600], ecx
	mov ecx, -1954254866
	mov DWORD PTR [ebx+604], ecx
	mov ecx, -1055211153
	mov DWORD PTR [ebx+608], ecx
	mov ecx, -1677836333
	mov DWORD PTR [ebx+612], ecx
	mov ecx, -250672432
	mov DWORD PTR [ebx+616], ecx
	mov ecx, -388720301
	mov DWORD PTR [ebx+620], ecx
	mov ecx, -1066632706
	mov DWORD PTR [ebx+624], ecx
	mov ecx, 1784455081
	mov DWORD PTR [ebx+628], ecx
	mov ecx, 1379495163
	mov DWORD PTR [ebx+632], ecx
	mov ecx, 1585524988
	mov DWORD PTR [ebx+636], ecx
	mov ecx, 772748259
	mov DWORD PTR [ebx+640], ecx
	mov ecx, -754202421
	mov DWORD PTR [ebx+644], ecx
	mov ecx, 748773497
	mov DWORD PTR [ebx+648], ecx
	mov ecx, 849682335
	mov DWORD PTR [ebx+652], ecx
	mov ecx, 89153909
	mov DWORD PTR [ebx+656], ecx
	mov ecx, 3220285
	mov DWORD PTR [ebx+660], ecx
	mov ecx, 394751836
	mov DWORD PTR [ebx+664], ecx
	mov ecx, 1332182594
	mov DWORD PTR [ebx+668], ecx
	mov ecx, -251671973
	mov DWORD PTR [ebx+672], ecx
	mov ecx, -772005382
	mov DWORD PTR [ebx+676], ecx
	mov ecx, -74516397
	mov DWORD PTR [ebx+680], ecx
	mov ecx, -453260323
	mov DWORD PTR [ebx+684], ecx
	mov ecx, -243370208
	mov DWORD PTR [ebx+688], ecx
	mov ecx, -1817341733
	mov DWORD PTR [ebx+692], ecx
	mov ecx, 1966917518
	mov DWORD PTR [ebx+696], ecx
	mov ecx, 227021558
	mov DWORD PTR [ebx+700], ecx
	mov ecx, -1462792275
	mov DWORD PTR [ebx+704], ecx
	mov ecx, 41225775
	mov DWORD PTR [ebx+708], ecx
	mov ecx, -1985187936
	mov DWORD PTR [ebx+712], ecx
	mov ecx, -1379658840
	mov DWORD PTR [ebx+716], ecx
	mov ecx, 449615199
	mov DWORD PTR [ebx+720], ecx
	mov ecx, -1655392851
	mov DWORD PTR [ebx+724], ecx
	mov ecx, 507592397
	mov DWORD PTR [ebx+728], ecx
	mov ecx, -1201114843
	mov DWORD PTR [ebx+732], ecx
	mov ecx, -547157660
	mov DWORD PTR [ebx+736], ecx
	mov ecx, -444769599
	mov DWORD PTR [ebx+740], ecx
	mov ecx, 1942525222
	mov DWORD PTR [ebx+744], ecx
	mov ecx, 1397822535
	mov DWORD PTR [ebx+748], ecx
	mov ecx, -429876465
	mov DWORD PTR [ebx+752], ecx
	mov ecx, 227941306
	mov DWORD PTR [ebx+756], ecx
	mov ecx, -2060142237
	mov DWORD PTR [ebx+760], ecx
	mov ecx, -2051366992
	mov DWORD PTR [ebx+764], ecx
	mov ecx, -802187055
	mov DWORD PTR [ebx+768], ecx
	mov ecx, -239441224
	mov DWORD PTR [ebx+772], ecx
	mov ecx, -2063027420
	mov DWORD PTR [ebx+776], ecx
	mov ecx, -190549661
	mov DWORD PTR [ebx+780], ecx
	mov ecx, -2106494451
	mov DWORD PTR [ebx+784], ecx
	mov ecx, 714916475
	mov DWORD PTR [ebx+788], ecx
	mov ecx, -1194710843
	mov DWORD PTR [ebx+792], ecx
	mov ecx, -1335074674
	mov DWORD PTR [ebx+796], ecx
	mov ecx, 1433976279
	mov DWORD PTR [ebx+800], ecx
	mov ecx, 1666689766
	mov DWORD PTR [ebx+804], ecx
	mov ecx, 297019989
	mov DWORD PTR [ebx+808], ecx
	mov ecx, 1672707233
	mov DWORD PTR [ebx+812], ecx
	mov ecx, -1680968661
	mov DWORD PTR [ebx+816], ecx
	mov ecx, 679111855
	mov DWORD PTR [ebx+820], ecx
	mov ecx, 1724148539
	mov DWORD PTR [ebx+824], ecx
	mov ecx, 1565064033
	mov DWORD PTR [ebx+828], ecx
	mov ecx, -337843729
	mov DWORD PTR [ebx+832], ecx
	mov ecx, -2096114909
	mov DWORD PTR [ebx+836], ecx
	mov ecx, -1637243858
	mov DWORD PTR [ebx+840], ecx
	mov ecx, -1419250143
	mov DWORD PTR [ebx+844], ecx
	mov ecx, -1416177558
	mov DWORD PTR [ebx+848], ecx
	mov ecx, 2126123886
	mov DWORD PTR [ebx+852], ecx
	mov ecx, -2107229791
	mov DWORD PTR [ebx+856], ecx
	mov ecx, 998065548
	mov DWORD PTR [ebx+860], ecx
	mov ecx, 1447069152
	mov DWORD PTR [ebx+864], ecx
	mov ecx, 1109079630
	mov DWORD PTR [ebx+868], ecx
	mov ecx, 1239142455
	mov DWORD PTR [ebx+872], ecx
	mov ecx, -165314553
	mov DWORD PTR [ebx+876], ecx
	mov ecx, 77051619
	mov DWORD PTR [ebx+880], ecx
	mov ecx, 425607361
	mov DWORD PTR [ebx+884], ecx
	mov ecx, 991116904
	mov DWORD PTR [ebx+888], ecx
	mov ecx, -1345545363
	mov DWORD PTR [ebx+892], ecx
	mov ecx, 426172094
	mov DWORD PTR [ebx+896], ecx
	mov ecx, -1177401920
	mov DWORD PTR [ebx+900], ecx
	mov ecx, 1087773269
	mov DWORD PTR [ebx+904], ecx
	mov ecx, -611386521
	mov DWORD PTR [ebx+908], ecx
	mov ecx, -1389363908
	mov DWORD PTR [ebx+912], ecx
	mov ecx, 1045691698
	mov DWORD PTR [ebx+916], ecx
	mov ecx, -551892322
	mov DWORD PTR [ebx+920], ecx
	mov ecx, -1934874411
	mov DWORD PTR [ebx+924], ecx
	mov ecx, -1193165975
	mov DWORD PTR [ebx+928], ecx
	mov ecx, 759889168
	mov DWORD PTR [ebx+932], ecx
	mov ecx, 1272100506
	mov DWORD PTR [ebx+936], ecx
	mov ecx, -832396063
	mov DWORD PTR [ebx+940], ecx
	mov ecx, 735065839
	mov DWORD PTR [ebx+944], ecx
	mov ecx, 1810542229
	mov DWORD PTR [ebx+948], ecx
	mov ecx, -1903251504
	mov DWORD PTR [ebx+952], ecx
	mov ecx, -1870073201
	mov DWORD PTR [ebx+956], ecx
	mov ecx, -1278121905
	mov DWORD PTR [ebx+960], ecx
	mov ecx, -1947550161
	mov DWORD PTR [ebx+964], ecx
	mov ecx, -837241371
	mov DWORD PTR [ebx+968], ecx
	mov ecx, -763560524
	mov DWORD PTR [ebx+972], ecx
	mov ecx, 563314710
	mov DWORD PTR [ebx+976], ecx
	mov ecx, -70813722
	mov DWORD PTR [ebx+980], ecx
	mov ecx, -1361675285
	mov DWORD PTR [ebx+984], ecx
	mov ecx, 1461854208
	mov DWORD PTR [ebx+988], ecx
	mov ecx, 1498804260
	mov DWORD PTR [ebx+992], ecx
	mov ecx, 35707256
	mov DWORD PTR [ebx+996], ecx
	mov ecx, 1309762179
	mov DWORD PTR [ebx+1000], ecx
	mov ecx, -1709474893
	mov DWORD PTR [ebx+1004], ecx
	mov ecx, -2127840042
	mov DWORD PTR [ebx+1008], ecx
	mov ecx, 720525064
	mov DWORD PTR [ebx+1012], ecx
	mov ecx, -973084746
	mov DWORD PTR [ebx+1016], ecx
	mov ecx, 1846061395
	mov DWORD PTR [ebx+1020], ecx
	mov ecx, 590234857
	mov DWORD PTR [ebx+1024], ecx
	mov ecx, 1723366832
	mov DWORD PTR [ebx+1028], ecx
	mov ecx, -512950415
	mov DWORD PTR [ebx+1032], ecx
	mov ecx, 1044392357
	mov DWORD PTR [ebx+1036], ecx
	mov ecx, -690592358
	mov DWORD PTR [ebx+1040], ecx
	mov ecx, -1041828601
	mov DWORD PTR [ebx+1044], ecx
	mov ecx, 1590044294
	mov DWORD PTR [ebx+1048], ecx
	mov ecx, -1592473281
	mov DWORD PTR [ebx+1052], ecx
	mov ecx, 923108996
	mov DWORD PTR [ebx+1056], ecx
	mov ecx, -1192469476
	mov DWORD PTR [ebx+1060], ecx
	mov ecx, -16511689
	mov DWORD PTR [ebx+1064], ecx
	mov ecx, -1118260710
	mov DWORD PTR [ebx+1068], ecx
	mov ecx, 24377081
	mov DWORD PTR [ebx+1072], ecx
	mov ecx, -1489707903
	mov DWORD PTR [ebx+1076], ecx
	mov ecx, 1094585926
	mov DWORD PTR [ebx+1080], ecx
	mov ecx, 832647065
	mov DWORD PTR [ebx+1084], ecx
	mov ecx, -1090320328
	mov DWORD PTR [ebx+1088], ecx
	mov ecx, -1351452272
	mov DWORD PTR [ebx+1092], ecx
	mov ecx, 772935711
	mov DWORD PTR [ebx+1096], ecx
	mov ecx, -2014960609
	mov DWORD PTR [ebx+1100], ecx
	mov ecx, -1933830376
	mov DWORD PTR [ebx+1104], ecx
	mov ecx, -765003206
	mov DWORD PTR [ebx+1108], ecx
	mov ecx, 372705351
	mov DWORD PTR [ebx+1112], ecx
	mov ecx, -587050685
	mov DWORD PTR [ebx+1116], ecx
	mov ecx, -1680452194
	mov DWORD PTR [ebx+1120], ecx
	mov ecx, 154889201
	mov DWORD PTR [ebx+1124], ecx
	mov ecx, 1848441581
	mov DWORD PTR [ebx+1128], ecx
	mov ecx, -1291144848
	mov DWORD PTR [ebx+1132], ecx
	mov ecx, 263846428
	mov DWORD PTR [ebx+1136], ecx
	mov ecx, 1786258902
	mov DWORD PTR [ebx+1140], ecx
	mov ecx, -195856198
	mov DWORD PTR [ebx+1144], ecx
	mov ecx, 1611611559
	mov DWORD PTR [ebx+1148], ecx
	mov ecx, 1718531592
	mov DWORD PTR [ebx+1152], ecx
	mov ecx, 684819349
	mov DWORD PTR [ebx+1156], ecx
	mov ecx, 42313199
	mov DWORD PTR [ebx+1160], ecx
	mov ecx, -2069021937
	mov DWORD PTR [ebx+1164], ecx
	mov ecx, 276131880
	mov DWORD PTR [ebx+1168], ecx
	mov ecx, -820079056
	mov DWORD PTR [ebx+1172], ecx
	mov ecx, 336279952
	mov DWORD PTR [ebx+1176], ecx
	mov ecx, 1856743356
	mov DWORD PTR [ebx+1180], ecx
	mov ecx, 1354353327
	mov DWORD PTR [ebx+1184], ecx
	mov ecx, -136989902
	mov DWORD PTR [ebx+1188], ecx
	mov ecx, -1468098279
	mov DWORD PTR [ebx+1192], ecx
	mov ecx, -2124449894
	mov DWORD PTR [ebx+1196], ecx
	mov ecx, -1717447127
	mov DWORD PTR [ebx+1200], ecx
	mov ecx, -1761647707
	mov DWORD PTR [ebx+1204], ecx
	mov ecx, 686052587
	mov DWORD PTR [ebx+1208], ecx
	mov ecx, 1935796975
	mov DWORD PTR [ebx+1212], ecx
	mov ecx, -535501863
	mov DWORD PTR [ebx+1216], ecx
	mov ecx, -803870026
	mov DWORD PTR [ebx+1220], ecx
	mov ecx, 85833026
	mov DWORD PTR [ebx+1224], ecx
	mov ecx, 1349175198
	mov DWORD PTR [ebx+1228], ecx
	mov ecx, -1549777166
	mov DWORD PTR [ebx+1232], ecx
	mov ecx, -2062839101
	mov DWORD PTR [ebx+1236], ecx
	mov ecx, 7642368
	mov DWORD PTR [ebx+1240], ecx
	mov ecx, 1631513130
	mov DWORD PTR [ebx+1244], ecx
	mov ecx, -604946030
	mov DWORD PTR [ebx+1248], ecx
	mov ecx, 1856462937
	mov DWORD PTR [ebx+1252], ecx
	mov ecx, 894803588
	mov DWORD PTR [ebx+1256], ecx
	mov ecx, -587414870
	mov DWORD PTR [ebx+1260], ecx
	mov ecx, -922385362
	mov DWORD PTR [ebx+1264], ecx
	mov ecx, 1081724371
	mov DWORD PTR [ebx+1268], ecx
	mov ecx, 547280997
	mov DWORD PTR [ebx+1272], ecx
	mov ecx, -148157721
	mov DWORD PTR [ebx+1276], ecx
	mov ecx, 638134640
	mov DWORD PTR [ebx+1280], ecx
	mov ecx, -1302274138
	mov DWORD PTR [ebx+1284], ecx
	mov ecx, -1638787188
	mov DWORD PTR [ebx+1288], ecx
	mov ecx, 974343170
	mov DWORD PTR [ebx+1292], ecx
	mov ecx, 1071947160
	mov DWORD PTR [ebx+1296], ecx
	mov ecx, 1563963548
	mov DWORD PTR [ebx+1300], ecx
	mov ecx, -857085152
	mov DWORD PTR [ebx+1304], ecx
	mov ecx, 1880682347
	mov DWORD PTR [ebx+1308], ecx
	mov ecx, 122937909
	mov DWORD PTR [ebx+1312], ecx
	mov ecx, -230379900
	mov DWORD PTR [ebx+1316], ecx
	mov ecx, -1289810726
	mov DWORD PTR [ebx+1320], ecx
	mov ecx, 561673461
	mov DWORD PTR [ebx+1324], ecx
	mov ecx, 1195847443
	mov DWORD PTR [ebx+1328], ecx
	mov ecx, -579413275
	mov DWORD PTR [ebx+1332], ecx
	mov ecx, 516359009
	mov DWORD PTR [ebx+1336], ecx
	mov ecx, -1279586611
	mov DWORD PTR [ebx+1340], ecx
	mov ecx, 68008331
	mov DWORD PTR [ebx+1344], ecx
	mov ecx, -1984922606
	mov DWORD PTR [ebx+1348], ecx
	mov ecx, 1068370039
	mov DWORD PTR [ebx+1352], ecx
	mov ecx, -841125518
	mov DWORD PTR [ebx+1356], ecx
	mov ecx, 2107300423
	mov DWORD PTR [ebx+1360], ecx
	mov ecx, -1019011604
	mov DWORD PTR [ebx+1364], ecx
	mov ecx, -1170482920
	mov DWORD PTR [ebx+1368], ecx
	mov ecx, -469711795
	mov DWORD PTR [ebx+1372], ecx
	mov ecx, 427249400
	mov DWORD PTR [ebx+1376], ecx
	mov ecx, -1525102762
	mov DWORD PTR [ebx+1380], ecx
	mov ecx, 1019214822
	mov DWORD PTR [ebx+1384], ecx
	mov ecx, 710831941
	mov DWORD PTR [ebx+1388], ecx
	mov ecx, 500958951
	mov DWORD PTR [ebx+1392], ecx
	mov ecx, -1278621559
	mov DWORD PTR [ebx+1396], ecx
	mov ecx, 758966798
	mov DWORD PTR [ebx+1400], ecx
	mov ecx, 2032544590
	mov DWORD PTR [ebx+1404], ecx
	mov ecx, 536744615
	mov DWORD PTR [ebx+1408], ecx
	mov ecx, -13121467
	mov DWORD PTR [ebx+1412], ecx
	mov ecx, -1742644515
	mov DWORD PTR [ebx+1416], ecx
	mov ecx, 796759461
	mov DWORD PTR [ebx+1420], ecx
	mov ecx, 356999606
	mov DWORD PTR [ebx+1424], ecx
	mov ecx, 1677639080
	mov DWORD PTR [ebx+1428], ecx
	mov ecx, -560029092
	mov DWORD PTR [ebx+1432], ecx
	mov ecx, -2074334074
	mov DWORD PTR [ebx+1436], ecx
	mov ecx, -1150685154
	mov DWORD PTR [ebx+1440], ecx
	mov ecx, -1192643494
	mov DWORD PTR [ebx+1444], ecx
	mov ecx, 2107219979
	mov DWORD PTR [ebx+1448], ecx
	mov ecx, 311635336
	mov DWORD PTR [ebx+1452], ecx
	mov ecx, -1159782520
	mov DWORD PTR [ebx+1456], ecx
	mov ecx, 1187213956
	mov DWORD PTR [ebx+1460], ecx
	mov ecx, 826814474
	mov DWORD PTR [ebx+1464], ecx
	mov ecx, 1022230514
	mov DWORD PTR [ebx+1468], ecx
	mov ecx, 324908820
	mov DWORD PTR [ebx+1472], ecx
	mov ecx, 1330621410
	mov DWORD PTR [ebx+1476], ecx
	mov ecx, 557562868
	mov DWORD PTR [ebx+1480], ecx
	mov ecx, 1648840057
	mov DWORD PTR [ebx+1484], ecx
	mov ecx, -1232918879
	mov DWORD PTR [ebx+1488], ecx
	mov ecx, -1299549148
	mov DWORD PTR [ebx+1492], ecx
	mov ecx, 246499519
	mov DWORD PTR [ebx+1496], ecx
	mov ecx, 1895101837
	mov DWORD PTR [ebx+1500], ecx
	mov ecx, 1005354736
	mov DWORD PTR [ebx+1504], ecx
	mov ecx, 854750263
	mov DWORD PTR [ebx+1508], ecx
	mov ecx, -1747431296
	mov DWORD PTR [ebx+1512], ecx
	mov ecx, -894761305
	mov DWORD PTR [ebx+1516], ecx
	mov ecx, -1637403526
	mov DWORD PTR [ebx+1520], ecx
	mov ecx, 1138395355
	mov DWORD PTR [ebx+1524], ecx
	mov ecx, -509900
	mov DWORD PTR [ebx+1528], ecx
	mov ecx, -1382073055
	mov DWORD PTR [ebx+1532], ecx
	mov ecx, 427144058
	mov DWORD PTR [ebx+1536], ecx
	mov ecx, -303126674
	mov DWORD PTR [ebx+1540], ecx
	mov ecx, -1318806870
	mov DWORD PTR [ebx+1544], ecx
	mov ecx, 408488246
	mov DWORD PTR [ebx+1548], ecx
	mov ecx, -141606316
	mov DWORD PTR [ebx+1552], ecx
	mov ecx, 623765714
	mov DWORD PTR [ebx+1556], ecx
	mov ecx, 511865053
	mov DWORD PTR [ebx+1560], ecx
	mov ecx, 1788328552
	mov DWORD PTR [ebx+1564], ecx
	mov ecx, 1352441983
	mov DWORD PTR [ebx+1568], ecx
	mov ecx, 377347591
	mov DWORD PTR [ebx+1572], ecx
	mov ecx, 1855546
	mov DWORD PTR [ebx+1576], ecx
	mov ecx, 159626508
	mov DWORD PTR [ebx+1580], ecx
	mov ecx, -181229167
	mov DWORD PTR [ebx+1584], ecx
	mov ecx, -206191899
	mov DWORD PTR [ebx+1588], ecx
	mov ecx, 1976094788
	mov DWORD PTR [ebx+1592], ecx
	mov ecx, 1048635960
	mov DWORD PTR [ebx+1596], ecx
	mov ecx, 172125524
	mov DWORD PTR [ebx+1600], ecx
	mov ecx, -1350985800
	mov DWORD PTR [ebx+1604], ecx
	mov ecx, -812936294
	mov DWORD PTR [ebx+1608], ecx
	mov ecx, -2078643438
	mov DWORD PTR [ebx+1612], ecx
	mov ecx, 1268713560
	mov DWORD PTR [ebx+1616], ecx
	mov ecx, 1678345594
	mov DWORD PTR [ebx+1620], ecx
	mov ecx, -1035791076
	mov DWORD PTR [ebx+1624], ecx
	mov ecx, 982803873
	mov DWORD PTR [ebx+1628], ecx
	mov ecx, 296497631
	mov DWORD PTR [ebx+1632], ecx
	mov ecx, 605135669
	mov DWORD PTR [ebx+1636], ecx
	mov ecx, 364573071
	mov DWORD PTR [ebx+1640], ecx
	mov ecx, 1041164771
	mov DWORD PTR [ebx+1644], ecx
	mov ecx, -412795617
	mov DWORD PTR [ebx+1648], ecx
	mov ecx, 273442366
	mov DWORD PTR [ebx+1652], ecx
	mov ecx, 184345109
	mov DWORD PTR [ebx+1656], ecx
	mov ecx, -1036444169
	mov DWORD PTR [ebx+1660], ecx
	mov ecx, -1012067549
	mov DWORD PTR [ebx+1664], ecx
	mov ecx, -1937802308
	mov DWORD PTR [ebx+1668], ecx
	mov ecx, -1420268494
	mov DWORD PTR [ebx+1672], ecx
	mov ecx, 1861169102
	mov DWORD PTR [ebx+1676], ecx
	mov ecx, -1612904671
	mov DWORD PTR [ebx+1680], ecx
	mov ecx, 53764556
	mov DWORD PTR [ebx+1684], ecx
	mov ecx, -1432457101
	mov DWORD PTR [ebx+1688], ecx
	mov ecx, -206871860
	mov DWORD PTR [ebx+1692], ecx
	mov ecx, 1512291723
	mov DWORD PTR [ebx+1696], ecx
	mov ecx, 564013672
	mov DWORD PTR [ebx+1700], ecx
	mov ecx, 1039621972
	mov DWORD PTR [ebx+1704], ecx
	mov ecx, 1760420663
	mov DWORD PTR [ebx+1708], ecx
	mov ecx, 1491002933
	mov DWORD PTR [ebx+1712], ecx
	mov ecx, -1031593227
	mov DWORD PTR [ebx+1716], ecx
	mov ecx, -1126617421
	mov DWORD PTR [ebx+1720], ecx
	mov ecx, 2083047147
	mov DWORD PTR [ebx+1724], ecx
	mov ecx, 1041261642
	mov DWORD PTR [ebx+1728], ecx
	mov ecx, -882070802
	mov DWORD PTR [ebx+1732], ecx
	mov ecx, -850433470
	mov DWORD PTR [ebx+1736], ecx
	mov ecx, -2125757154
	mov DWORD PTR [ebx+1740], ecx
	mov ecx, -947352222
	mov DWORD PTR [ebx+1744], ecx
	mov ecx, -1836791019
	mov DWORD PTR [ebx+1748], ecx
	mov ecx, -2107500197
	mov DWORD PTR [ebx+1752], ecx
	mov ecx, 1068324162
	mov DWORD PTR [ebx+1756], ecx
	mov ecx, 576689010
	mov DWORD PTR [ebx+1760], ecx
	mov ecx, 2005266142
	mov DWORD PTR [ebx+1764], ecx
	mov ecx, -638584825
	mov DWORD PTR [ebx+1768], ecx
	mov ecx, 184814697
	mov DWORD PTR [ebx+1772], ecx
	mov ecx, 517293380
	mov DWORD PTR [ebx+1776], ecx
	mov ecx, 1734301043
	mov DWORD PTR [ebx+1780], ecx
	mov ecx, 1831354052
	mov DWORD PTR [ebx+1784], ecx
	mov ecx, -2082230210
	mov DWORD PTR [ebx+1788], ecx
	mov ecx, -992234165
	mov DWORD PTR [ebx+1792], ecx
	mov ecx, -1885582931
	mov DWORD PTR [ebx+1796], ecx
	mov ecx, -1034524180
	mov DWORD PTR [ebx+1800], ecx
	mov ecx, -459246311
	mov DWORD PTR [ebx+1804], ecx
	mov ecx, -1721017537
	mov DWORD PTR [ebx+1808], ecx
	mov ecx, -263327839
	mov DWORD PTR [ebx+1812], ecx
	mov ecx, 40076364
	mov DWORD PTR [ebx+1816], ecx
	mov ecx, 1799110153
	mov DWORD PTR [ebx+1820], ecx
	mov ecx, -1430826392
	mov DWORD PTR [ebx+1824], ecx
	mov ecx, 1468956478
	mov DWORD PTR [ebx+1828], ecx
	mov ecx, 49344688
	mov DWORD PTR [ebx+1832], ecx
	mov ecx, -601539410
	mov DWORD PTR [ebx+1836], ecx
	mov ecx, 580156625
	mov DWORD PTR [ebx+1840], ecx
	mov ecx, -1698154694
	mov DWORD PTR [ebx+1844], ecx
	mov ecx, -1528033367
	mov DWORD PTR [ebx+1848], ecx
	mov ecx, 405945314
	mov DWORD PTR [ebx+1852], ecx
	mov ecx, -160477362
	mov DWORD PTR [ebx+1856], ecx
	mov ecx, -1135205332
	mov DWORD PTR [ebx+1860], ecx
	mov ecx, -592193058
	mov DWORD PTR [ebx+1864], ecx
	mov ecx, -1622135211
	mov DWORD PTR [ebx+1868], ecx
	mov ecx, -373525382
	mov DWORD PTR [ebx+1872], ecx
	mov ecx, -1000088596
	mov DWORD PTR [ebx+1876], ecx
	mov ecx, 618476271
	mov DWORD PTR [ebx+1880], ecx
	mov ecx, 324020754
	mov DWORD PTR [ebx+1884], ecx
	mov ecx, 1602293873
	mov DWORD PTR [ebx+1888], ecx
	mov ecx, 1497159428
	mov DWORD PTR [ebx+1892], ecx
	mov ecx, 513710066
	mov DWORD PTR [ebx+1896], ecx
	mov ecx, 1518791302
	mov DWORD PTR [ebx+1900], ecx
	mov ecx, -1725346185
	mov DWORD PTR [ebx+1904], ecx
	mov ecx, -1674685824
	mov DWORD PTR [ebx+1908], ecx
	mov ecx, 514168006
	mov DWORD PTR [ebx+1912], ecx
	mov ecx, 421082866
	mov DWORD PTR [ebx+1916], ecx
	mov ecx, -353634478
	mov DWORD PTR [ebx+1920], ecx
	mov ecx, 28419811
	mov DWORD PTR [ebx+1924], ecx
	mov ecx, 1751498435
	mov DWORD PTR [ebx+1928], ecx
	mov ecx, 1529535470
	mov DWORD PTR [ebx+1932], ecx
	mov ecx, 1642866965
	mov DWORD PTR [ebx+1936], ecx
	mov ecx, -1442583789
	mov DWORD PTR [ebx+1940], ecx
	mov ecx, -875213643
	mov DWORD PTR [ebx+1944], ecx
	mov ecx, -1298374418
	mov DWORD PTR [ebx+1948], ecx
	mov ecx, 1704991076
	mov DWORD PTR [ebx+1952], ecx
	mov ecx, -1070515136
	mov DWORD PTR [ebx+1956], ecx
	mov ecx, 1653966747
	mov DWORD PTR [ebx+1960], ecx
	mov ecx, 370251768
	mov DWORD PTR [ebx+1964], ecx
	mov ecx, 2023147278
	mov DWORD PTR [ebx+1968], ecx
	mov ecx, 446372695
	mov DWORD PTR [ebx+1972], ecx
	mov ecx, 1838109645
	mov DWORD PTR [ebx+1976], ecx
	mov ecx, -285330344
	mov DWORD PTR [ebx+1980], ecx
	mov ecx, 541255773
	mov DWORD PTR [ebx+1984], ecx
	mov ecx, -86269115
	mov DWORD PTR [ebx+1988], ecx
	mov ecx, 1097199559
	mov DWORD PTR [ebx+1992], ecx
	mov ecx, 1038386904
	mov DWORD PTR [ebx+1996], ecx
	mov ecx, -1040426033
	mov DWORD PTR [ebx+2000], ecx
	mov ecx, 1447520639
	mov DWORD PTR [ebx+2004], ecx
	mov ecx, 588557577
	mov DWORD PTR [ebx+2008], ecx
	mov ecx, 589106264
	mov DWORD PTR [ebx+2012], ecx
	mov ecx, 1826000179
	mov DWORD PTR [ebx+2016], ecx
	mov ecx, -834614404
	mov DWORD PTR [ebx+2020], ecx
	mov ecx, 1642600870
	mov DWORD PTR [ebx+2024], ecx
	mov ecx, -2141534807
	mov DWORD PTR [ebx+2028], ecx
	mov ecx, 251511710
	mov DWORD PTR [ebx+2032], ecx
	mov ecx, -479784741
	mov DWORD PTR [ebx+2036], ecx
	mov ecx, -247631419
	mov DWORD PTR [ebx+2040], ecx
	mov ecx, -605647083
	mov DWORD PTR [ebx+2044], ecx
	mov ecx, 874313576
	mov DWORD PTR [ebx+2048], ecx
	mov ecx, 1747908599
	mov DWORD PTR [ebx+2052], ecx
	mov ecx, -1346934159
	mov DWORD PTR [ebx+2056], ecx
	mov ecx, 1081361966
	mov DWORD PTR [ebx+2060], ecx
	mov ecx, 1171500829
	mov DWORD PTR [ebx+2064], ecx
	mov ecx, 80774636
	mov DWORD PTR [ebx+2068], ecx
	mov ecx, -1696185933
	mov DWORD PTR [ebx+2072], ecx
	mov ecx, -69536731
	mov DWORD PTR [ebx+2076], ecx
	mov ecx, -291241886
	mov DWORD PTR [ebx+2080], ecx
	mov ecx, -1241084766
	mov DWORD PTR [ebx+2084], ecx
	mov ecx, 1117383804
	mov DWORD PTR [ebx+2088], ecx
	mov ecx, -1951680203
	mov DWORD PTR [ebx+2092], ecx
	mov ecx, -1305389321
	mov DWORD PTR [ebx+2096], ecx
	mov ecx, -67685772
	mov DWORD PTR [ebx+2100], ecx
	mov ecx, 665622350
	mov DWORD PTR [ebx+2104], ecx
	mov ecx, 1270318906
	mov DWORD PTR [ebx+2108], ecx
	mov ecx, 862148796
	mov DWORD PTR [ebx+2112], ecx
	mov ecx, 2082273622
	mov DWORD PTR [ebx+2116], ecx
	mov ecx, -480481278
	mov DWORD PTR [ebx+2120], ecx
	mov ecx, -599842232
	mov DWORD PTR [ebx+2124], ecx
	mov ecx, 396627950
	mov DWORD PTR [ebx+2128], ecx
	mov ecx, 1687146987
	mov DWORD PTR [ebx+2132], ecx
	mov ecx, 463691828
	mov DWORD PTR [ebx+2136], ecx
	mov ecx, 366059202
	mov DWORD PTR [ebx+2140], ecx
	mov ecx, 576905696
	mov DWORD PTR [ebx+2144], ecx
	mov ecx, 680302862
	mov DWORD PTR [ebx+2148], ecx
	mov ecx, -261948091
	mov DWORD PTR [ebx+2152], ecx
	mov ecx, 505936495
	mov DWORD PTR [ebx+2156], ecx
	mov ecx, 933983297
	mov DWORD PTR [ebx+2160], ecx
	mov ecx, 223148128
	mov DWORD PTR [ebx+2164], ecx
	mov ecx, 70989584
	mov DWORD PTR [ebx+2168], ecx
	mov ecx, 194159559
	mov DWORD PTR [ebx+2172], ecx
	mov ecx, -1559520005
	mov DWORD PTR [ebx+2176], ecx
	mov ecx, -339794808
	mov DWORD PTR [ebx+2180], ecx
	mov ecx, 764901811
	mov DWORD PTR [ebx+2184], ecx
	mov ecx, 483146663
	mov DWORD PTR [ebx+2188], ecx
	mov ecx, 1357309751
	mov DWORD PTR [ebx+2192], ecx
	mov ecx, -908527080
	mov DWORD PTR [ebx+2196], ecx
	mov ecx, 711886425
	mov DWORD PTR [ebx+2200], ecx
	mov ecx, -24617138
	mov DWORD PTR [ebx+2204], ecx
	mov ecx, 1308132951
	mov DWORD PTR [ebx+2208], ecx
	mov ecx, -872107962
	mov DWORD PTR [ebx+2212], ecx
	mov ecx, 1602711859
	mov DWORD PTR [ebx+2216], ecx
	mov ecx, 1637426366
	mov DWORD PTR [ebx+2220], ecx
	mov ecx, -1036475761
	mov DWORD PTR [ebx+2224], ecx
	mov ecx, -1185581885
	mov DWORD PTR [ebx+2228], ecx
	mov ecx, -495352735
	mov DWORD PTR [ebx+2232], ecx
	mov ecx, 1284599950
	mov DWORD PTR [ebx+2236], ecx
	mov ecx, -1639395103
	mov DWORD PTR [ebx+2240], ecx
	mov ecx, 866191798
	mov DWORD PTR [ebx+2244], ecx
	mov ecx, 270896130
	mov DWORD PTR [ebx+2248], ecx
	mov ecx, 1762647837
	mov DWORD PTR [ebx+2252], ecx
	mov ecx, 1385954947
	mov DWORD PTR [ebx+2256], ecx
	mov ecx, 667220481
	mov DWORD PTR [ebx+2260], ecx
	mov ecx, -1257881305
	mov DWORD PTR [ebx+2264], ecx
	mov ecx, 1655365672
	mov DWORD PTR [ebx+2268], ecx
	mov ecx, 882140119
	mov DWORD PTR [ebx+2272], ecx
	mov ecx, 1990319702
	mov DWORD PTR [ebx+2276], ecx
	mov ecx, 608012297
	mov DWORD PTR [ebx+2280], ecx
	mov ecx, -55264929
	mov DWORD PTR [ebx+2284], ecx
	mov ecx, -992758408
	mov DWORD PTR [ebx+2288], ecx
	mov ecx, 1020917854
	mov DWORD PTR [ebx+2292], ecx
	mov ecx, 936297703
	mov DWORD PTR [ebx+2296], ecx
	mov ecx, -527560140
	mov DWORD PTR [ebx+2300], ecx
	mov ecx, 690372698
	mov DWORD PTR [ebx+2304], ecx
	mov ecx, 7066656
	mov DWORD PTR [ebx+2308], ecx
	mov ecx, 1641346084
	mov DWORD PTR [ebx+2312], ecx
	mov ecx, -2008070666
	mov DWORD PTR [ebx+2316], ecx
	mov ecx, 803049980
	mov DWORD PTR [ebx+2320], ecx
	mov ecx, -2056415479
	mov DWORD PTR [ebx+2324], ecx
	mov ecx, 172439847
	mov DWORD PTR [ebx+2328], ecx
	mov ecx, 1837508984
	mov DWORD PTR [ebx+2332], ecx
	mov ecx, -1916770028
	mov DWORD PTR [ebx+2336], ecx
	mov ecx, -689918466
	mov DWORD PTR [ebx+2340], ecx
	mov ecx, 715349790
	mov DWORD PTR [ebx+2344], ecx
	mov ecx, 1322747294
	mov DWORD PTR [ebx+2348], ecx
	mov ecx, -1754916614
	mov DWORD PTR [ebx+2352], ecx
	mov ecx, 552027130
	mov DWORD PTR [ebx+2356], ecx
	mov ecx, -1789479947
	mov DWORD PTR [ebx+2360], ecx
	mov ecx, -1784050374
	mov DWORD PTR [ebx+2364], ecx
	mov ecx, -618030489
	mov DWORD PTR [ebx+2368], ecx
	mov ecx, 830350666
	mov DWORD PTR [ebx+2372], ecx
	mov ecx, 739586024
	mov DWORD PTR [ebx+2376], ecx
	mov ecx, -2045547243
	mov DWORD PTR [ebx+2380], ecx
	mov ecx, 1853431753
	mov DWORD PTR [ebx+2384], ecx
	mov ecx, 901890129
	mov DWORD PTR [ebx+2388], ecx
	mov ecx, 1827183736
	mov DWORD PTR [ebx+2392], ecx
	mov ecx, -2125516108
	mov DWORD PTR [ebx+2396], ecx
	mov ecx, -1190423915
	mov DWORD PTR [ebx+2400], ecx
	mov ecx, -150205022
	mov DWORD PTR [ebx+2404], ecx
	mov ecx, -183987080
	mov DWORD PTR [ebx+2408], ecx
	mov ecx, -1912780637
	mov DWORD PTR [ebx+2412], ecx
	mov ecx, -43057309
	mov DWORD PTR [ebx+2416], ecx
	mov ecx, 1809964508
	mov DWORD PTR [ebx+2420], ecx
	mov ecx, -388748203
	mov DWORD PTR [ebx+2424], ecx
	mov ecx, -317718771
	mov DWORD PTR [ebx+2428], ecx
	mov ecx, 1590656415
	mov DWORD PTR [ebx+2432], ecx
	mov ecx, -696668881
	mov DWORD PTR [ebx+2436], ecx
	mov ecx, 836917550
	mov DWORD PTR [ebx+2440], ecx
	mov ecx, -246666323
	mov DWORD PTR [ebx+2444], ecx
	mov ecx, 1673220418
	mov DWORD PTR [ebx+2448], ecx
	mov ecx, -1010963184
	mov DWORD PTR [ebx+2452], ecx
	mov ecx, -353627370
	mov DWORD PTR [ebx+2456], ecx
	mov ecx, -1008097177
	mov DWORD PTR [ebx+2460], ecx
	mov ecx, 1618722944
	mov DWORD PTR [ebx+2464], ecx
	mov ecx, -55697533
	mov DWORD PTR [ebx+2468], ecx
	mov ecx, 1581362027
	mov DWORD PTR [ebx+2472], ecx
	mov ecx, 776121943
	mov DWORD PTR [ebx+2476], ecx
	mov ecx, -1108345356
	mov DWORD PTR [ebx+2480], ecx
	mov ecx, -638415111
	mov DWORD PTR [ebx+2484], ecx
	mov ecx, -1794187482
	mov DWORD PTR [ebx+2488], ecx
	mov ecx, -564832423
	mov DWORD PTR [ebx+2492], ecx
	mov ecx, -1453193812
	mov DWORD PTR [ebx+2496], ecx
	mov ecx, 1175051289
	mov DWORD PTR [ebx+2500], ecx
	mov ecx, -23020001
	mov DWORD PTR [ebx+2504], ecx
	mov ecx, -235756483
	mov DWORD PTR [ebx+2508], ecx
	mov ecx, 2144208602
	mov DWORD PTR [ebx+2512], ecx
	mov ecx, -793410722
	mov DWORD PTR [ebx+2516], ecx
	mov ecx, 105678476
	mov DWORD PTR [ebx+2520], ecx
	mov ecx, 2102953594
	mov DWORD PTR [ebx+2524], ecx
	mov ecx, 383642270
	mov DWORD PTR [ebx+2528], ecx
	mov ecx, 494778094
	mov DWORD PTR [ebx+2532], ecx
	mov ecx, 2081030628
	mov DWORD PTR [ebx+2536], ecx
	mov ecx, -1201955470
	mov DWORD PTR [ebx+2540], ecx
	mov ecx, 259827029
	mov DWORD PTR [ebx+2544], ecx
	mov ecx, 320136943
	mov DWORD PTR [ebx+2548], ecx
	mov ecx, -926986553
	mov DWORD PTR [ebx+2552], ecx
	mov ecx, 16417330
	mov DWORD PTR [ebx+2556], ecx
	mov ecx, 1766621501
	mov DWORD PTR [ebx+2560], ecx
	mov ecx, -1561066987
	mov DWORD PTR [ebx+2564], ecx
	mov ecx, 12001288
	mov DWORD PTR [ebx+2568], ecx
	mov ecx, -1960762311
	mov DWORD PTR [ebx+2572], ecx
	mov ecx, -1594575467
	mov DWORD PTR [ebx+2576], ecx
	mov ecx, -877871684
	mov DWORD PTR [ebx+2580], ecx
	mov ecx, -903479829
	mov DWORD PTR [ebx+2584], ecx
	mov ecx, -1238629296
	mov DWORD PTR [ebx+2588], ecx
	mov ecx, -1592899364
	mov DWORD PTR [ebx+2592], ecx
	mov ecx, -192116929
	mov DWORD PTR [ebx+2596], ecx
	mov ecx, 1803040718
	mov DWORD PTR [ebx+2600], ecx
	mov ecx, 305787902
	mov DWORD PTR [ebx+2604], ecx
	mov ecx, -475828791
	mov DWORD PTR [ebx+2608], ecx
	mov ecx, 2017549166
	mov DWORD PTR [ebx+2612], ecx
	mov ecx, 1212218890
	mov DWORD PTR [ebx+2616], ecx
	mov ecx, -1771338925
	mov DWORD PTR [ebx+2620], ecx
	mov ecx, -509012568
	mov DWORD PTR [ebx+2624], ecx
	mov ecx, 703869226
	mov DWORD PTR [ebx+2628], ecx
	mov ecx, 683354104
	mov DWORD PTR [ebx+2632], ecx
	mov ecx, 264357569
	mov DWORD PTR [ebx+2636], ecx
	mov ecx, -2008611591
	mov DWORD PTR [ebx+2640], ecx
	mov ecx, 297573215
	mov DWORD PTR [ebx+2644], ecx
	mov ecx, 1677208187
	mov DWORD PTR [ebx+2648], ecx
	mov ecx, -781786862
	mov DWORD PTR [ebx+2652], ecx
	mov ecx, -1104921053
	mov DWORD PTR [ebx+2656], ecx
	mov ecx, -1569539406
	mov DWORD PTR [ebx+2660], ecx
	mov ecx, -864176366
	mov DWORD PTR [ebx+2664], ecx
	mov ecx, 1050508617
	mov DWORD PTR [ebx+2668], ecx
	mov ecx, -126931385
	mov DWORD PTR [ebx+2672], ecx
	mov ecx, 1847323410
	mov DWORD PTR [ebx+2676], ecx
	mov ecx, -798660741
	mov DWORD PTR [ebx+2680], ecx
	mov ecx, 255393833
	mov DWORD PTR [ebx+2684], ecx
	mov ecx, 361880443
	mov DWORD PTR [ebx+2688], ecx
	mov ecx, 999578387
	mov DWORD PTR [ebx+2692], ecx
	mov ecx, 774246713
	mov DWORD PTR [ebx+2696], ecx
	mov ecx, 779446850
	mov DWORD PTR [ebx+2700], ecx
	mov ecx, -73297390
	mov DWORD PTR [ebx+2704], ecx
	mov ecx, -517617045
	mov DWORD PTR [ebx+2708], ecx
	mov ecx, -1425272254
	mov DWORD PTR [ebx+2712], ecx
	mov ecx, -457210193
	mov DWORD PTR [ebx+2716], ecx
	mov ecx, 58259388
	mov DWORD PTR [ebx+2720], ecx
	mov ecx, 910506237
	mov DWORD PTR [ebx+2724], ecx
	mov ecx, 8396354
	mov DWORD PTR [ebx+2728], ecx
	mov ecx, 1481042080
	mov DWORD PTR [ebx+2732], ecx
	mov ecx, -1988829864
	mov DWORD PTR [ebx+2736], ecx
	mov ecx, -59395226
	mov DWORD PTR [ebx+2740], ecx
	mov ecx, 1600789995
	mov DWORD PTR [ebx+2744], ecx
	mov ecx, 47559790
	mov DWORD PTR [ebx+2748], ecx
	mov ecx, 1957200395
	mov DWORD PTR [ebx+2752], ecx
	mov ecx, 841853311
	mov DWORD PTR [ebx+2756], ecx
	mov ecx, 1855582298
	mov DWORD PTR [ebx+2760], ecx
	mov ecx, 1753654713
	mov DWORD PTR [ebx+2764], ecx
	mov ecx, -840812105
	mov DWORD PTR [ebx+2768], ecx
	mov ecx, -436074991
	mov DWORD PTR [ebx+2772], ecx
	mov ecx, -1470087176
	mov DWORD PTR [ebx+2776], ecx
	mov ecx, -597625577
	mov DWORD PTR [ebx+2780], ecx
	mov ecx, -1027458842
	mov DWORD PTR [ebx+2784], ecx
	mov ecx, 1509735627
	mov DWORD PTR [ebx+2788], ecx
	mov ecx, -1837990907
	mov DWORD PTR [ebx+2792], ecx
	mov ecx, -1631498781
	mov DWORD PTR [ebx+2796], ecx
	mov ecx, -1388446636
	mov DWORD PTR [ebx+2800], ecx
	mov ecx, 1367695696
	mov DWORD PTR [ebx+2804], ecx
	mov ecx, -970268203
	mov DWORD PTR [ebx+2808], ecx
	mov ecx, 1611555738
	mov DWORD PTR [ebx+2812], ecx
	mov ecx, -1795779351
	mov DWORD PTR [ebx+2816], ecx
	mov ecx, -725846463
	mov DWORD PTR [ebx+2820], ecx
	mov ecx, 1346581460
	mov DWORD PTR [ebx+2824], ecx
	mov ecx, -1089169634
	mov DWORD PTR [ebx+2828], ecx
	mov ecx, 1718654541
	mov DWORD PTR [ebx+2832], ecx
	mov ecx, 830407615
	mov DWORD PTR [ebx+2836], ecx
	mov ecx, -1411754602
	mov DWORD PTR [ebx+2840], ecx
	mov ecx, -385199320
	mov DWORD PTR [ebx+2844], ecx
	mov ecx, 661182312
	mov DWORD PTR [ebx+2848], ecx
	mov ecx, 2058741839
	mov DWORD PTR [ebx+2852], ecx
	mov ecx, 1087296426
	mov DWORD PTR [ebx+2856], ecx
	mov ecx, 1005508896
	mov DWORD PTR [ebx+2860], ecx
	mov ecx, -366589155
	mov DWORD PTR [ebx+2864], ecx
	mov ecx, -899097286
	mov DWORD PTR [ebx+2868], ecx
	mov ecx, -1169827589
	mov DWORD PTR [ebx+2872], ecx
	mov ecx, -788651947
	mov DWORD PTR [ebx+2876], ecx
	mov ecx, -1714642603
	mov DWORD PTR [ebx+2880], ecx
	mov ecx, -1872871514
	mov DWORD PTR [ebx+2884], ecx
	mov ecx, 92275965
	mov DWORD PTR [ebx+2888], ecx
	mov ecx, -951524203
	mov DWORD PTR [ebx+2892], ecx
	mov ecx, 1564492039
	mov DWORD PTR [ebx+2896], ecx
	mov ecx, 1106433330
	mov DWORD PTR [ebx+2900], ecx
	mov ecx, 534732837
	mov DWORD PTR [ebx+2904], ecx
	mov ecx, -894500338
	mov DWORD PTR [ebx+2908], ecx
	mov ecx, -298110101
	mov DWORD PTR [ebx+2912], ecx
	mov ecx, 769582725
	mov DWORD PTR [ebx+2916], ecx
	mov ecx, -412838448
	mov DWORD PTR [ebx+2920], ecx
	mov ecx, -205289644
	mov DWORD PTR [ebx+2924], ecx
	mov ecx, -197486326
	mov DWORD PTR [ebx+2928], ecx
	mov ecx, -610688600
	mov DWORD PTR [ebx+2932], ecx
	mov ecx, -601395770
	mov DWORD PTR [ebx+2936], ecx
	mov ecx, 1773522161
	mov DWORD PTR [ebx+2940], ecx
	mov ecx, -643772826
	mov DWORD PTR [ebx+2944], ecx
	mov ecx, 1987793339
	mov DWORD PTR [ebx+2948], ecx
	mov ecx, -192885705
	mov DWORD PTR [ebx+2952], ecx
	mov ecx, 2014496360
	mov DWORD PTR [ebx+2956], ecx
	mov ecx, 1258731370
	mov DWORD PTR [ebx+2960], ecx
	mov ecx, -499314406
	mov DWORD PTR [ebx+2964], ecx
	mov ecx, -707196348
	mov DWORD PTR [ebx+2968], ecx
	mov ecx, 1690229348
	mov DWORD PTR [ebx+2972], ecx
	mov ecx, 1616965789
	mov DWORD PTR [ebx+2976], ecx
	mov ecx, -680003887
	mov DWORD PTR [ebx+2980], ecx
	mov ecx, 1018228867
	mov DWORD PTR [ebx+2984], ecx
	mov ecx, -1084899977
	mov DWORD PTR [ebx+2988], ecx
	mov ecx, -2013990322
	mov DWORD PTR [ebx+2992], ecx
	mov ecx, 1186252883
	mov DWORD PTR [ebx+2996], ecx
	mov ecx, -1853584518
	mov DWORD PTR [ebx+3000], ecx
	mov ecx, -913563578
	mov DWORD PTR [ebx+3004], ecx
	mov ecx, 1964096441
	mov DWORD PTR [ebx+3008], ecx
	mov ecx, -999890761
	mov DWORD PTR [ebx+3012], ecx
	mov ecx, 491391464
	mov DWORD PTR [ebx+3016], ecx
	mov ecx, 681642778
	mov DWORD PTR [ebx+3020], ecx
	mov ecx, 1335973852
	mov DWORD PTR [ebx+3024], ecx
	mov ecx, 228632400
	mov DWORD PTR [ebx+3028], ecx
	mov ecx, 1640200090
	mov DWORD PTR [ebx+3032], ecx
	mov ecx, 805355760
	mov DWORD PTR [ebx+3036], ecx
	mov ecx, -1034738927
	mov DWORD PTR [ebx+3040], ecx
	mov ecx, -823422789
	mov DWORD PTR [ebx+3044], ecx
	mov ecx, 2084129647
	mov DWORD PTR [ebx+3048], ecx
	mov ecx, -753241466
	mov DWORD PTR [ebx+3052], ecx
	mov ecx, 1306003693
	mov DWORD PTR [ebx+3056], ecx
	mov ecx, 1822601502
	mov DWORD PTR [ebx+3060], ecx
	mov ecx, -583641489
	mov DWORD PTR [ebx+3064], ecx
	mov ecx, 1080529623
	mov DWORD PTR [ebx+3068], ecx
	mov ecx, 456642359
	mov DWORD PTR [ebx+3072], ecx
	mov ecx, -1103084898
	mov DWORD PTR [ebx+3076], ecx
	mov ecx, 2071860637
	mov DWORD PTR [ebx+3080], ecx
	mov ecx, -1262598805
	mov DWORD PTR [ebx+3084], ecx
	mov ecx, -925730513
	mov DWORD PTR [ebx+3088], ecx
	mov ecx, -971145746
	mov DWORD PTR [ebx+3092], ecx
	mov ecx, 82333915
	mov DWORD PTR [ebx+3096], ecx
	mov ecx, 585276144
	mov DWORD PTR [ebx+3100], ecx
	mov ecx, -1532299592
	mov DWORD PTR [ebx+3104], ecx
	mov ecx, -699380294
	mov DWORD PTR [ebx+3108], ecx
	mov ecx, -377036295
	mov DWORD PTR [ebx+3112], ecx
	mov ecx, 1500109523
	mov DWORD PTR [ebx+3116], ecx
	mov ecx, -1817378539
	mov DWORD PTR [ebx+3120], ecx
	mov ecx, 1373214554
	mov DWORD PTR [ebx+3124], ecx
	mov ecx, 685145402
	mov DWORD PTR [ebx+3128], ecx
	mov ecx, 1282579407
	mov DWORD PTR [ebx+3132], ecx
	mov ecx, -1677859215
	mov DWORD PTR [ebx+3136], ecx
	mov ecx, 673827981
	mov DWORD PTR [ebx+3140], ecx
	mov ecx, -1941678703
	mov DWORD PTR [ebx+3144], ecx
	mov ecx, -1121600812
	mov DWORD PTR [ebx+3148], ecx
	mov ecx, 720151061
	mov DWORD PTR [ebx+3152], ecx
	mov ecx, 435942811
	mov DWORD PTR [ebx+3156], ecx
	mov ecx, -1149045464
	mov DWORD PTR [ebx+3160], ecx
	mov ecx, 1600649233
	mov DWORD PTR [ebx+3164], ecx
	mov ecx, -1855812015
	mov DWORD PTR [ebx+3168], ecx
	mov ecx, 845467330
	mov DWORD PTR [ebx+3172], ecx
	mov ecx, -2140584322
	mov DWORD PTR [ebx+3176], ecx
	mov ecx, 1727865872
	mov DWORD PTR [ebx+3180], ecx
	mov ecx, -1362109174
	mov DWORD PTR [ebx+3184], ecx
	mov ecx, -1149288227
	mov DWORD PTR [ebx+3188], ecx
	mov ecx, -716946050
	mov DWORD PTR [ebx+3192], ecx
	mov ecx, 1202633640
	mov DWORD PTR [ebx+3196], ecx
	mov ecx, 1880858211
	mov DWORD PTR [ebx+3200], ecx
	mov ecx, 1567709069
	mov DWORD PTR [ebx+3204], ecx
	mov ecx, -2073375736
	mov DWORD PTR [ebx+3208], ecx
	mov ecx, 1219763496
	mov DWORD PTR [ebx+3212], ecx
	mov ecx, -129269118
	mov DWORD PTR [ebx+3216], ecx
	mov ecx, -1121198927
	mov DWORD PTR [ebx+3220], ecx
	mov ecx, -910734367
	mov DWORD PTR [ebx+3224], ecx
	mov ecx, -943458690
	mov DWORD PTR [ebx+3228], ecx
	mov ecx, 952867401
	mov DWORD PTR [ebx+3232], ecx
	mov ecx, 1333552938
	mov DWORD PTR [ebx+3236], ecx
	mov ecx, -1660994889
	mov DWORD PTR [ebx+3240], ecx
	mov ecx, 628173356
	mov DWORD PTR [ebx+3244], ecx
	mov ecx, -782636191
	mov DWORD PTR [ebx+3248], ecx
	mov ecx, 1113918558
	mov DWORD PTR [ebx+3252], ecx
	mov ecx, 1690188558
	mov DWORD PTR [ebx+3256], ecx
	mov ecx, 506191666
	mov DWORD PTR [ebx+3260], ecx
	mov ecx, -668955583
	mov DWORD PTR [ebx+3264], ecx
	mov ecx, 491204237
	mov DWORD PTR [ebx+3268], ecx
	mov ecx, 1875874132
	mov DWORD PTR [ebx+3272], ecx
	mov ecx, -1715141274
	mov DWORD PTR [ebx+3276], ecx
	mov ecx, 36774743
	mov DWORD PTR [ebx+3280], ecx
	mov ecx, -862472862
	mov DWORD PTR [ebx+3284], ecx
	mov ecx, 337367186
	mov DWORD PTR [ebx+3288], ecx
	mov ecx, -1710880067
	mov DWORD PTR [ebx+3292], ecx
	mov ecx, -152960771
	mov DWORD PTR [ebx+3296], ecx
	mov ecx, 729555461
	mov DWORD PTR [ebx+3300], ecx
	mov ecx, -262089792
	mov DWORD PTR [ebx+3304], ecx
	mov ecx, 1623553692
	mov DWORD PTR [ebx+3308], ecx
	mov ecx, 2125518926
	mov DWORD PTR [ebx+3312], ecx
	mov ecx, -102462372
	mov DWORD PTR [ebx+3316], ecx
	mov ecx, -1624399767
	mov DWORD PTR [ebx+3320], ecx
	mov ecx, -421307598
	mov DWORD PTR [ebx+3324], ecx
	mov ecx, 762836430
	mov DWORD PTR [ebx+3328], ecx
	mov ecx, -1691928729
	mov DWORD PTR [ebx+3332], ecx
	mov ecx, -1004768370
	mov DWORD PTR [ebx+3336], ecx
	mov ecx, 1857130523
	mov DWORD PTR [ebx+3340], ecx
	mov ecx, -1032425813
	mov DWORD PTR [ebx+3344], ecx
	mov ecx, 1292558072
	mov DWORD PTR [ebx+3348], ecx
	mov ecx, -484030789
	mov DWORD PTR [ebx+3352], ecx
	mov ecx, -292793899
	mov DWORD PTR [ebx+3356], ecx
	mov ecx, -805097790
	mov DWORD PTR [ebx+3360], ecx
	mov ecx, 1528130145
	mov DWORD PTR [ebx+3364], ecx
	mov ecx, 1653947042
	mov DWORD PTR [ebx+3368], ecx
	mov ecx, 175110127
	mov DWORD PTR [ebx+3372], ecx
	mov ecx, -437877079
	mov DWORD PTR [ebx+3376], ecx
	mov ecx, -1950885891
	mov DWORD PTR [ebx+3380], ecx
	mov ecx, 759080620
	mov DWORD PTR [ebx+3384], ecx
	mov ecx, -172705755
	mov DWORD PTR [ebx+3388], ecx
	mov ecx, -89348692
	mov DWORD PTR [ebx+3392], ecx
	mov ecx, 778459076
	mov DWORD PTR [ebx+3396], ecx
	mov ecx, 1578000385
	mov DWORD PTR [ebx+3400], ecx
	mov ecx, -262050451
	mov DWORD PTR [ebx+3404], ecx
	mov ecx, 119166878
	mov DWORD PTR [ebx+3408], ecx
	mov ecx, -211410579
	mov DWORD PTR [ebx+3412], ecx
	mov ecx, 1010105817
	mov DWORD PTR [ebx+3416], ecx
	mov ecx, -1840129673
	mov DWORD PTR [ebx+3420], ecx
	mov ecx, -111617001
	mov DWORD PTR [ebx+3424], ecx
	mov ecx, -1093764208
	mov DWORD PTR [ebx+3428], ecx
	mov ecx, -430752285
	mov DWORD PTR [ebx+3432], ecx
	mov ecx, 556642824
	mov DWORD PTR [ebx+3436], ecx
	mov ecx, -924925882
	mov DWORD PTR [ebx+3440], ecx
	mov ecx, -486437385
	mov DWORD PTR [ebx+3444], ecx
	mov ecx, -854917270
	mov DWORD PTR [ebx+3448], ecx
	mov ecx, 1863484622
	mov DWORD PTR [ebx+3452], ecx
	mov ecx, 1668767204
	mov DWORD PTR [ebx+3456], ecx
	mov ecx, 2098598669
	mov DWORD PTR [ebx+3460], ecx
	mov ecx, -1354308917
	mov DWORD PTR [ebx+3464], ecx
	mov ecx, -1600177660
	mov DWORD PTR [ebx+3468], ecx
	mov ecx, 656255803
	mov DWORD PTR [ebx+3472], ecx
	mov ecx, 628703072
	mov DWORD PTR [ebx+3476], ecx
	mov ecx, -1161201351
	mov DWORD PTR [ebx+3480], ecx
	mov ecx, -1441672760
	mov DWORD PTR [ebx+3484], ecx
	mov ecx, -622936697
	mov DWORD PTR [ebx+3488], ecx
	mov ecx, 724645571
	mov DWORD PTR [ebx+3492], ecx
	mov ecx, 1159314265
	mov DWORD PTR [ebx+3496], ecx
	mov ecx, 368901154
	mov DWORD PTR [ebx+3500], ecx
	mov ecx, -1469801325
	mov DWORD PTR [ebx+3504], ecx
	mov ecx, -1538233849
	mov DWORD PTR [ebx+3508], ecx
	mov ecx, -375334034
	mov DWORD PTR [ebx+3512], ecx
	mov ecx, -231435627
	mov DWORD PTR [ebx+3516], ecx
	mov ecx, 846279796
	mov DWORD PTR [ebx+3520], ecx
	mov ecx, -244371553
	mov DWORD PTR [ebx+3524], ecx
	mov ecx, 2121914586
	mov DWORD PTR [ebx+3528], ecx
	mov ecx, 584195505
	mov DWORD PTR [ebx+3532], ecx
	mov ecx, -852134157
	mov DWORD PTR [ebx+3536], ecx
	mov ecx, 1932979073
	mov DWORD PTR [ebx+3540], ecx
	mov ecx, 1452296546
	mov DWORD PTR [ebx+3544], ecx
	mov ecx, 2077234375
	mov DWORD PTR [ebx+3548], ecx
	mov ecx, -759230637
	mov DWORD PTR [ebx+3552], ecx
	mov ecx, -1664155031
	mov DWORD PTR [ebx+3556], ecx
	mov ecx, -1380064450
	mov DWORD PTR [ebx+3560], ecx
	mov ecx, 1621216800
	mov DWORD PTR [ebx+3564], ecx
	mov ecx, -1426485762
	mov DWORD PTR [ebx+3568], ecx
	mov ecx, -513111358
	mov DWORD PTR [ebx+3572], ecx
	mov ecx, -433725704
	mov DWORD PTR [ebx+3576], ecx
	mov ecx, 1927275105
	mov DWORD PTR [ebx+3580], ecx
	mov ecx, -977077703
	mov DWORD PTR [ebx+3584], ecx
	mov ecx, -1132289104
	mov DWORD PTR [ebx+3588], ecx
	mov ecx, 2952977
	mov DWORD PTR [ebx+3592], ecx
	mov ecx, 913219980
	mov DWORD PTR [ebx+3596], ecx
	mov ecx, 1235457096
	mov DWORD PTR [ebx+3600], ecx
	mov ecx, -797733617
	mov DWORD PTR [ebx+3604], ecx
	mov ecx, 1586870841
	mov DWORD PTR [ebx+3608], ecx
	mov ecx, -2031145478
	mov DWORD PTR [ebx+3612], ecx
	mov ecx, -232905591
	mov DWORD PTR [ebx+3616], ecx
	mov ecx, 1692789184
	mov DWORD PTR [ebx+3620], ecx
	mov ecx, 1437153830
	mov DWORD PTR [ebx+3624], ecx
	mov ecx, -100380113
	mov DWORD PTR [ebx+3628], ecx
	mov ecx, 1040822500
	mov DWORD PTR [ebx+3632], ecx
	mov ecx, 737162384
	mov DWORD PTR [ebx+3636], ecx
	mov ecx, 2110750165
	mov DWORD PTR [ebx+3640], ecx
	mov ecx, -1999179105
	mov DWORD PTR [ebx+3644], ecx
	mov ecx, -1817175767
	mov DWORD PTR [ebx+3648], ecx
	mov ecx, 332741587
	mov DWORD PTR [ebx+3652], ecx
	mov ecx, -745114273
	mov DWORD PTR [ebx+3656], ecx
	mov ecx, 1688335365
	mov DWORD PTR [ebx+3660], ecx
	mov ecx, 975671531
	mov DWORD PTR [ebx+3664], ecx
	mov ecx, -593730753
	mov DWORD PTR [ebx+3668], ecx
	mov ecx, -1168747213
	mov DWORD PTR [ebx+3672], ecx
	mov ecx, -1379136943
	mov DWORD PTR [ebx+3676], ecx
	mov ecx, 547172584
	mov DWORD PTR [ebx+3680], ecx
	mov ecx, 1327578746
	mov DWORD PTR [ebx+3684], ecx
	mov ecx, 333326774
	mov DWORD PTR [ebx+3688], ecx
	mov ecx, 126184878
	mov DWORD PTR [ebx+3692], ecx
	mov ecx, 543966618
	mov DWORD PTR [ebx+3696], ecx
	mov ecx, -1261283138
	mov DWORD PTR [ebx+3700], ecx
	mov ecx, -1271572062
	mov DWORD PTR [ebx+3704], ecx
	mov ecx, 1013343466
	mov DWORD PTR [ebx+3708], ecx
	mov ecx, 1321349019
	mov DWORD PTR [ebx+3712], ecx
	mov ecx, 1400003342
	mov DWORD PTR [ebx+3716], ecx
	mov ecx, 366130240
	mov DWORD PTR [ebx+3720], ecx
	mov ecx, 1857591472
	mov DWORD PTR [ebx+3724], ecx
	mov ecx, 1914314815
	mov DWORD PTR [ebx+3728], ecx
	mov ecx, 1161466645
	mov DWORD PTR [ebx+3732], ecx
	mov ecx, 523423368
	mov DWORD PTR [ebx+3736], ecx
	mov ecx, -402536676
	mov DWORD PTR [ebx+3740], ecx
	mov ecx, 182079376
	mov DWORD PTR [ebx+3744], ecx
	mov ecx, -1309044423
	mov DWORD PTR [ebx+3748], ecx
	mov ecx, -640289378
	mov DWORD PTR [ebx+3752], ecx
	mov ecx, -1802377577
	mov DWORD PTR [ebx+3756], ecx
	mov ecx, -1163348251
	mov DWORD PTR [ebx+3760], ecx
	mov ecx, 64095681
	mov DWORD PTR [ebx+3764], ecx
	mov ecx, 2023266540
	mov DWORD PTR [ebx+3768], ecx
	mov ecx, 1906365215
	mov DWORD PTR [ebx+3772], ecx
	mov ecx, 1992205066
	mov DWORD PTR [ebx+3776], ecx
	mov ecx, -485779147
	mov DWORD PTR [ebx+3780], ecx
	mov ecx, 1046665804
	mov DWORD PTR [ebx+3784], ecx
	mov ecx, -74503144
	mov DWORD PTR [ebx+3788], ecx
	mov ecx, -861392349
	mov DWORD PTR [ebx+3792], ecx
	mov ecx, -770279952
	mov DWORD PTR [ebx+3796], ecx
	mov ecx, -967788138
	mov DWORD PTR [ebx+3800], ecx
	mov ecx, -220103994
	mov DWORD PTR [ebx+3804], ecx
	mov ecx, -1121605462
	mov DWORD PTR [ebx+3808], ecx
	mov ecx, 1993016338
	mov DWORD PTR [ebx+3812], ecx
	mov ecx, 1202405393
	mov DWORD PTR [ebx+3816], ecx
	mov ecx, 1974421048
	mov DWORD PTR [ebx+3820], ecx
	mov ecx, -106239797
	mov DWORD PTR [ebx+3824], ecx
	mov ecx, -339477688
	mov DWORD PTR [ebx+3828], ecx
	mov ecx, 134831316
	mov DWORD PTR [ebx+3832], ecx
	mov ecx, -1014007986
	mov DWORD PTR [ebx+3836], ecx
	mov ecx, 1521210170
	mov DWORD PTR [ebx+3840], ecx
	mov ecx, -1714204836
	mov DWORD PTR [ebx+3844], ecx
	mov ecx, -942227499
	mov DWORD PTR [ebx+3848], ecx
	mov ecx, 1790058935
	mov DWORD PTR [ebx+3852], ecx
	mov ecx, 1707523159
	mov DWORD PTR [ebx+3856], ecx
	mov ecx, 1289045587
	mov DWORD PTR [ebx+3860], ecx
	mov ecx, -1095980759
	mov DWORD PTR [ebx+3864], ecx
	mov ecx, -1704760671
	mov DWORD PTR [ebx+3868], ecx
	mov ecx, -1666890816
	mov DWORD PTR [ebx+3872], ecx
	mov ecx, -1164993661
	mov DWORD PTR [ebx+3876], ecx
	mov ecx, -280254680
	mov DWORD PTR [ebx+3880], ecx
	mov ecx, 2000680903
	mov DWORD PTR [ebx+3884], ecx
	mov ecx, 1000048512
	mov DWORD PTR [ebx+3888], ecx
	mov ecx, 36478697
	mov DWORD PTR [ebx+3892], ecx
	mov ecx, 2094072214
	mov DWORD PTR [ebx+3896], ecx
	mov ecx, 1515891999
	mov DWORD PTR [ebx+3900], ecx
	mov ecx, -314056480
	mov DWORD PTR [ebx+3904], ecx
	mov ecx, 2046306536
	mov DWORD PTR [ebx+3908], ecx
	mov ecx, -470291080
	mov DWORD PTR [ebx+3912], ecx
	mov ecx, 84117525
	mov DWORD PTR [ebx+3916], ecx
	mov ecx, -1449706301
	mov DWORD PTR [ebx+3920], ecx
	mov ecx, 653598235
	mov DWORD PTR [ebx+3924], ecx
	mov ecx, -1979469451
	mov DWORD PTR [ebx+3928], ecx
	mov ecx, -861158872
	mov DWORD PTR [ebx+3932], ecx
	mov ecx, -1825097651
	mov DWORD PTR [ebx+3936], ecx
	mov ecx, 2001861610
	mov DWORD PTR [ebx+3940], ecx
	mov ecx, 1682490280
	mov DWORD PTR [ebx+3944], ecx
	mov ecx, 157932962
	mov DWORD PTR [ebx+3948], ecx
	mov ecx, 475554995
	mov DWORD PTR [ebx+3952], ecx
	mov ecx, 1808538459
	mov DWORD PTR [ebx+3956], ecx
	mov ecx, -1136772387
	mov DWORD PTR [ebx+3960], ecx
	mov ecx, -1081214350
	mov DWORD PTR [ebx+3964], ecx
	mov ecx, -156347182
	mov DWORD PTR [ebx+3968], ecx
	mov ecx, -1342642316
	mov DWORD PTR [ebx+3972], ecx
	mov ecx, 20205120
	mov DWORD PTR [ebx+3976], ecx
	mov ecx, -838429215
	mov DWORD PTR [ebx+3980], ecx
	mov ecx, 654390639
	mov DWORD PTR [ebx+3984], ecx
	mov ecx, 884729697
	mov DWORD PTR [ebx+3988], ecx
	mov ecx, -1607511648
	mov DWORD PTR [ebx+3992], ecx
	mov ecx, -1580221216
	mov DWORD PTR [ebx+3996], ecx
	mov ecx, -707734502
	mov DWORD PTR [ebx+4000], ecx
	mov ecx, -527579645
	mov DWORD PTR [ebx+4004], ecx
	mov ecx, 670188535
	mov DWORD PTR [ebx+4008], ecx
	mov ecx, -1693510209
	mov DWORD PTR [ebx+4012], ecx
	mov ecx, 314756858
	mov DWORD PTR [ebx+4016], ecx
	mov ecx, -888085578
	mov DWORD PTR [ebx+4020], ecx
	mov ecx, 843847392
	mov DWORD PTR [ebx+4024], ecx
	mov ecx, -1982603105
	mov DWORD PTR [ebx+4028], ecx
	mov ecx, -1010480357
	mov DWORD PTR [ebx+4032], ecx
	mov ecx, 266771423
	mov DWORD PTR [ebx+4036], ecx
	mov ecx, -842129691
	mov DWORD PTR [ebx+4040], ecx
	mov ecx, -159056618
	mov DWORD PTR [ebx+4044], ecx
	mov ecx, 1452517109
	mov DWORD PTR [ebx+4048], ecx
	mov ecx, -2006033748
	mov DWORD PTR [ebx+4052], ecx
	mov ecx, 1900839390
	mov DWORD PTR [ebx+4056], ecx
	mov ecx, -1018875162
	mov DWORD PTR [ebx+4060], ecx
	mov ecx, 901472969
	mov DWORD PTR [ebx+4064], ecx
	mov ecx, -843664783
	mov DWORD PTR [ebx+4068], ecx
	mov ecx, 624432723
	mov DWORD PTR [ebx+4072], ecx
	mov ecx, 544733114
	mov DWORD PTR [ebx+4076], ecx
	mov ecx, 1283099269
	mov DWORD PTR [ebx+4080], ecx
	mov ecx, -704576999
	mov DWORD PTR [ebx+4084], ecx
	mov ecx, -1036015984
	mov DWORD PTR [ebx+4088], ecx
	mov ecx, 978833079
	mov DWORD PTR [ebx+4092], ecx
	mov ecx, 608135816
	mov DWORD PTR [ebx+4096], ecx
	mov ecx, -2052912941
	mov DWORD PTR [ebx+4100], ecx
	mov ecx, 320440878
	mov DWORD PTR [ebx+4104], ecx
	mov ecx, 57701188
	mov DWORD PTR [ebx+4108], ecx
	mov ecx, -1542899678
	mov DWORD PTR [ebx+4112], ecx
	mov ecx, 698298832
	mov DWORD PTR [ebx+4116], ecx
	mov ecx, 137296536
	mov DWORD PTR [ebx+4120], ecx
	mov ecx, -330404727
	mov DWORD PTR [ebx+4124], ecx
	mov ecx, 1160258022
	mov DWORD PTR [ebx+4128], ecx
	mov ecx, 953160567
	mov DWORD PTR [ebx+4132], ecx
	mov ecx, -1101764913
	mov DWORD PTR [ebx+4136], ecx
	mov ecx, 887688300
	mov DWORD PTR [ebx+4140], ecx
	mov ecx, -1062458953
	mov DWORD PTR [ebx+4144], ecx
	mov ecx, -914599715
	mov DWORD PTR [ebx+4148], ecx
	mov ecx, 1065670069
	mov DWORD PTR [ebx+4152], ecx
	mov ecx, -1253635817
	mov DWORD PTR [ebx+4156], ecx
	mov ecx, -1843997223
	mov DWORD PTR [ebx+4160], ecx
	mov ecx, -1988494565
	mov DWORD PTR [ebx+4164], ecx
	mov esi, 0
	mov ebx, DWORD PTR [esp+12]
	add ebx, 0
	mov edi, 18
20:
	mov edx, 0
	mov eax, DWORD PTR [esp+4]
	add eax, esi
	movzx ecx, BYTE PTR [eax]
	ror edx, 24
	or edx, ecx
	add esi, 1
	mov eax, DWORD PTR [esp+8]
	cmp esi, eax
	je 21f
	jmp 22f
21:
	mov esi, 0
22:
	mov eax, DWORD PTR [esp+4]
	add eax, esi
	movzx ecx, BYTE PTR [eax]
	ror edx, 24
	or edx, ecx
	add esi, 1
	mov eax, DWORD PTR [esp+8]
	cmp esi, eax
	je 23f
	jmp 24f
23:
	mov esi, 0
24:
	mov eax, DWORD PTR [esp+4]
	add eax, esi
	movzx ecx, BYTE PTR [eax]
	ror edx, 24
	or edx, ecx
	add esi, 1
	mov eax, DWORD PTR [esp+8]
	cmp esi, eax
	je 25f
	jmp 26f
25:
	mov esi, 0
26:
	mov eax, DWORD PTR [esp+4]
	add eax, esi
	movzx ecx, BYTE PTR [eax]
	ror edx, 24
	or edx, ecx
	add esi, 1
	mov eax, DWORD PTR [esp+8]
	cmp esi, eax
	je 27f
	jmp 28f
27:
	mov esi, 0
28:
	mov eax, DWORD PTR [ebx+4096]
	xor eax, edx
	mov DWORD PTR [ebx+4096], eax
	add ebx, 4
	sub edi, 1
	jne 20b
	mov eax, 0
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], eax
	mov ebx, DWORD PTR [esp+12]
	add ebx, 4096
	mov DWORD PTR [ebp+32], ebx
	mov ecx, 9
	mov DWORD PTR [ebp+36], ecx
29:
	mov ebx, DWORD PTR [esp+12]
	add ebx, 4096
	mov DWORD PTR [ebp+28], ebx
210:
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	mov eax, DWORD PTR [ebp+16]
	xor eax, ecx
	mov DWORD PTR [ebp+16], eax
	mov esi, DWORD PTR [ebp+16]
	shr esi, 24
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+12]
211:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+256]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+512]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+768]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -256
	jne 211b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov DWORD PTR [ebp+24], edi
	mov esi, DWORD PTR [ebp+16]
	shr esi, 16
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+12]
212:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+1024]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1280]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1536]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1792]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -256
	jne 212b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	shr esi, 8
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+12]
213:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+2048]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2304]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2560]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2816]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -256
	jne 213b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+12]
214:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+3072]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3328]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3584]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3840]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -256
	jne 214b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+24]
	mov ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+20], ecx
	mov DWORD PTR [ebp+16], eax
	mov ebx, DWORD PTR [ebp+28]
	add ebx, 4
	mov DWORD PTR [ebp+28], ebx
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -4160
	jne 210b
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	xor ecx, DWORD PTR [ebp+16]
	mov eax, DWORD PTR [ebx+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], ecx
	mov ebx, DWORD PTR [ebp+32]
	mov edx, DWORD PTR [ebp+36]
	mov eax, DWORD PTR [ebp+16]
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebx+4], eax
	add ebx, 8
	mov DWORD PTR [ebp+32], ebx
	sub edx, 1
	mov DWORD PTR [ebp+36], edx
	jne 29b
	mov ebx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+32], ebx
	mov ecx, 512
	mov DWORD PTR [ebp+36], ecx
215:
	mov ebx, DWORD PTR [esp+12]
	add ebx, 4096
	mov DWORD PTR [ebp+28], ebx
216:
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	mov eax, DWORD PTR [ebp+16]
	xor eax, ecx
	mov DWORD PTR [ebp+16], eax
	mov esi, DWORD PTR [ebp+16]
	shr esi, 24
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+12]
217:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+256]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+512]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+768]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -256
	jne 217b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov DWORD PTR [ebp+24], edi
	mov esi, DWORD PTR [ebp+16]
	shr esi, 16
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+12]
218:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+1024]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1280]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1536]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1792]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -256
	jne 218b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	shr esi, 8
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+12]
219:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+2048]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2304]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2560]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2816]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -256
	jne 219b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+12]
220:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+3072]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3328]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3584]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3840]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -256
	jne 220b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+24]
	mov ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+20], ecx
	mov DWORD PTR [ebp+16], eax
	mov ebx, DWORD PTR [ebp+28]
	add ebx, 4
	mov DWORD PTR [ebp+28], ebx
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	cmp ecx, -4160
	jne 216b
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	xor ecx, DWORD PTR [ebp+16]
	mov eax, DWORD PTR [ebx+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], ecx
	mov ebx, DWORD PTR [ebp+32]
	mov edx, DWORD PTR [ebp+36]
	mov eax, DWORD PTR [ebp+16]
	mov BYTE PTR [ebx], al
	shr eax, 8
	mov BYTE PTR [ebx+256], al
	shr eax, 8
	mov BYTE PTR [ebx+512], al
	shr eax, 8
	mov BYTE PTR [ebx+768], al
	mov eax, DWORD PTR [ebp+20]
	mov BYTE PTR [ebx+1], al
	shr eax, 8
	mov BYTE PTR [ebx+257], al
	shr eax, 8
	mov BYTE PTR [ebx+513], al
	shr eax, 8
	mov BYTE PTR [ebx+769], al
	add ebx, 2
	mov ecx, DWORD PTR [esp+12]
	sub ecx, ebx
	test ecx, 255
	je 221f
	jmp 222f
221:
	add ebx, 768
222:
	mov DWORD PTR [ebp+32], ebx
	sub edx, 1
	mov DWORD PTR [ebp+36], edx
	jne 215b
	mov ebx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+4]
	mov edi, DWORD PTR [ebp+8]
	mov ebp, DWORD PTR [ebp+12]
	mov ecx, 0
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	lea esp, [esp+84]
	ret
	.p2align 6

vg_blowfish_ecb_encrypt:
	lea esp, [esp-276]
	mov eax, DWORD PTR [esp+280]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+284]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+288]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+36], ecx
	test ecx, ecx
	je 20f
22:
	mov ebx, DWORD PTR [ebp+32]
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 4096
	mov DWORD PTR [ebp+28], ebx
23:
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	mov eax, DWORD PTR [ebp+16]
	xor eax, ecx
	mov DWORD PTR [ebp+16], eax
	mov esi, DWORD PTR [ebp+16]
	shr esi, 24
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
24:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+256]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+512]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+768]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 24b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov DWORD PTR [ebp+24], edi
	mov esi, DWORD PTR [ebp+16]
	shr esi, 16
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
25:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+1024]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1280]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1536]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1792]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 25b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	shr esi, 8
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
26:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+2048]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2304]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2560]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2816]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 26b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
27:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+3072]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3328]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3584]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3840]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 27b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+24]
	mov ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+20], ecx
	mov DWORD PTR [ebp+16], eax
	mov ebx, DWORD PTR [ebp+28]
	add ebx, 4
	mov DWORD PTR [ebp+28], ebx
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -4160
	jne 23b
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx]
	xor ecx, DWORD PTR [ebp+16]
	mov eax, DWORD PTR [ebx+4]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], ecx
	mov ebx, DWORD PTR [ebp+32]
	mov edx, DWORD PTR [ebp+36]
	mov eax, DWORD PTR [ebp+16]
	bswap eax
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [ebp+20]
	bswap eax
	mov DWORD PTR [ebx+4], eax
	add ebx, 8
	mov DWORD PTR [ebp+32], ebx
	sub edx, 1
	mov DWORD PTR [ebp+36], edx
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+4]
	mov edi, DWORD PTR [ebp+8]
	mov ebp, DWORD PTR [ebp+12]
	mov ecx, 0
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	lea esp, [esp+276]
	ret
	.p2align 6

vg_blowfish_ecb_decrypt:
	lea esp, [esp-276]
	mov eax, DWORD PTR [esp+280]
	mov DWORD PTR [esp+4], eax
	mov eax, DWORD PTR [esp+284]
	mov DWORD PTR [esp+8], eax
	mov eax, DWORD PTR [esp+288]
	mov DWORD PTR [esp+12], eax
	mov eax, esp
	add eax, 20
	mov DWORD PTR [esp+16], eax
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov ebp, eax
	mov ecx, DWORD PTR [esp+8]
	mov DWORD PTR [ebp+32], ecx
	mov ecx, DWORD PTR [esp+12]
	mov DWORD PTR [ebp+36], ecx
	test ecx, ecx
	je 20f
22:
	mov ebx, DWORD PTR [ebp+32]
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [ebp+16], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [ebp+20], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 4160
	mov DWORD PTR [ebp+28], ebx
23:
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx+4]
	mov eax, DWORD PTR [ebp+16]
	xor eax, ecx
	mov DWORD PTR [ebp+16], eax
	mov esi, DWORD PTR [ebp+16]
	shr esi, 24
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
24:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+256]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+512]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+768]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 24b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov DWORD PTR [ebp+24], edi
	mov esi, DWORD PTR [ebp+16]
	shr esi, 16
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
25:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+1024]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1280]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1536]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+1792]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 25b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	shr esi, 8
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
26:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+2048]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2304]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2560]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+2816]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 26b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	xor ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov esi, DWORD PTR [ebp+16]
	and esi, 255
	mov eax, 255
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 24
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, eax
	ror ecx, 16
	xor eax, ecx
	and eax, edx
	xor eax, ecx
	mov edi, 0
	mov ebx, DWORD PTR [esp+4]
27:
	cmp esi, 4
	sbb edx, edx
	and edx, eax
	sub esi, 4
	mov ecx, DWORD PTR [ebx+3072]
	and ecx, edx
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3328]
	and ecx, edx
	ror ecx, 24
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3584]
	and ecx, edx
	ror ecx, 16
	or edi, ecx
	mov ecx, DWORD PTR [ebx+3840]
	and ecx, edx
	ror ecx, 8
	or edi, ecx
	add ebx, 4
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -256
	jne 27b
	mov edx, esi
	and edx, 1
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 8
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov edx, esi
	and edx, 2
	cmp edx, 1
	sbb edx, edx
	mov ecx, edi
	ror ecx, 16
	xor edi, ecx
	and edi, edx
	xor edi, ecx
	mov ecx, DWORD PTR [ebp+24]
	add ecx, edi
	mov DWORD PTR [ebp+24], ecx
	mov eax, DWORD PTR [ebp+20]
	xor eax, DWORD PTR [ebp+24]
	mov ecx, DWORD PTR [ebp+16]
	mov DWORD PTR [ebp+20], ecx
	mov DWORD PTR [ebp+16], eax
	mov ebx, DWORD PTR [ebp+28]
	sub ebx, 4
	mov DWORD PTR [ebp+28], ebx
	mov ecx, DWORD PTR [esp+4]
	sub ecx, ebx
	cmp ecx, -4096
	jne 23b
	mov ebx, DWORD PTR [ebp+28]
	mov ecx, DWORD PTR [ebx+4]
	xor ecx, DWORD PTR [ebp+16]
	mov eax, DWORD PTR [ebx]
	xor eax, DWORD PTR [ebp+20]
	mov DWORD PTR [ebp+16], eax
	mov DWORD PTR [ebp+20], ecx
	mov ebx, DWORD PTR [ebp+32]
	mov edx, DWORD PTR [ebp+36]
	mov eax, DWORD PTR [ebp+16]
	bswap eax
	mov DWORD PTR [ebx], eax
	mov eax, DWORD PTR [ebp+20]
	bswap eax
	mov DWORD PTR [ebx+4], eax
	add ebx, 8
	mov DWORD PTR [ebp+32], ebx
	sub edx, 1
	mov DWORD PTR [ebp+36], edx
	jne 22b
	jmp 21f
20:
21:
	mov ebx, DWORD PTR [ebp]
	mov esi, DWORD PTR [ebp+4]
	mov edi, DWORD PTR [ebp+8]
	mov ebp, DWORD PTR [ebp+12]
	mov ecx, 0
	mov DWORD PTR [esp+20], ecx
	mov DWORD PTR [esp+24], ecx
	mov DWORD PTR [esp+28], ecx
	mov DWORD PTR [esp+32], ecx
	mov DWORD PTR [esp+36], ecx
	mov DWORD PTR [esp+40], ecx
	mov DWORD PTR [esp+44], ecx
	mov DWORD PTR [esp+48], ecx
	mov DWORD PTR [esp+52], ecx
	mov DWORD PTR [esp+56], ecx
	lea esp, [esp+276]
	ret
	.p2align 6
