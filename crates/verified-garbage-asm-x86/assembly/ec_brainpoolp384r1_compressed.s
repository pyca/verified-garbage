// The functions of `src/ec_brainpoolp384r1_compressed.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ec_brainpoolp384r1_compress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1596], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1644], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1692], eax
	mov eax, 822602835
	mov DWORD PTR [edi+64], eax
	mov eax, -2025390061
	mov DWORD PTR [edi+68], eax
	mov eax, -1877140879
	mov DWORD PTR [edi+72], eax
	mov eax, -1395415255
	mov DWORD PTR [edi+76], eax
	mov eax, 2142703907
	mov DWORD PTR [edi+80], eax
	mov eax, 313645593
	mov DWORD PTR [edi+84], eax
	mov eax, -313239884
	mov DWORD PTR [edi+88], eax
	mov eax, 355430665
	mov DWORD PTR [edi+92], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+96], eax
	mov eax, 257781630
	mov DWORD PTR [edi+100], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+104], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+108], eax
	mov eax, -385587867
	mov DWORD PTR [edi+112], eax
	mov eax, 998781442
	mov DWORD PTR [edi+116], eax
	mov eax, 1803535120
	mov DWORD PTR [edi+120], eax
	mov eax, -818235729
	mov DWORD PTR [edi+124], eax
	mov eax, -1409014361
	mov DWORD PTR [edi+128], eax
	mov eax, 521563756
	mov DWORD PTR [edi+132], eax
	mov eax, -313239885
	mov DWORD PTR [edi+136], eax
	mov eax, 355430665
	mov DWORD PTR [edi+140], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+144], eax
	mov eax, 257781630
	mov DWORD PTR [edi+148], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+152], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+156], eax
	mov eax, 0
	mov DWORD PTR [edi+208], eax
	mov eax, 0
	mov DWORD PTR [edi+212], eax
	mov eax, 0
	mov DWORD PTR [edi+216], eax
	mov eax, 0
	mov DWORD PTR [edi+220], eax
	mov eax, 0
	mov DWORD PTR [edi+224], eax
	mov eax, 0
	mov DWORD PTR [edi+228], eax
	mov eax, 0
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov DWORD PTR [edi+236], eax
	mov eax, 0
	mov DWORD PTR [edi+240], eax
	mov eax, 0
	mov DWORD PTR [edi+244], eax
	mov eax, 0
	mov DWORD PTR [edi+248], eax
	mov eax, 0
	mov DWORD PTR [edi+252], eax
	mov eax, 1
	mov DWORD PTR [edi+256], eax
	mov eax, 0
	mov DWORD PTR [edi+260], eax
	mov eax, 0
	mov DWORD PTR [edi+264], eax
	mov eax, 0
	mov DWORD PTR [edi+268], eax
	mov eax, 0
	mov DWORD PTR [edi+272], eax
	mov eax, 0
	mov DWORD PTR [edi+276], eax
	mov eax, 0
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov DWORD PTR [edi+284], eax
	mov eax, 0
	mov DWORD PTR [edi+288], eax
	mov eax, 0
	mov DWORD PTR [edi+292], eax
	mov eax, 0
	mov DWORD PTR [edi+296], eax
	mov eax, 0
	mov DWORD PTR [edi+300], eax
	mov eax, -822602835
	mov DWORD PTR [edi+304], eax
	mov eax, 2025390060
	mov DWORD PTR [edi+308], eax
	mov eax, 1877140878
	mov DWORD PTR [edi+312], eax
	mov eax, 1395415254
	mov DWORD PTR [edi+316], eax
	mov eax, -2142703908
	mov DWORD PTR [edi+320], eax
	mov eax, -313645594
	mov DWORD PTR [edi+324], eax
	mov eax, 313239883
	mov DWORD PTR [edi+328], eax
	mov eax, -355430666
	mov DWORD PTR [edi+332], eax
	mov eax, -1357267424
	mov DWORD PTR [edi+336], eax
	mov eax, -257781631
	mov DWORD PTR [edi+340], eax
	mov eax, 1556583127
	mov DWORD PTR [edi+344], eax
	mov eax, 1934025085
	mov DWORD PTR [edi+348], eax
	mov eax, 1181498521
	mov DWORD PTR [edi+352], eax
	mov eax, -618219371
	mov DWORD PTR [edi+356], eax
	mov eax, -245911429
	mov DWORD PTR [edi+360], eax
	mov eax, 1977086974
	mov DWORD PTR [edi+364], eax
	mov eax, -672068172
	mov DWORD PTR [edi+368], eax
	mov eax, -1821937223
	mov DWORD PTR [edi+372], eax
	mov eax, 894604148
	mov DWORD PTR [edi+376], eax
	mov eax, -402658843
	mov DWORD PTR [edi+380], eax
	mov eax, 1118833760
	mov DWORD PTR [edi+384], eax
	mov eax, 1074434015
	mov DWORD PTR [edi+388], eax
	mov eax, -1561804591
	mov DWORD PTR [edi+392], eax
	mov eax, 2083749921
	mov DWORD PTR [edi+396], eax
	mov eax, -783108108
	mov DWORD PTR [edi+400], eax
	mov eax, -708118102
	mov DWORD PTR [edi+404], eax
	mov eax, -789506761
	mov DWORD PTR [edi+408], eax
	mov eax, -172408786
	mov DWORD PTR [edi+412], eax
	mov eax, 1705851754
	mov DWORD PTR [edi+416], eax
	mov eax, 1449863730
	mov DWORD PTR [edi+420], eax
	mov eax, 236168662
	mov DWORD PTR [edi+424], eax
	mov eax, 815019886
	mov DWORD PTR [edi+428], eax
	mov eax, 612445752
	mov DWORD PTR [edi+432], eax
	mov eax, 1916572679
	mov DWORD PTR [edi+436], eax
	mov eax, 362489558
	mov DWORD PTR [edi+440], eax
	mov eax, 1124093550
	mov DWORD PTR [edi+444], eax
	mov eax, -734463039
	mov DWORD PTR [edi+448], eax
	mov eax, -1584800021
	mov DWORD PTR [edi+452], eax
	mov eax, -710375745
	mov DWORD PTR [edi+456], eax
	mov eax, 1727824104
	mov DWORD PTR [edi+460], eax
	mov eax, -1658835165
	mov DWORD PTR [edi+464], eax
	mov eax, -1799128855
	mov DWORD PTR [edi+468], eax
	mov eax, -111402652
	mov DWORD PTR [edi+472], eax
	mov eax, 109782606
	mov DWORD PTR [edi+476], eax
	mov eax, -1160970087
	mov DWORD PTR [edi+480], eax
	mov eax, -1663234609
	mov DWORD PTR [edi+484], eax
	mov eax, -1997193279
	mov DWORD PTR [edi+488], eax
	mov eax, -2063567565
	mov DWORD PTR [edi+492], eax
	mov eax, 232865957
	mov DWORD PTR [edi+496], eax
	mov eax, -415714511
	mov DWORD PTR [edi+500], eax
	mov eax, -946245803
	mov DWORD PTR [edi+504], eax
	mov eax, -169815482
	mov DWORD PTR [edi+508], eax
	mov eax, -1895352324
	mov DWORD PTR [edi+512], eax
	mov eax, -125630045
	mov DWORD PTR [edi+516], eax
	mov eax, -713977321
	mov DWORD PTR [edi+520], eax
	mov eax, -1585402668
	mov DWORD PTR [edi+524], eax
	mov eax, 1327619510
	mov DWORD PTR [edi+528], eax
	mov eax, -971627162
	mov DWORD PTR [edi+532], eax
	mov eax, 1166633141
	mov DWORD PTR [edi+536], eax
	mov eax, 754229346
	mov DWORD PTR [edi+540], eax
	mov eax, -562619250
	mov DWORD PTR [edi+544], eax
	mov eax, -1404120158
	mov DWORD PTR [edi+548], eax
	mov eax, 791374702
	mov DWORD PTR [edi+552], eax
	mov eax, 925257248
	mov DWORD PTR [edi+556], eax
	mov eax, -1744672630
	mov DWORD PTR [edi+560], eax
	mov eax, 714243643
	mov DWORD PTR [edi+564], eax
	mov eax, 1389840639
	mov DWORD PTR [edi+568], eax
	mov eax, 1464497355
	mov DWORD PTR [edi+572], eax
	mov eax, 1695965147
	mov DWORD PTR [edi+576], eax
	mov eax, -1886884407
	mov DWORD PTR [edi+580], eax
	mov eax, 1632540610
	mov DWORD PTR [edi+584], eax
	mov eax, 216568858
	mov DWORD PTR [edi+588], eax
	mov eax, 385587867
	mov DWORD PTR [edi+592], eax
	mov eax, -998781443
	mov DWORD PTR [edi+596], eax
	mov eax, -1803535121
	mov DWORD PTR [edi+600], eax
	mov eax, 818235728
	mov DWORD PTR [edi+604], eax
	mov eax, 1409014360
	mov DWORD PTR [edi+608], eax
	mov eax, -521563757
	mov DWORD PTR [edi+612], eax
	mov eax, 313239884
	mov DWORD PTR [edi+616], eax
	mov eax, -355430666
	mov DWORD PTR [edi+620], eax
	mov eax, -1357267424
	mov DWORD PTR [edi+624], eax
	mov eax, -257781631
	mov DWORD PTR [edi+628], eax
	mov eax, 1556583127
	mov DWORD PTR [edi+632], eax
	mov eax, 1934025085
	mov DWORD PTR [edi+636], eax
	mov eax, 822602833
	mov DWORD PTR [edi+640], eax
	mov eax, -2025390061
	mov DWORD PTR [edi+644], eax
	mov eax, -1877140879
	mov DWORD PTR [edi+648], eax
	mov eax, -1395415255
	mov DWORD PTR [edi+652], eax
	mov eax, 2142703907
	mov DWORD PTR [edi+656], eax
	mov eax, 313645593
	mov DWORD PTR [edi+660], eax
	mov eax, -313239884
	mov DWORD PTR [edi+664], eax
	mov eax, 355430665
	mov DWORD PTR [edi+668], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+672], eax
	mov eax, 257781630
	mov DWORD PTR [edi+676], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+680], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+684], eax
	mov eax, -385587869
	mov DWORD PTR [edi+688], eax
	mov eax, 998781442
	mov DWORD PTR [edi+692], eax
	mov eax, 1803535120
	mov DWORD PTR [edi+696], eax
	mov eax, -818235729
	mov DWORD PTR [edi+700], eax
	mov eax, -1409014361
	mov DWORD PTR [edi+704], eax
	mov eax, 521563756
	mov DWORD PTR [edi+708], eax
	mov eax, -313239885
	mov DWORD PTR [edi+712], eax
	mov eax, 355430665
	mov DWORD PTR [edi+716], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+720], eax
	mov eax, 257781630
	mov DWORD PTR [edi+724], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+728], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+732], eax
	mov eax, 0
	mov DWORD PTR [edi+736], eax
	mov eax, 0
	mov DWORD PTR [edi+740], eax
	mov eax, 0
	mov DWORD PTR [edi+744], eax
	mov eax, 0
	mov DWORD PTR [edi+748], eax
	mov eax, 0
	mov DWORD PTR [edi+752], eax
	mov eax, 0
	mov DWORD PTR [edi+756], eax
	mov eax, 0
	mov DWORD PTR [edi+760], eax
	mov eax, 0
	mov DWORD PTR [edi+764], eax
	mov eax, 0
	mov DWORD PTR [edi+768], eax
	mov eax, 0
	mov DWORD PTR [edi+772], eax
	mov eax, 0
	mov DWORD PTR [edi+776], eax
	mov eax, 0
	mov DWORD PTR [edi+780], eax
	mov eax, -822602835
	mov DWORD PTR [edi+784], eax
	mov eax, 2025390060
	mov DWORD PTR [edi+788], eax
	mov eax, 1877140878
	mov DWORD PTR [edi+792], eax
	mov eax, 1395415254
	mov DWORD PTR [edi+796], eax
	mov eax, -2142703908
	mov DWORD PTR [edi+800], eax
	mov eax, -313645594
	mov DWORD PTR [edi+804], eax
	mov eax, 313239883
	mov DWORD PTR [edi+808], eax
	mov eax, -355430666
	mov DWORD PTR [edi+812], eax
	mov eax, -1357267424
	mov DWORD PTR [edi+816], eax
	mov eax, -257781631
	mov DWORD PTR [edi+820], eax
	mov eax, 1556583127
	mov DWORD PTR [edi+824], eax
	mov eax, 1934025085
	mov DWORD PTR [edi+828], eax
	mov eax, 0
	mov DWORD PTR [edi+832], eax
	mov eax, 0
	mov DWORD PTR [edi+836], eax
	mov eax, 0
	mov DWORD PTR [edi+840], eax
	mov eax, 0
	mov DWORD PTR [edi+844], eax
	mov eax, 0
	mov DWORD PTR [edi+848], eax
	mov eax, 0
	mov DWORD PTR [edi+852], eax
	mov eax, 0
	mov DWORD PTR [edi+856], eax
	mov eax, 0
	mov DWORD PTR [edi+860], eax
	mov eax, 0
	mov DWORD PTR [edi+864], eax
	mov eax, 0
	mov DWORD PTR [edi+868], eax
	mov eax, 0
	mov DWORD PTR [edi+872], eax
	mov eax, 0
	mov DWORD PTR [edi+876], eax
	mov eax, -1
	mov DWORD PTR [edi+2176], eax
	mov eax, 1085688798
	mov DWORD PTR [edi+1936], eax
	mov eax, 142405631
	mov DWORD PTR [edi+1940], eax
	mov eax, 1031788901
	mov DWORD PTR [edi+1944], eax
	mov eax, 1397916468
	mov DWORD PTR [edi+1948], eax
	mov eax, -913045351
	mov DWORD PTR [edi+1952], eax
	mov eax, -1909917284
	mov DWORD PTR [edi+1956], eax
	mov eax, -1726425681
	mov DWORD PTR [edi+1960], eax
	mov eax, 1645478289
	mov DWORD PTR [edi+1964], eax
	mov eax, -1518467796
	mov DWORD PTR [edi+1968], eax
	mov eax, -708382917
	mov DWORD PTR [edi+1972], eax
	mov eax, 395180098
	mov DWORD PTR [edi+1976], eax
	mov eax, 918513795
	mov DWORD PTR [edi+1980], eax
	mov eax, 13164909
	mov DWORD PTR [edi+1984], eax
	mov eax, 520486378
	mov DWORD PTR [edi+1988], eax
	mov eax, 542773219
	mov DWORD PTR [edi+1992], eax
	mov eax, 909047752
	mov DWORD PTR [edi+1996], eax
	mov eax, -148803878
	mov DWORD PTR [edi+2000], eax
	mov eax, -843819325
	mov DWORD PTR [edi+2004], eax
	mov eax, -25690408
	mov DWORD PTR [edi+2008], eax
	mov eax, 390150183
	mov DWORD PTR [edi+2012], eax
	mov eax, -775084707
	mov DWORD PTR [edi+2016], eax
	mov eax, 724784769
	mov DWORD PTR [edi+2020], eax
	mov eax, -398031190
	mov DWORD PTR [edi+2024], eax
	mov eax, 1161678586
	mov DWORD PTR [edi+2028], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1692], eax
	add ebx, 48
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1792], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1796], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1800], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1804], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1808], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1812], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1832], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1836], eax
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	xor edx, 4
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov edx, DWORD PTR [edi+1648]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1652]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1656]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1660]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1664]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1668]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1672]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1676]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+1680]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1684]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+1688]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1692]
	sbb edx, DWORD PTR [edi+108]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov edx, DWORD PTR [edi+1792]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1796]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1800]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1804]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1808]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1812]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1816]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1820]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+1824]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1828]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+1832]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1836]
	sbb edx, DWORD PTR [edi+108]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov eax, 1936
	mov ecx, 1648
	mov edx, 1696
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1936
	mov ecx, 1792
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1744
	mov ecx, 1744
	mov edx, 1840
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1696
	mov ecx, 1696
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1696
	mov ecx, 2032
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1696
	mov ecx, 352
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2032
	mov ecx, 2080
	mov edx, 1888
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1888
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 1840
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+2032]
	or edx, DWORD PTR [edi+2036]
	or edx, DWORD PTR [edi+2040]
	or edx, DWORD PTR [edi+2044]
	or edx, DWORD PTR [edi+2048]
	or edx, DWORD PTR [edi+2052]
	or edx, DWORD PTR [edi+2056]
	or edx, DWORD PTR [edi+2060]
	or edx, DWORD PTR [edi+2064]
	or edx, DWORD PTR [edi+2068]
	or edx, DWORD PTR [edi+2072]
	or edx, DWORD PTR [edi+2076]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov ecx, DWORD PTR [edi+2176]
	mov eax, DWORD PTR [edi+448]
	mov edx, DWORD PTR [edi+1696]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1888], eax
	mov eax, DWORD PTR [edi+452]
	mov edx, DWORD PTR [edi+1700]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1892], eax
	mov eax, DWORD PTR [edi+456]
	mov edx, DWORD PTR [edi+1704]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1896], eax
	mov eax, DWORD PTR [edi+460]
	mov edx, DWORD PTR [edi+1708]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1900], eax
	mov eax, DWORD PTR [edi+464]
	mov edx, DWORD PTR [edi+1712]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1904], eax
	mov eax, DWORD PTR [edi+468]
	mov edx, DWORD PTR [edi+1716]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1908], eax
	mov eax, DWORD PTR [edi+472]
	mov edx, DWORD PTR [edi+1720]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1912], eax
	mov eax, DWORD PTR [edi+476]
	mov edx, DWORD PTR [edi+1724]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1916], eax
	mov eax, DWORD PTR [edi+480]
	mov edx, DWORD PTR [edi+1728]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+484]
	mov edx, DWORD PTR [edi+1732]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+488]
	mov edx, DWORD PTR [edi+1736]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+492]
	mov edx, DWORD PTR [edi+1740]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+496]
	mov edx, DWORD PTR [edi+1744]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2128], eax
	mov eax, DWORD PTR [edi+500]
	mov edx, DWORD PTR [edi+1748]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2132], eax
	mov eax, DWORD PTR [edi+504]
	mov edx, DWORD PTR [edi+1752]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2136], eax
	mov eax, DWORD PTR [edi+508]
	mov edx, DWORD PTR [edi+1756]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2140], eax
	mov eax, DWORD PTR [edi+512]
	mov edx, DWORD PTR [edi+1760]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2144], eax
	mov eax, DWORD PTR [edi+516]
	mov edx, DWORD PTR [edi+1764]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2148], eax
	mov eax, DWORD PTR [edi+520]
	mov edx, DWORD PTR [edi+1768]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [edi+524]
	mov edx, DWORD PTR [edi+1772]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [edi+528]
	mov edx, DWORD PTR [edi+1776]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [edi+532]
	mov edx, DWORD PTR [edi+1780]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [edi+536]
	mov edx, DWORD PTR [edi+1784]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [edi+540]
	mov edx, DWORD PTR [edi+1788]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2172], eax
	mov ecx, DWORD PTR [edi+2176]
	mov ebx, DWORD PTR [esp+4]
	mov eax, DWORD PTR [edi+1792]
	and eax, 1
	or eax, 2
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+45], eax
	mov eax, DWORD PTR [edi+1652]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+41], eax
	mov eax, DWORD PTR [edi+1656]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+37], eax
	mov eax, DWORD PTR [edi+1660]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+33], eax
	mov eax, DWORD PTR [edi+1664]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+29], eax
	mov eax, DWORD PTR [edi+1668]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, DWORD PTR [edi+1672]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+1676]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+1680]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+1684]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+1688]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+1692]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+1], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6

vg_ec_brainpoolp384r1_decompress_public_key:
	mov eax, DWORD PTR [esp+12]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1552], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1556], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1560], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1564], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1568], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1572], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1576], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1580], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1584], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1588], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1592], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1596], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1600], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1604], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1608], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1612], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1616], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1620], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1624], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1628], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1632], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1636], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1640], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1644], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1692], eax
	mov eax, 822602835
	mov DWORD PTR [edi+64], eax
	mov eax, -2025390061
	mov DWORD PTR [edi+68], eax
	mov eax, -1877140879
	mov DWORD PTR [edi+72], eax
	mov eax, -1395415255
	mov DWORD PTR [edi+76], eax
	mov eax, 2142703907
	mov DWORD PTR [edi+80], eax
	mov eax, 313645593
	mov DWORD PTR [edi+84], eax
	mov eax, -313239884
	mov DWORD PTR [edi+88], eax
	mov eax, 355430665
	mov DWORD PTR [edi+92], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+96], eax
	mov eax, 257781630
	mov DWORD PTR [edi+100], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+104], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+108], eax
	mov eax, -385587867
	mov DWORD PTR [edi+112], eax
	mov eax, 998781442
	mov DWORD PTR [edi+116], eax
	mov eax, 1803535120
	mov DWORD PTR [edi+120], eax
	mov eax, -818235729
	mov DWORD PTR [edi+124], eax
	mov eax, -1409014361
	mov DWORD PTR [edi+128], eax
	mov eax, 521563756
	mov DWORD PTR [edi+132], eax
	mov eax, -313239885
	mov DWORD PTR [edi+136], eax
	mov eax, 355430665
	mov DWORD PTR [edi+140], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+144], eax
	mov eax, 257781630
	mov DWORD PTR [edi+148], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+152], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+156], eax
	mov eax, 0
	mov DWORD PTR [edi+208], eax
	mov eax, 0
	mov DWORD PTR [edi+212], eax
	mov eax, 0
	mov DWORD PTR [edi+216], eax
	mov eax, 0
	mov DWORD PTR [edi+220], eax
	mov eax, 0
	mov DWORD PTR [edi+224], eax
	mov eax, 0
	mov DWORD PTR [edi+228], eax
	mov eax, 0
	mov DWORD PTR [edi+232], eax
	mov eax, 0
	mov DWORD PTR [edi+236], eax
	mov eax, 0
	mov DWORD PTR [edi+240], eax
	mov eax, 0
	mov DWORD PTR [edi+244], eax
	mov eax, 0
	mov DWORD PTR [edi+248], eax
	mov eax, 0
	mov DWORD PTR [edi+252], eax
	mov eax, 1
	mov DWORD PTR [edi+256], eax
	mov eax, 0
	mov DWORD PTR [edi+260], eax
	mov eax, 0
	mov DWORD PTR [edi+264], eax
	mov eax, 0
	mov DWORD PTR [edi+268], eax
	mov eax, 0
	mov DWORD PTR [edi+272], eax
	mov eax, 0
	mov DWORD PTR [edi+276], eax
	mov eax, 0
	mov DWORD PTR [edi+280], eax
	mov eax, 0
	mov DWORD PTR [edi+284], eax
	mov eax, 0
	mov DWORD PTR [edi+288], eax
	mov eax, 0
	mov DWORD PTR [edi+292], eax
	mov eax, 0
	mov DWORD PTR [edi+296], eax
	mov eax, 0
	mov DWORD PTR [edi+300], eax
	mov eax, -822602835
	mov DWORD PTR [edi+304], eax
	mov eax, 2025390060
	mov DWORD PTR [edi+308], eax
	mov eax, 1877140878
	mov DWORD PTR [edi+312], eax
	mov eax, 1395415254
	mov DWORD PTR [edi+316], eax
	mov eax, -2142703908
	mov DWORD PTR [edi+320], eax
	mov eax, -313645594
	mov DWORD PTR [edi+324], eax
	mov eax, 313239883
	mov DWORD PTR [edi+328], eax
	mov eax, -355430666
	mov DWORD PTR [edi+332], eax
	mov eax, -1357267424
	mov DWORD PTR [edi+336], eax
	mov eax, -257781631
	mov DWORD PTR [edi+340], eax
	mov eax, 1556583127
	mov DWORD PTR [edi+344], eax
	mov eax, 1934025085
	mov DWORD PTR [edi+348], eax
	mov eax, 1181498521
	mov DWORD PTR [edi+352], eax
	mov eax, -618219371
	mov DWORD PTR [edi+356], eax
	mov eax, -245911429
	mov DWORD PTR [edi+360], eax
	mov eax, 1977086974
	mov DWORD PTR [edi+364], eax
	mov eax, -672068172
	mov DWORD PTR [edi+368], eax
	mov eax, -1821937223
	mov DWORD PTR [edi+372], eax
	mov eax, 894604148
	mov DWORD PTR [edi+376], eax
	mov eax, -402658843
	mov DWORD PTR [edi+380], eax
	mov eax, 1118833760
	mov DWORD PTR [edi+384], eax
	mov eax, 1074434015
	mov DWORD PTR [edi+388], eax
	mov eax, -1561804591
	mov DWORD PTR [edi+392], eax
	mov eax, 2083749921
	mov DWORD PTR [edi+396], eax
	mov eax, -783108108
	mov DWORD PTR [edi+400], eax
	mov eax, -708118102
	mov DWORD PTR [edi+404], eax
	mov eax, -789506761
	mov DWORD PTR [edi+408], eax
	mov eax, -172408786
	mov DWORD PTR [edi+412], eax
	mov eax, 1705851754
	mov DWORD PTR [edi+416], eax
	mov eax, 1449863730
	mov DWORD PTR [edi+420], eax
	mov eax, 236168662
	mov DWORD PTR [edi+424], eax
	mov eax, 815019886
	mov DWORD PTR [edi+428], eax
	mov eax, 612445752
	mov DWORD PTR [edi+432], eax
	mov eax, 1916572679
	mov DWORD PTR [edi+436], eax
	mov eax, 362489558
	mov DWORD PTR [edi+440], eax
	mov eax, 1124093550
	mov DWORD PTR [edi+444], eax
	mov eax, -734463039
	mov DWORD PTR [edi+448], eax
	mov eax, -1584800021
	mov DWORD PTR [edi+452], eax
	mov eax, -710375745
	mov DWORD PTR [edi+456], eax
	mov eax, 1727824104
	mov DWORD PTR [edi+460], eax
	mov eax, -1658835165
	mov DWORD PTR [edi+464], eax
	mov eax, -1799128855
	mov DWORD PTR [edi+468], eax
	mov eax, -111402652
	mov DWORD PTR [edi+472], eax
	mov eax, 109782606
	mov DWORD PTR [edi+476], eax
	mov eax, -1160970087
	mov DWORD PTR [edi+480], eax
	mov eax, -1663234609
	mov DWORD PTR [edi+484], eax
	mov eax, -1997193279
	mov DWORD PTR [edi+488], eax
	mov eax, -2063567565
	mov DWORD PTR [edi+492], eax
	mov eax, 232865957
	mov DWORD PTR [edi+496], eax
	mov eax, -415714511
	mov DWORD PTR [edi+500], eax
	mov eax, -946245803
	mov DWORD PTR [edi+504], eax
	mov eax, -169815482
	mov DWORD PTR [edi+508], eax
	mov eax, -1895352324
	mov DWORD PTR [edi+512], eax
	mov eax, -125630045
	mov DWORD PTR [edi+516], eax
	mov eax, -713977321
	mov DWORD PTR [edi+520], eax
	mov eax, -1585402668
	mov DWORD PTR [edi+524], eax
	mov eax, 1327619510
	mov DWORD PTR [edi+528], eax
	mov eax, -971627162
	mov DWORD PTR [edi+532], eax
	mov eax, 1166633141
	mov DWORD PTR [edi+536], eax
	mov eax, 754229346
	mov DWORD PTR [edi+540], eax
	mov eax, -562619250
	mov DWORD PTR [edi+544], eax
	mov eax, -1404120158
	mov DWORD PTR [edi+548], eax
	mov eax, 791374702
	mov DWORD PTR [edi+552], eax
	mov eax, 925257248
	mov DWORD PTR [edi+556], eax
	mov eax, -1744672630
	mov DWORD PTR [edi+560], eax
	mov eax, 714243643
	mov DWORD PTR [edi+564], eax
	mov eax, 1389840639
	mov DWORD PTR [edi+568], eax
	mov eax, 1464497355
	mov DWORD PTR [edi+572], eax
	mov eax, 1695965147
	mov DWORD PTR [edi+576], eax
	mov eax, -1886884407
	mov DWORD PTR [edi+580], eax
	mov eax, 1632540610
	mov DWORD PTR [edi+584], eax
	mov eax, 216568858
	mov DWORD PTR [edi+588], eax
	mov eax, 385587867
	mov DWORD PTR [edi+592], eax
	mov eax, -998781443
	mov DWORD PTR [edi+596], eax
	mov eax, -1803535121
	mov DWORD PTR [edi+600], eax
	mov eax, 818235728
	mov DWORD PTR [edi+604], eax
	mov eax, 1409014360
	mov DWORD PTR [edi+608], eax
	mov eax, -521563757
	mov DWORD PTR [edi+612], eax
	mov eax, 313239884
	mov DWORD PTR [edi+616], eax
	mov eax, -355430666
	mov DWORD PTR [edi+620], eax
	mov eax, -1357267424
	mov DWORD PTR [edi+624], eax
	mov eax, -257781631
	mov DWORD PTR [edi+628], eax
	mov eax, 1556583127
	mov DWORD PTR [edi+632], eax
	mov eax, 1934025085
	mov DWORD PTR [edi+636], eax
	mov eax, 822602833
	mov DWORD PTR [edi+640], eax
	mov eax, -2025390061
	mov DWORD PTR [edi+644], eax
	mov eax, -1877140879
	mov DWORD PTR [edi+648], eax
	mov eax, -1395415255
	mov DWORD PTR [edi+652], eax
	mov eax, 2142703907
	mov DWORD PTR [edi+656], eax
	mov eax, 313645593
	mov DWORD PTR [edi+660], eax
	mov eax, -313239884
	mov DWORD PTR [edi+664], eax
	mov eax, 355430665
	mov DWORD PTR [edi+668], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+672], eax
	mov eax, 257781630
	mov DWORD PTR [edi+676], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+680], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+684], eax
	mov eax, -385587869
	mov DWORD PTR [edi+688], eax
	mov eax, 998781442
	mov DWORD PTR [edi+692], eax
	mov eax, 1803535120
	mov DWORD PTR [edi+696], eax
	mov eax, -818235729
	mov DWORD PTR [edi+700], eax
	mov eax, -1409014361
	mov DWORD PTR [edi+704], eax
	mov eax, 521563756
	mov DWORD PTR [edi+708], eax
	mov eax, -313239885
	mov DWORD PTR [edi+712], eax
	mov eax, 355430665
	mov DWORD PTR [edi+716], eax
	mov eax, 1357267423
	mov DWORD PTR [edi+720], eax
	mov eax, 257781630
	mov DWORD PTR [edi+724], eax
	mov eax, -1556583128
	mov DWORD PTR [edi+728], eax
	mov eax, -1934025086
	mov DWORD PTR [edi+732], eax
	mov eax, 0
	mov DWORD PTR [edi+736], eax
	mov eax, 0
	mov DWORD PTR [edi+740], eax
	mov eax, 0
	mov DWORD PTR [edi+744], eax
	mov eax, 0
	mov DWORD PTR [edi+748], eax
	mov eax, 0
	mov DWORD PTR [edi+752], eax
	mov eax, 0
	mov DWORD PTR [edi+756], eax
	mov eax, 0
	mov DWORD PTR [edi+760], eax
	mov eax, 0
	mov DWORD PTR [edi+764], eax
	mov eax, 0
	mov DWORD PTR [edi+768], eax
	mov eax, 0
	mov DWORD PTR [edi+772], eax
	mov eax, 0
	mov DWORD PTR [edi+776], eax
	mov eax, 0
	mov DWORD PTR [edi+780], eax
	mov eax, -822602835
	mov DWORD PTR [edi+784], eax
	mov eax, 2025390060
	mov DWORD PTR [edi+788], eax
	mov eax, 1877140878
	mov DWORD PTR [edi+792], eax
	mov eax, 1395415254
	mov DWORD PTR [edi+796], eax
	mov eax, -2142703908
	mov DWORD PTR [edi+800], eax
	mov eax, -313645594
	mov DWORD PTR [edi+804], eax
	mov eax, 313239883
	mov DWORD PTR [edi+808], eax
	mov eax, -355430666
	mov DWORD PTR [edi+812], eax
	mov eax, -1357267424
	mov DWORD PTR [edi+816], eax
	mov eax, -257781631
	mov DWORD PTR [edi+820], eax
	mov eax, 1556583127
	mov DWORD PTR [edi+824], eax
	mov eax, 1934025085
	mov DWORD PTR [edi+828], eax
	mov eax, 0
	mov DWORD PTR [edi+832], eax
	mov eax, 0
	mov DWORD PTR [edi+836], eax
	mov eax, 0
	mov DWORD PTR [edi+840], eax
	mov eax, 0
	mov DWORD PTR [edi+844], eax
	mov eax, 0
	mov DWORD PTR [edi+848], eax
	mov eax, 0
	mov DWORD PTR [edi+852], eax
	mov eax, 0
	mov DWORD PTR [edi+856], eax
	mov eax, 0
	mov DWORD PTR [edi+860], eax
	mov eax, 0
	mov DWORD PTR [edi+864], eax
	mov eax, 0
	mov DWORD PTR [edi+868], eax
	mov eax, 0
	mov DWORD PTR [edi+872], eax
	mov eax, 0
	mov DWORD PTR [edi+876], eax
	mov eax, -1
	mov DWORD PTR [edi+2176], eax
	mov eax, 1085688798
	mov DWORD PTR [edi+1936], eax
	mov eax, 142405631
	mov DWORD PTR [edi+1940], eax
	mov eax, 1031788901
	mov DWORD PTR [edi+1944], eax
	mov eax, 1397916468
	mov DWORD PTR [edi+1948], eax
	mov eax, -913045351
	mov DWORD PTR [edi+1952], eax
	mov eax, -1909917284
	mov DWORD PTR [edi+1956], eax
	mov eax, -1726425681
	mov DWORD PTR [edi+1960], eax
	mov eax, 1645478289
	mov DWORD PTR [edi+1964], eax
	mov eax, -1518467796
	mov DWORD PTR [edi+1968], eax
	mov eax, -708382917
	mov DWORD PTR [edi+1972], eax
	mov eax, 395180098
	mov DWORD PTR [edi+1976], eax
	mov eax, 918513795
	mov DWORD PTR [edi+1980], eax
	mov eax, 13164909
	mov DWORD PTR [edi+1984], eax
	mov eax, 520486378
	mov DWORD PTR [edi+1988], eax
	mov eax, 542773219
	mov DWORD PTR [edi+1992], eax
	mov eax, 909047752
	mov DWORD PTR [edi+1996], eax
	mov eax, -148803878
	mov DWORD PTR [edi+2000], eax
	mov eax, -843819325
	mov DWORD PTR [edi+2004], eax
	mov eax, -25690408
	mov DWORD PTR [edi+2008], eax
	mov eax, 390150183
	mov DWORD PTR [edi+2012], eax
	mov eax, -775084707
	mov DWORD PTR [edi+2016], eax
	mov eax, 724784769
	mov DWORD PTR [edi+2020], eax
	mov eax, -398031190
	mov DWORD PTR [edi+2024], eax
	mov eax, 1161678586
	mov DWORD PTR [edi+2028], eax
	mov ebx, DWORD PTR [esp+8]
	add ebx, 1
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+1648], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+1652], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+1656], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+1660], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+1664], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+1668], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+1672], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+1676], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+1680], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+1684], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+1688], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+1692], eax
	mov ebx, DWORD PTR [esp+8]
	movzx edx, BYTE PTR [ebx]
	mov DWORD PTR [edi+1600], edx
	or edx, 1
	xor edx, 3
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov edx, DWORD PTR [edi+1648]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+1652]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+1656]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+1660]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+1664]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+1668]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+1672]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+1676]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+1680]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+1684]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+1688]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+1692]
	sbb edx, DWORD PTR [edi+108]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov eax, 1936
	mov ecx, 1648
	mov edx, 1696
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1696
	mov ecx, 1696
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1696
	mov ecx, 2032
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1696
	mov ecx, 352
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2032
	mov ecx, 2080
	mov edx, 1888
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1984
	mov ecx, 1888
	mov edx, 2080
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, -868091115
	mov DWORD PTR [edi+640], eax
	mov eax, 1641136132
	mov DWORD PTR [edi+644], eax
	mov eax, 1678198428
	mov DWORD PTR [edi+648], eax
	mov eax, -348853814
	mov DWORD PTR [edi+652], eax
	mov eax, 1609417800
	mov DWORD PTR [edi+656], eax
	mov eax, 78411398
	mov DWORD PTR [edi+660], eax
	mov eax, 2069173677
	mov DWORD PTR [edi+664], eax
	mov eax, -984884158
	mov DWORD PTR [edi+668], eax
	mov eax, -1808166793
	mov DWORD PTR [edi+672], eax
	mov eax, 64445407
	mov DWORD PTR [edi+676], eax
	mov eax, -1462887606
	mov DWORD PTR [edi+680], eax
	mov eax, 590235552
	mov DWORD PTR [edi+684], eax
	mov esi, 48
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+640]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4872], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4873], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4874], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4875], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4876], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4877], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4878], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4879], dl
	test esi, esi
	jne 20b
	mov eax, DWORD PTR [edi+304]
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+308]
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+312]
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+316]
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+320]
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+324]
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+328]
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+332]
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+336]
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+340]
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+344]
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+348]
	mov DWORD PTR [edi+1500], eax
	mov esi, 384
21:
	sub esi, 1
	mov eax, 1456
	mov ecx, 1456
	mov edx, 1456
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 1456
	mov edx, 1504
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4872]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1456]
	mov edx, DWORD PTR [edi+1504]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1456], eax
	mov eax, DWORD PTR [edi+1460]
	mov edx, DWORD PTR [edi+1508]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1460], eax
	mov eax, DWORD PTR [edi+1464]
	mov edx, DWORD PTR [edi+1512]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1464], eax
	mov eax, DWORD PTR [edi+1468]
	mov edx, DWORD PTR [edi+1516]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1468], eax
	mov eax, DWORD PTR [edi+1472]
	mov edx, DWORD PTR [edi+1520]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1472], eax
	mov eax, DWORD PTR [edi+1476]
	mov edx, DWORD PTR [edi+1524]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1476], eax
	mov eax, DWORD PTR [edi+1480]
	mov edx, DWORD PTR [edi+1528]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1480], eax
	mov eax, DWORD PTR [edi+1484]
	mov edx, DWORD PTR [edi+1532]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1484], eax
	mov eax, DWORD PTR [edi+1488]
	mov edx, DWORD PTR [edi+1536]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1488], eax
	mov eax, DWORD PTR [edi+1492]
	mov edx, DWORD PTR [edi+1540]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1492], eax
	mov eax, DWORD PTR [edi+1496]
	mov edx, DWORD PTR [edi+1544]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1496], eax
	mov eax, DWORD PTR [edi+1500]
	mov edx, DWORD PTR [edi+1548]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1500], eax
	test esi, esi
	jne 21b
	mov eax, 256
	mov ecx, 1456
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 208
	mov edx, 1840
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1792]
	mov ecx, DWORD PTR [edi+1600]
	xor ecx, eax
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	mov ecx, edx
	mov eax, DWORD PTR [edi+1792]
	mov edx, DWORD PTR [edi+1840]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1792], eax
	mov eax, DWORD PTR [edi+1796]
	mov edx, DWORD PTR [edi+1844]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1796], eax
	mov eax, DWORD PTR [edi+1800]
	mov edx, DWORD PTR [edi+1848]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1800], eax
	mov eax, DWORD PTR [edi+1804]
	mov edx, DWORD PTR [edi+1852]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1804], eax
	mov eax, DWORD PTR [edi+1808]
	mov edx, DWORD PTR [edi+1856]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1808], eax
	mov eax, DWORD PTR [edi+1812]
	mov edx, DWORD PTR [edi+1860]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1812], eax
	mov eax, DWORD PTR [edi+1816]
	mov edx, DWORD PTR [edi+1864]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1816], eax
	mov eax, DWORD PTR [edi+1820]
	mov edx, DWORD PTR [edi+1868]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1820], eax
	mov eax, DWORD PTR [edi+1824]
	mov edx, DWORD PTR [edi+1872]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1824], eax
	mov eax, DWORD PTR [edi+1828]
	mov edx, DWORD PTR [edi+1876]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1828], eax
	mov eax, DWORD PTR [edi+1832]
	mov edx, DWORD PTR [edi+1880]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1832], eax
	mov eax, DWORD PTR [edi+1836]
	mov edx, DWORD PTR [edi+1884]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1836], eax
	mov eax, 1936
	mov ecx, 1792
	mov edx, 1744
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1744
	mov ecx, 1744
	mov edx, 2032
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2080
	mov ecx, 2032
	mov edx, 1888
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp384r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1888]
	or edx, DWORD PTR [edi+1892]
	or edx, DWORD PTR [edi+1896]
	or edx, DWORD PTR [edi+1900]
	or edx, DWORD PTR [edi+1904]
	or edx, DWORD PTR [edi+1908]
	or edx, DWORD PTR [edi+1912]
	or edx, DWORD PTR [edi+1916]
	or edx, DWORD PTR [edi+1920]
	or edx, DWORD PTR [edi+1924]
	or edx, DWORD PTR [edi+1928]
	or edx, DWORD PTR [edi+1932]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [edi+1792]
	mov ecx, DWORD PTR [edi+1600]
	xor ecx, eax
	and ecx, 1
	mov edx, 0
	sub edx, ecx
	mov ecx, edx
	mov edx, ecx
	add edx, 1
	mov eax, 0
	sub eax, edx
	mov edx, eax
	mov eax, DWORD PTR [edi+2176]
	and eax, edx
	mov DWORD PTR [edi+2176], eax
	mov ecx, DWORD PTR [edi+2176]
	mov ebx, DWORD PTR [esp+4]
	mov eax, 4
	and eax, ecx
	mov BYTE PTR [ebx], al
	mov eax, DWORD PTR [edi+1648]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+45], eax
	mov eax, DWORD PTR [edi+1652]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+41], eax
	mov eax, DWORD PTR [edi+1656]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+37], eax
	mov eax, DWORD PTR [edi+1660]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+33], eax
	mov eax, DWORD PTR [edi+1664]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+29], eax
	mov eax, DWORD PTR [edi+1668]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+25], eax
	mov eax, DWORD PTR [edi+1672]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+21], eax
	mov eax, DWORD PTR [edi+1676]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+17], eax
	mov eax, DWORD PTR [edi+1680]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+13], eax
	mov eax, DWORD PTR [edi+1684]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+9], eax
	mov eax, DWORD PTR [edi+1688]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+5], eax
	mov eax, DWORD PTR [edi+1692]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+1], eax
	mov eax, DWORD PTR [edi+1792]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+93], eax
	mov eax, DWORD PTR [edi+1796]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+89], eax
	mov eax, DWORD PTR [edi+1800]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+85], eax
	mov eax, DWORD PTR [edi+1804]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+81], eax
	mov eax, DWORD PTR [edi+1808]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+77], eax
	mov eax, DWORD PTR [edi+1812]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+73], eax
	mov eax, DWORD PTR [edi+1816]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+69], eax
	mov eax, DWORD PTR [edi+1820]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+65], eax
	mov eax, DWORD PTR [edi+1824]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+61], eax
	mov eax, DWORD PTR [edi+1828]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+57], eax
	mov eax, DWORD PTR [edi+1832]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+53], eax
	mov eax, DWORD PTR [edi+1836]
	and eax, ecx
	bswap eax
	mov DWORD PTR [ebx+49], eax
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
