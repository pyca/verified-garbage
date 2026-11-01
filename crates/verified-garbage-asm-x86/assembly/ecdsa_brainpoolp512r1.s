// The functions of `src/ecdsa_brainpoolp512r1.rs` of `verified-garbage-asm-x86`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ecdsa_brainpoolp512r1_verify:
	mov eax, DWORD PTR [esp+16]
	mov DWORD PTR [eax], ebx
	mov DWORD PTR [eax+4], esi
	mov DWORD PTR [eax+8], edi
	mov DWORD PTR [eax+12], ebp
	mov edi, eax
	mov ebx, DWORD PTR [esp+12]
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2048], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2052], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2056], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2060], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2064], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2068], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2072], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2076], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2080], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2084], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2088], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2092], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2096], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2100], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2104], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2108], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2112], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2116], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2120], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2124], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2128], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2132], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2136], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2140], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2144], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2148], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2152], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2156], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2160], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2164], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2168], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2172], eax
	mov ebx, DWORD PTR [esp+8]
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2220], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2236], eax
	mov eax, 1480214771
	mov DWORD PTR [edi+64], eax
	mov eax, 682254422
	mov DWORD PTR [edi+68], eax
	mov eax, 763545221
	mov DWORD PTR [edi+72], eax
	mov eax, 679608111
	mov DWORD PTR [edi+76], eax
	mov eax, -425492250
	mov DWORD PTR [edi+80], eax
	mov eax, -1362255574
	mov DWORD PTR [edi+84], eax
	mov eax, -1681495998
	mov DWORD PTR [edi+88], eax
	mov eax, 2102237952
	mov DWORD PTR [edi+92], eax
	mov eax, 1882392689
	mov DWORD PTR [edi+96], eax
	mov eax, -698114870
	mov DWORD PTR [edi+100], eax
	mov eax, -1278619122
	mov DWORD PTR [edi+104], eax
	mov eax, -886010445
	mov DWORD PTR [edi+108], eax
	mov eax, 868875271
	mov DWORD PTR [edi+112], eax
	mov eax, 1070917294
	mov DWORD PTR [edi+116], eax
	mov eax, -605436789
	mov DWORD PTR [edi+120], eax
	mov eax, -1428316744
	mov DWORD PTR [edi+124], eax
	mov eax, -1666645911
	mov DWORD PTR [edi+128], eax
	mov eax, -1249405310
	mov DWORD PTR [edi+132], eax
	mov eax, 140368605
	mov DWORD PTR [edi+136], eax
	mov eax, 498193281
	mov DWORD PTR [edi+140], eax
	mov eax, 2141982791
	mov DWORD PTR [edi+144], eax
	mov eax, 1099325721
	mov DWORD PTR [edi+148], eax
	mov eax, 1286153753
	mov DWORD PTR [edi+152], eax
	mov eax, 1430150209
	mov DWORD PTR [edi+156], eax
	mov eax, 1882392688
	mov DWORD PTR [edi+160], eax
	mov eax, -698114870
	mov DWORD PTR [edi+164], eax
	mov eax, -1278619122
	mov DWORD PTR [edi+168], eax
	mov eax, -886010445
	mov DWORD PTR [edi+172], eax
	mov eax, 868875271
	mov DWORD PTR [edi+176], eax
	mov eax, 1070917294
	mov DWORD PTR [edi+180], eax
	mov eax, -605436789
	mov DWORD PTR [edi+184], eax
	mov eax, -1428316744
	mov DWORD PTR [edi+188], eax
	mov eax, 0
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
	mov eax, 0
	mov DWORD PTR [edi+304], eax
	mov eax, 0
	mov DWORD PTR [edi+308], eax
	mov eax, 0
	mov DWORD PTR [edi+312], eax
	mov eax, 0
	mov DWORD PTR [edi+316], eax
	mov eax, 1
	mov DWORD PTR [edi+320], eax
	mov eax, 0
	mov DWORD PTR [edi+324], eax
	mov eax, 0
	mov DWORD PTR [edi+328], eax
	mov eax, 0
	mov DWORD PTR [edi+332], eax
	mov eax, 0
	mov DWORD PTR [edi+336], eax
	mov eax, 0
	mov DWORD PTR [edi+340], eax
	mov eax, 0
	mov DWORD PTR [edi+344], eax
	mov eax, 0
	mov DWORD PTR [edi+348], eax
	mov eax, 0
	mov DWORD PTR [edi+352], eax
	mov eax, 0
	mov DWORD PTR [edi+356], eax
	mov eax, 0
	mov DWORD PTR [edi+360], eax
	mov eax, 0
	mov DWORD PTR [edi+364], eax
	mov eax, 0
	mov DWORD PTR [edi+368], eax
	mov eax, 0
	mov DWORD PTR [edi+372], eax
	mov eax, 0
	mov DWORD PTR [edi+376], eax
	mov eax, 0
	mov DWORD PTR [edi+380], eax
	mov eax, -1480214771
	mov DWORD PTR [edi+384], eax
	mov eax, -682254423
	mov DWORD PTR [edi+388], eax
	mov eax, -763545222
	mov DWORD PTR [edi+392], eax
	mov eax, -679608112
	mov DWORD PTR [edi+396], eax
	mov eax, 425492249
	mov DWORD PTR [edi+400], eax
	mov eax, 1362255573
	mov DWORD PTR [edi+404], eax
	mov eax, 1681495997
	mov DWORD PTR [edi+408], eax
	mov eax, -2102237953
	mov DWORD PTR [edi+412], eax
	mov eax, -1882392690
	mov DWORD PTR [edi+416], eax
	mov eax, 698114869
	mov DWORD PTR [edi+420], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+424], eax
	mov eax, 886010444
	mov DWORD PTR [edi+428], eax
	mov eax, -868875272
	mov DWORD PTR [edi+432], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+436], eax
	mov eax, 605436788
	mov DWORD PTR [edi+440], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+444], eax
	mov eax, -367999930
	mov DWORD PTR [edi+448], eax
	mov eax, -635467212
	mov DWORD PTR [edi+452], eax
	mov eax, -1347956093
	mov DWORD PTR [edi+456], eax
	mov eax, 350524797
	mov DWORD PTR [edi+460], eax
	mov eax, 1182120875
	mov DWORD PTR [edi+464], eax
	mov eax, 1085295474
	mov DWORD PTR [edi+468], eax
	mov eax, -1636923393
	mov DWORD PTR [edi+472], eax
	mov eax, -812711663
	mov DWORD PTR [edi+476], eax
	mov eax, 1065406919
	mov DWORD PTR [edi+480], eax
	mov eax, -1511247672
	mov DWORD PTR [edi+484], eax
	mov eax, -199325832
	mov DWORD PTR [edi+488], eax
	mov eax, 405606233
	mov DWORD PTR [edi+492], eax
	mov eax, -489650932
	mov DWORD PTR [edi+496], eax
	mov eax, -1204058886
	mov DWORD PTR [edi+500], eax
	mov eax, 578628227
	mov DWORD PTR [edi+504], eax
	mov eax, 1589965191
	mov DWORD PTR [edi+508], eax
	mov eax, 176240041
	mov DWORD PTR [edi+512], eax
	mov eax, -925816212
	mov DWORD PTR [edi+516], eax
	mov eax, -2094512105
	mov DWORD PTR [edi+520], eax
	mov eax, -649057240
	mov DWORD PTR [edi+524], eax
	mov eax, -1577980649
	mov DWORD PTR [edi+528], eax
	mov eax, -176862249
	mov DWORD PTR [edi+532], eax
	mov eax, 765514181
	mov DWORD PTR [edi+536], eax
	mov eax, -663947335
	mov DWORD PTR [edi+540], eax
	mov eax, -1976343511
	mov DWORD PTR [edi+544], eax
	mov eax, -247691167
	mov DWORD PTR [edi+548], eax
	mov eax, -1820477879
	mov DWORD PTR [edi+552], eax
	mov eax, -1738639023
	mov DWORD PTR [edi+556], eax
	mov eax, -279510048
	mov DWORD PTR [edi+560], eax
	mov eax, -325824192
	mov DWORD PTR [edi+564], eax
	mov eax, -109975702
	mov DWORD PTR [edi+568], eax
	mov eax, -1811782301
	mov DWORD PTR [edi+572], eax
	mov eax, 1365367251
	mov DWORD PTR [edi+576], eax
	mov eax, -993094135
	mov DWORD PTR [edi+580], eax
	mov eax, 657195684
	mov DWORD PTR [edi+584], eax
	mov eax, 1748913508
	mov DWORD PTR [edi+588], eax
	mov eax, 1844797071
	mov DWORD PTR [edi+592], eax
	mov eax, 883622932
	mov DWORD PTR [edi+596], eax
	mov eax, 348135368
	mov DWORD PTR [edi+600], eax
	mov eax, -2058333291
	mov DWORD PTR [edi+604], eax
	mov eax, -1872984265
	mov DWORD PTR [edi+608], eax
	mov eax, 607377263
	mov DWORD PTR [edi+612], eax
	mov eax, -210944777
	mov DWORD PTR [edi+616], eax
	mov eax, -1296635337
	mov DWORD PTR [edi+620], eax
	mov eax, 7161203
	mov DWORD PTR [edi+624], eax
	mov eax, -2028161590
	mov DWORD PTR [edi+628], eax
	mov eax, 160754049
	mov DWORD PTR [edi+632], eax
	mov eax, 1512808780
	mov DWORD PTR [edi+636], eax
	mov eax, 621029997
	mov DWORD PTR [edi+640], eax
	mov eax, 797992489
	mov DWORD PTR [edi+644], eax
	mov eax, 1195569957
	mov DWORD PTR [edi+648], eax
	mov eax, 1964564335
	mov DWORD PTR [edi+652], eax
	mov eax, 1283822736
	mov DWORD PTR [edi+656], eax
	mov eax, -1081846445
	mov DWORD PTR [edi+660], eax
	mov eax, 1502530622
	mov DWORD PTR [edi+664], eax
	mov eax, 906938229
	mov DWORD PTR [edi+668], eax
	mov eax, -1880739876
	mov DWORD PTR [edi+672], eax
	mov eax, 2081885064
	mov DWORD PTR [edi+676], eax
	mov eax, -845332596
	mov DWORD PTR [edi+680], eax
	mov eax, 1482500983
	mov DWORD PTR [edi+684], eax
	mov eax, -2029043813
	mov DWORD PTR [edi+688], eax
	mov eax, -1705060390
	mov DWORD PTR [edi+692], eax
	mov eax, 717976193
	mov DWORD PTR [edi+696], eax
	mov eax, -1940862511
	mov DWORD PTR [edi+700], eax
	mov eax, -844622223
	mov DWORD PTR [edi+704], eax
	mov eax, -761042914
	mov DWORD PTR [edi+708], eax
	mov eax, -1792524835
	mov DWORD PTR [edi+712], eax
	mov eax, 143046488
	mov DWORD PTR [edi+716], eax
	mov eax, 867656319
	mov DWORD PTR [edi+720], eax
	mov eax, 1053182928
	mov DWORD PTR [edi+724], eax
	mov eax, 788662248
	mov DWORD PTR [edi+728], eax
	mov eax, -1494077241
	mov DWORD PTR [edi+732], eax
	mov eax, 997789155
	mov DWORD PTR [edi+736], eax
	mov eax, -671495130
	mov DWORD PTR [edi+740], eax
	mov eax, 790019039
	mov DWORD PTR [edi+744], eax
	mov eax, 1916549026
	mov DWORD PTR [edi+748], eax
	mov eax, 424357462
	mov DWORD PTR [edi+752], eax
	mov eax, -1780540596
	mov DWORD PTR [edi+756], eax
	mov eax, 1904478128
	mov DWORD PTR [edi+760], eax
	mov eax, -1483450262
	mov DWORD PTR [edi+764], eax
	mov eax, 1666645911
	mov DWORD PTR [edi+768], eax
	mov eax, 1249405309
	mov DWORD PTR [edi+772], eax
	mov eax, -140368606
	mov DWORD PTR [edi+776], eax
	mov eax, -498193282
	mov DWORD PTR [edi+780], eax
	mov eax, -2141982792
	mov DWORD PTR [edi+784], eax
	mov eax, -1099325722
	mov DWORD PTR [edi+788], eax
	mov eax, -1286153754
	mov DWORD PTR [edi+792], eax
	mov eax, -1430150210
	mov DWORD PTR [edi+796], eax
	mov eax, -1882392689
	mov DWORD PTR [edi+800], eax
	mov eax, 698114869
	mov DWORD PTR [edi+804], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+808], eax
	mov eax, 886010444
	mov DWORD PTR [edi+812], eax
	mov eax, -868875272
	mov DWORD PTR [edi+816], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+820], eax
	mov eax, 605436788
	mov DWORD PTR [edi+824], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+828], eax
	mov eax, 1480214769
	mov DWORD PTR [edi+832], eax
	mov eax, 682254422
	mov DWORD PTR [edi+836], eax
	mov eax, 763545221
	mov DWORD PTR [edi+840], eax
	mov eax, 679608111
	mov DWORD PTR [edi+844], eax
	mov eax, -425492250
	mov DWORD PTR [edi+848], eax
	mov eax, -1362255574
	mov DWORD PTR [edi+852], eax
	mov eax, -1681495998
	mov DWORD PTR [edi+856], eax
	mov eax, 2102237952
	mov DWORD PTR [edi+860], eax
	mov eax, 1882392689
	mov DWORD PTR [edi+864], eax
	mov eax, -698114870
	mov DWORD PTR [edi+868], eax
	mov eax, -1278619122
	mov DWORD PTR [edi+872], eax
	mov eax, -886010445
	mov DWORD PTR [edi+876], eax
	mov eax, 868875271
	mov DWORD PTR [edi+880], eax
	mov eax, 1070917294
	mov DWORD PTR [edi+884], eax
	mov eax, -605436789
	mov DWORD PTR [edi+888], eax
	mov eax, -1428316744
	mov DWORD PTR [edi+892], eax
	mov eax, -1666645913
	mov DWORD PTR [edi+896], eax
	mov eax, -1249405310
	mov DWORD PTR [edi+900], eax
	mov eax, 140368605
	mov DWORD PTR [edi+904], eax
	mov eax, 498193281
	mov DWORD PTR [edi+908], eax
	mov eax, 2141982791
	mov DWORD PTR [edi+912], eax
	mov eax, 1099325721
	mov DWORD PTR [edi+916], eax
	mov eax, 1286153753
	mov DWORD PTR [edi+920], eax
	mov eax, 1430150209
	mov DWORD PTR [edi+924], eax
	mov eax, 1882392688
	mov DWORD PTR [edi+928], eax
	mov eax, -698114870
	mov DWORD PTR [edi+932], eax
	mov eax, -1278619122
	mov DWORD PTR [edi+936], eax
	mov eax, -886010445
	mov DWORD PTR [edi+940], eax
	mov eax, 868875271
	mov DWORD PTR [edi+944], eax
	mov eax, 1070917294
	mov DWORD PTR [edi+948], eax
	mov eax, -605436789
	mov DWORD PTR [edi+952], eax
	mov eax, -1428316744
	mov DWORD PTR [edi+956], eax
	mov eax, 0
	mov DWORD PTR [edi+960], eax
	mov eax, 0
	mov DWORD PTR [edi+964], eax
	mov eax, 0
	mov DWORD PTR [edi+968], eax
	mov eax, 0
	mov DWORD PTR [edi+972], eax
	mov eax, 0
	mov DWORD PTR [edi+976], eax
	mov eax, 0
	mov DWORD PTR [edi+980], eax
	mov eax, 0
	mov DWORD PTR [edi+984], eax
	mov eax, 0
	mov DWORD PTR [edi+988], eax
	mov eax, 0
	mov DWORD PTR [edi+992], eax
	mov eax, 0
	mov DWORD PTR [edi+996], eax
	mov eax, 0
	mov DWORD PTR [edi+1000], eax
	mov eax, 0
	mov DWORD PTR [edi+1004], eax
	mov eax, 0
	mov DWORD PTR [edi+1008], eax
	mov eax, 0
	mov DWORD PTR [edi+1012], eax
	mov eax, 0
	mov DWORD PTR [edi+1016], eax
	mov eax, 0
	mov DWORD PTR [edi+1020], eax
	mov eax, -1480214771
	mov DWORD PTR [edi+1024], eax
	mov eax, -682254423
	mov DWORD PTR [edi+1028], eax
	mov eax, -763545222
	mov DWORD PTR [edi+1032], eax
	mov eax, -679608112
	mov DWORD PTR [edi+1036], eax
	mov eax, 425492249
	mov DWORD PTR [edi+1040], eax
	mov eax, 1362255573
	mov DWORD PTR [edi+1044], eax
	mov eax, 1681495997
	mov DWORD PTR [edi+1048], eax
	mov eax, -2102237953
	mov DWORD PTR [edi+1052], eax
	mov eax, -1882392690
	mov DWORD PTR [edi+1056], eax
	mov eax, 698114869
	mov DWORD PTR [edi+1060], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+1064], eax
	mov eax, 886010444
	mov DWORD PTR [edi+1068], eax
	mov eax, -868875272
	mov DWORD PTR [edi+1072], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+1076], eax
	mov eax, 605436788
	mov DWORD PTR [edi+1080], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+1084], eax
	mov eax, 0
	mov DWORD PTR [edi+1088], eax
	mov eax, 0
	mov DWORD PTR [edi+1092], eax
	mov eax, 0
	mov DWORD PTR [edi+1096], eax
	mov eax, 0
	mov DWORD PTR [edi+1100], eax
	mov eax, 0
	mov DWORD PTR [edi+1104], eax
	mov eax, 0
	mov DWORD PTR [edi+1108], eax
	mov eax, 0
	mov DWORD PTR [edi+1112], eax
	mov eax, 0
	mov DWORD PTR [edi+1116], eax
	mov eax, 0
	mov DWORD PTR [edi+1120], eax
	mov eax, 0
	mov DWORD PTR [edi+1124], eax
	mov eax, 0
	mov DWORD PTR [edi+1128], eax
	mov eax, 0
	mov DWORD PTR [edi+1132], eax
	mov eax, 0
	mov DWORD PTR [edi+1136], eax
	mov eax, 0
	mov DWORD PTR [edi+1140], eax
	mov eax, 0
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	mov DWORD PTR [edi+1148], eax
	mov eax, -1
	mov DWORD PTR [edi+2880], eax
	mov esi, 64
20:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+2048]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4096], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4097], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4098], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4099], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4100], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4101], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4102], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4103], dl
	test esi, esi
	jne 20b
	mov esi, 64
21:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+832]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4612], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4613], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4614], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4615], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4616], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4617], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4618], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4619], dl
	test esi, esi
	jne 21b
	mov esi, 64
22:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+896]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+5128], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+5129], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+5130], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+5131], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+5132], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+5133], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+5134], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+5135], dl
	test esi, esi
	jne 22b
	mov ebx, DWORD PTR [esp+12]
	add ebx, 64
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+1984], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+1988], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+1992], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+1996], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2000], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2004], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2008], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2012], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2016], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2020], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2024], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2028], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2032], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2036], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2040], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2044], eax
	mov eax, 1633219077
	mov DWORD PTR [edi+2560], eax
	mov eax, 1236079690
	mov DWORD PTR [edi+2564], eax
	mov eax, 655718661
	mov DWORD PTR [edi+2568], eax
	mov eax, 2034217264
	mov DWORD PTR [edi+2572], eax
	mov eax, -1873084461
	mov DWORD PTR [edi+2576], eax
	mov eax, 1404565948
	mov DWORD PTR [edi+2580], eax
	mov eax, -2091824603
	mov DWORD PTR [edi+2584], eax
	mov eax, -524182921
	mov DWORD PTR [edi+2588], eax
	mov eax, -712409001
	mov DWORD PTR [edi+2592], eax
	mov eax, 424177624
	mov DWORD PTR [edi+2596], eax
	mov eax, -735314045
	mov DWORD PTR [edi+2600], eax
	mov eax, -1586648481
	mov DWORD PTR [edi+2604], eax
	mov eax, 542568140
	mov DWORD PTR [edi+2608], eax
	mov eax, 539892032
	mov DWORD PTR [edi+2612], eax
	mov eax, -1442880432
	mov DWORD PTR [edi+2616], eax
	mov eax, 1011653893
	mov DWORD PTR [edi+2620], eax
	mov eax, 552151604
	mov DWORD PTR [edi+2624], eax
	mov eax, 1350468502
	mov DWORD PTR [edi+2628], eax
	mov eax, -443655628
	mov DWORD PTR [edi+2632], eax
	mov eax, 10183623
	mov DWORD PTR [edi+2636], eax
	mov eax, 763831466
	mov DWORD PTR [edi+2640], eax
	mov eax, -513039274
	mov DWORD PTR [edi+2644], eax
	mov eax, -1736983038
	mov DWORD PTR [edi+2648], eax
	mov eax, -952225560
	mov DWORD PTR [edi+2652], eax
	mov eax, -31316941
	mov DWORD PTR [edi+2656], eax
	mov eax, -1746924445
	mov DWORD PTR [edi+2660], eax
	mov eax, 1830279197
	mov DWORD PTR [edi+2664], eax
	mov eax, -874883156
	mov DWORD PTR [edi+2668], eax
	mov eax, 196455074
	mov DWORD PTR [edi+2672], eax
	mov eax, 1680020133
	mov DWORD PTR [edi+2676], eax
	mov eax, 1193184935
	mov DWORD PTR [edi+2680], eax
	mov eax, 1783278516
	mov DWORD PTR [edi+2684], eax
	mov ebx, DWORD PTR [esp+4]
	add ebx, 1
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2176], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2180], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2184], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2188], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2192], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2196], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2200], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2204], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2208], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2212], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2216], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2220], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2224], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2228], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2232], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2236], eax
	add ebx, 64
	mov eax, DWORD PTR [ebx+60]
	bswap eax
	mov DWORD PTR [edi+2368], eax
	mov eax, DWORD PTR [ebx+56]
	bswap eax
	mov DWORD PTR [edi+2372], eax
	mov eax, DWORD PTR [ebx+52]
	bswap eax
	mov DWORD PTR [edi+2376], eax
	mov eax, DWORD PTR [ebx+48]
	bswap eax
	mov DWORD PTR [edi+2380], eax
	mov eax, DWORD PTR [ebx+44]
	bswap eax
	mov DWORD PTR [edi+2384], eax
	mov eax, DWORD PTR [ebx+40]
	bswap eax
	mov DWORD PTR [edi+2388], eax
	mov eax, DWORD PTR [ebx+36]
	bswap eax
	mov DWORD PTR [edi+2392], eax
	mov eax, DWORD PTR [ebx+32]
	bswap eax
	mov DWORD PTR [edi+2396], eax
	mov eax, DWORD PTR [ebx+28]
	bswap eax
	mov DWORD PTR [edi+2400], eax
	mov eax, DWORD PTR [ebx+24]
	bswap eax
	mov DWORD PTR [edi+2404], eax
	mov eax, DWORD PTR [ebx+20]
	bswap eax
	mov DWORD PTR [edi+2408], eax
	mov eax, DWORD PTR [ebx+16]
	bswap eax
	mov DWORD PTR [edi+2412], eax
	mov eax, DWORD PTR [ebx+12]
	bswap eax
	mov DWORD PTR [edi+2416], eax
	mov eax, DWORD PTR [ebx+8]
	bswap eax
	mov DWORD PTR [edi+2420], eax
	mov eax, DWORD PTR [ebx+4]
	bswap eax
	mov DWORD PTR [edi+2424], eax
	mov eax, DWORD PTR [ebx]
	bswap eax
	mov DWORD PTR [edi+2428], eax
	mov ebx, DWORD PTR [esp+4]
	movzx edx, BYTE PTR [ebx]
	xor edx, 4
	sub edx, 1
	sbb edx, edx
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov edx, DWORD PTR [edi+2176]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+2180]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+2184]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+2188]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+2192]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+2196]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+2200]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+2204]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+2208]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+2212]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+2216]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+2220]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+2224]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+2228]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+2232]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+2236]
	sbb edx, DWORD PTR [edi+124]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov edx, DWORD PTR [edi+2368]
	sub edx, DWORD PTR [edi+64]
	mov edx, DWORD PTR [edi+2372]
	sbb edx, DWORD PTR [edi+68]
	mov edx, DWORD PTR [edi+2376]
	sbb edx, DWORD PTR [edi+72]
	mov edx, DWORD PTR [edi+2380]
	sbb edx, DWORD PTR [edi+76]
	mov edx, DWORD PTR [edi+2384]
	sbb edx, DWORD PTR [edi+80]
	mov edx, DWORD PTR [edi+2388]
	sbb edx, DWORD PTR [edi+84]
	mov edx, DWORD PTR [edi+2392]
	sbb edx, DWORD PTR [edi+88]
	mov edx, DWORD PTR [edi+2396]
	sbb edx, DWORD PTR [edi+92]
	mov edx, DWORD PTR [edi+2400]
	sbb edx, DWORD PTR [edi+96]
	mov edx, DWORD PTR [edi+2404]
	sbb edx, DWORD PTR [edi+100]
	mov edx, DWORD PTR [edi+2408]
	sbb edx, DWORD PTR [edi+104]
	mov edx, DWORD PTR [edi+2412]
	sbb edx, DWORD PTR [edi+108]
	mov edx, DWORD PTR [edi+2416]
	sbb edx, DWORD PTR [edi+112]
	mov edx, DWORD PTR [edi+2420]
	sbb edx, DWORD PTR [edi+116]
	mov edx, DWORD PTR [edi+2424]
	sbb edx, DWORD PTR [edi+120]
	mov edx, DWORD PTR [edi+2428]
	sbb edx, DWORD PTR [edi+124]
	sbb eax, eax
	mov edx, eax
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov eax, 2560
	mov ecx, 2176
	mov edx, 2240
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2560
	mov ecx, 2368
	mov edx, 2304
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2304
	mov ecx, 2304
	mov edx, 2432
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2240
	mov edx, 2688
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 2688
	mov edx, 2752
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2240
	mov ecx, 448
	mov edx, 2688
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2688
	mov ecx, 2752
	mov edx, 2496
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2624
	mov ecx, 2496
	mov edx, 2752
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2752
	mov ecx, 2432
	mov edx, 2688
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+2688]
	or edx, DWORD PTR [edi+2692]
	or edx, DWORD PTR [edi+2696]
	or edx, DWORD PTR [edi+2700]
	or edx, DWORD PTR [edi+2704]
	or edx, DWORD PTR [edi+2708]
	or edx, DWORD PTR [edi+2712]
	or edx, DWORD PTR [edi+2716]
	or edx, DWORD PTR [edi+2720]
	or edx, DWORD PTR [edi+2724]
	or edx, DWORD PTR [edi+2728]
	or edx, DWORD PTR [edi+2732]
	or edx, DWORD PTR [edi+2736]
	or edx, DWORD PTR [edi+2740]
	or edx, DWORD PTR [edi+2744]
	or edx, DWORD PTR [edi+2748]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov ecx, DWORD PTR [edi+2880]
	mov eax, DWORD PTR [edi+576]
	mov edx, DWORD PTR [edi+2240]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2496], eax
	mov eax, DWORD PTR [edi+580]
	mov edx, DWORD PTR [edi+2244]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2500], eax
	mov eax, DWORD PTR [edi+584]
	mov edx, DWORD PTR [edi+2248]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2504], eax
	mov eax, DWORD PTR [edi+588]
	mov edx, DWORD PTR [edi+2252]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2508], eax
	mov eax, DWORD PTR [edi+592]
	mov edx, DWORD PTR [edi+2256]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2512], eax
	mov eax, DWORD PTR [edi+596]
	mov edx, DWORD PTR [edi+2260]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2516], eax
	mov eax, DWORD PTR [edi+600]
	mov edx, DWORD PTR [edi+2264]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2520], eax
	mov eax, DWORD PTR [edi+604]
	mov edx, DWORD PTR [edi+2268]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2524], eax
	mov eax, DWORD PTR [edi+608]
	mov edx, DWORD PTR [edi+2272]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2528], eax
	mov eax, DWORD PTR [edi+612]
	mov edx, DWORD PTR [edi+2276]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2532], eax
	mov eax, DWORD PTR [edi+616]
	mov edx, DWORD PTR [edi+2280]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2536], eax
	mov eax, DWORD PTR [edi+620]
	mov edx, DWORD PTR [edi+2284]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2540], eax
	mov eax, DWORD PTR [edi+624]
	mov edx, DWORD PTR [edi+2288]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2544], eax
	mov eax, DWORD PTR [edi+628]
	mov edx, DWORD PTR [edi+2292]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2548], eax
	mov eax, DWORD PTR [edi+632]
	mov edx, DWORD PTR [edi+2296]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2552], eax
	mov eax, DWORD PTR [edi+636]
	mov edx, DWORD PTR [edi+2300]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2556], eax
	mov eax, DWORD PTR [edi+640]
	mov edx, DWORD PTR [edi+2304]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2816], eax
	mov eax, DWORD PTR [edi+644]
	mov edx, DWORD PTR [edi+2308]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2820], eax
	mov eax, DWORD PTR [edi+648]
	mov edx, DWORD PTR [edi+2312]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2824], eax
	mov eax, DWORD PTR [edi+652]
	mov edx, DWORD PTR [edi+2316]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2828], eax
	mov eax, DWORD PTR [edi+656]
	mov edx, DWORD PTR [edi+2320]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2832], eax
	mov eax, DWORD PTR [edi+660]
	mov edx, DWORD PTR [edi+2324]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2836], eax
	mov eax, DWORD PTR [edi+664]
	mov edx, DWORD PTR [edi+2328]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2840], eax
	mov eax, DWORD PTR [edi+668]
	mov edx, DWORD PTR [edi+2332]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2844], eax
	mov eax, DWORD PTR [edi+672]
	mov edx, DWORD PTR [edi+2336]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2848], eax
	mov eax, DWORD PTR [edi+676]
	mov edx, DWORD PTR [edi+2340]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2852], eax
	mov eax, DWORD PTR [edi+680]
	mov edx, DWORD PTR [edi+2344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2856], eax
	mov eax, DWORD PTR [edi+684]
	mov edx, DWORD PTR [edi+2348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2860], eax
	mov eax, DWORD PTR [edi+688]
	mov edx, DWORD PTR [edi+2352]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2864], eax
	mov eax, DWORD PTR [edi+692]
	mov edx, DWORD PTR [edi+2356]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2868], eax
	mov eax, DWORD PTR [edi+696]
	mov edx, DWORD PTR [edi+2360]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2872], eax
	mov eax, DWORD PTR [edi+700]
	mov edx, DWORD PTR [edi+2364]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+2876], eax
	mov edx, DWORD PTR [edi+2048]
	sub edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+2052]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+2056]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+2060]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+2064]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+2068]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+2072]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+2076]
	sbb edx, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+2080]
	sbb edx, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+2084]
	sbb edx, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+2088]
	sbb edx, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+2092]
	sbb edx, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+2096]
	sbb edx, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+2100]
	sbb edx, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+2104]
	sbb edx, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+2108]
	sbb edx, DWORD PTR [edi+188]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+2048]
	or edx, DWORD PTR [edi+2052]
	or edx, DWORD PTR [edi+2056]
	or edx, DWORD PTR [edi+2060]
	or edx, DWORD PTR [edi+2064]
	or edx, DWORD PTR [edi+2068]
	or edx, DWORD PTR [edi+2072]
	or edx, DWORD PTR [edi+2076]
	or edx, DWORD PTR [edi+2080]
	or edx, DWORD PTR [edi+2084]
	or edx, DWORD PTR [edi+2088]
	or edx, DWORD PTR [edi+2092]
	or edx, DWORD PTR [edi+2096]
	or edx, DWORD PTR [edi+2100]
	or edx, DWORD PTR [edi+2104]
	or edx, DWORD PTR [edi+2108]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov edx, DWORD PTR [edi+1984]
	sub edx, DWORD PTR [edi+128]
	mov edx, DWORD PTR [edi+1988]
	sbb edx, DWORD PTR [edi+132]
	mov edx, DWORD PTR [edi+1992]
	sbb edx, DWORD PTR [edi+136]
	mov edx, DWORD PTR [edi+1996]
	sbb edx, DWORD PTR [edi+140]
	mov edx, DWORD PTR [edi+2000]
	sbb edx, DWORD PTR [edi+144]
	mov edx, DWORD PTR [edi+2004]
	sbb edx, DWORD PTR [edi+148]
	mov edx, DWORD PTR [edi+2008]
	sbb edx, DWORD PTR [edi+152]
	mov edx, DWORD PTR [edi+2012]
	sbb edx, DWORD PTR [edi+156]
	mov edx, DWORD PTR [edi+2016]
	sbb edx, DWORD PTR [edi+160]
	mov edx, DWORD PTR [edi+2020]
	sbb edx, DWORD PTR [edi+164]
	mov edx, DWORD PTR [edi+2024]
	sbb edx, DWORD PTR [edi+168]
	mov edx, DWORD PTR [edi+2028]
	sbb edx, DWORD PTR [edi+172]
	mov edx, DWORD PTR [edi+2032]
	sbb edx, DWORD PTR [edi+176]
	mov edx, DWORD PTR [edi+2036]
	sbb edx, DWORD PTR [edi+180]
	mov edx, DWORD PTR [edi+2040]
	sbb edx, DWORD PTR [edi+184]
	mov edx, DWORD PTR [edi+2044]
	sbb edx, DWORD PTR [edi+188]
	sbb eax, eax
	mov ebx, eax
	mov edx, DWORD PTR [edi+1984]
	or edx, DWORD PTR [edi+1988]
	or edx, DWORD PTR [edi+1992]
	or edx, DWORD PTR [edi+1996]
	or edx, DWORD PTR [edi+2000]
	or edx, DWORD PTR [edi+2004]
	or edx, DWORD PTR [edi+2008]
	or edx, DWORD PTR [edi+2012]
	or edx, DWORD PTR [edi+2016]
	or edx, DWORD PTR [edi+2020]
	or edx, DWORD PTR [edi+2024]
	or edx, DWORD PTR [edi+2028]
	or edx, DWORD PTR [edi+2032]
	or edx, DWORD PTR [edi+2036]
	or edx, DWORD PTR [edi+2040]
	or edx, DWORD PTR [edi+2044]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	and edx, ebx
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov eax, 704
	mov ecx, 1984
	mov edx, 2432
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+768]
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+772]
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+776]
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+780]
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+784]
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+788]
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+792]
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+796]
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+800]
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+804]
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+808]
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+812]
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+816]
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+820]
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+824]
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+828]
	mov DWORD PTR [edi+1980], eax
	mov esi, 512
23:
	sub esi, 1
	mov eax, 1920
	mov ecx, 1920
	mov edx, 1920
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2432
	mov ecx, 1920
	mov edx, 1984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+5128]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1920]
	mov edx, DWORD PTR [edi+1984]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+1924]
	mov edx, DWORD PTR [edi+1988]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+1928]
	mov edx, DWORD PTR [edi+1992]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+1932]
	mov edx, DWORD PTR [edi+1996]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+1936]
	mov edx, DWORD PTR [edi+2000]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+1940]
	mov edx, DWORD PTR [edi+2004]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+1944]
	mov edx, DWORD PTR [edi+2008]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+1948]
	mov edx, DWORD PTR [edi+2012]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+1952]
	mov edx, DWORD PTR [edi+2016]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+1956]
	mov edx, DWORD PTR [edi+2020]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+1960]
	mov edx, DWORD PTR [edi+2024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+1964]
	mov edx, DWORD PTR [edi+2028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+1968]
	mov edx, DWORD PTR [edi+2032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+1972]
	mov edx, DWORD PTR [edi+2036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+1976]
	mov edx, DWORD PTR [edi+2040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+1980]
	mov edx, DWORD PTR [edi+2044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1980], eax
	test esi, esi
	jne 23b
	mov eax, 704
	mov ecx, 2112
	mov edx, 2624
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 2048
	mov edx, 2560
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1920
	mov ecx, 2624
	mov edx, 2688
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1920
	mov ecx, 2560
	mov edx, 2752
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 2688
	mov edx, 2240
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 2752
	mov edx, 2304
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov esi, 64
24:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+2240]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4096], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4097], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4098], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4099], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4100], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4101], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4102], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4103], dl
	test esi, esi
	jne 24b
	mov esi, 512
25:
	sub esi, 1
	mov eax, 960
	mov ecx, 960
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1024
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1088
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 960
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 960
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 960
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 960
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1024
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1024
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 512
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 512
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1728
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1856
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1280
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 576
	mov ecx, 1152
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 1216
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 1280
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1152
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 640
	mov ecx, 576
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 576
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1216
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 640
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 512
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1600
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1600
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 512
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1728
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1344
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1856
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1472
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4096]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1152]
	mov edx, DWORD PTR [edi+1344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+1156]
	mov edx, DWORD PTR [edi+1348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+1160]
	mov edx, DWORD PTR [edi+1352]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+1164]
	mov edx, DWORD PTR [edi+1356]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+1168]
	mov edx, DWORD PTR [edi+1360]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+1172]
	mov edx, DWORD PTR [edi+1364]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+1176]
	mov edx, DWORD PTR [edi+1368]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+1180]
	mov edx, DWORD PTR [edi+1372]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+1184]
	mov edx, DWORD PTR [edi+1376]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+1188]
	mov edx, DWORD PTR [edi+1380]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1192]
	mov edx, DWORD PTR [edi+1384]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1196]
	mov edx, DWORD PTR [edi+1388]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1200]
	mov edx, DWORD PTR [edi+1392]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1204]
	mov edx, DWORD PTR [edi+1396]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1208]
	mov edx, DWORD PTR [edi+1400]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1212]
	mov edx, DWORD PTR [edi+1404]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [edi+1216]
	mov edx, DWORD PTR [edi+1408]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1220]
	mov edx, DWORD PTR [edi+1412]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1224]
	mov edx, DWORD PTR [edi+1416]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1228]
	mov edx, DWORD PTR [edi+1420]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+1232]
	mov edx, DWORD PTR [edi+1424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1236]
	mov edx, DWORD PTR [edi+1428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1240]
	mov edx, DWORD PTR [edi+1432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1244]
	mov edx, DWORD PTR [edi+1436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+1248]
	mov edx, DWORD PTR [edi+1440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1252]
	mov edx, DWORD PTR [edi+1444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1256]
	mov edx, DWORD PTR [edi+1448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1260]
	mov edx, DWORD PTR [edi+1452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+1264]
	mov edx, DWORD PTR [edi+1456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1268]
	mov edx, DWORD PTR [edi+1460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1272]
	mov edx, DWORD PTR [edi+1464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1276]
	mov edx, DWORD PTR [edi+1468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1280]
	mov edx, DWORD PTR [edi+1472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1284]
	mov edx, DWORD PTR [edi+1476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1288]
	mov edx, DWORD PTR [edi+1480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1292]
	mov edx, DWORD PTR [edi+1484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1296]
	mov edx, DWORD PTR [edi+1488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1300]
	mov edx, DWORD PTR [edi+1492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1304]
	mov edx, DWORD PTR [edi+1496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1308]
	mov edx, DWORD PTR [edi+1500]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1312]
	mov edx, DWORD PTR [edi+1504]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1316]
	mov edx, DWORD PTR [edi+1508]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1320]
	mov edx, DWORD PTR [edi+1512]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1324]
	mov edx, DWORD PTR [edi+1516]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1328]
	mov edx, DWORD PTR [edi+1520]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1332]
	mov edx, DWORD PTR [edi+1524]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1336]
	mov edx, DWORD PTR [edi+1528]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1340]
	mov edx, DWORD PTR [edi+1532]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1148], eax
	test esi, esi
	jne 25b
	mov eax, DWORD PTR [edi+960]
	mov DWORD PTR [edi+2688], eax
	mov eax, DWORD PTR [edi+964]
	mov DWORD PTR [edi+2692], eax
	mov eax, DWORD PTR [edi+968]
	mov DWORD PTR [edi+2696], eax
	mov eax, DWORD PTR [edi+972]
	mov DWORD PTR [edi+2700], eax
	mov eax, DWORD PTR [edi+976]
	mov DWORD PTR [edi+2704], eax
	mov eax, DWORD PTR [edi+980]
	mov DWORD PTR [edi+2708], eax
	mov eax, DWORD PTR [edi+984]
	mov DWORD PTR [edi+2712], eax
	mov eax, DWORD PTR [edi+988]
	mov DWORD PTR [edi+2716], eax
	mov eax, DWORD PTR [edi+992]
	mov DWORD PTR [edi+2720], eax
	mov eax, DWORD PTR [edi+996]
	mov DWORD PTR [edi+2724], eax
	mov eax, DWORD PTR [edi+1000]
	mov DWORD PTR [edi+2728], eax
	mov eax, DWORD PTR [edi+1004]
	mov DWORD PTR [edi+2732], eax
	mov eax, DWORD PTR [edi+1008]
	mov DWORD PTR [edi+2736], eax
	mov eax, DWORD PTR [edi+1012]
	mov DWORD PTR [edi+2740], eax
	mov eax, DWORD PTR [edi+1016]
	mov DWORD PTR [edi+2744], eax
	mov eax, DWORD PTR [edi+1020]
	mov DWORD PTR [edi+2748], eax
	mov eax, DWORD PTR [edi+1024]
	mov DWORD PTR [edi+2752], eax
	mov eax, DWORD PTR [edi+1028]
	mov DWORD PTR [edi+2756], eax
	mov eax, DWORD PTR [edi+1032]
	mov DWORD PTR [edi+2760], eax
	mov eax, DWORD PTR [edi+1036]
	mov DWORD PTR [edi+2764], eax
	mov eax, DWORD PTR [edi+1040]
	mov DWORD PTR [edi+2768], eax
	mov eax, DWORD PTR [edi+1044]
	mov DWORD PTR [edi+2772], eax
	mov eax, DWORD PTR [edi+1048]
	mov DWORD PTR [edi+2776], eax
	mov eax, DWORD PTR [edi+1052]
	mov DWORD PTR [edi+2780], eax
	mov eax, DWORD PTR [edi+1056]
	mov DWORD PTR [edi+2784], eax
	mov eax, DWORD PTR [edi+1060]
	mov DWORD PTR [edi+2788], eax
	mov eax, DWORD PTR [edi+1064]
	mov DWORD PTR [edi+2792], eax
	mov eax, DWORD PTR [edi+1068]
	mov DWORD PTR [edi+2796], eax
	mov eax, DWORD PTR [edi+1072]
	mov DWORD PTR [edi+2800], eax
	mov eax, DWORD PTR [edi+1076]
	mov DWORD PTR [edi+2804], eax
	mov eax, DWORD PTR [edi+1080]
	mov DWORD PTR [edi+2808], eax
	mov eax, DWORD PTR [edi+1084]
	mov DWORD PTR [edi+2812], eax
	mov eax, DWORD PTR [edi+1088]
	mov DWORD PTR [edi+2432], eax
	mov eax, DWORD PTR [edi+1092]
	mov DWORD PTR [edi+2436], eax
	mov eax, DWORD PTR [edi+1096]
	mov DWORD PTR [edi+2440], eax
	mov eax, DWORD PTR [edi+1100]
	mov DWORD PTR [edi+2444], eax
	mov eax, DWORD PTR [edi+1104]
	mov DWORD PTR [edi+2448], eax
	mov eax, DWORD PTR [edi+1108]
	mov DWORD PTR [edi+2452], eax
	mov eax, DWORD PTR [edi+1112]
	mov DWORD PTR [edi+2456], eax
	mov eax, DWORD PTR [edi+1116]
	mov DWORD PTR [edi+2460], eax
	mov eax, DWORD PTR [edi+1120]
	mov DWORD PTR [edi+2464], eax
	mov eax, DWORD PTR [edi+1124]
	mov DWORD PTR [edi+2468], eax
	mov eax, DWORD PTR [edi+1128]
	mov DWORD PTR [edi+2472], eax
	mov eax, DWORD PTR [edi+1132]
	mov DWORD PTR [edi+2476], eax
	mov eax, DWORD PTR [edi+1136]
	mov DWORD PTR [edi+2480], eax
	mov eax, DWORD PTR [edi+1140]
	mov DWORD PTR [edi+2484], eax
	mov eax, DWORD PTR [edi+1144]
	mov DWORD PTR [edi+2488], eax
	mov eax, DWORD PTR [edi+1148]
	mov DWORD PTR [edi+2492], eax
	mov eax, 0
	mov DWORD PTR [edi+960], eax
	mov eax, 0
	mov DWORD PTR [edi+964], eax
	mov eax, 0
	mov DWORD PTR [edi+968], eax
	mov eax, 0
	mov DWORD PTR [edi+972], eax
	mov eax, 0
	mov DWORD PTR [edi+976], eax
	mov eax, 0
	mov DWORD PTR [edi+980], eax
	mov eax, 0
	mov DWORD PTR [edi+984], eax
	mov eax, 0
	mov DWORD PTR [edi+988], eax
	mov eax, 0
	mov DWORD PTR [edi+992], eax
	mov eax, 0
	mov DWORD PTR [edi+996], eax
	mov eax, 0
	mov DWORD PTR [edi+1000], eax
	mov eax, 0
	mov DWORD PTR [edi+1004], eax
	mov eax, 0
	mov DWORD PTR [edi+1008], eax
	mov eax, 0
	mov DWORD PTR [edi+1012], eax
	mov eax, 0
	mov DWORD PTR [edi+1016], eax
	mov eax, 0
	mov DWORD PTR [edi+1020], eax
	mov eax, -1480214771
	mov DWORD PTR [edi+1024], eax
	mov eax, -682254423
	mov DWORD PTR [edi+1028], eax
	mov eax, -763545222
	mov DWORD PTR [edi+1032], eax
	mov eax, -679608112
	mov DWORD PTR [edi+1036], eax
	mov eax, 425492249
	mov DWORD PTR [edi+1040], eax
	mov eax, 1362255573
	mov DWORD PTR [edi+1044], eax
	mov eax, 1681495997
	mov DWORD PTR [edi+1048], eax
	mov eax, -2102237953
	mov DWORD PTR [edi+1052], eax
	mov eax, -1882392690
	mov DWORD PTR [edi+1056], eax
	mov eax, 698114869
	mov DWORD PTR [edi+1060], eax
	mov eax, 1278619121
	mov DWORD PTR [edi+1064], eax
	mov eax, 886010444
	mov DWORD PTR [edi+1068], eax
	mov eax, -868875272
	mov DWORD PTR [edi+1072], eax
	mov eax, -1070917295
	mov DWORD PTR [edi+1076], eax
	mov eax, 605436788
	mov DWORD PTR [edi+1080], eax
	mov eax, 1428316743
	mov DWORD PTR [edi+1084], eax
	mov eax, 0
	mov DWORD PTR [edi+1088], eax
	mov eax, 0
	mov DWORD PTR [edi+1092], eax
	mov eax, 0
	mov DWORD PTR [edi+1096], eax
	mov eax, 0
	mov DWORD PTR [edi+1100], eax
	mov eax, 0
	mov DWORD PTR [edi+1104], eax
	mov eax, 0
	mov DWORD PTR [edi+1108], eax
	mov eax, 0
	mov DWORD PTR [edi+1112], eax
	mov eax, 0
	mov DWORD PTR [edi+1116], eax
	mov eax, 0
	mov DWORD PTR [edi+1120], eax
	mov eax, 0
	mov DWORD PTR [edi+1124], eax
	mov eax, 0
	mov DWORD PTR [edi+1128], eax
	mov eax, 0
	mov DWORD PTR [edi+1132], eax
	mov eax, 0
	mov DWORD PTR [edi+1136], eax
	mov eax, 0
	mov DWORD PTR [edi+1140], eax
	mov eax, 0
	mov DWORD PTR [edi+1144], eax
	mov eax, 0
	mov DWORD PTR [edi+1148], eax
	mov esi, 64
26:
	sub esi, 1
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+2304]
	mov ebx, esi
	add ebx, ebx
	add ebx, ebx
	add ebx, ebx
	add ebx, edi
	mov edx, eax
	and edx, 1
	mov BYTE PTR [ebx+4096], dl
	mov edx, eax
	shr edx, 1
	and edx, 1
	mov BYTE PTR [ebx+4097], dl
	mov edx, eax
	shr edx, 2
	and edx, 1
	mov BYTE PTR [ebx+4098], dl
	mov edx, eax
	shr edx, 3
	and edx, 1
	mov BYTE PTR [ebx+4099], dl
	mov edx, eax
	shr edx, 4
	and edx, 1
	mov BYTE PTR [ebx+4100], dl
	mov edx, eax
	shr edx, 5
	and edx, 1
	mov BYTE PTR [ebx+4101], dl
	mov edx, eax
	shr edx, 6
	and edx, 1
	mov BYTE PTR [ebx+4102], dl
	mov edx, eax
	shr edx, 7
	and edx, 1
	mov BYTE PTR [ebx+4103], dl
	test esi, esi
	jne 26b
	mov esi, 512
27:
	sub esi, 1
	mov eax, 960
	mov ecx, 960
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 1024
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1088
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 960
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 960
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 960
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 960
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1024
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1024
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 512
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 512
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1728
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1856
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1280
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2496
	mov ecx, 1152
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2816
	mov ecx, 1216
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 1280
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1216
	mov ecx, 1152
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2816
	mov ecx, 2496
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 2496
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1216
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 384
	mov ecx, 2816
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 512
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1600
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1600
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1344
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 512
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1408
	mov edx, 1408
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1344
	mov ecx, 1728
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1344
	mov edx, 1344
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1472
	mov ecx, 1856
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1472
	mov edx, 1472
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4096]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1152]
	mov edx, DWORD PTR [edi+1344]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+1156]
	mov edx, DWORD PTR [edi+1348]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+1160]
	mov edx, DWORD PTR [edi+1352]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+1164]
	mov edx, DWORD PTR [edi+1356]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+1168]
	mov edx, DWORD PTR [edi+1360]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+1172]
	mov edx, DWORD PTR [edi+1364]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+1176]
	mov edx, DWORD PTR [edi+1368]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+1180]
	mov edx, DWORD PTR [edi+1372]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+1184]
	mov edx, DWORD PTR [edi+1376]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+1188]
	mov edx, DWORD PTR [edi+1380]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1192]
	mov edx, DWORD PTR [edi+1384]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1196]
	mov edx, DWORD PTR [edi+1388]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1200]
	mov edx, DWORD PTR [edi+1392]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1204]
	mov edx, DWORD PTR [edi+1396]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1208]
	mov edx, DWORD PTR [edi+1400]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1212]
	mov edx, DWORD PTR [edi+1404]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [edi+1216]
	mov edx, DWORD PTR [edi+1408]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1220]
	mov edx, DWORD PTR [edi+1412]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1224]
	mov edx, DWORD PTR [edi+1416]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1228]
	mov edx, DWORD PTR [edi+1420]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+1232]
	mov edx, DWORD PTR [edi+1424]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1236]
	mov edx, DWORD PTR [edi+1428]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1240]
	mov edx, DWORD PTR [edi+1432]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1244]
	mov edx, DWORD PTR [edi+1436]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+1248]
	mov edx, DWORD PTR [edi+1440]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1252]
	mov edx, DWORD PTR [edi+1444]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1256]
	mov edx, DWORD PTR [edi+1448]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1260]
	mov edx, DWORD PTR [edi+1452]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+1264]
	mov edx, DWORD PTR [edi+1456]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1268]
	mov edx, DWORD PTR [edi+1460]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1272]
	mov edx, DWORD PTR [edi+1464]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1276]
	mov edx, DWORD PTR [edi+1468]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1280]
	mov edx, DWORD PTR [edi+1472]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1284]
	mov edx, DWORD PTR [edi+1476]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1288]
	mov edx, DWORD PTR [edi+1480]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1292]
	mov edx, DWORD PTR [edi+1484]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1296]
	mov edx, DWORD PTR [edi+1488]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1300]
	mov edx, DWORD PTR [edi+1492]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1304]
	mov edx, DWORD PTR [edi+1496]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1308]
	mov edx, DWORD PTR [edi+1500]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1312]
	mov edx, DWORD PTR [edi+1504]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1316]
	mov edx, DWORD PTR [edi+1508]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1320]
	mov edx, DWORD PTR [edi+1512]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1324]
	mov edx, DWORD PTR [edi+1516]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1328]
	mov edx, DWORD PTR [edi+1520]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1332]
	mov edx, DWORD PTR [edi+1524]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1336]
	mov edx, DWORD PTR [edi+1528]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1340]
	mov edx, DWORD PTR [edi+1532]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1148], eax
	test esi, esi
	jne 27b
	mov eax, 960
	mov ecx, 2688
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 2752
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 2432
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2752
	mov ecx, 2688
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1024
	mov ecx, 960
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1536
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1728
	mov edx, 1728
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2432
	mov ecx, 2688
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 960
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1856
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2432
	mov ecx, 2752
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1024
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1856
	mov edx, 1856
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 448
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 512
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1600
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1152
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1536
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 512
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1600
	mov edx, 1600
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1536
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 448
	mov edx, 1664
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1664
	mov ecx, 1792
	mov edx, 1792
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1600
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1216
	mov edx, 1216
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1792
	mov ecx, 1856
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1152
	mov ecx, 1728
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1152
	mov edx, 1152
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1600
	mov ecx, 1728
	mov edx, 1536
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1280
	mov ecx, 1856
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1536
	mov ecx, 1280
	mov edx, 1280
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_add_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, DWORD PTR [edi+1152]
	mov DWORD PTR [edi+960], eax
	mov eax, DWORD PTR [edi+1156]
	mov DWORD PTR [edi+964], eax
	mov eax, DWORD PTR [edi+1160]
	mov DWORD PTR [edi+968], eax
	mov eax, DWORD PTR [edi+1164]
	mov DWORD PTR [edi+972], eax
	mov eax, DWORD PTR [edi+1168]
	mov DWORD PTR [edi+976], eax
	mov eax, DWORD PTR [edi+1172]
	mov DWORD PTR [edi+980], eax
	mov eax, DWORD PTR [edi+1176]
	mov DWORD PTR [edi+984], eax
	mov eax, DWORD PTR [edi+1180]
	mov DWORD PTR [edi+988], eax
	mov eax, DWORD PTR [edi+1184]
	mov DWORD PTR [edi+992], eax
	mov eax, DWORD PTR [edi+1188]
	mov DWORD PTR [edi+996], eax
	mov eax, DWORD PTR [edi+1192]
	mov DWORD PTR [edi+1000], eax
	mov eax, DWORD PTR [edi+1196]
	mov DWORD PTR [edi+1004], eax
	mov eax, DWORD PTR [edi+1200]
	mov DWORD PTR [edi+1008], eax
	mov eax, DWORD PTR [edi+1204]
	mov DWORD PTR [edi+1012], eax
	mov eax, DWORD PTR [edi+1208]
	mov DWORD PTR [edi+1016], eax
	mov eax, DWORD PTR [edi+1212]
	mov DWORD PTR [edi+1020], eax
	mov eax, DWORD PTR [edi+1216]
	mov DWORD PTR [edi+1024], eax
	mov eax, DWORD PTR [edi+1220]
	mov DWORD PTR [edi+1028], eax
	mov eax, DWORD PTR [edi+1224]
	mov DWORD PTR [edi+1032], eax
	mov eax, DWORD PTR [edi+1228]
	mov DWORD PTR [edi+1036], eax
	mov eax, DWORD PTR [edi+1232]
	mov DWORD PTR [edi+1040], eax
	mov eax, DWORD PTR [edi+1236]
	mov DWORD PTR [edi+1044], eax
	mov eax, DWORD PTR [edi+1240]
	mov DWORD PTR [edi+1048], eax
	mov eax, DWORD PTR [edi+1244]
	mov DWORD PTR [edi+1052], eax
	mov eax, DWORD PTR [edi+1248]
	mov DWORD PTR [edi+1056], eax
	mov eax, DWORD PTR [edi+1252]
	mov DWORD PTR [edi+1060], eax
	mov eax, DWORD PTR [edi+1256]
	mov DWORD PTR [edi+1064], eax
	mov eax, DWORD PTR [edi+1260]
	mov DWORD PTR [edi+1068], eax
	mov eax, DWORD PTR [edi+1264]
	mov DWORD PTR [edi+1072], eax
	mov eax, DWORD PTR [edi+1268]
	mov DWORD PTR [edi+1076], eax
	mov eax, DWORD PTR [edi+1272]
	mov DWORD PTR [edi+1080], eax
	mov eax, DWORD PTR [edi+1276]
	mov DWORD PTR [edi+1084], eax
	mov eax, DWORD PTR [edi+1280]
	mov DWORD PTR [edi+1088], eax
	mov eax, DWORD PTR [edi+1284]
	mov DWORD PTR [edi+1092], eax
	mov eax, DWORD PTR [edi+1288]
	mov DWORD PTR [edi+1096], eax
	mov eax, DWORD PTR [edi+1292]
	mov DWORD PTR [edi+1100], eax
	mov eax, DWORD PTR [edi+1296]
	mov DWORD PTR [edi+1104], eax
	mov eax, DWORD PTR [edi+1300]
	mov DWORD PTR [edi+1108], eax
	mov eax, DWORD PTR [edi+1304]
	mov DWORD PTR [edi+1112], eax
	mov eax, DWORD PTR [edi+1308]
	mov DWORD PTR [edi+1116], eax
	mov eax, DWORD PTR [edi+1312]
	mov DWORD PTR [edi+1120], eax
	mov eax, DWORD PTR [edi+1316]
	mov DWORD PTR [edi+1124], eax
	mov eax, DWORD PTR [edi+1320]
	mov DWORD PTR [edi+1128], eax
	mov eax, DWORD PTR [edi+1324]
	mov DWORD PTR [edi+1132], eax
	mov eax, DWORD PTR [edi+1328]
	mov DWORD PTR [edi+1136], eax
	mov eax, DWORD PTR [edi+1332]
	mov DWORD PTR [edi+1140], eax
	mov eax, DWORD PTR [edi+1336]
	mov DWORD PTR [edi+1144], eax
	mov eax, DWORD PTR [edi+1340]
	mov DWORD PTR [edi+1148], eax
	mov eax, DWORD PTR [edi+384]
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+388]
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+392]
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+396]
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+400]
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+404]
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+408]
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+412]
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+416]
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+420]
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+424]
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+428]
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+432]
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+436]
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+440]
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+444]
	mov DWORD PTR [edi+1980], eax
	mov esi, 512
28:
	sub esi, 1
	mov eax, 1920
	mov ecx, 1920
	mov edx, 1920
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 1088
	mov ecx, 1920
	mov edx, 1984
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, edi
	add eax, esi
	movzx eax, BYTE PTR [eax+4612]
	mov ecx, 0
	sub ecx, eax
	mov eax, DWORD PTR [edi+1920]
	mov edx, DWORD PTR [edi+1984]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1920], eax
	mov eax, DWORD PTR [edi+1924]
	mov edx, DWORD PTR [edi+1988]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1924], eax
	mov eax, DWORD PTR [edi+1928]
	mov edx, DWORD PTR [edi+1992]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1928], eax
	mov eax, DWORD PTR [edi+1932]
	mov edx, DWORD PTR [edi+1996]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1932], eax
	mov eax, DWORD PTR [edi+1936]
	mov edx, DWORD PTR [edi+2000]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1936], eax
	mov eax, DWORD PTR [edi+1940]
	mov edx, DWORD PTR [edi+2004]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1940], eax
	mov eax, DWORD PTR [edi+1944]
	mov edx, DWORD PTR [edi+2008]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1944], eax
	mov eax, DWORD PTR [edi+1948]
	mov edx, DWORD PTR [edi+2012]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1948], eax
	mov eax, DWORD PTR [edi+1952]
	mov edx, DWORD PTR [edi+2016]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1952], eax
	mov eax, DWORD PTR [edi+1956]
	mov edx, DWORD PTR [edi+2020]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1956], eax
	mov eax, DWORD PTR [edi+1960]
	mov edx, DWORD PTR [edi+2024]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1960], eax
	mov eax, DWORD PTR [edi+1964]
	mov edx, DWORD PTR [edi+2028]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1964], eax
	mov eax, DWORD PTR [edi+1968]
	mov edx, DWORD PTR [edi+2032]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1968], eax
	mov eax, DWORD PTR [edi+1972]
	mov edx, DWORD PTR [edi+2036]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1972], eax
	mov eax, DWORD PTR [edi+1976]
	mov edx, DWORD PTR [edi+2040]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1976], eax
	mov eax, DWORD PTR [edi+1980]
	mov edx, DWORD PTR [edi+2044]
	xor edx, eax
	and edx, ecx
	xor eax, edx
	mov DWORD PTR [edi+1980], eax
	test esi, esi
	jne 28b
	mov eax, 1920
	mov ecx, 960
	mov edx, 2240
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 320
	mov ecx, 2240
	mov edx, 2304
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_p}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 704
	mov ecx, 2304
	mov edx, 2496
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_mul_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov eax, 2560
	mov ecx, 2496
	mov edx, 2624
	push eax
	push ecx
	push edx
	push edi
	call {vg_brainpoolp512r1_sub_mod_n}
	pop eax
	pop eax
	pop eax
	pop eax
	mov edx, DWORD PTR [edi+1088]
	or edx, DWORD PTR [edi+1092]
	or edx, DWORD PTR [edi+1096]
	or edx, DWORD PTR [edi+1100]
	or edx, DWORD PTR [edi+1104]
	or edx, DWORD PTR [edi+1108]
	or edx, DWORD PTR [edi+1112]
	or edx, DWORD PTR [edi+1116]
	or edx, DWORD PTR [edi+1120]
	or edx, DWORD PTR [edi+1124]
	or edx, DWORD PTR [edi+1128]
	or edx, DWORD PTR [edi+1132]
	or edx, DWORD PTR [edi+1136]
	or edx, DWORD PTR [edi+1140]
	or edx, DWORD PTR [edi+1144]
	or edx, DWORD PTR [edi+1148]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov edx, DWORD PTR [edi+2624]
	or edx, DWORD PTR [edi+2628]
	or edx, DWORD PTR [edi+2632]
	or edx, DWORD PTR [edi+2636]
	or edx, DWORD PTR [edi+2640]
	or edx, DWORD PTR [edi+2644]
	or edx, DWORD PTR [edi+2648]
	or edx, DWORD PTR [edi+2652]
	or edx, DWORD PTR [edi+2656]
	or edx, DWORD PTR [edi+2660]
	or edx, DWORD PTR [edi+2664]
	or edx, DWORD PTR [edi+2668]
	or edx, DWORD PTR [edi+2672]
	or edx, DWORD PTR [edi+2676]
	or edx, DWORD PTR [edi+2680]
	or edx, DWORD PTR [edi+2684]
	mov ecx, 0
	sub ecx, edx
	sbb edx, edx
	xor edx, -1
	mov eax, DWORD PTR [edi+2880]
	and eax, edx
	mov DWORD PTR [edi+2880], eax
	mov ecx, DWORD PTR [edi+2880]
	mov eax, ecx
	and eax, 1
	mov edx, edi
	mov ebx, DWORD PTR [edx]
	mov esi, DWORD PTR [edx+4]
	mov ebp, DWORD PTR [edx+12]
	mov edi, DWORD PTR [edx+8]
	ret
	.p2align 6
